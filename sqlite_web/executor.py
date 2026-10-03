import base64
import json
import os
import re
import sqlite3
import tempfile
import time
from dataclasses import dataclass, field
from urllib.parse import quote

from peewee import DatabaseError
from peewee import SqliteDatabase
from peewee import sqlite3
from playhouse.dataset import DataSet


@dataclass
class Result:
    kind: str  # 'rows', 'affected', 'error'
    statement: str = ''
    columns: list = field(default_factory=list)
    rows: list = field(default_factory=list)
    keys: list = None  # Encoded row keys.
    has_next: bool = False
    affected: int = -1
    error: str = ''
    duration: float = 0.0  # Milliseconds spent executing the statement.


def wrap(sql, ordering=None, limit=None, offset=0, select='*'):
    # The one place user sql gets wrapped in a subselect. The \n before
    # the closing paren terminates any trailing "--..." comment.
    wrapped = 'SELECT %s FROM (\n%s\n) AS _' % (
        select, sql.rstrip('; \t\r\n'))
    if ordering:
        wrapped += ' ORDER BY %d %s' % (abs(ordering),
                                        'DESC' if ordering < 0 else 'ASC')
    if limit is not None:
        wrapped += ' LIMIT %d OFFSET %d' % (limit, offset)
    return wrapped


def run_one(dataset, sql, page=1, page_size=50, ordering=None):
    # The query box allows whatever kinds of query/ies. We wrap the user query
    # to provide ordering + pagination, but cannot wrap DDL or DML statements.
    # Rather than try to parse the user SQL, attempt to wrap + execute (this
    # only works for SELECTs), and on failure fall-back to unwrapped.
    page = max(page, 1)
    started = time.perf_counter()
    try:
        # Fetch page_size + 1 rows so a "next" page can be detected.
        cursor = dataset.query(wrap(sql, ordering, page_size + 1,
                                    (page - 1) * page_size))
        paged = True
    except DatabaseError:
        try:
            cursor = dataset.query(sql)
            paged = False
        except Exception as exc:
            return Result('error', sql, error=str(exc),
                          duration=_elapsed(started))

    if cursor.description is None:
        return Result('affected', sql, affected=cursor.rowcount,
                      duration=_elapsed(started))

    columns = [d[0] for d in cursor.description]
    rows = cursor.fetchall()
    return Result(
        'rows',
        sql,
        columns=columns,
        rows=rows[:page_size] if paged else rows,
        has_next=paged and len(rows) > page_size,
        duration=_elapsed(started))


def split_statements(script):
    stmts, buf = [], ''
    for ch in script:
        buf += ch
        if ch == ';' and sqlite3.complete_statement(buf):
            if buf.strip():
                stmts.append(buf.strip())
            buf = ''
    if buf.strip():
        stmts.append(buf.strip())
    return stmts


def run_script(dataset, statements, page_size=50):
    # Allow running multiple statements from the query box.
    results = []
    for stmt in statements:
        result = run_one(dataset, stmt, page_size=page_size)
        results.append(result)
        if result.kind == 'error':
            break
    return results


def is_read(dataset, sql):
    try:
        dataset.query(wrap(sql, limit=0))
        return True
    except DatabaseError:
        return False


#
# Atomic script execution.
#

# Keywords that put the connection into (or out of) a self-managed
# transaction. Scripts containing them cannot be wrapped in our own
# transaction, so they are refused rather than half-applied.
_TXN_CONTROL_RE = re.compile(
    r'\b(BEGIN|COMMIT|END|RELEASE|SAVEPOINT|ROLLBACK)\b', re.I)

# ATTACH/DETACH reach database files outside the main one. Writes to an
# attached database are not covered by the main transaction (they commit
# independently), and a preview snapshot must never touch a file outside
# its temporary copy, so they are refused.
_ATTACH_RE = re.compile(r'\b(ATTACH|DETACH)\b', re.I)


def strip_comments(sql):
    # Remove SQL comments while keeping string literals intact. The result
    # is used only for keyword detection.
    out, i, n = [], 0, len(sql)
    quote = None
    while i < n:
        ch = sql[i]
        if quote:
            out.append(ch)
            if ch == quote:
                # A doubled quote is an escaped quote.
                if i + 1 < n and sql[i + 1] == quote:
                    out.append(sql[i + 1])
                    i += 2
                    continue
                quote = None
            i += 1
        elif ch in ("'", '"', '`'):
            quote = ch
            out.append(ch)
            i += 1
        elif ch == '-' and i + 1 < n and sql[i + 1] == '-':
            while i < n and sql[i] != '\n':
                i += 1
        elif ch == '/' and i + 1 < n and sql[i + 1] == '*':
            i += 2
            while i + 1 < n and not (sql[i] == '*' and sql[i + 1] == '/'):
                i += 1
            i += 2
        else:
            out.append(ch)
            i += 1
    return ''.join(out)


def mask_literals(sql):
    # Replace the contents of comments and quoted strings with spaces, so
    # keyword detection only sees real SQL syntax.
    out, i, n = [], 0, len(sql)
    quote = None
    while i < n:
        ch = sql[i]
        if quote:
            out.append('\n' if ch == '\n' else ' ')
            if ch == quote:
                if i + 1 < n and sql[i + 1] == quote:
                    out.append(' ')
                    i += 2
                    continue
                quote = None
            i += 1
        elif ch in ("'", '"', '`'):
            quote = ch
            out.append(' ')
            i += 1
        elif ch == '[':
            # Bracketed identifier, e.g. [weird col].
            j = sql.find(']', i + 1)
            j = n if j == -1 else j + 1
            out.extend(' ' for _ in range(j - i))
            i = j
        elif ch == '-' and i + 1 < n and sql[i + 1] == '-':
            while i < n and sql[i] != '\n':
                out.append(' ')
                i += 1
        elif ch == '/' and i + 1 < n and sql[i + 1] == '*':
            out.extend('  ')
            i += 2
            while i + 1 < n and not (sql[i] == '*' and sql[i + 1] == '/'):
                out.append('\n' if sql[i] == '\n' else ' ')
                i += 1
            if i + 1 < n:
                out.extend('  ')
                i += 2
        else:
            out.append(ch)
            i += 1
    return ''.join(out)


def find_transaction_control(statements):
    # Return the first statement that tries to manage its own transaction,
    # or None. "END" by itself also closes a transaction; bare END that
    # belongs to a trigger body (CREATE TRIGGER ... END) is not control
    # flow, so CREATE TRIGGER bodies are exempt.
    for stmt in statements:
        text = mask_literals(stmt)
        match = _TXN_CONTROL_RE.search(text)
        if not match:
            continue
        head = text.lstrip().upper()
        if head.startswith('CREATE') or head.startswith('DROP'):
            # CREATE/DROP TRIGGER bodies contain BEGIN ... END.
            continue
        return stmt
    return None


def find_attach(statements):
    # ATTACH/DETACH escape the single-file transaction/snapshot boundary.
    for stmt in statements:
        if _ATTACH_RE.search(mask_literals(stmt)):
            return stmt
    return None


def meaningful_statements(statements):
    # Split may hand back a trailing comment-only chunk ("-- done"). It
    # has no effect and must not be reported as an error.
    result = []
    for stmt in statements:
        text = strip_comments(stmt).strip().rstrip(';').strip()
        if text:
            result.append(stmt)
    return result


def _elapsed(started):
    return round((time.perf_counter() - started) * 1000, 2)


def _schema_version(dataset):
    try:
        return dataset.query('PRAGMA schema_version').fetchone()[0]
    except Exception:
        return None


def _run_statement(dataset, stmt, page_size, schema_before):
    # Like run_one, but reports whether the statement wrote anything so
    # the caller can decide whether a commit is necessary.
    started = time.perf_counter()
    try:
        cursor = dataset.query(stmt)
    except Exception as exc:
        return Result('error', stmt, error=str(exc),
                      duration=_elapsed(started)), False

    if cursor.description is None:
        changed = (cursor.rowcount not in (0, -1) or
                   _schema_version(dataset) != schema_before)
        return Result('affected', stmt, affected=cursor.rowcount,
                      duration=_elapsed(started)), changed

    columns = [d[0] for d in cursor.description]
    rows = cursor.fetchall()
    return Result(
        'rows',
        stmt,
        columns=columns,
        rows=rows[:page_size],
        has_next=len(rows) > page_size,
        duration=_elapsed(started)), False


class _ScriptAbort(Exception):
    # Raised inside the transaction block when a statement fails, so the
    # context manager performs the rollback.
    pass


def execute_script(dataset, statements, page_size=1000, atomic=True):
    """Run several statements as a unit.

    When atomic the whole batch is wrapped in BEGIN IMMEDIATE / COMMIT.
    Any error rolls back every earlier statement. Returns the list of
    results (the last one carries the error) and a flag telling whether
    at least one statement wrote data.
    """
    statements = meaningful_statements(statements)
    if not statements:
        return [], False

    controlled = find_transaction_control(statements)
    if controlled is not None:
        return [Result(
            'error', controlled,
            error=('Script manages its own transaction (BEGIN/COMMIT/'
                   'ROLLBACK/SAVEPOINT). Remove transaction control '
                   'statements so the script can be run atomically.'))], False

    attached = find_attach(statements)
    if attached is not None:
        return [Result(
            'error', attached,
            error=('ATTACH/DETACH is not supported: an attached database '
                   'commits independently and cannot be part of an atomic '
                   'script.'))], False

    results = []
    wrote = False

    def run_all():
        nonlocal wrote
        for stmt in statements:
            schema_before = _schema_version(dataset)
            result, changed = _run_statement(dataset, stmt, page_size,
                                             schema_before)
            results.append(result)
            wrote = wrote or changed
            if result.kind == 'error':
                return False
        return True

    db = dataset._database
    if not atomic:
        run_all()
        return results, wrote

    try:
        with db.transaction(lock_type='IMMEDIATE'):
            if not run_all():
                raise _ScriptAbort()
    except _ScriptAbort:
        # The context manager has rolled everything back.
        return results, False
    except Exception as exc:
        # Acquiring the write lock ("database is locked") or the final
        # COMMIT (e.g. a deferred foreign-key violation) can fail. Attach
        # the failure to whichever statement it belongs to.
        message = str(exc)
        if results and results[-1].kind == 'error':
            return results, False
        if results:
            results.append(Result('error', 'COMMIT', error=message))
        else:
            results.append(Result('error', statements[0], error=message))
        return results, False

    return results, wrote


def _uri(path, mode='ro'):
    return 'file:%s?mode=%s' % (quote(os.path.abspath(path)), mode)


def make_snapshot(source_path, dest_path):
    """Produce a consistent read-only copy of an on-disk database.

    The source is opened read-only, so the copy cannot change it. The
    sqlite backup API includes any committed WAL pages, unlike a plain
    file copy.
    """
    src = sqlite3.connect(_uri(source_path), uri=True)
    dst = sqlite3.connect(dest_path)
    try:
        dst.execute('PRAGMA foreign_keys = OFF')
        src.backup(dst)
        dst.commit()
    finally:
        src.close()
        dst.close()


def preview_script(source_path, statements, page_size=1000,
                   foreign_keys=False, extensions=(), startup_hook=None):
    """Run statements against a throwaway snapshot.

    Returns (results, wrote). The real database file is never opened for
    writing and every temporary resource is closed and removed.
    """
    fd, copy_path = tempfile.mkstemp(prefix='sqlite-web-preview-',
                                     suffix='.db')
    os.close(fd)
    os.unlink(copy_path)  # backup() wants to create the file itself.
    try:
        make_snapshot(source_path, copy_path)
        db = SqliteDatabase(copy_path)
        if foreign_keys:
            db.pragma('foreign_keys', True, permanent=True)
        for ext in extensions or ():
            db.load_extension(ext)
        if startup_hook is not None:
            startup_hook(db)
        dataset = DataSet(db)  # DataSet opens the connection itself.
        try:
            return execute_script(dataset, statements, page_size,
                                  atomic=True)
        finally:
            if not db.is_closed():
                dataset.close()
    finally:
        if os.path.exists(copy_path):
            for suffix in ('-wal', '-shm'):
                sidecar = copy_path + suffix
                if os.path.exists(sidecar):
                    os.unlink(sidecar)
            os.unlink(copy_path)


def _enc(value):
    if isinstance(value, (bytes, bytearray, memoryview)):
        return {'b64': base64.b64encode(bytes(value)).decode()}
    if value is None or isinstance(value, (int, float, str, bool)):
        return value
    return str(value)  # date, Decimal, etc. fall back to their text form.

def _dec(value):
    if isinstance(value, dict) and 'b64' in value:
        return base64.b64decode(value['b64'])
    return value


def key_encode(values):
    val_json = json.dumps([_enc(v) for v in values])
    return base64.urlsafe_b64encode(val_json.encode()).decode()

def key_decode(token):
    decoded = base64.urlsafe_b64decode(token.encode())
    return [_dec(v) for v in json.loads(decoded)]
