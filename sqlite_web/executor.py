import base64
import json
import re
import time
from dataclasses import dataclass, field

from peewee import DatabaseError
from peewee import sqlite3


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
    elapsed: float = None  # Seconds the statement took to run.


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
    start = time.perf_counter()
    result = _run_one(dataset, sql, page=page, page_size=page_size,
                      ordering=ordering)
    result.elapsed = time.perf_counter() - start
    return result


def _run_one(dataset, sql, page=1, page_size=50, ordering=None):
    # The query box allows whatever kinds of query/ies. We wrap the user query
    # to provide ordering + pagination, but cannot wrap DDL or DML statements.
    # Rather than try to parse the user SQL, attempt to wrap + execute (this
    # only works for SELECTs), and on failure fall-back to unwrapped.
    page = max(page, 1)
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
            return Result('error', sql, error=str(exc))

    if cursor.description is None:
        return Result('affected', sql, affected=cursor.rowcount)

    columns = [d[0] for d in cursor.description]
    rows = cursor.fetchall()
    return Result(
        'rows',
        sql,
        columns=columns,
        rows=rows[:page_size] if paged else rows,
        has_next=paged and len(rows) > page_size)


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


# Transaction-control statements cannot run inside the transaction a script
# executes in: BEGIN would error, and COMMIT/ROLLBACK would silently commit
# or discard the statements that ran before them, breaking atomicity.
TXN_CONTROL_RE = re.compile(
    r'^\s*(?:begin|commit|rollback|end|savepoint|release)\b', re.I)


def run_script_atomic(dataset, statements, page_size=50, commit=True):
    """
    Run a script as one atomic unit: either every statement applies or
    none of them do. Returns (results, committed).

    Statements run in order inside a single transaction, stopping at the
    first error. With commit=False (a preview) the transaction always
    rolls back, leaving the database untouched; the per-statement results
    are the same ones a committing run produces, since both run the same
    statements against the same starting state. If the connection drops
    before commit, sqlite rolls the transaction back on close, so the
    database can never be left half-applied.
    """
    for stmt in statements:
        if TXN_CONTROL_RE.match(stmt):
            error = ('Transaction-control statements cannot run inside a '
                     'script; the script itself executes in a single '
                     'transaction: %s' % stmt.strip())
            return [Result('error', stmt, error=error)], False

    db = dataset._database
    if db.is_closed():
        db.connect()

    results = []
    committed = False
    with db.manual_commit():
        db.begin()
        try:
            for stmt in statements:
                result = run_one(dataset, stmt, page_size=page_size)
                results.append(result)
                if result.kind == 'error':
                    break
            else:
                if commit:
                    try:
                        db.commit()
                    except Exception as exc:
                        # e.g. a deferred constraint checked at commit time.
                        results.append(Result('error', 'COMMIT',
                                              error=str(exc)))
                    else:
                        committed = True
        finally:
            if not committed:
                try:
                    db.rollback()
                except Exception:
                    # sqlite may already have rolled the transaction back;
                    # closing the connection finishes the job either way.
                    pass
    return results, committed


def is_read(dataset, sql):
    try:
        dataset.query(wrap(sql, limit=0))
        return True
    except DatabaseError:
        return False


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
