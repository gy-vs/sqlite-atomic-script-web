import glob
import os
import re
import shutil
import sqlite3
import tempfile
import threading
import unittest
import urllib.error
import urllib.parse
import urllib.request

from peewee import SqliteDatabase
from playhouse.dataset import DataSet

from sqlite_web import sqlite_web as sw
from sqlite_web import executor as executor_module
from sqlite_web.executor import Result
from sqlite_web.executor import execute_script
from sqlite_web.executor import find_attach
from sqlite_web.executor import find_transaction_control
from sqlite_web.executor import is_read
from sqlite_web.executor import key_decode
from sqlite_web.executor import key_encode
from sqlite_web.executor import meaningful_statements
from sqlite_web.executor import preview_script
from sqlite_web.executor import run_one
from sqlite_web.executor import run_script
from sqlite_web.executor import split_statements
from sqlite_web.executor import strip_comments
from sqlite_web.executor import wrap


class BaseExecutorTestCase(unittest.TestCase):
    def setUp(self):
        self.db = SqliteDatabase(':memory:')
        self.dataset = DataSet(self.db)
        self.dataset.query('CREATE TABLE users (id INTEGER PRIMARY KEY, '
                           'username TEXT)')
        for username in ('huey', 'mickey', 'zaizee'):
            self.dataset.query('INSERT INTO users (username) VALUES (?)',
                               (username,))

    def user_count(self):
        return self.dataset.query('SELECT COUNT(*) FROM users').fetchone()[0]


class TestRunOne(BaseExecutorTestCase):
    def test_read_paginates(self):
        r = run_one(self.dataset, 'SELECT * FROM users', page_size=2)
        self.assertEqual(r.kind, 'rows')
        self.assertEqual(r.columns, ['id', 'username'])
        self.assertEqual(len(r.rows), 2)
        self.assertTrue(r.has_next)
        self.assertIsNone(r.keys)

        r = run_one(self.dataset, 'SELECT * FROM users', page=2, page_size=2)
        self.assertEqual(len(r.rows), 1)
        self.assertFalse(r.has_next)

    def test_page_bounds(self):
        r = run_one(self.dataset, 'SELECT * FROM users', page=0, page_size=2)
        self.assertEqual(len(r.rows), 2)

        r = run_one(self.dataset, 'SELECT * FROM users', page=99, page_size=2)
        self.assertEqual(r.kind, 'rows')
        self.assertEqual(r.rows, [])
        self.assertFalse(r.has_next)

    def test_ordering(self):
        r = run_one(self.dataset, 'SELECT * FROM users', ordering=-2)
        self.assertEqual(r.rows[0][1], 'zaizee')
        r = run_one(self.dataset, 'SELECT * FROM users', ordering=2)
        self.assertEqual(r.rows[0][1], 'huey')

    def test_write_autocommits(self):
        r = run_one(self.dataset, "INSERT INTO users (username) VALUES ('x')")
        self.assertEqual(r.kind, 'affected')
        self.assertEqual(r.affected, 1)
        self.assertFalse(self.db.connection().in_transaction)
        self.assertEqual(self.user_count(), 4)

    def test_ddl(self):
        r = run_one(self.dataset, 'CREATE TABLE t2 (id INTEGER)')
        self.assertEqual(r.kind, 'affected')
        self.assertEqual(r.affected, -1)
        self.assertEqual(run_one(self.dataset, 'SELECT * FROM t2').kind,
                         'rows')

    def test_pragma(self):
        r = run_one(self.dataset, 'PRAGMA journal_mode')
        self.assertEqual(r.kind, 'rows')
        self.assertEqual(len(r.rows), 1)

    def test_returning(self):
        r = run_one(self.dataset,
                    "INSERT INTO users (username) VALUES ('r') RETURNING *")
        self.assertEqual(r.kind, 'rows')
        self.assertEqual(len(r.rows), 1)
        self.assertEqual(self.user_count(), 4)

    def test_error(self):
        r = run_one(self.dataset, 'SELECT nocolumn FROM users')
        self.assertEqual(r.kind, 'error')
        self.assertIn('nocolumn', r.error)

    def test_multi_statement_is_error(self):
        r = run_one(self.dataset, 'SELECT 1; SELECT 2')
        self.assertEqual(r.kind, 'error')

    def test_trailing_junk(self):
        for sql in ('SELECT * FROM users -- a comment',
                    'SELECT * FROM users;',
                    'SELECT * FROM users; \n ;'):
            r = run_one(self.dataset, sql)
            self.assertEqual(r.kind, 'rows', sql)
            self.assertEqual(len(r.rows), 3, sql)


class TestSplitStatements(unittest.TestCase):
    def test_split(self):
        script = ('CREATE TABLE t1 (id INTEGER);\n'
                  'CREATE TRIGGER trg AFTER INSERT ON t1 BEGIN '
                  'UPDATE t1 SET id = id; END;\n'
                  'INSERT INTO t1 VALUES (1);')
        stmts = split_statements(script)
        self.assertEqual(len(stmts), 3)
        self.assertTrue(stmts[1].startswith('CREATE TRIGGER'))
        self.assertTrue(stmts[1].endswith('END;'))

    def test_semicolon_in_string(self):
        self.assertEqual(split_statements("SELECT ';'; SELECT 2;"),
                         ["SELECT ';';", 'SELECT 2;'])

    def test_trailing_comment_chunk(self):
        self.assertEqual(split_statements('SELECT 1; -- done'),
                         ['SELECT 1;', '-- done'])


class TestRunScript(BaseExecutorTestCase):
    def run_sql(self, script, **kwargs):
        return run_script(self.dataset, split_statements(script), **kwargs)

    def test_statements_apply_independently(self):
        results = self.run_sql(
            "INSERT INTO users (username) VALUES ('a');"
            "INSERT INTO users (username) VALUES ('b');")
        self.assertEqual([r.kind for r in results], ['affected', 'affected'])
        self.assertFalse(self.db.connection().in_transaction)
        self.assertEqual(self.user_count(), 5)

    def test_stops_at_first_error(self):
        results = self.run_sql(
            "INSERT INTO users (username) VALUES ('a');"
            'CREATE TABLE t2 (id INTEGER);'
            'SELECT nocolumn FROM users;'
            "INSERT INTO users (username) VALUES ('never');")
        self.assertEqual([r.kind for r in results],
                         ['affected', 'affected', 'error'])
        # Statements before the error stay applied, DDL included.
        self.assertEqual(self.user_count(), 4)
        self.assertEqual(run_one(self.dataset, 'SELECT * FROM t2').kind,
                         'rows')

    def test_select_inside_script(self):
        results = self.run_sql(
            'SELECT * FROM users; SELECT COUNT(*) FROM users;', page_size=2)
        self.assertEqual(len(results[0].rows), 2)
        self.assertTrue(results[0].has_next)
        self.assertEqual(results[1].rows[0][0], 3)

    def test_user_owned_transaction(self):
        results = self.run_sql(
            "BEGIN; INSERT INTO users (username) VALUES ('a'); COMMIT;")
        self.assertEqual([r.kind for r in results], ['affected'] * 3)
        self.assertFalse(self.db.connection().in_transaction)
        self.assertEqual(self.user_count(), 4)

        self.run_sql(
            "BEGIN; INSERT INTO users (username) VALUES ('b'); ROLLBACK;")
        self.assertEqual(self.user_count(), 4)

    def test_dangling_begin_rolls_back_on_close(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db = SqliteDatabase(os.path.join(tmpdir, 'x.db'))
            ds = DataSet(db)
            ds.query('CREATE TABLE t1 (id INTEGER)')
            results = run_script(ds, split_statements(
                'BEGIN; INSERT INTO t1 VALUES (1); SELECT nocolumn FROM t1;'))
            self.assertEqual(results[-1].kind, 'error')
            self.assertTrue(db.connection().in_transaction)
            # Request teardown closes the connection; sqlite rolls back.
            db.close()
            db.connect()
            self.assertEqual(
                ds.query('SELECT COUNT(*) FROM t1').fetchone()[0], 0)
            db.close()


class TestExecuteScript(BaseExecutorTestCase):
    def run_atomic(self, script, **kwargs):
        return execute_script(self.dataset, split_statements(script), **kwargs)

    def test_commit_applies_everything(self):
        results, wrote = self.run_atomic(
            "INSERT INTO users (username) VALUES ('a');"
            "INSERT INTO users (username) VALUES ('b');"
            'SELECT COUNT(*) FROM users;')
        self.assertEqual([r.kind for r in results],
                         ['affected', 'affected', 'rows'])
        self.assertTrue(wrote)
        self.assertFalse(self.db.connection().in_transaction)
        self.assertEqual(self.user_count(), 5)
        self.assertEqual(results[-1].rows, [(5,)])
        for result in results:
            self.assertGreaterEqual(result.duration, 0)

    def test_error_rolls_back_every_statement(self):
        results, wrote = self.run_atomic(
            "INSERT INTO users (username) VALUES ('a');"
            'CREATE TABLE t2 (id INTEGER);'
            'SELECT nocolumn FROM users;'
            "INSERT INTO users (username) VALUES ('never');")
        self.assertEqual([r.kind for r in results],
                         ['affected', 'affected', 'error'])
        self.assertFalse(wrote)
        self.assertFalse(self.db.connection().in_transaction)
        # Everything is undone, including the DDL.
        self.assertEqual(self.user_count(), 3)
        self.assertEqual(run_one(self.dataset,
                                 "SELECT name FROM sqlite_master "
                                 "WHERE name='t2'").rows, [])

    def test_order_and_timing_reported(self):
        results, _ = self.run_atomic(
            'SELECT 1; SELECT 2; SELECT 3;')
        self.assertEqual([r.rows for r in results], [[(1,)], [(2,)], [(3,)]])
        self.assertTrue(all(r.duration >= 0 for r in results))

    def test_transaction_control_refused(self):
        results, wrote = self.run_atomic(
            "BEGIN; INSERT INTO users (username) VALUES ('a'); COMMIT;")
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0].kind, 'error')
        self.assertIn('transaction', results[0].error)
        self.assertEqual(self.user_count(), 3)

    def test_trigger_body_allowed(self):
        results, wrote = self.run_atomic(
            'CREATE TRIGGER trg AFTER INSERT ON users BEGIN '
            'UPDATE users SET username = username WHERE 0; END;')
        self.assertEqual([r.kind for r in results], ['affected'])

    def test_savepoint_refused(self):
        results, _ = self.run_atomic('SAVEPOINT x; INSERT INTO users (id) '
                                     "VALUES (99); RELEASE SAVEPOINT x;")
        self.assertEqual(results[0].kind, 'error')

    def test_ddl_counts_as_write(self):
        results, wrote = self.run_atomic('CREATE TABLE t2 (id INTEGER)')
        self.assertEqual(results[0].kind, 'affected')
        self.assertTrue(wrote)

    def test_deferred_foreign_key_rolls_back_commit(self):
        # FK enforcement is deferred to COMMIT by default; the failing
        # commit must still undo every earlier statement.
        self.db.pragma('foreign_keys', True, permanent=True)
        self.dataset.query('CREATE TABLE parent (id INTEGER PRIMARY KEY)')
        self.dataset.query('CREATE TABLE child (id INTEGER PRIMARY KEY, '
                           'pid INTEGER REFERENCES parent(id))')
        results, _ = self.run_atomic(
            'INSERT INTO parent VALUES (1);'
            'INSERT INTO child VALUES (1, 99);')
        self.assertEqual([r.kind for r in results], ['affected', 'error'])
        self.assertEqual(self.dataset.query(
            'SELECT COUNT(*) FROM parent').fetchone()[0], 0)

    def test_comment_only_chunk_ignored(self):
        self.assertEqual(
            meaningful_statements(split_statements('SELECT 1; -- done')),
            ['SELECT 1;'])
        results, _ = self.run_atomic('SELECT 1; -- done')
        self.assertEqual([r.kind for r in results], ['rows'])

    def test_strip_comments_preserves_strings(self):
        sql = "SELECT '-- not a comment', 1; /* x */ SELECT 2;"
        cleaned = strip_comments(sql)
        self.assertIn("'-- not a comment'", cleaned)
        self.assertNotIn('/* x */', cleaned)


class TestPreviewScript(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.path = os.path.join(self.tmp, 'preview.db')
        conn = sqlite3.connect(self.path)
        conn.execute('CREATE TABLE t (id INTEGER PRIMARY KEY, v TEXT)')
        conn.executemany('INSERT INTO t (v) VALUES (?)',
                         [('a',), ('b',), ('c',)])
        conn.commit()
        conn.close()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def file_state(self):
        return (os.stat(self.path).st_mtime_ns, os.stat(self.path).st_size)

    def test_preview_does_not_change_file(self):
        before = self.file_state()
        results, wrote = preview_script(
            self.path,
            split_statements("INSERT INTO t (v) VALUES ('z'); "
                             'DELETE FROM t; '
                             'CREATE TABLE x (id INTEGER); '
                             'SELECT COUNT(*) FROM t;'))
        self.assertEqual([r.kind for r in results],
                         ['affected', 'affected', 'affected', 'rows'])
        self.assertTrue(wrote)
        self.assertEqual(before, self.file_state())
        # Snapshot changes were visible within the preview.
        self.assertEqual(results[-1].rows, [(0,)])
        # Nothing reached the real file.
        conn = sqlite3.connect(self.path)
        self.assertEqual(conn.execute('SELECT COUNT(*) FROM t').fetchone()[0],
                         3)
        self.assertIsNone(conn.execute(
            "SELECT name FROM sqlite_master WHERE name='x'").fetchone())
        conn.close()

    def test_preview_results_match_commit(self):
        script = ("INSERT INTO t (v) VALUES ('d');"
                  'UPDATE t SET v = upper(v);'
                  'SELECT v FROM t ORDER BY id;')
        preview, _ = preview_script(self.path, split_statements(script))

        db = SqliteDatabase(self.path)
        dataset = DataSet(db)
        committed, _ = execute_script(dataset, split_statements(script))
        db.close()

        self.assertEqual([r.kind for r in preview],
                         [r.kind for r in committed])
        self.assertEqual(preview[-1].rows, committed[-1].rows)
        self.assertEqual(preview[-1].rows,
                         [('A',), ('B',), ('C',), ('D',)])

    def test_preview_cleans_up_connections_and_files(self):
        created = []
        original = executor_module.sqlite3.connect

        def spy(*args, **kwargs):
            conn = original(*args, **kwargs)
            created.append(conn)
            return conn

        executor_module.sqlite3.connect = spy
        try:
            results, _ = preview_script(
                self.path, split_statements("INSERT INTO t (v) "
                                            "VALUES ('z'); SELECT 1;"))
            self.assertEqual([r.kind for r in results], ['affected', 'rows'])
        finally:
            executor_module.sqlite3.connect = original

        self.assertTrue(created)
        for conn in created:
            with self.assertRaises(sqlite3.ProgrammingError):
                conn.execute('SELECT 1')
        leftovers = glob.glob(os.path.join(tempfile.gettempdir(),
                                           'sqlite-web-preview-*'))
        self.assertEqual(leftovers, [])

    def test_preview_error_leaves_real_file_unchanged(self):
        before = self.file_state()
        results, wrote = preview_script(
            self.path,
            split_statements("INSERT INTO t (v) VALUES ('z'); "
                             'SELECT bad FROM t;'))
        self.assertEqual(results[-1].kind, 'error')
        self.assertEqual(before, self.file_state())
        conn = sqlite3.connect(self.path)
        self.assertEqual(conn.execute('SELECT COUNT(*) FROM t').fetchone()[0],
                         3)
        conn.close()
        leftovers = glob.glob(os.path.join(tempfile.gettempdir(),
                                           'sqlite-web-preview-*'))
        self.assertEqual(leftovers, [])

    def test_preview_includes_wal_pages(self):
        # Keep a connection open so committed pages remain in the WAL.
        holder = sqlite3.connect(self.path)
        holder.execute('PRAGMA journal_mode=WAL')
        holder.execute("INSERT INTO t (v) VALUES ('wal-row')")
        holder.commit()
        try:
            results, _ = preview_script(
                self.path, split_statements('SELECT COUNT(*) FROM t;'))
            self.assertEqual(results[0].rows, [(4,)])
        finally:
            holder.close()


class TestTransactionControlDetection(unittest.TestCase):
    def test_detects_control_statements(self):
        for script in ('BEGIN;', 'BEGIN IMMEDIATE;', 'COMMIT;', 'ROLLBACK;',
                       'END;', 'SAVEPOINT x;', 'RELEASE x;'):
            stmt = find_transaction_control(split_statements(script))
            self.assertIsNotNone(stmt, script)

    def test_trigger_body_is_not_control(self):
        script = ('CREATE TRIGGER trg AFTER INSERT ON t '
                 'BEGIN UPDATE t SET v=v; END;')
        self.assertIsNone(find_transaction_control(split_statements(script)))
        self.assertIsNone(find_transaction_control(
            split_statements('DROP TRIGGER trg;')))

    def test_commented_control_ignored(self):
        self.assertIsNone(find_transaction_control(
            split_statements('SELECT 1; -- COMMIT')))


class TestAttachRejection(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.path = os.path.join(self.tmp, 'a.db')
        conn = sqlite3.connect(self.path)
        conn.execute('CREATE TABLE t (id INTEGER, note TEXT)')
        conn.execute("INSERT INTO t VALUES (1, 'ATTACH DATABASE /x')")
        conn.commit()
        conn.close()
        self.outside = os.path.join(self.tmp, 'outside.db')

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_detector_distinguishes_syntax_from_literals(self):
        self.assertIsNotNone(find_attach(split_statements(
            "ATTACH DATABASE '%s' AS e;" % self.outside)))
        self.assertIsNone(find_attach(split_statements(
            "SELECT 'ATTACH' AS x;")))
        self.assertIsNone(find_attach(split_statements(
            "SELECT * FROM t WHERE note = 'BEGIN';")))
        self.assertIsNone(find_attach(split_statements(
            'SELECT 1; -- ATTACH me')))

    def test_preview_attach_does_not_touch_other_files(self):
        results, _ = preview_script(
            self.path,
            split_statements("ATTACH DATABASE '%s' AS e; "
                             'CREATE TABLE e.x (id INTEGER);' % self.outside))
        self.assertEqual(results[0].kind, 'error')
        self.assertIn('ATTACH', results[0].error)
        self.assertFalse(os.path.exists(self.outside))

    def test_commit_attach_is_refused(self):
        db = SqliteDatabase(self.path)
        dataset = DataSet(db)
        results, _ = execute_script(
            dataset,
            split_statements("ATTACH DATABASE '%s' AS e; "
                             'SELECT 1;' % self.outside))
        self.assertEqual(results[0].kind, 'error')
        self.assertFalse(os.path.exists(self.outside))
        db.close()


class TestIsRead(BaseExecutorTestCase):
    def test_is_read(self):
        self.assertTrue(is_read(self.dataset, 'SELECT * FROM users'))
        self.assertTrue(is_read(self.dataset, 'SELECT * FROM users -- x'))
        self.assertFalse(is_read(self.dataset, 'DROP TABLE users'))
        self.assertFalse(is_read(self.dataset,
                                 "UPDATE users SET username = 'x'"))
        self.assertFalse(is_read(self.dataset, 'SELECT 1; SELECT 2'))
        self.assertEqual(self.user_count(), 3)


class TestWrap(unittest.TestCase):
    def test_shapes(self):
        self.assertEqual(wrap('SELECT 1;'),
                         'SELECT * FROM (\nSELECT 1\n) AS _')
        self.assertEqual(wrap('SELECT 1', ordering=-2),
                         'SELECT * FROM (\nSELECT 1\n) AS _ ORDER BY 2 DESC')
        self.assertEqual(wrap('SELECT 1', ordering=2, limit=51, offset=50),
                         'SELECT * FROM (\nSELECT 1\n) AS _ '
                         'ORDER BY 2 ASC LIMIT 51 OFFSET 50')
        self.assertEqual(wrap('SELECT 1', limit=0),
                         'SELECT * FROM (\nSELECT 1\n) AS _ LIMIT 0 OFFSET 0')
        self.assertEqual(wrap('SELECT 1', select='COUNT(*)'),
                         'SELECT COUNT(*) FROM (\nSELECT 1\n) AS _')


class TestRowKey(unittest.TestCase):
    def test_round_trips(self):
        for values in ([42], ['abc'], [b'\x01\x02\xff'], ['US', 'A:::B'],
                       [None, 1.5], ['✓']):
            self.assertEqual(key_decode(key_encode(values)), values)

    def test_url_safe(self):
        token = key_encode([b'\xfb\xff' * 30])
        self.assertNotIn('+', token)
        self.assertNotIn('/', token)


class BaseAppTestCase(unittest.TestCase):
    SCHEMA = """
        CREATE TABLE users (id INTEGER PRIMARY KEY, username TEXT);
        INSERT INTO users (username) VALUES ('huey'), ('mickey'), ('zaizee');
        CREATE TABLE comp (a TEXT, b TEXT, label TEXT, PRIMARY KEY (a, b));
        INSERT INTO comp VALUES ('US', 'A:::B', 'composite-row');
        CREATE TABLE blobs (id BLOB PRIMARY KEY, note TEXT);
        CREATE TABLE parent (id INTEGER PRIMARY KEY, name TEXT);
        INSERT INTO parent (name) VALUES ('p-one');
        CREATE TABLE child (id INTEGER PRIMARY KEY,
            parent_id INTEGER REFERENCES parent, label TEXT);
        INSERT INTO child (parent_id, label) VALUES (1, 'c-one');
        CREATE TABLE nopk (a TEXT);
        INSERT INTO nopk VALUES ('no-pk-row');
        CREATE TABLE oddpk ("user id" INTEGER NOT NULL, grp TEXT NOT NULL,
            val TEXT, PRIMARY KEY ("user id", grp));
        INSERT INTO oddpk VALUES (7, 'a', 'odd-row'), (8, 'a', 'same-grp');
        CREATE TABLE tag (name TEXT PRIMARY KEY);
        INSERT INTO tag VALUES (''), ('red');
        CREATE TABLE post (id INTEGER PRIMARY KEY,
            tag TEXT REFERENCES tag(name), body TEXT);
        CREATE VIEW v_users AS SELECT * FROM users;
    """

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.db_path = os.path.join(self.tmp, 'app.db')
        conn = sqlite3.connect(self.db_path)
        conn.executescript(self.SCHEMA)
        conn.execute('INSERT INTO blobs VALUES (?, ?)', (b'\x00\xff', 'blob'))
        conn.commit()
        conn.close()
        sw.datasets.clear()
        sw.initialize_app([self.db_path])
        sw.app.config['TESTING'] = True
        self.client = sw.app.test_client()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def dbrows(self, sql, *params):
        conn = sqlite3.connect(self.db_path)
        rows = conn.execute(sql, params).fetchall()
        conn.close()
        return rows


class TestExecutionPolicy(BaseAppTestCase):
    def test_cross_site_post_rejected(self):
        r = self.client.post('/query/', data={'sql': 'SELECT 1'},
                             headers={'Sec-Fetch-Site': 'cross-site'})
        self.assertEqual(r.status_code, 403)
        r = self.client.post('/query/', data={'sql': 'SELECT 1'},
                             headers={'Sec-Fetch-Site': 'same-origin'})
        self.assertEqual(r.status_code, 200)
        r = self.client.post('/query/', data={'sql': 'SELECT 1'})
        self.assertEqual(r.status_code, 200)

    def test_get_does_not_execute_writes(self):
        self.client.get('/query/', query_string={'sql': 'DELETE FROM users'})
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_post_runs_write_and_ddl(self):
        r = self.client.post('/query/',
                             data={'sql': "INSERT INTO users (username) "
                                          "VALUES ('x')"})
        self.assertIn(b'Rows modified', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)
        self.client.post('/query/', data={'sql': 'CREATE TABLE t2 (id INT)'})
        self.assertEqual(self.client.get('/t2/').status_code, 200)

    def test_export_refuses_non_select(self):
        r = self.client.post('/query/', data={'sql': 'DROP TABLE users',
                                              'export_csv': '1'})
        self.assertIn(b'Only a single query may be exported', r.data)
        self.assertTrue(self.dbrows('SELECT COUNT(*) FROM users'))


class TestValueFilter(unittest.TestCase):
    def setUp(self):
        self._truncate = sw.app.config['TRUNCATE_VALUES']

    def tearDown(self):
        sw.app.config['TRUNCATE_VALUES'] = self._truncate

    def test_link_requires_full_match(self):
        url = 'https://example.com/x'
        self.assertEqual(sw.value_filter(url),
                         '<a href="%s">%s</a>' % (url, url))
        self.assertNotIn('<a ', sw.value_filter(url + ' trailing text'))

    def test_mailto(self):
        self.assertIn('<a href="mailto:huey@example.com"',
                      sw.value_filter('mailto:huey@example.com'))

    def test_long_link_label_truncated(self):
        url = 'https://example.com/' + 'x' * 60
        out = sw.value_filter(url)
        self.assertIn('href="%s"' % url, out)
        self.assertIn('...', out)

    def test_multiline_value_wrapped(self):
        self.assertEqual(sw.value_filter('line one\nline two'),
                         '<span class="pre">line one\nline two</span>')
        self.assertEqual(sw.value_filter('plain'), 'plain')

    def test_blob_respects_truncate_flag(self):
        data = b'\xff' * 600  # Undecodable, 1200 hex chars.
        sw.app.config['TRUNCATE_VALUES'] = True
        self.assertNotIn('ff' * 600, sw.value_filter(data))
        sw.app.config['TRUNCATE_VALUES'] = False
        self.assertIn('ff' * 600, sw.value_filter(data))


class TestExplain(BaseAppTestCase):
    def test_explain_select(self):
        r = self.client.post('/query/', data={'sql': 'SELECT * FROM users',
                                              'explain': '1'})
        self.assertIn(b'SCAN', r.data)

    def test_explain_compiles_writes_without_running(self):
        self.client.post('/query/', data={
            'sql': "INSERT INTO users (username) VALUES ('x')",
            'explain': '1'})
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_explain_suppresses_row_keys(self):
        # Plan rows have an "id" column, which must not become edit links.
        r = self.client.post('/users/query/', data={
            'sql': 'SELECT * FROM users', 'explain': '1'})
        self.assertNotIn(b'/users/update/', r.data)
        self.assertNotIn(b'/users/row/', r.data)
        self.assertNotIn(b'name="count"', r.data)


class TestPaginationGating(BaseAppTestCase):
    def test_read_paginates(self):
        r = self.client.post('/users/query/',
                             data={'sql': 'SELECT * FROM users'})
        self.assertIn(b'name="count"', r.data)
        self.assertIn(b'bulk-action', r.data)

    def test_returning_hides_pagination_and_bulk(self):
        # The count button and bulk form re-submit the sql. For a write
        # that would execute it again.
        r = self.client.post('/users/query/', data={
            'sql': "INSERT INTO users (username) VALUES ('r') RETURNING *"})
        self.assertNotIn(b'name="count"', r.data)
        self.assertNotIn(b'bulk-action', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)

    def test_query_tab_bulk_delete(self):
        r = self.client.post('/users/query/', data={
            'sql': 'SELECT * FROM users', 'action': 'bulk-delete',
            'pk': key_encode([1])})
        self.assertEqual(r.status_code, 200)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 2)
        self.assertIn(b'bulk-action', r.data)  # Fresh results offer bulk.


class TestForeignKeyLinks(BaseAppTestCase):
    def test_content_links_fk_values(self):
        r = self.client.get('/child/content/')
        self.assertIn(b'/parent/query/', r.data)

    def test_table_query_links_fk_values(self):
        r = self.client.post('/child/query/',
                             data={'sql': 'SELECT * FROM child'})
        self.assertIn(b'/parent/query/', r.data)

    def test_structure_shows_fk_target(self):
        r = self.client.get('/child/')
        self.assertIn(b'<code>parent.id</code>', r.data)

    def test_fk_link_resolves(self):
        r = self.client.get('/parent/query/', query_string={
            'sql': 'SELECT * FROM "parent" WHERE "id" = 1'})
        self.assertIn(b'p-one', r.data)

    def test_no_fk_links_on_generic_query(self):
        r = self.client.post('/query/', data={'sql': 'SELECT * FROM child'})
        self.assertNotIn(b'/parent/query/', r.data)


class TestLastViewed(BaseAppTestCase):
    def test_single_capped_session_key(self):
        with self.client.session_transaction() as s:
            s['users.last_viewed'] = [5, None]  # Legacy per-table key.
        self.client.get('/users/content/')
        self.client.get('/child/content/')
        with self.client.session_transaction() as s:
            self.assertNotIn('users.last_viewed', s)
            self.assertEqual([e[0] for e in s['last_viewed']],
                             ['child', 'users'])

    def test_back_links_carry_saved_position(self):
        # Real destination urls rendered into the hrefs, no bounce route.
        with self.client.session_transaction() as s:
            s['last_viewed'] = [['users', 3, -2]]
        for url in ('/users/row/%s/' % key_encode([1]),
                    '/users/update/%s/' % key_encode([1])):
            r = self.client.get(url)
            self.assertIn(b'page=3', r.data, url)
            self.assertIn(b'ordering=-2', r.data, url)
        # No saved entry falls back to plain content.
        r = self.client.get('/child/row/%s/' % key_encode([1]))
        self.assertIn(b'href="/child/content/"', r.data)

    def test_redirect_to_previous_uses_saved_position(self):
        with self.client.session_transaction() as s:
            s['last_viewed'] = [['users', 3, -2]]
        r = self.client.post('/users/delete/%s/' % key_encode([1]))
        self.assertIn(r.status_code, (302, 303))
        self.assertIn('page=3', r.headers['Location'])
        self.assertIn('ordering=-2', r.headers['Location'])


class TestRowKeyRoutes(BaseAppTestCase):
    def test_composite_key_with_delimiter(self):
        token = key_encode(['US', 'A:::B'])
        r = self.client.get('/comp/update/%s/' % token)
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'composite-row', r.data)

    def test_blob_update_form_renders_hex(self):
        r = self.client.get('/blobs/update/%s/' % key_encode([b'\x00\xff']))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'00ff', r.data)

    def test_blob_bulk_delete(self):
        token = key_encode([b'\x00\xff'])
        r = self.client.post('/blobs/content/',
                             data={'action': 'bulk-delete', 'pk': token},
                             headers={'Sec-Fetch-Site': 'same-origin'})
        self.assertIn(r.status_code, (302, 303))
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM blobs')[0][0], 0)

    def test_text_pk_valued_like_old_sentinel(self):
        self.client.post('/query/', data={'sql': "INSERT INTO users (id, "
                                          "username) VALUES (42, '__uneditable__')"})
        # A row whose value collides with the retired sentinel is still edited
        # by its own pk, not the username.
        token = key_encode([42])
        r = self.client.get('/users/update/%s/' % token)
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'__uneditable__', r.data)

    def test_malformed_key_404s(self):
        self.assertEqual(self.client.get('/users/update/@@bad@@/').status_code,
                         404)

    def test_short_composite_token_cannot_multi_delete(self):
        # A one-value token against the two-column pk must be refused, a
        # zip would otherwise under-constrain the WHERE.
        token = key_encode(['US'])
        r = self.client.post('/comp/delete/%s/' % token)
        self.assertIn(r.status_code, (302, 303))
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM comp')[0][0], 1)
        r = self.client.get('/comp/row/%s/' % token)
        self.assertIn(r.status_code, (302, 303))

    def test_sanitized_pk_column_stays_in_key(self):
        # "user id" reflects as user_id and still keys the row. A grp-only
        # pk would target every row sharing grp.
        token = key_encode([7, 'a'])
        r = self.client.get('/oddpk/content/')
        self.assertIn(('/oddpk/row/%s/' % token).encode(), r.data)
        r = self.client.post('/oddpk/delete/%s/' % token)
        self.assertIn(r.status_code, (302, 303))
        self.assertEqual(self.dbrows('SELECT val FROM oddpk'), [('same-grp',)])


class TestDownload(BaseAppTestCase):
    def test_download_is_a_valid_snapshot(self):
        r = self.client.get('/download/')
        self.assertEqual(r.status_code, 200)
        self.assertIn('attachment', r.headers['Content-Disposition'])
        self.assertIn('app.db', r.headers['Content-Disposition'])
        self.assertTrue(r.data.startswith(b'SQLite format 3\x00'))

        path = os.path.join(self.tmp, 'snapshot.db')
        with open(path, 'wb') as f:
            f.write(r.data)
        r.close()  # Fires call_on_close, which removes the temp snapshot.
        conn = sqlite3.connect(path)
        count, = conn.execute('SELECT COUNT(*) FROM users').fetchone()
        conn.close()
        self.assertEqual(count, 3)

    def test_temp_dir_removed_after_streaming(self):
        marker = os.path.join(self.tmp, 'dl-tmp')
        os.mkdir(marker)
        orig = sw.tempfile.mkdtemp
        sw.tempfile.mkdtemp = lambda: marker
        try:
            r = self.client.get('/download/')
            self.assertTrue(os.path.exists(marker))  # Held while streaming.
            self.assertTrue(r.data.startswith(b'SQLite format 3\x00'))
            self.assertFalse(os.path.exists(marker))  # Gone once consumed.
            r.close()
        finally:
            sw.tempfile.mkdtemp = orig

    def test_head_request_does_not_leak(self):
        # HEAD never starts the body generator, so cleanup must not depend
        # on the generator running.
        marker = os.path.join(self.tmp, 'dl-head')
        os.mkdir(marker)
        orig = sw.tempfile.mkdtemp
        sw.tempfile.mkdtemp = lambda: marker
        try:
            r = self.client.head('/download/')
            self.assertEqual(r.status_code, 200)
            self.assertIn('attachment', r.headers['Content-Disposition'])
            r.close()
            self.assertFalse(os.path.exists(marker))
        finally:
            sw.tempfile.mkdtemp = orig

    def test_temp_dir_removed_on_abandoned_download(self):
        # A client that disconnects mid-stream must not leak the snapshot.
        marker = os.path.join(self.tmp, 'dl-abandon')
        os.mkdir(marker)
        orig = sw.tempfile.mkdtemp
        sw.tempfile.mkdtemp = lambda: marker
        try:
            r = self.client.get('/download/')
            self.assertTrue(os.path.exists(marker))
            r.close()  # Closed without ever reading the body.
            self.assertFalse(os.path.exists(marker))
        finally:
            sw.tempfile.mkdtemp = orig

    def test_error_flashes_and_cleans_up(self):
        marker = os.path.join(self.tmp, 'dl-err')
        os.mkdir(marker)
        os.chmod(marker, 0o500)  # VACUUM INTO cannot create its file.
        orig = sw.tempfile.mkdtemp
        sw.tempfile.mkdtemp = lambda: marker
        try:
            r = self.client.get('/download/', follow_redirects=True)
            self.assertEqual(r.status_code, 200)
            self.assertIn(b'Error creating database snapshot', r.data)
            self.assertFalse(os.path.exists(marker))
        finally:
            sw.tempfile.mkdtemp = orig
            if os.path.exists(marker):
                os.chmod(marker, 0o700)


class TestMultiDb(BaseAppTestCase):
    def setUp(self):
        super().setUp()
        self.db2 = os.path.join(self.tmp, 'two.db')
        conn = sqlite3.connect(self.db2)
        conn.execute('CREATE TABLE t2 (id INTEGER PRIMARY KEY)')
        conn.commit()
        conn.close()
        sw.datasets.clear()
        sw.initialize_app([self.db_path, self.db2])
        self.client = sw.app.test_client()

    def test_download_follows_selected_dataset(self):
        self.client.get('/select-dataset/',
                        query_string={'name': os.path.realpath(self.db2)})
        r = self.client.get('/download/')
        self.assertIn('two.db', r.headers['Content-Disposition'])
        path = os.path.join(self.tmp, 'snap2.db')
        with open(path, 'wb') as f:
            f.write(r.data)
        r.close()
        conn = sqlite3.connect(path)
        tables = [t for t, in conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table'")]
        conn.close()
        self.assertEqual(tables, ['t2'])

        self.client.get('/select-dataset/',
                        query_string={'name': os.path.realpath(self.db_path)})
        r = self.client.get('/download/')
        self.assertIn('app.db', r.headers['Content-Disposition'])
        r.close()


class TestDuplicateBasenames(BaseAppTestCase):
    def setUp(self):
        super().setUp()
        self.db2 = os.path.join(self.tmp, 'alt', 'app.db')
        os.makedirs(os.path.dirname(self.db2))
        conn = sqlite3.connect(self.db2)
        conn.execute('CREATE TABLE t2 (id INTEGER PRIMARY KEY)')
        conn.commit()
        conn.close()
        sw.datasets.clear()
        sw.initialize_app([self.db_path, self.db2])
        sw.app.config['ENABLE_FILESYSTEM'] = True
        self.client = sw.app.test_client()

    def tearDown(self):
        super().tearDown()
        sw.app.config['ENABLE_FILESYSTEM'] = False

    def select(self, path):
        return self.client.get('/select-dataset/',
                               query_string={'name': os.path.realpath(path)})

    def test_both_databases_are_loaded(self):
        self.assertEqual(sorted(sw.datasets), sorted([
            os.path.realpath(self.db_path), os.path.realpath(self.db2)]))

    def test_each_database_is_selectable(self):
        self.select(self.db2)
        self.assertIn(b'href="/t2/"', self.client.get('/').data)

        self.select(self.db_path)
        self.assertIn(b'href="/users/"', self.client.get('/').data)

    def test_menu_shows_the_parent_directory(self):
        # Long paths stay in the link target, out of the menu text.
        r = self.client.get('/')
        self.assertIn(b'>alt/app.db<', r.data)
        self.assertIn(b'>%s/app.db<'
                      % os.path.basename(os.path.realpath(self.tmp)).encode(),
                      r.data)
        self.assertNotIn(b'>%s<' % os.path.realpath(self.db2).encode(), r.data)

    def test_download_uses_basename(self):
        self.select(self.db2)
        r = self.client.get('/download/')
        self.assertIn('app.db', r.headers['Content-Disposition'])
        r.close()

    def test_runtime_load_leaves_loaded_databases_alone(self):
        before = list(sw.datasets)
        third = os.path.join(self.tmp, 'other', 'app.db')
        os.makedirs(os.path.dirname(third))
        conn = sqlite3.connect(third)
        conn.execute('CREATE TABLE t3 (id INTEGER PRIMARY KEY)')
        conn.commit()
        conn.close()
        r = self.client.post('/load/', data={'mode': 'filesystem',
                                             'filename': third})
        self.assertIn(r.status_code, (302, 303))
        self.assertEqual(list(sw.datasets),
                         before + [os.path.realpath(third)])
        # The newly-loaded database becomes the selected one.
        self.assertIn(b'href="/t3/"', self.client.get('/').data)

    def test_unload_removes_only_the_named_database(self):
        r = self.client.post('/unload/',
                             data={'dataset': os.path.realpath(self.db2)})
        self.assertIn(r.status_code, (302, 303))
        self.assertEqual(list(sw.datasets), [os.path.realpath(self.db_path)])


class TestRowDetailEdges(BaseAppTestCase):
    def test_blob_pk_detail(self):
        r = self.client.get('/blobs/row/%s/' % key_encode([b'\x00\xff']))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'blob', r.data)

    def test_extra_key_values_ignored(self):
        # Same behavior as update/delete, the first value drives the lookup.
        r = self.client.get('/users/row/%s/' % key_encode([1, 2]))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'huey', r.data)

    def test_empty_key_404s(self):
        # A token holding no values, [] or a crafted {}, must 404 instead
        # of raising IndexError in decode_pk.
        for token in (key_encode([]), 'e30='):
            for route in ('row', 'update', 'delete'):
                url = '/users/%s/%s/' % (route, token)
                self.assertEqual(self.client.get(url).status_code, 404, url)

    def test_no_pk_table(self):
        r = self.client.get('/nopk/content/')
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'no-pk-row', r.data)
        self.assertNotIn(b'/nopk/row/', r.data)
        r = self.client.get('/nopk/row/%s/' % key_encode(['no-pk-row']))
        self.assertIn(r.status_code, (302, 303))

    def test_sql_view(self):
        r = self.client.get('/v_users/content/')
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'huey', r.data)
        self.assertNotIn(b'/v_users/row/', r.data)
        for route in ('row', 'update', 'delete'):
            r = self.client.get('/v_users/%s/%s/' % (route, key_encode([1])))
            self.assertIn(r.status_code, (302, 303), route)


class TestRowDetail(BaseAppTestCase):
    def test_detail_page(self):
        r = self.client.get('/users/row/%s/' % key_encode([1]))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'huey', r.data)
        self.assertIn(b'/users/update/', r.data)

    def test_missing_row_redirects(self):
        r = self.client.get('/users/row/%s/' % key_encode([999]))
        self.assertIn(r.status_code, (302, 303))

    def test_malformed_key_404s(self):
        self.assertEqual(self.client.get('/users/row/@@bad@@/').status_code,
                         404)

    def test_composite_pk_detail(self):
        r = self.client.get('/comp/row/%s/' % key_encode(['US', 'A:::B']))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'composite-row', r.data)

    def test_detail_links_fk_values(self):
        r = self.client.get('/child/row/%s/' % key_encode([1]))
        self.assertIn(b'/parent/query/', r.data)

    def test_view_links_on_content_and_query_tabs(self):
        self.assertIn(b'/users/row/', self.client.get('/users/content/').data)
        r = self.client.post('/users/query/',
                             data={'sql': 'SELECT * FROM users'})
        self.assertIn(b'/users/row/', r.data)

    def test_no_view_links_on_generic_query(self):
        r = self.client.post('/query/', data={'sql': 'SELECT * FROM users'})
        self.assertNotIn(b'/users/row/', r.data)


class TestReadOnlyRowDetail(BaseAppTestCase):
    def setUp(self):
        super().setUp()
        sw.datasets.clear()
        sw.initialize_app([self.db_path], read_only=True)
        self.client = sw.app.test_client()

    def tearDown(self):
        super().tearDown()
        sw.dataset_config['read_only'] = False

    def test_read_only_gets_view_but_not_edit(self):
        r = self.client.get('/users/content/')
        self.assertIn(b'/users/row/', r.data)
        self.assertNotIn(b'/users/update/', r.data)
        self.assertNotIn(b'toggle-pk-all', r.data)

    def test_read_only_detail_page(self):
        r = self.client.get('/users/row/%s/' % key_encode([2]))
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'mickey', r.data)
        self.assertNotIn(b'/users/update/', r.data)

    def test_read_only_download(self):
        # VACUUM INTO runs against the mode=ro connection.
        r = self.client.get('/download/')
        self.assertEqual(r.status_code, 200)
        self.assertTrue(r.data.startswith(b'SQLite format 3\x00'))
        r.close()

    def test_read_only_smoke(self):
        for url in ('/', '/users/', '/users/content/', '/users/query/'):
            self.assertEqual(self.client.get(url).status_code, 200, url)
        r = self.client.get('/users/content/')
        self.assertNotIn(b'/users/insert/', r.data)
        r = self.client.post('/users/query/',
                             data={'sql': 'SELECT * FROM users'})
        self.assertIn(b'huey', r.data)

    def test_read_only_writes_fail_at_the_database(self):
        # Enforcement is the mode=ro connection. Writes must fail safely
        # with data unchanged and no 500s.
        r = self.client.post('/users/insert/', data={
            'chk_username': 'on', 'username': 'nope'},
            follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

        r = self.client.post('/users/drop/', follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        self.assertTrue(self.dbrows('SELECT COUNT(*) FROM users'))

        r = self.client.post('/users/update/%s/' % key_encode([1]),
                             data={'chk_username': 'on', 'username': 'x'},
                             follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        rows = self.dbrows('SELECT username FROM users WHERE id = 1')
        self.assertEqual(rows, [('huey',)])

        r = self.client.post('/create-table/', data={
            'table_name': 'zz', 'redirect': '/'}, follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'Error', r.data)


class TestPasswordlessLogin(BaseAppTestCase):
    def test_login_redirects_when_no_password(self):
        r = self.client.get('/login/')
        self.assertIn(r.status_code, (302, 303))
        r = self.client.post('/login/', data={})
        self.assertIn(r.status_code, (302, 303))
        with self.client.session_transaction() as s:
            self.assertNotIn('authorized', s)


class TestCreateTable(BaseAppTestCase):
    def test_create_failure_keeps_flash_destination(self):
        # The sqlite_ prefix is reserved, so creation fails. The redirect
        # must go back to the caller, not to a 404ing import page.
        r = self.client.post('/create-table/', data={
            'table_name': 'sqlite_nope', 'redirect': '/'},
            follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'Error', r.data)

    def test_create_success_lands_on_import(self):
        r = self.client.post('/create-table/', data={
            'table_name': 'fresh', 'redirect': '/'})
        self.assertIn('/fresh/import/', r.headers['Location'])


class TestErrorPages(BaseAppTestCase):
    def test_404_renders_in_chrome(self):
        r = self.client.get('/nope-not-a-table/')
        self.assertEqual(r.status_code, 404)
        self.assertIn(b'Not Found', r.data)
        self.assertIn(b'powered by', r.data)

    def test_403_renders_in_chrome(self):
        r = self.client.post('/query/', data={'sql': 'SELECT 1'},
                             headers={'Sec-Fetch-Site': 'cross-site'})
        self.assertEqual(r.status_code, 403)
        self.assertIn(b'powered by', r.data)

    def test_empty_registry_500_renders(self):
        # The error page renders even when no dataset can be resolved.
        sw.datasets.clear()
        r = self.client.get('/')
        self.assertEqual(r.status_code, 500)
        self.assertIn(b'powered by', r.data)


class TestQueryTemplates(BaseAppTestCase):
    def test_shared_form_renders_on_both_pages(self):
        for url, textarea_id in (('/query/', b'id="sql"'),
                                 ('/users/query/', b'id="table-sql"')):
            r = self.client.get(url)
            self.assertEqual(r.status_code, 200)
            self.assertIn(b'name="explain"', r.data)
            self.assertIn(b'id="bookmark-modal"', r.data)
            self.assertIn(b'id="import-bookmarks"', r.data)
            self.assertIn(b'__TABLE__', r.data)
            self.assertIn(b'id="sql-image-modal"', r.data)
            self.assertIn(textarea_id, r.data)

    def test_copy_affordances_present(self):
        r = self.client.get('/users/content/')
        self.assertIn(b'copy-row', r.data)
        self.assertIn(b'data-col="username"', r.data)

    def test_script_results_offer_copy(self):
        r = self.client.post('/users/query/',
                             data={'sql': 'SELECT 1; SELECT 2;'})
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'copy-row', r.data)
        self.assertNotIn(b'/users/row/', r.data)

    def test_missing_table_query_keeps_sql(self):
        # A bookmark can reference a dropped or foreign table. Its sql
        # falls back to the generic query page.
        r = self.client.get('/nope/query/', query_string={'sql': 'SELECT 1'})
        self.assertEqual(r.status_code, 302)
        self.assertIn('/query/?sql=SELECT', r.headers['Location'])
        r = self.client.get('/nope/query/', query_string={'sql': 'SELECT 1'},
                            follow_redirects=True)
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'SELECT 1', r.data)

    def test_missing_table_query_404s_without_sql(self):
        self.assertEqual(self.client.get('/nope/query/').status_code, 404)


class TestInsertForm(BaseAppTestCase):
    def test_blank_numeric_inserts_null(self):
        # The form pre-enables every column, so a blank numeric input must
        # mean NULL instead of failing validation.
        r = self.client.post('/child/insert/', data={
            'chk_parent_id': 'on', 'parent_id': '',
            'chk_label': 'on', 'label': 'blank-num'})
        self.assertIn(r.status_code, (302, 303))
        rows = self.dbrows(
            'SELECT parent_id, label FROM child WHERE label = ?', 'blank-num')
        self.assertEqual(rows, [(None, 'blank-num')])

    def test_blank_text_inserts_empty_string(self):
        r = self.client.post('/child/insert/', data={
            'chk_label': 'on', 'label': ''})
        self.assertIn(r.status_code, (302, 303))
        rows = self.dbrows("SELECT COUNT(*) FROM child WHERE label = ''")
        self.assertEqual(rows, [(1,)])

    def test_blank_text_fk_keeps_empty_string(self):
        # A TEXT primary key can legitimately be '', so a blank input on
        # a text-keyed fk must not become NULL.
        r = self.client.post('/post/insert/', data={
            'chk_tag': 'on', 'tag': '',
            'chk_body': 'on', 'body': 'text-fk'})
        self.assertIn(r.status_code, (302, 303))
        rows = self.dbrows("SELECT tag FROM post WHERE body = 'text-fk'")
        self.assertEqual(rows, [('',)])


class TestContentTab(BaseAppTestCase):
    def test_renders_with_row_actions(self):
        r = self.client.get('/users/content/')
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'/users/update/', r.data)
        self.assertIn(b'/users/delete/', r.data)
        self.assertIn(b'toggle-pk-all', r.data)

    def test_ordinal_ordering(self):
        asc = self.client.get('/users/content/',
                              query_string={'ordering': '2'}).data
        desc = self.client.get('/users/content/',
                               query_string={'ordering': '-2'}).data
        self.assertLess(asc.index(b'huey'), asc.index(b'zaizee'))
        self.assertLess(desc.index(b'zaizee'), desc.index(b'huey'))

    def test_bad_ordering_ignored(self):
        for value in ('99', 'abc', '-abc'):
            r = self.client.get('/users/content/',
                                query_string={'ordering': value})
            self.assertEqual(r.status_code, 200)

    def test_disabled_pager_arrows_are_not_links(self):
        # Single page of data, so all four arrows must render as spans.
        r = self.client.get('/users/content/')
        for arrow in (b'&laquo;', b'&lsaquo;', b'&rsaquo;', b'&raquo;'):
            self.assertIn(b'<span class="page-link">' + arrow, r.data)

    def test_flash_alerts_are_dismissible(self):
        r = self.client.get('/users/row/%s/' % key_encode([999]),
                            follow_redirects=True)
        self.assertIn(b'alert-dismissible', r.data)
        self.assertNotIn(b'alert-dismissable', r.data)


class TestUrlPrefix(BaseAppTestCase):
    def setUp(self):
        super(TestUrlPrefix, self).setUp()
        self.wsgi_app = sw.app.wsgi_app
        sw.initialize_app([], url_prefix='/sqlite/')

    def tearDown(self):
        sw.app.wsgi_app = self.wsgi_app
        sw.app.config['SESSION_COOKIE_PATH'] = None
        super(TestUrlPrefix, self).tearDown()

    def test_session_cookie_scoped_to_prefix(self):
        r = self.client.get('/sqlite/users/content/')
        self.assertIn('Path=/sqlite', r.headers['Set-Cookie'])


class AtomicScriptAppTestCase(BaseAppTestCase):
    SCRIPT = ("INSERT INTO users (username) VALUES ('new1');"
              "CREATE TABLE migrated (id INTEGER PRIMARY KEY, note TEXT);"
              'SELECT COUNT(*) FROM users;')

    def preview(self, script=None):
        script = self.SCRIPT if script is None else script
        r = self.client.post('/query/', data={'sql': script})
        self.assertEqual(r.status_code, 200)
        return r

    @staticmethod
    def token(response):
        match = re.search(
            rb'name="preview_token"[^>]*value="([^"]+)"', response.data)
        assert match, 'no preview token in response'
        return match.group(1).decode()

    def commit(self, token, script=None):
        script = self.SCRIPT if script is None else script
        return self.client.post('/query/', data={
            'sql': script,
            'script_action': 'commit',
            'preview_token': token})


class TestAtomicScriptHttp(AtomicScriptAppTestCase):
    def test_preview_shows_order_timing_results_and_commit_button(self):
        r = self.preview()
        self.assertIn(b'Preview.', r.data)
        self.assertIn(b'Commit script', r.data)
        # Every statement is listed in order with index and timing.
        for badge in (b'1/3', b'2/3', b'3/3'):
            self.assertIn(badge, r.data)
        self.assertIn(b' ms</small>', r.data)
        # Snapshot effects are visible within the preview results.
        self.assertIn(b'<td class="num">\n              4\n', r.data)

    def test_preview_does_not_modify_database_file(self):
        before = (os.stat(self.db_path).st_mtime_ns,
                  os.stat(self.db_path).st_size)
        r = self.preview()
        after = (os.stat(self.db_path).st_mtime_ns,
                 os.stat(self.db_path).st_size)
        self.assertEqual(before, after)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)
        self.assertEqual(self.dbrows(
            "SELECT name FROM sqlite_master WHERE type='table' AND "
            "name='migrated'"), [])
        # Preview ran all three statements in order.
        self.assertIn(b'1/3', r.data)

    def test_commit_applies_all_statements_together(self):
        token = self.token(self.preview())
        r = self.commit(token)
        self.assertIn(b'Committed.', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)
        self.assertEqual(self.dbrows(
            "SELECT name FROM sqlite_master WHERE name='migrated'")[0][0],
                         'migrated')
        # Committed results show no second commit button.
        self.assertNotIn(b'Commit script', r.data)

    def test_preview_and_commit_show_same_results(self):
        preview = self.preview()
        token = self.token(preview)
        committed = self.commit(token)
        for needle in (b'new1', b'migrated', b'1/3'):
            self.assertIn(needle, preview.data)
            self.assertIn(needle, committed.data)

    def test_failed_commit_rolls_back_and_reports_statement(self):
        script = ("INSERT INTO users (username) VALUES ('half1');"
                  "INSERT INTO users (username) VALUES ('half2');"
                  'SELECT nocolumn FROM users;')
        token = self.token(self.preview(script))
        r = self.commit(token, script)
        self.assertIn(b'Rolled back.', r.data)
        self.assertIn(b'no such column: nocolumn', r.data)
        # The error was the 3rd statement; its badge marks it.
        self.assertIn(b'3/3', r.data)
        self.assertIn(b'badge-danger', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)
        # The fourth statement never ran at all.
        self.assertEqual(self.dbrows(
            "SELECT COUNT(*) FROM users WHERE username IN "
            "('half1','half2')")[0][0], 0)

    def test_failed_ddl_commit_rolls_back_schema(self):
        script = ('CREATE TABLE mig (id INTEGER);'
                  'ALTER TABLE users ADD COLUMN extra TEXT;'
                  'SELECT broken FROM users;')
        token = self.token(self.preview(script))
        r = self.commit(token, script)
        self.assertIn(b'Rolled back.', r.data)
        self.assertEqual(self.dbrows(
            "SELECT name FROM sqlite_master WHERE name='mig'"), [])
        columns = [row[1] for row in sqlite3.connect(
            self.db_path).execute('PRAGMA table_info(users)')]
        self.assertNotIn('extra', columns)

    def test_token_is_single_use(self):
        token = self.token(self.preview())
        self.assertEqual(self.commit(token).status_code, 200)
        r = self.commit(token)
        self.assertIn(b'Preview expired or was already used', r.data)
        # The reuse applied nothing extra.
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)

    def test_commit_requires_a_preview(self):
        r = self.client.post('/query/', data={
            'sql': self.SCRIPT, 'script_action': 'commit'})
        self.assertIn(b'Preview expired', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_modified_script_rejects_stale_token(self):
        token = self.token(self.preview(self.SCRIPT))
        other = ("INSERT INTO users (username) VALUES ('different');"
                 'SELECT COUNT(*) FROM users;')
        r = self.commit(token, other)
        self.assertIn(b'changed since it was previewed', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_database_changed_between_preview_and_commit_is_refused(self):
        token = self.token(self.preview(self.SCRIPT))
        conn = sqlite3.connect(self.db_path)
        conn.execute("INSERT INTO users (username) VALUES ('outside')")
        conn.commit()
        conn.close()
        r = self.commit(token)
        self.assertIn(b'changed after the preview', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)
        # None of the previewed script landed.
        self.assertEqual(self.dbrows(
            "SELECT name FROM sqlite_master WHERE name='migrated'"), [])

    def test_transaction_control_is_refused_without_preview_changes(self):
        script = ("BEGIN; INSERT INTO users (username) "
                  "VALUES ('x'); COMMIT;")
        r = self.client.post('/query/', data={'sql': script})
        self.assertIn(b'manages its own transaction', r.data)
        self.assertNotIn(b'Commit script', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_attach_is_refused_and_creates_no_other_file(self):
        outside = os.path.join(self.tmp, 'attached.db')
        script = ("ATTACH DATABASE '%s' AS ext; "
                  'CREATE TABLE ext.x (id INTEGER);' % outside)
        r = self.client.post('/query/', data={'sql': script})
        self.assertIn(b'ATTACH', r.data)
        self.assertNotIn(b'Commit script', r.data)
        self.assertFalse(os.path.exists(outside))

    def test_attach_word_inside_string_is_allowed(self):
        r = self.client.post('/query/', data={
            'sql': "SELECT 'ATTACH DATABASE' AS x; SELECT 1;"})
        self.assertEqual(r.status_code, 200)
        self.assertNotIn(b'Commit script', r.data)
        self.assertIn(b'1/2', r.data)

    def test_read_only_multi_runs_directly_without_preview(self):
        r = self.client.post('/query/',
                             data={'sql': 'SELECT 1; SELECT 2;'})
        self.assertNotIn(b'Commit script', r.data)
        self.assertNotIn(b'Preview.', r.data)
        self.assertIn(b'1/2', r.data)

    def test_get_bookmark_still_renders(self):
        r = self.client.get('/query/', query_string={'sql': 'SELECT 1'})
        self.assertEqual(r.status_code, 200)

    def test_single_write_still_one_click(self):
        r = self.client.post('/query/', data={
            'sql': "INSERT INTO users (username) VALUES ('solo')"})
        self.assertIn(b'Rows modified', r.data)
        self.assertNotIn(b'Commit script', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 4)

    def test_preview_temporary_connections_are_closed(self):
        created = []
        original = executor_module.sqlite3.connect

        def spy(*args, **kwargs):
            conn = original(*args, **kwargs)
            created.append(conn)
            return conn

        executor_module.sqlite3.connect = spy
        try:
            self.preview()
        finally:
            executor_module.sqlite3.connect = original

        self.assertTrue(created)
        for conn in created:
            with self.assertRaises(sqlite3.ProgrammingError):
                conn.execute('SELECT 1')

    def test_preview_temporary_files_are_removed(self):
        before = set(glob.glob(os.path.join(
            tempfile.gettempdir(), 'sqlite-web-preview-*')))
        self.preview()
        after = set(glob.glob(os.path.join(
            tempfile.gettempdir(), 'sqlite-web-preview-*')))
        self.assertEqual(before, after)


class TestConcurrentScriptCommits(AtomicScriptAppTestCase):
    def setUp(self):
        super().setUp()
        conn = sqlite3.connect(self.db_path)
        conn.execute('CREATE TABLE queue (id INTEGER PRIMARY KEY, '
                     'batch TEXT)')
        conn.commit()
        conn.close()
        # Independent clients act as two browser tabs.
        self.client_b = sw.app.test_client()

    def script_for(self, letter):
        return ''.join(
            "INSERT INTO queue (batch) VALUES ('%s%d');" % (letter, i)
            for i in range(1, 6))

    def preview_for(self, client, script):
        r = client.post('/query/', data={'sql': script})
        return self.token(r)

    def test_two_tabs_cannot_interleave_statements(self):
        sa, sb = self.script_for('a'), self.script_for('b')
        ta = self.preview_for(self.client, sa)
        tb = self.preview_for(self.client_b, sb)
        outcomes = {}

        def commit(client, token, script, name):
            r = client.post('/query/', data={
                'sql': script, 'script_action': 'commit',
                'preview_token': token})
            outcomes[name] = b'Committed.' in r.data

        t1 = threading.Thread(target=commit,
                              args=(self.client, ta, sa, 'a'))
        t2 = threading.Thread(target=commit,
                              args=(self.client_b, tb, sb, 'b'))
        t1.start(); t2.start(); t1.join(); t2.join()

        self.assertTrue(all(outcomes.values()))
        rows = self.dbrows('SELECT id, batch FROM queue ORDER BY id')
        self.assertEqual(len(rows), 10)
        # Each batch occupies one contiguous block of rowids: no mixing.
        batches = [batch for _, batch in rows]
        self.assertTrue(
            batches == ['a%d' % i for i in range(1, 6)] +
                       ['b%d' % i for i in range(1, 6)] or
            batches == ['b%d' % i for i in range(1, 6)] +
                       ['a%d' % i for i in range(1, 6)])


class TestRealHttpServer(unittest.TestCase):
    # Exercises the full stack over a real TCP socket: werkzeug serving
    # HTTP, urllib posting forms, request teardown closing connections.
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.db_path = os.path.join(self.tmp, 'http.db')
        conn = sqlite3.connect(self.db_path)
        conn.execute('CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)')
        conn.executemany('INSERT INTO users (name) VALUES (?)',
                         [('a',), ('b',)])
        conn.commit()
        conn.close()

        sw.datasets.clear()
        sw.initialize_app([self.db_path])
        sw.app.config['TESTING'] = False
        import werkzeug.serving
        self.server = werkzeug.serving.make_server(
            '127.0.0.1', 0, sw.app, threaded=True)
        self.port = self.server.server_port
        self.thread = threading.Thread(target=self.server.serve_forever,
                                       daemon=True)
        self.thread.start()

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(timeout=5)
        sw.app.config['TESTING'] = True
        shutil.rmtree(self.tmp, ignore_errors=True)

    def post(self, data, cookie=None):
        import urllib.request
        import urllib.parse
        body = urllib.parse.urlencode(data).encode()
        req = urllib.request.Request(
            'http://127.0.0.1:%d/query/' % self.port, data=body)
        if cookie:
            req.add_header('Cookie', cookie)
        try:
            resp = urllib.request.urlopen(req, timeout=10)
            payload = resp.read()
            set_cookie = resp.headers.get('Set-Cookie')
        except urllib.error.HTTPError as exc:
            payload = exc.read()
            set_cookie = exc.headers.get('Set-Cookie')
        return payload, set_cookie

    def dbcount(self):
        conn = sqlite3.connect(self.db_path)
        try:
            return conn.execute('SELECT COUNT(*) FROM users').fetchone()[0]
        finally:
            conn.close()

    @staticmethod
    def token(payload):
        match = re.search(rb'name="preview_token"[^>]*value="([^"]+)"',
                          payload)
        return match.group(1).decode()

    def test_preview_then_commit_over_http(self):
        script = ("INSERT INTO users (name) VALUES ('c');"
                  "INSERT INTO users (name) VALUES ('d');")
        before = (os.stat(self.db_path).st_mtime_ns,
                  os.stat(self.db_path).st_size)
        payload, _ = self.post({'sql': script})
        self.assertIn(b'Preview.', payload)
        self.assertEqual((os.stat(self.db_path).st_mtime_ns,
                          os.stat(self.db_path).st_size), before)
        self.assertEqual(self.dbcount(), 2)

        payload, _ = self.post(
            {'sql': script, 'script_action': 'commit',
             'preview_token': self.token(payload)})
        self.assertIn(b'Committed.', payload)
        self.assertEqual(self.dbcount(), 4)

    def test_failed_commit_rolls_back_over_http(self):
        script = ("INSERT INTO users (name) VALUES ('x');"
                  'SELECT broken FROM users;')
        payload, _ = self.post({'sql': script})
        payload, _ = self.post(
            {'sql': script, 'script_action': 'commit',
             'preview_token': self.token(payload)})
        self.assertIn(b'Rolled back.', payload)
        self.assertIn(b'no such column: broken', payload)
        self.assertEqual(self.dbcount(), 2)

    def test_connections_are_returned_after_requests(self):
        # After a full HTTP cycle the per-request connection must be closed;
        # repeatedly previewing must not accumulate open sqlite handles.
        script = "INSERT INTO users (name) VALUES ('z'); SELECT 1;"
        for _ in range(3):
            payload, _ = self.post({'sql': script})
            self.assertIn(b'Preview.', payload)
        leftovers = glob.glob(os.path.join(tempfile.gettempdir(),
                                           'sqlite-web-preview-*'))
        self.assertEqual(leftovers, [])


class TestPreviewOnReadOnlyDatabase(BaseAppTestCase):
    def setUp(self):
        super().setUp()
        sw.datasets.clear()
        sw.initialize_app([self.db_path], read_only=True)
        self.client = sw.app.test_client()

    def tearDown(self):
        super().tearDown()
        sw.dataset_config['read_only'] = False

    def test_write_script_is_refused_without_changes(self):
        r = self.client.post('/query/', data={
            'sql': "INSERT INTO users (username) VALUES ('x'); SELECT 1;"})
        self.assertEqual(r.status_code, 200)
        self.assertIn(b'read-only', r.data)
        self.assertNotIn(b'Commit script', r.data)
        self.assertEqual(self.dbrows('SELECT COUNT(*) FROM users')[0][0], 3)

    def test_read_script_runs(self):
        r = self.client.post('/query/', data={
            'sql': 'SELECT COUNT(*) FROM users; SELECT 1;'})
        self.assertIn(b'1/2', r.data)
        self.assertNotIn(b'Commit script', r.data)
        self.assertIn(b'<td class="num">\n              3\n', r.data)


if __name__ == '__main__':
    unittest.main()
