"""
Run prove_BSD(two_desc='pari') over ALL rank<=1 optimal curves in the LMFDB
and emit a JSON file keyed by lmfdb_iso label (as in verify_bsd.json).

Design notes (this is a ~1.8M-curve, multi-day job):
  * Processed in conductor WINDOWS so memory stays bounded and the DB is
    queried in modest chunks.
  * RESUMABLE: every processed curve is appended to a JSONL working file, and
    each fully-completed window index is recorded in a progress file. On
    restart, already-done curves are skipped and done windows are not re-queried.
  * PARALLEL with a hard per-curve TIMEOUT (worker process is killed & replaced).
  * Errors / timeouts are recorded in the JSONL (so they are not retried) but
    are EXCLUDED from the final JSON, which contains only clean results.

Usage:
    sage -python bsd_full_run.py            # run / resume the computation
    sage -python bsd_full_run.py build-json # (re)build the JSON from the JSONL
"""
import sys
import os
import io
import re
import json
import time
import contextlib
import multiprocessing as mp

from lmfdb import db

# ---- config ----
QUERY = {'rank': {'$lte': 1}, 'optimality': 1}
COLS = ['ainvs', 'lmfdb_label']
TWO_DESC = 'pari'
TIMEOUT = 120              # seconds per curve
NWORKERS = 6
WINDOW = 2000             # conductor window size
COND_MAX = 500000        # max conductor in db is 499998

JSONL = 'verify_bsd_full.jsonl'      # resumable per-curve log
PROGRESS = 'verify_bsd_full.progress'  # completed window indices
FINAL_JSON = 'verify_bsd_full.json'   # final dict output


def iso_label(label):
    return re.sub(r'\d+$', '', label)


# ---------------- worker ----------------
def worker_loop(in_q, out_q):
    from sage.all import EllipticCurve
    while True:
        item = in_q.get()
        if item is None:
            return
        label, ainvs = item
        try:
            E = EllipticCurve(ainvs)
            with contextlib.redirect_stdout(io.StringIO()):
                r = E.prove_BSD(two_desc=TWO_DESC)
            if isinstance(r, list):
                out = ('ok', sorted(int(p) for p in r))
            else:
                out = ('allprimes', None)  # Set of all primes
        except Exception as e:
            out = ('error', f'{type(e).__name__}: {e}')
        out_q.put((label, out))


def make_worker():
    in_q, out_q = mp.Queue(), mp.Queue()
    p = mp.Process(target=worker_loop, args=(in_q, out_q), daemon=True)
    p.start()
    return {'proc': p, 'in_q': in_q, 'out_q': out_q, 'task': None, 'start': None}


def kill_worker(w):
    try:
        w['proc'].terminate()
        w['proc'].join(timeout=5)
        if w['proc'].is_alive():
            w['proc'].kill()
            w['proc'].join(timeout=5)
    except Exception:
        pass
    for q in (w['in_q'], w['out_q']):
        try:
            q.close()
        except Exception:
            pass


# ---------------- resume state ----------------
def load_done_labels():
    done = set()
    if os.path.exists(JSONL):
        with open(JSONL) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    done.add(json.loads(line)['label'])
                except Exception:
                    pass
    return done


def load_done_windows():
    done = set()
    if os.path.exists(PROGRESS):
        with open(PROGRESS) as f:
            for line in f:
                line = line.strip()
                if line:
                    done.add(int(line))
    return done


# ---------------- main run ----------------
def run():
    ec = db.ec_curvedata
    done_labels = load_done_labels()
    done_windows = load_done_windows()
    print(f"[info] resume: {len(done_labels)} curves already logged, "
          f"{len(done_windows)} windows complete", file=sys.stderr, flush=True)

    windows = [(i, i * WINDOW, (i + 1) * WINDOW)
               for i in range((COND_MAX + WINDOW - 1) // WINDOW)]
    windows = [w for w in windows if w[0] not in done_windows]

    jsonl_f = open(JSONL, 'a', buffering=1)  # line-buffered append
    workers = [make_worker() for _ in range(NWORKERS)]

    t_start = time.monotonic()
    n_done_session = 0

    def write_result(label, status, out):
        rec = {'label': label, 'iso': iso_label(label), 'status': status, 'out': out}
        jsonl_f.write(json.dumps(rec) + '\n')

    for widx, lo, hi in windows:
        # query this conductor window
        q = dict(QUERY)
        q['conductor'] = {'$gte': lo, '$lt': hi}
        curves = list(ec.search(q, projection=COLS))
        # tasks = curves not already logged
        tasks = [(c['lmfdb_label'], c['ainvs'])
                 for c in curves if c['lmfdb_label'] not in done_labels]
        outstanding = len(tasks)
        tasks.reverse()

        if outstanding == 0:
            # window had nothing new -> mark done
            with open(PROGRESS, 'a') as pf:
                pf.write(f"{widx}\n")
            continue

        # schedule this window to completion
        completed = 0
        while completed < outstanding:
            for w in workers:
                if w['task'] is None:
                    continue
                try:
                    label, (status, out) = w['out_q'].get_nowait()
                except Exception:
                    continue
                write_result(label, status, out)
                done_labels.add(label)
                w['task'] = None
                w['start'] = None
                completed += 1
                n_done_session += 1
            now = time.monotonic()
            for i, w in enumerate(workers):
                if w['task'] is not None and now - w['start'] > TIMEOUT:
                    label = w['task']
                    write_result(label, 'timeout', None)
                    done_labels.add(label)
                    kill_worker(w)
                    workers[i] = make_worker()
                    completed += 1
                    n_done_session += 1
            for w in workers:
                if w['task'] is None and tasks:
                    label, ainvs = tasks.pop()
                    w['in_q'].put((label, ainvs))
                    w['task'] = label
                    w['start'] = time.monotonic()
            time.sleep(0.02)

        with open(PROGRESS, 'a') as pf:
            pf.write(f"{widx}\n")
        rate = n_done_session / max(1e-9, time.monotonic() - t_start)
        print(f"[info] window {widx} (N in [{lo},{hi})) done: "
              f"{outstanding} curves | session total {n_done_session} | "
              f"{rate:.1f} curves/s | {len(done_labels)} logged overall",
              file=sys.stderr, flush=True)

    for w in workers:
        try:
            w['in_q'].put(None)
        except Exception:
            pass
    jsonl_f.close()
    print("[info] ALL WINDOWS COMPLETE -- building final JSON", file=sys.stderr, flush=True)
    build_json()


# ---------------- build final json ----------------
def build_json():
    out = {}
    kept = skipped = 0
    with open(JSONL) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if rec['status'] in ('ok', 'allprimes'):
                out[rec['iso']] = {'verify_bsd': rec['out']}
                kept += 1
            else:
                skipped += 1
    with open(FINAL_JSON, 'w') as f:
        json.dump(out, f)
    print(f"[info] wrote {FINAL_JSON}: {len(out)} entries "
          f"(kept {kept} clean, skipped {skipped} error/timeout)",
          file=sys.stderr, flush=True)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'build-json':
        build_json()
    else:
        mp.set_start_method('spawn', force=True)
        run()
