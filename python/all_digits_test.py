"""All hex digits of pi by independent windows: how does it compare with y-cruncher?

    python all_digits_test.py scan   <position> <window> [<window> ...]
    python all_digits_test.py full   <N> <window> <output file> [reference hex file]
    python all_digits_test.py sample <N> <window> <how many>

All sizes are in hex digits. `scan` times single windows of several sizes at one
position. `full` computes every window from 0 to N and writes the digits. `sample`
times a few evenly spaced windows and scales up to all N/window of them.

For each run it reports elapsed time and processor time (all threads of the process,
from the operating system). The window program also uses the GPU; its GPU stage is
reported as elapsed time ("word").
"""
import ctypes
import os
import re
import subprocess
import sys
import time
from ctypes import wintypes

HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, "..", "engine", "piwindow.exe")
FORMULA = os.environ.get("PIW_FORMULA", "new")


def cpu_seconds(handle):
    c, e, k, u = wintypes.FILETIME(), wintypes.FILETIME(), wintypes.FILETIME(), wintypes.FILETIME()
    ok = ctypes.windll.kernel32.GetProcessTimes(wintypes.HANDLE(handle), ctypes.byref(c), ctypes.byref(e),
                                                ctypes.byref(k), ctypes.byref(u))
    if not ok:
        return float("nan")
    val = lambda ft: (ft.dwHighDateTime << 32 | ft.dwLowDateTime) / 1e7
    return val(k) + val(u)


def window(position, digits, out, extra=()):
    """Run one window. Returns a dict of timings."""
    t = time.time()
    proc = subprocess.Popen([EXE, str(position), str(digits), "--formula", FORMULA, "--out", out, *extra],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    _, err = proc.communicate()
    wall = time.time() - t
    cpu = cpu_seconds(int(proc._handle))
    if proc.returncode != 0:
        raise RuntimeError("piwindow failed at %d: %s" % (position, err[-400:]))
    res = {"wall": wall, "cpu": cpu}
    m = re.search(r"word stage ([\d.]+)s, sieve ([\d.]+)s, big-number sums ([\d.]+)s, tail ([\d.]+)s", err)
    if m:
        res.update(word=float(m.group(1)), sieve=float(m.group(2)), sums=float(m.group(3)), tail=float(m.group(4)))
    m = re.search(r"trees ([\d.]+)s, divisions ([\d.]+)s", err)
    if m:
        res.update(trees=float(m.group(1)), divs=float(m.group(2)))
    m = re.search(r"\((\d+) fractions, (\d+) blocks\)", err)
    if m:
        res.update(fractions=int(m.group(1)), blocks=int(m.group(2)))
    return res


def fmt(r):
    return ("wall %7.1f s  cpu %8.1f s  | word %6.1f  sieve %6.1f  sums %6.1f  tail %5.1f | trees %8.1f  divs %7.1f | %d blocks"
            % (r["wall"], r["cpu"], r.get("word", 0), r.get("sieve", 0), r.get("sums", 0), r.get("tail", 0),
               r.get("trees", 0), r.get("divs", 0), r.get("blocks", 0)))


def scan(position, sizes):
    tmp = os.path.join(os.environ.get("TEMP", HERE), "piw_scan.txt")
    print("single windows at hex position %d (formula %s)" % (position, FORMULA))
    for w in sizes:
        r = window(position, w, tmp)
        print("  window %11d: %s | per digit: wall %.3g s, cpu %.3g s" % (w, fmt(r), r["wall"] / w, r["cpu"] / w))
        sys.stdout.flush()


def full(n, w, outfile, reference=None):
    tmp = os.path.join(os.environ.get("TEMP", HERE), "piw_full.txt")
    tot = {"wall": 0.0, "cpu": 0.0}
    t0 = time.time()
    with open(outfile, "w") as out:
        pos = 0
        while pos < n:
            count = min(w, n - pos)
            r = window(pos, count, tmp)
            digits = open(tmp).read().strip()
            assert len(digits) == count, (pos, len(digits))
            out.write(digits)
            tot["wall"] += r["wall"]
            tot["cpu"] += r["cpu"]
            pos += count
    print("all %d hex digits in windows of %d: %d windows, wall %.1f s (sum of windows %.1f), cpu %.1f s"
          % (n, w, -(-n // w), time.time() - t0, tot["wall"], tot["cpu"]))
    if reference:
        ref = open(reference).read()
        ref = ref.split(".", 1)[1] if "." in ref[:4] else ref
        got = open(outfile).read()
        same = got == ref[:len(got)].upper()
        print("compared %d digits with %s: %s" % (len(got), os.path.basename(reference), "MATCH" if same else "MISMATCH"))
        if not same:
            bad = next(i for i, (a, b) in enumerate(zip(got, ref.upper())) if a != b)
            print("  first difference at digit %d" % (bad + 1))
    return tot


def sample(n, w, k):
    tmp = os.path.join(os.environ.get("TEMP", HERE), "piw_sample.txt")
    count = -(-n // w)
    picks = sorted({min(count - 1, int((i + 0.5) * count / k)) for i in range(k)})
    walls, cpus = [], []
    print("N = %d, window %d: %d windows in all; timing %d of them" % (n, w, count, len(picks)))
    for i in picks:
        r = window(i * w, min(w, n - i * w), tmp)
        walls.append(r["wall"])
        cpus.append(r["cpu"])
        print("  window %4d at %11d: %s" % (i, i * w, fmt(r)))
        sys.stdout.flush()
    est_wall = sum(walls) / len(walls) * count
    est_cpu = sum(cpus) / len(cpus) * count
    print("  estimate for all %d windows: wall %.0f s, cpu %.0f s" % (count, est_wall, est_cpu))
    return est_wall, est_cpu


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "scan":
        scan(int(sys.argv[2]), [int(x) for x in sys.argv[3:]])
    elif mode == "full":
        full(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5] if len(sys.argv) > 5 else None)
    elif mode == "sample":
        sample(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
