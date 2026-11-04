"""Run a subprocess with a wall-clock timeout and a memory (RSS) cap.

Adapted from popso's benchmarks/lib/proc.py (same author, Apache-2.0).  The machine is shared,
so every solver / checker process started by the tooling is memory-capped:

* Parent side, portable (macOS and Linux): a watchdog samples the resident set size of the
  child's whole process group with `ps` every `poll` seconds and kills the group when it
  exceeds the cap (reason 'memlimit').  macOS does not enforce RLIMIT_AS, so this is the
  mechanism that matters there.
* Linux additionally gets RLIMIT_AS = 2 x the cap on the child (prlimit after spawn), so a
  runaway allocation between two samples fails inside the child instead of swapping.
* The child runs in its own session/process group; on timeout, memlimit or interruption the
  whole group is killed, so no grandchild (e.g. a solver started by a wrapper) survives.
* The exit status is collected with os.wait4 in a helper thread: exact end time and the
  child's own peak RSS (ru_maxrss) and CPU time.
"""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass

IS_POSIX = os.name == "posix"


@dataclass
class RunResult:
    returncode: int | None      # None if killed by us; negative = killed by that signal
    reason: str | None          # None, 'timeout' or 'memlimit'
    wall: float                 # seconds
    cpu: float                  # user + system seconds of the child (POSIX), else wall
    peak_rss_mb: float          # max of sampled group RSS and the child's ru_maxrss


def limit_self(mb):
    """RLIMIT_AS/RLIMIT_DATA for the current process (enforced on Linux, mostly not on macOS)."""
    if not mb:
        return
    try:
        import resource
    except ImportError:  # Windows
        return
    lim = int(mb) * 1024 * 1024
    for name in ("RLIMIT_AS", "RLIMIT_DATA"):
        r = getattr(resource, name, None)
        if r is None:
            continue
        try:
            _, hard = resource.getrlimit(r)
            soft = lim if hard == resource.RLIM_INFINITY else min(lim, hard)
            resource.setrlimit(r, (soft, hard))
        except (ValueError, OSError):
            pass


def _group_rss_mb(pgid: int) -> float:
    """Resident set size (MB) summed over a process group (POSIX `ps`)."""
    try:
        out = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True,
                             timeout=5).stdout
    except (OSError, subprocess.SubprocessError):
        return 0.0
    total = 0
    for ln in out.splitlines():
        f = ln.split()
        if len(f) == 2 and f[0] == str(pgid) and f[1].isdigit():
            total += int(f[1])
    return total / 1024.0


def _rss_mb_psutil(pid) -> float:
    try:
        import psutil  # optional, Windows only
        p = psutil.Process(pid)
        return sum(q.memory_info().rss for q in [p] + p.children(recursive=True)) / 1048576.0
    except Exception:  # noqa: BLE001 - no psutil / process gone
        return 0.0


_live: set = set()  # running children (killed by kill_all on interruption)
_live_lock = threading.Lock()


def _kill_group(p):
    if IS_POSIX:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
    else:
        try:
            p.kill()
        except OSError:
            pass


def kill_all():
    """Kill every process group started by run_capped that is still running."""
    with _live_lock:
        procs = list(_live)
    for p in procs:
        _kill_group(p)


def _set_rlimit_as(pid, mb):
    if not mb or not sys.platform.startswith("linux"):
        return
    try:
        import resource
        lim = int(mb * 2) * 1024 * 1024
        resource.prlimit(pid, resource.RLIMIT_AS, (lim, lim))
    except (ImportError, AttributeError, ValueError, OSError):
        pass


def run_capped(cmd, timeout, mem_mb=None, stdout=None, stderr=None, poll=0.5, cwd=None,
               env=None, stdin=subprocess.DEVNULL) -> RunResult:
    """Run cmd (argv list) with a wall-clock limit (seconds; None = none) and an RSS cap
    (MB; None/0 = none).  If the caller is interrupted, the child's group is killed."""
    t0 = time.perf_counter()
    kw = {"start_new_session": True} if IS_POSIX else {}
    p = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, stdin=stdin, cwd=cwd, env=env, **kw)
    with _live_lock:
        _live.add(p)
    _set_rlimit_as(p.pid, mem_mb)
    done = threading.Event()
    res = {}

    def waiter():
        if IS_POSIX:
            try:
                _, status, ru = os.wait4(p.pid, 0)
                res["t"] = time.perf_counter()
                res["rc"] = os.waitstatus_to_exitcode(status)
                maxrss = ru.ru_maxrss / (1048576.0 if sys.platform == "darwin" else 1024.0)
                res["cpu"], res["maxrss"] = ru.ru_utime + ru.ru_stime, maxrss
            except ChildProcessError:
                res["t"], res["rc"] = time.perf_counter(), None
        else:
            res["rc"] = p.wait()
            res["t"] = time.perf_counter()
        done.set()

    th = threading.Thread(target=waiter, daemon=True)
    th.start()
    reason = None
    peak = 0.0
    try:
        while not done.wait(poll):
            if mem_mb:
                rss = _group_rss_mb(p.pid) if IS_POSIX else _rss_mb_psutil(p.pid)
                peak = max(peak, rss)
                if rss > mem_mb:
                    reason = "memlimit"
            if timeout is not None and time.perf_counter() - t0 > timeout:
                reason = reason or "timeout"
            if reason:
                _kill_group(p)
                done.wait()
                break
    except BaseException:
        _kill_group(p)
        done.wait(5)
        raise
    finally:
        # orphans of the group (e.g. a wrapper's worker) must not outlive the run
        _kill_group(p)
        with _live_lock:
            _live.discard(p)
    p.returncode = res.get("rc") if res.get("rc") is not None else -9
    wall = res.get("t", time.perf_counter()) - t0
    peak = max(peak, res.get("maxrss", 0.0))
    return RunResult(None if reason else res.get("rc"), reason, wall, res.get("cpu", wall), peak)
