#!/usr/bin/env python3
# Source: fv/kraken/gen/tools/memory_limit.py of methodical-ssz commit 320929dd.
# Changes: without /proc (macOS), session_rss_ps reads the process table from `ps`. The /proc path did not change.
# killpg also ignores EPERM, which macOS returns for a group that holds only zombies.
"""Memory limit for one command.

The tool runs a command in its own session.
Each 0.1 s, it adds the anonymous RSS (RssAnon) of all processes in that session.
If the sum is more than the limit, the tool sends SIGKILL to the whole session and exits with 125.
With --per-proc, it also does this when the full VmRSS of one process is more than its limit.
At the end, the tool prints the peak values.
A trigger of the limit for one process sets its own flag. It does not change the reported session peak.

Usage: memory_limit.py <limit in bytes> [--per-proc <bytes>] -- command arguments...
       --per-proc: also kill the session when one process uses more than <bytes>
Exit status: the exit status of the command, or 125 if the limit killed it."""
import os
import signal
import subprocess
import sys
import time

cap = int(sys.argv[1])
args = sys.argv[2:]
pcap = None
if args[0] == "--per-proc":
    pcap = int(args[1]); args = args[2:]
assert args[0] == "--"
cmd = args[1:]
ppeak = 0
ptrig = False
child = subprocess.Popen(cmd, start_new_session=True)
sid = child.pid
peak = 0
killed = False


def session_rss_ps():
    """The session sum from `ps`, for a system without /proc (macOS).
    macOS `ps` prints 0 for the `sess` keyword. Thus os.getsid gives the session id.
    `ps` has no anonymous RSS. Thus the session sum adds the full RSS of each process.
    This sum also counts shared file pages, so it is larger than or equal to the /proc sum."""
    global ppeak, ptrig
    total = 0
    out = subprocess.run(["ps", "-axo", "pid=,rss="], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        try:
            pid, rss = (int(x) for x in line.split())
            if os.getsid(pid) != sid:  # the process can end between ps and getsid
                continue
        except (OSError, ValueError):
            continue
        r1 = rss * 1024  # ps prints the RSS in KiB
        ppeak = max(ppeak, r1)
        if pcap is not None and r1 > pcap:
            ptrig = True
        total += r1
    return total


def session_rss():
    global ppeak, ptrig
    if not os.path.isdir("/proc"):
        return session_rss_ps()
    total = 0
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            with open(f"/proc/{p}/stat") as f:
                st = f.read()
            fields = st[st.rindex(")") + 2:].split()
            if int(fields[3]) != sid:  # session id (field 6 overall)
                continue
            with open(f"/proc/{p}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):  # per process: full RSS
                        r1 = int(line.split()[1]) * 1024
                        ppeak = max(ppeak, r1)
                        if pcap is not None and r1 > pcap:
                            ptrig = True
                    elif line.startswith("RssAnon:"):  # session total: anonymous memory
                        total += int(line.split()[1]) * 1024
                        # VmRSS counts the shared file pages of mapped .olean files one time for each process.
                        # These pages are page cache. The OOM killer does not free them.
        except (OSError, ValueError, IndexError):
            continue
    return total


while child.poll() is None:
    r = session_rss()
    peak = max(peak, r)
    if r > cap or ptrig:
        killed = True
        try:
            os.killpg(sid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):  # macOS: EPERM when the group holds only zombies
            pass
        break
    time.sleep(0.1)
child.wait()
# Kill each process that is still in the session.
try:
    os.killpg(sid, signal.SIGKILL)
except (ProcessLookupError, PermissionError):  # macOS: EPERM when the group holds only zombies
    pass
print(f"MEMCAP peak_session_rss={peak} bytes ({peak / 2**30:.2f} GiB) cap={cap} peak_process_rss={ppeak} "
      f"({ppeak / 2**30:.2f} GiB) per_proc_cap={pcap} killed={killed} per_proc_trigger={ptrig} child_rc={child.returncode}",
      flush=True)
sys.exit(125 if killed else child.returncode)
