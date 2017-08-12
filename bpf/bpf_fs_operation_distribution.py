#!/usr/bin/python
from __future__ import print_function
from bcc import BPF
import argparse
import time
import datetime
import sys
import ctypes


BPF_PROGRAM = '''
#include <uapi/linux/ptrace.h>
#include <uapi/linux/limits.h>
#include <linux/sched.h>

BPF_HASH(start_at, u32, u64);
BPF_HISTOGRAM(dist, u32);

int trace_entry(struct pt_regs *ctx, const char __user *filename) {
    u64 pid_tgid = bpf_get_current_pid_tgid();
    u32 tid = (u32)pid_tgid;
    u32 pid = pid_tgid >> 32;

    %FILTER_PID%

    u64 ts = bpf_ktime_get_ns();
    start_at.update(&tid, &ts);
    return 0;
}

int trace_return(struct pt_regs *ctx) {
    u32 tid = (u32)bpf_get_current_pid_tgid();

    u64 *p = start_at.lookup(&tid);
    if (!p)
        return 0;
    u64 ts_start = *p;
    u64 ts_end = bpf_ktime_get_ns();
    u64 delta = ts_end - ts_start;

    u32 key = bpf_log2l(delta);
    dist.increment(key);

    start_at.delete(&tid);
    return 0;
}
'''


TARGET_EVENTS = {
    'open': ["ext4_file_open"],
    'read': ["generic_file_read_iter"],
    'write': ["ext4_file_write_iter"],
    'stat': ["sys_stat", "sys_statfs", "sys_newstat"],
    'unlink': ["vfs_unlink"],
    'sync': ["sys_sync"],
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--pid', metavar='PID', help='trace only this PID.')
    parser.add_argument('--interval', metavar='SEC', type=float, default=5.0, help='interval in seconds.')
    parser.add_argument('target', choices=['open', 'read', 'write', 'stat', 'unlink', 'sync'])
    args = parser.parse_args()

    interval_sec = args.interval
    target = args.target

    if args.pid is None:
        bpf_program = BPF_PROGRAM.replace('%FILTER_PID%', '')
    else:
        pid = int(args.pid)
        bpf_program = BPF_PROGRAM.replace('%FILTER_PID%', 'if (pid != {}) return 0;'.format(pid))

    bpf = BPF(text=bpf_program)
    for event in TARGET_EVENTS[args.target]:
        bpf.attach_kprobe(event=event, fn_name="trace_entry")
        bpf.attach_kretprobe(event=event, fn_name="trace_return")

    while True:
        time.sleep(interval_sec)
        ts = datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
        sys.stdout.write("ts:" + ts + "\ttarget:" + target)
        table = bpf['dist']
        for k, v in sorted(table.items(), key=lambda x: x[0].value):
            sys.stdout.write("\t" + str(2 ** k.value) + ":" + str(v.value))
        sys.stdout.write("\n")
        sys.stdout.flush()
        table.clear()


if __name__ == '__main__':
    main()
