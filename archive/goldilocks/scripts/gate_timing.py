"""Small timing records, separate from command stdout and stderr."""
import argparse
import json
from pathlib import Path
import re
import time


def write(path, record):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, sort_keys=True) + '\n')
    temporary.replace(path)


def begin(path, label, args=(), control=None):
    now = time.time()
    write(path, dict(label=label, control=control, command=list(args), queued=now,
                     start=None, slot_acquired=None, end=None, rc=None,
                     cpu_user_s=None, cpu_system_s=None, peak_rss_bytes=None))


def update(path, **fields):
    record = json.loads(path.read_text())
    record.update(fields)
    write(path, record)


def resources(path):
    result = {}
    if not path.exists():
        return result
    raw = path.read_text()
    # GNU time (-v) and BSD time (-l) use different units for peak RSS.
    for field, patterns in (
        ('cpu_user_s', (r'User time \(seconds\): ([\d.]+)', r'([\d.]+) user')),
        ('cpu_system_s', (r'System time \(seconds\): ([\d.]+)', r'([\d.]+) sys')),
        ('peak_rss_bytes', (r'Maximum resident set size \(kbytes\): (\d+)',
                            r'(\d+)\s+maximum resident set size')),
    ):
        for i, pattern in enumerate(patterns):
            match = re.search(pattern, raw)
            if match:
                value = float(match[1])
                result[field] = int(value * (1024 if i == 0 else 1)) \
                    if field == 'peak_rss_bytes' else value
                break
    # Bash reserved `time`, used for shell functions and their descendants.
    match = re.search(r'GATE_CPU ([\d.]+) ([\d.]+)', raw)
    if match:
        result.update(cpu_user_s=float(match[1]), cpu_system_s=float(match[2]))
    return result


def finish(path, rc, resource_path=None):
    slots = path.with_suffix('.slots')
    acquired = [float(x) for x in slots.read_text().splitlines()] if slots.exists() else []
    measured = resources(Path(str(path) + '.time'))
    if resource_path:
        measured.update(resources(resource_path))
    update(path, end=time.time(), rc=rc,
           slot_acquired=min(acquired) if acquired else None,
           slot_acquisitions=acquired,
           **measured)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('queue', 'start', 'slot', 'finish', 'cancel'))
    parser.add_argument('path', type=Path)
    parser.add_argument('extra', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.action == 'queue':
        begin(args.path, *args.extra)
    elif args.action == 'start':
        if not args.path.exists():
            begin(args.path, args.extra[0])
        update(args.path, start=time.time(), command=args.extra[1:],
               control=args.extra[0] if 'control' in args.extra[0] else None)
    elif args.action == 'slot':
        with args.path.with_suffix('.slots').open('a') as out:
            out.write(str(time.time()) + '\n')
    elif args.action == 'cancel':
        record = json.loads(args.path.read_text())
        if record['end'] is None:
            finish(args.path, 143 if record['start'] is not None else 125)
            update(args.path, status='terminated' if record['start'] is not None else 'not submitted')
    else:
        finish(args.path, int(args.extra[0]),
               Path(args.extra[1]) if len(args.extra) > 1 else None)
