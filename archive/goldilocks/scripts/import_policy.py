"""One import-policy data source for source and compiled checks."""
import json
from pathlib import Path
import re

DATA = Path(__file__).with_name('import-policy.json')


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f'duplicate import-policy key: {key}')
        out[key] = value
    return out


def read_policy(text):
    policy = json.loads(text, object_pairs_hook=unique_object)
    rows = list(policy['groups'].values())
    rows += [entries for profile in policy['profiles'].values() for entries in profile.values()]
    for entries in rows:
        if len(entries) != len(set(entries)):
            raise ValueError('duplicate import-policy entry')
    return policy


POLICY = read_policy(DATA.read_text())


def expand(rows, seen=()):
    if len(rows) != len(set(rows)):
        raise ValueError('duplicate import-policy entry')
    out = []
    for row in rows:
        if row.startswith('@'):
            name = row[1:]
            if name in seen or name not in POLICY['groups']:
                raise ValueError(f'invalid import-policy group: {name}')
            out.extend(expand(POLICY['groups'][name], (*seen, name)))
        else:
            if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9]*)*'
                                r'(?:\.\*\*?)?', row):
                raise ValueError(f'invalid import-policy entry: {row}')
            out.append(row)
    if len(out) != len(set(out)):
        raise ValueError('duplicate expanded import-policy entry')
    return out


def matches_rows(rows, name):
    for row in expand(rows):
        if row.endswith('.**'):
            if name == row[:-3] or name.startswith(row[:-2]):
                return True
        elif row.endswith('.*'):
            if name.startswith(row[:-1]):
                return True
        elif name == row:
            return True
    return False


def matches(group, name):
    return matches_rows(POLICY['groups'][group], name)


def allowed(library, layer, name):
    return matches_rows(POLICY['profiles'][library].get(layer, []), name)
