"""Make target controls and inspect the policy copy without running its checker."""
import ast
from pathlib import Path
import sys
import importlib.util
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
spec = importlib.util.spec_from_file_location('guards',
    Path(__file__).resolve().parents[1] / 'guard-lists.py')
guards = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guards)

NAMES = ('EXPECTED', 'ORDER')


def read(path):
    lines, _ = guards.read_guard(Path(path).read_text(), path)
    header, rest = ''.join(lines).split("<<'PY'\n", 1)
    body, trailer = rest.split('\nPY', 1)
    tree = ast.parse(body)
    nodes = {node.targets[0].id: node for node in tree.body
             if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name)
             and node.targets[0].id in NAMES}
    values = {name: ast.literal_eval(nodes[name].value) for name in NAMES}
    source = {name: ast.get_source_segment(body, nodes[name]) for name in NAMES}
    tree.body = [node for node in tree.body if node not in nodes.values()]
    return values, source, (header, ast.dump(tree), trailer)


mode, path, reference = sys.argv[1:4]
values, source, code = read(reference)
if mode == 'verify':
    merged_values, merged_source, merged_code = read(path)
    _, _, main_code = read(sys.argv[4])
    assert merged_values == values, 'policy copy lost target entries'
    assert merged_source == source, 'policy copy changed target literal source'
    assert merged_code == main_code, 'policy copy changed main checker code'
    print('guard list merge: target data and main code OK')
else:
    if mode == 'extra':
        values['EXPECTED'] += ('AvailableChain.FGSA.Run.precheckGuardListExtra',)
        values['ORDER'] += ('PrecheckGuardListExtra',)
    elif mode == 'drop':
        print(values['EXPECTED'][0])
        values['EXPECTED'] = values['EXPECTED'][1:]
    else:
        assert mode == 'permissive'
    # Poison target code in the list controls. Only main code may reach the copy.
    status = 0 if mode == 'permissive' else 99
    Path(path).write_text("#!/usr/bin/env bash\nexec python3 - \"$@\" <<'PY'\n"
                          + ''.join(f'{name} = {values[name]!r}\n' for name in NAMES)
                          + f'raise SystemExit({status})\nPY\n')
