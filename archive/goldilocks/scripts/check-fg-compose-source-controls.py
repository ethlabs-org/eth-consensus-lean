#!/usr/bin/env python3
"""Focused positive and negative controls for the Compose constructor inventory."""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import subprocess
import sys
import tempfile
from unittest.mock import patch

import check_common as C
import check_inventory as I

CHECKER = 'scripts/check-fg-compose-source.py'
PREFIX = 'AvailableChain.FGCompose.'


def check(fixture, label, source, names, code=0, diagnostic=''):
    fixture.write_text(source)
    lf = C.LeanFile('AvailableChainFGCompose', str(fixture),
                    'AvailableChainFGCompose.Statements.ConstructorFixture')
    output, result = io.StringIO(), 0
    with patch.object(C, 'library_files', return_value=[lf]), \
            patch.object(I, 'read_names', return_value=names), redirect_stdout(output):
        try:
            runpy.run_path(CHECKER)
        except SystemExit as error:
            result = error.code
    if code == 'reject':
        valid = isinstance(result, str) and result.startswith('UNSUPPORTED INDUCTIVE ')
    else:
        valid = result == code and diagnostic in output.getvalue()
    if not valid:
        raise AssertionError((label, result, output.getvalue()))
    print(label + ': PASS')


def main():
    count = 0
    with tempfile.TemporaryDirectory(prefix='ctor-controls-', dir='.lake') as scratch:
        fixture = Path(scratch) / 'Fixture.lean'
        layouts = {
            'ordinary': 'inductive I : Prop\n  | make : I\n  | overlooked : I\n',
            'where': 'inductive I : Prop where\n  | make : I\n  | overlooked : I\n',
            'header line': 'inductive I : Prop where | make : I | overlooked : I\n',
            'same line': 'inductive I : Prop\n  | make : I | overlooked : I\n',
            'split bar/name': ('inductive I : Prop where\n  |\n    make : I\n'
                               '  |\n    overlooked : I\n'),
            'multiline binders': ('inductive I : Prop where\n  | make\n    (n : Nat)\n'
                                  '    : I\n  | overlooked\n    (n : Nat) : I\n'),
            'comments/docstrings': ('/-! | fake -/\ninductive I : Prop where\n'
                                    '  /-- | fake /- | nested -/ -/\n  | /- gap -/ make : I\n'
                                    '  -- | fake\n  | overlooked : I\n'),
        }
        names = {PREFIX + name for name in ('I', 'I.make', 'I.overlooked')}
        for label, body in layouts.items():
            source = 'namespace AvailableChain.FGCompose\n' + body + 'end\n'
            check(fixture, label + ' complete', source, names)
            check(fixture, label + ' unlisted', source, names - {PREFIX + 'I.overlooked'},
                  2, 'UNLISTED: [\'' + PREFIX + 'I.overlooked')
            count += 2
        check(fixture, 'comment-only constructor excluded',
              'namespace AvailableChain.FGCompose\n' + layouts['comments/docstrings'] + 'end\n',
              names | {PREFIX + 'I.fake'}, 2, 'MISSING:')
        count += 1
        for name in ("make'", 'make!', 'make?', 'étape₂', '_make'):
            source = f'namespace AvailableChain.FGCompose\ninductive I where | {name} : I\nend\n'
            exact = {PREFIX + 'I', PREFIX + 'I.' + name}
            check(fixture, name + ' exact', source, exact)
            check(fixture, name + ' unlisted', source, {PREFIX + 'I'}, 2, 'UNLISTED:')
            check(fixture, name + ' substituted', source, {PREFIX + 'I', PREFIX + 'I.make'},
                  2, 'UNLISTED:')
            count += 3
        source = ('namespace AvailableChain.FGCompose\ninductive I where | make : I\n'
                  '#check match true with\n  | true => I.make\n  | false => I.make\nend\n')
        exact = {PREFIX + 'I', PREFIX + 'I.make'}
        check(fixture, '#check-match excluded', source, exact)
        check(fixture, '#check-match fabricated', source,
              exact | {PREFIX + 'I.true', PREFIX + 'I.false'}, 2, 'MISSING:')
        check(fixture, '#check-match unlisted real constructor', source,
              {PREFIX + 'I'}, 2, 'UNLISTED:')
        count += 3
        source = ('namespace AvailableChain.FGCompose\nnamespace Nested\n'
                  'inductive I where | make : I\n'
                  'private inductive Hidden where | secret : Hidden\n'
                  'def following : Nat := 0\nend Nested\nend\n')
        exact = {PREFIX + 'Nested.' + name for name in ('I', 'I.make', 'following')}
        check(fixture, 'namespace and following declaration', source, exact)
        check(fixture, 'private constructor excluded', source,
              exact | {PREFIX + 'Nested.Hidden.secret'}, 2, 'MISSING:')
        check(fixture, 'qualified unlisted', source, exact - {PREFIX + 'Nested.I.make'},
              2, 'UNLISTED:')
        count += 3
        for label, body in {
            'escaped identifier': 'inductive I where | «make with space» : I\n',
            'combining identifier': 'inductive I where | e\u0301 : I\n',
            'unindented constructor': 'inductive I where\n| make : I\n',
            'indented command': ('inductive I where\n  | make : I\n'
                                 '  #check match true with\n    | true => I.make\n'),
            'nested match': 'inductive I where | make : (match true with | _ => I)\n',
            'nested bar': 'inductive I where | make (x : (Nat | Nat)) : I\n',
            'pattern lambda': 'inductive I where | make : (fun | _ => I) true\n',
            'constructor modifier': 'inductive I where | protected make : I\n',
            'same-line command': 'inductive I where | make : I #check true\n',
        }.items():
            source = 'namespace AvailableChain.FGCompose\n' + body + 'end\n'
            check(fixture, label + ' rejected', source, {PREFIX + 'I'}, 'reject')
            count += 1
        for modifier in ('private', 'public', 'protected', 'meta', 'noncomputable',
                         'unsafe', 'partial', 'nonrec'):
            source = ('namespace AvailableChain.FGCompose\ninductive I where\n'
                      f'  | {modifier} make : I\nend\n')
            for label, names in (('exact', {'make'}), ('substituted', {modifier})):
                check(fixture, f'{modifier} constructor modifier with {label} inventory rejected',
                      source, {PREFIX + 'I'} | {PREFIX + 'I.' + n for n in names}, 'reject')
                count += 1
        derived = 'inductive I where\n  | make | other\n  deriving DecidableEq\n'
        exact = {PREFIX + n for n in ('I', 'I.make', 'I.other', 'instDecidableEqI')}
        source = 'namespace AvailableChain.FGCompose\n' + derived + 'end\n'
        check(fixture, 'deriving DecidableEq exact', source, exact)
        check(fixture, 'deriving DecidableEq unlisted instance', source,
              exact - {PREFIX + 'instDecidableEqI'}, 2, 'UNLISTED:')
        check(fixture, 'deriving DecidableEq fabricated deriving name', source,
              exact | {PREFIX + 'I.deriving'}, 2, 'MISSING:')
        source = ('namespace AvailableChain.FGCompose\nnamespace Nested\n' + derived
                  + 'end Nested\nend\n')
        check(fixture, 'nested deriving DecidableEq exact', source,
              {PREFIX + 'Nested.' + n for n in ('I', 'I.make', 'I.other', 'instDecidableEqI')})
        count += 4
        for label, body in {
            'deriving two classes': 'inductive I where\n  | make\n  deriving DecidableEq, Repr\n',
            'deriving other class': 'inductive I where\n  | make\n  deriving Repr\n',
            'same-line deriving': 'inductive I where | make deriving DecidableEq\n',
            'dotted deriving type': 'inductive Q.I where\n  | make\n  deriving DecidableEq\n',
            'lowercase deriving type': 'inductive lower where\n  | make\n  deriving DecidableEq\n',
        }.items():
            source = 'namespace AvailableChain.FGCompose\n' + body + 'end\n'
            check(fixture, label + ' rejected', source, {PREFIX + 'I'}, 'reject')
            count += 1
        source = ('namespace AvailableChain.FGCompose\nnamespace Nested\ninductive lower where\n'
                  '  | a | b\n  deriving DecidableEq\nend Nested\nend\n')
        for label, inst in (('actual', 'instDecidableEqLower'),
                            ('fabricated', 'instDecidableEqlower')):
            names = {PREFIX + 'Nested.' + n for n in ('lower', 'lower.a', 'lower.b', inst)}
            check(fixture, f'nested lowercase deriving, {label} instance, rejected', source,
                  names, 'reject')
            count += 1
        collision = ('namespace AvailableChain.FGCompose\ndef instDecidableEqI : Nat := 0\n'
                     'inductive I where\n  | a | b\n  deriving DecidableEq\nend\n')
        base = {PREFIX + n for n in ('instDecidableEqI', 'I', 'I.a', 'I.b')}
        for label, names in (('omitted', base),
                             ('suffixed', base | {PREFIX + 'instDecidableEqI_1'})):
            check(fixture, f'derived name collision with {label} instance rejected', collision,
                  names, 'reject')
            count += 1
        holder = ('inductive I where\n  | a | b\n  deriving DecidableEq\n'
                  'end Holder\n')
        for label, body, extra in (
                ('constructor', 'inductive Holder where\n  | instDecidableEqI\n'
                 'namespace Holder\n' + holder, ('Holder', 'Holder.instDecidableEqI')),
                ('projection', 'structure Holder where\n  instDecidableEqI : Nat\n'
                 'namespace Holder\n' + holder,
                 ('Holder', 'Holder.mk', 'Holder.instDecidableEqI')),
                ('private derived', 'private inductive i where\n  | a\n  deriving DecidableEq\n'
                 'namespace Holder\n' + holder, ())):
            source = 'namespace AvailableChain.FGCompose\n' + body + 'end\n'
            base = {PREFIX + n for n in extra + ('Holder.I', 'Holder.I.a', 'Holder.I.b')}
            for kind, names in (('omitted', base),
                                ('complete', base | {PREFIX + 'Holder.instDecidableEqI_1'})):
                check(fixture, f'{label} collision, {kind} instance, rejected', source,
                      names, 'reject')
                count += 1
        source = ('namespace AvailableChain.FGCompose\nprivate inductive lower where\n'
                  '  | a | b\n  deriving DecidableEq\ninductive Lower where\n  | a | b\n'
                  '  deriving DecidableEq\nend\n')
        base = {PREFIX + n for n in ('Lower', 'Lower.a', 'Lower.b')}
        for kind, inst in (('fabricated', 'instDecidableEqLower'),
                           ('actual', 'instDecidableEqLower_1')):
            check(fixture, f'private/public derived clash, {kind} instance, rejected', source,
                  base | {PREFIX + inst}, 'reject')
            count += 1
        public = 'inductive Lower where\n  | a | b\n  deriving DecidableEq\n'
        base = {PREFIX + n for n in ('Lower', 'Lower.a', 'Lower.b')}
        for label, body, extra in (
                ('inline private header', 'private inductive lower where | a | b deriving '
                 'DecidableEq\n', ()),
                ('inline private constructor', 'private inductive lower where\n  | a | b deriving '
                 'DecidableEq\n', ()),
                ('inline private structure', 'private structure lower where\n  x : Nat deriving '
                 'DecidableEq\n', ()),
                ('inline public structure', 'structure lower where\n  x : Nat deriving '
                 'DecidableEq\n', ('lower', 'lower.mk', 'lower.x'))):
            source = 'namespace AvailableChain.FGCompose\n' + body + public + 'end\n'
            names = base | {PREFIX + n for n in extra}
            for kind, inst in (('omitted', 'instDecidableEqLower'),
                               ('complete', 'instDecidableEqLower_1')):
                check(fixture, f'{label} deriving, {kind} instance, rejected', source,
                      names | {PREFIX + inst}, 'reject')
                count += 1
    result = subprocess.run([sys.executable, '-B', CHECKER], check=True,
                            capture_output=True, text=True)
    coverage = re.search(r'; (\d+) public declarations/projections', result.stdout)
    if not coverage or int(coverage[1]) < 373:
        raise AssertionError(result.stdout)
    print(result.stdout, end='')
    print(f'Compose constructor controls: PASS ({count} fixtures; real tree)')


if __name__ == '__main__':
    main()
