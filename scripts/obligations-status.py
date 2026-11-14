#!/usr/bin/env python3
"""Regenerate the obligations status ledger (the sorry status of the Goldilocks `MeetsObligations`
proof); paper classifications are preserved, never inferred.

Run after building ConsensusLean and spec-surface. Historical source scans select
former sorry declarations; compiled dependency edges determine their current status.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

# Whole-statement ratings: (rating, evidence) of a sorry owner's paper argument. A rating applies to a row that has
# no status yet, or on every run to a REFRESH row; the ledger's own earlier status otherwise stands.
# Evidence of a proved row outside REFRESH: the compiled audit fact, not prose.
PROVED_EVIDENCE = 'Proved; no direct owner in compiled audit at '
# Rows whose RATINGS entry replaces the previous row's rating and evidence on every run.
# contract_catchUp/heal/latency are defined in Statements/Obligations, outside the Lemmas scan, so they are never
# rows: their REFRESH/RATINGS entries (and their RENAMED_COMPONENTS entries) take effect only in the self-test
# fixture; the real ledger lists them under historical_removed by their old names. (Their *_ge_sleepy lemmas are
# in Lemmas/Obligations/ContractDefs and are rows.)
REFRESH = ('contract_heal', 'final_window_extract', 'final_reset_premises')
RATINGS = {
    'contract_catchUp': ('paper-partial', 'Settled coefficient audit: simultaneous finite engine envelope and repaired transport remain; no arbitrary witness choice.'),
    'contract_heal': ('lean-proved', 'Closed at 4078bc74 (S6): contract_catchUp + 2·healMargin + 3 at every capability, a named parameter-only value (ResetCoefficients) fitted to the proved reset envelope. contract_heal_ge_reset is the coefficient inequality of the nonfinal envelope, contract_heal_ge_final the final route heal-bound margin; a later leaf may raise healMargin, consumers use only these ≥-forms.'),
    'contract_latency': ('paper-partial', 'Settled coefficient audit: joint nonfinal/four-anchor latency and actual carrier acceptance remain.'),
    'contract_catchUp_ge_sleepy': ('paper-partial', 'Settled coefficient audit: 37 is a verified constraint, not a proof about the opaque shared witness; enlargement needs monotonicity audit.'),
    'contract_latency_ge_sleepy': ('paper-partial', 'Settled coefficient audit: 8idx+12 is a verified constraint, not a jointly admissible selected witness.'),
    'final_window_extract': ('lean-proved', "Body final_window_extract_of' from final_reset_premises (closed at e621acd7) and final_duty_proposal (final_duty_proposal_run)."),
    # Route-A split of final_window_extract: its body is final_window_extract_of'
    # from these two leaves (final_duty_proposal has a proved body); the rating is inherited
    # from final_window_extract.
    'final_reset_premises': ('lean-proved', "Closed at e621acd7 by final_reset_premises_of_query (FinalResetPremises.lean): exists_reset_of_drain_awake at r = ready, G = X, L_drain = healthyDrainLen, λ = 2Δ, b = horizon, with the guarded gap final_query_gap and drainOutputs_of_service; (H3) and the horizon fit from contract_heal_ge_final."),
    'final_duty_proposal': ('paper-partial', "(H2) of final_window_extract_of': duty → proposal adapter, bounded by 0 < s and ts s ≤ horizon; body proved by final_duty_proposal_run (FinalDutyProposal.lean)."),
    # Historical rating; the declaration is retired by route A, see RETIRED.
    'final_inherited_progress': ('paper-open (research)', 'Settled final-liveness audit: arbitrary dirty inherited permissions/held or credited rows must yield same-entry progress without a birth lower bound.'),
    'final_row_supply': ('paper-open (research)', 'Research refinement: high same-entry/high-predecessor row algebra is proved conditionally; report_cover, inherited/low entries and carrier credit/acceptance remain.'),
    'final_cache_acceptance': ('paper-partial', 'Settled final-liveness audit: actual last-carrier acceptance, retained lookup/cache for every reader and processing/read deadline budget remain.'),
    # Historical rating; the declaration is retired by R0, see RETIRED.
    'healthy_old_inventory_initialize': ('paper-open (research)', 'Global future first arrivals require upper coverage or strict below-hj, including equality; bounded actual reset production missing.'),
    'outage_repair': ('paper-open (research)', 'Covering nonvetoed renewal, pool bound/resolutions, RESULT compatibility, persistence and both reader branches remain.'),
    'vote_old_live_lock_below_parent': ('paper-proved awaiting Lean', 'Provenance+l+2 transfer and separate optimistic u−1 branch; non-vote full-tree domain/service integration remains.'),
    'ready_unanimous': ('paper-partial', 'Actual first-deviation head/walk/payload equality remains, not merely parent extension.'),
    'higher_report_window_origin': ('paper-proved awaiting Lean', 'Reset_origin_below and same-store high_of_anc establish high C, then high_report_origin; no unheld receiver height.'),
    'update_window_kept': ('paper-partial', 'Actual update-frame viable-or-higher-origin dichotomy remains; hsrc can be vacuous; no reverse raw→stored ancestry.'),
}


def run(*args):
    return subprocess.check_output(args, text=True)


def declarations(text):
    # Preserve line numbers while removing nested Lean comments and strings.
    text = re.sub(r'"(?:\\.|[^"\\])*"', lambda m: '"' + '\n' * m[0].count('\n') + '"', text)
    depth = 0
    clean = []
    i = 0
    while i < len(text):
        if text[i:i + 2] == '/-':
            depth += 1
            clean.append('  ')
            i += 2
        elif depth and text[i:i + 2] == '-/':
            depth -= 1
            clean.append('  ')
            i += 2
        elif not depth and text[i:i + 2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            clean.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    text = ''.join(clean)
    matches = list(re.finditer(
        r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+([\w.]+)',
        text, re.M))
    namespace = re.search(r'^namespace (Consensus\.[\w.]+)', text, re.M)
    if not namespace:
        return []
    result = []
    for index, match in enumerate(matches):
        name = match[1]
        if name.startswith('_root_.'):
            name = name[7:]
        else:
            # The namespace blocks open at the declaration (a file may close one and open another).
            stack = []
            for block in re.finditer(r'^(namespace|end)\s+([\w.]+)', text[:match.start()], re.M):
                if block[1] == 'namespace':
                    stack.append(block[2])
                elif stack and stack[-1] == block[2]:
                    stack.pop()
            name = ('.'.join(stack) if stack else namespace[1]) + '.' + name
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result.append((name, text.count('\n', 0, match.start()) + 1,
                       bool(re.search(r'\bsorry\b', text[match.end():end]))))
    return result


# Renames of declarations and of name components since the ledger's first audit. `Goldilocks.Refinement` was split
# into `Goldilocks.AsChainShape`, `.Simulation`, `.Obligations` and the root `Consensus.Goldilocks`; the contract,
# endpoint and family names were renamed, then the FG attestation lemmas, `rowDelay` (and its lemmas) to
# `protoFGDelay`, `PSyncFGRowTransport` to `PSyncFGAttTransport`, and Concrete's field theorems and existential
# endpoint (`accepted`, the step 3c root) after `MeetsObligations`. Historical source blobs still carry the old
# names; `renamed` maps such a name to the one current declaration it became, so a former owner keeps its row
# across the renames.
RENAMED_COMPONENTS = {
    'AcceptanceAssumptions': 'ContractAssumptions', 'AcceptanceCoefficients': 'ContractCoefficients',
    'acceptanceContract': 'goldilocksContract', 'acceptanceContract_params_eq': 'goldilocksContract_params_eq',
    'AcceptedEndpoint': 'MeetsObligations', 'accepted_endpoint': 'meets_obligations',
    'accepted_concrete': 'meetsObligations_concrete', 'family': 'goldilocks', 'FamilyState': 'PubState',
    'RefinementStatements': 'SimulationStatements', 'refinement_statements': 'simulation_statements',
    **{'accepted_' + s: 'contract_' + s for s in (
        'catchUp', 'catchUp_val', 'catchUp_ge_sleepy', 'heal', 'heal_val', 'heal_ge_reset', 'heal_ge_final',
        'latency', 'latency_final', 'latency_available', 'latency_stable', 'latency_ge_sleepy', 'coefficients',
        'coefficients_catchUp', 'coefficients_heal', 'coefficients_latency')},
    **{'rowDelay' + s: 'protoFGDelay' + s for s in (
        '', '_eq', '_pos', '_delivery', '_delivery_of_healthy', '_timeout_of_healthy')},
    'PSyncFGRowTransport': 'PSyncFGAttTransport', 'psyncFGRowTransport_iff': 'psyncFGAttTransport_iff',
    # The FG attestation names in the scanned Lemmas; the removed cF lemmas have no successor.
    'clean_rowCut': 'clean_fgAttCut', 'isRow_attObj': 'isFGAtt_attObj', 'log_row_iff': 'log_fgAtt_iff',
    'not_isRow_forwardObj': 'not_isFGAtt_forwardObj', 'not_isRow_of_decodeForward': 'not_isFGAtt_of_decodeForward',
    # The field theorems and the existential endpoint of the former constant-fault obligations proof
    # (Lemmas/Obligations/Concrete, deleted): historical targets. A target that no longer exists leaves the
    # name as it is, so its rows stay historical.
    'accepted': 'meetsObligations_exists',
    **{'accepted_' + s: 'meetsObligations_' + s for s in (
        'outputValid', 'nested', 'finalMonotone', 'finalAccountable', 'healthyLive_final', 'healthyLive',
        'sleepySafe', 'sleepyLive', 'healedSafe', 'persists', 'claims', 'progressFits', 'progressTolerant',
        'admissible')}}
STEP1_OLD = 'Consensus.Goldilocks.Refinement.'
STEP1_NEW = ('Consensus.Goldilocks.Obligations.', 'Consensus.Goldilocks.Simulation.',
             'Consensus.Goldilocks.AsChainShape.', 'Consensus.Goldilocks.')
# The `fields` keys: the closure members named `Refinement.accepted_*` before the split (the contract coefficients
# and their lemmas, the endpoint proof's field theorems, and `accepted_in_view`), the growing endpoint's field
# theorems (`Obligations.Growing.meetsObligations_*`), and the root itself.
FIELD_PREFIXES = ('Consensus.Goldilocks.contract_', 'Consensus.Goldilocks.Obligations.contract_',
                  'Consensus.Goldilocks.Obligations.accepted_', 'Consensus.Goldilocks.Obligations.meetsObligations_',
                  'Consensus.Goldilocks.Obligations.Growing.meetsObligations_',
                  'Consensus.Goldilocks.Simulation.accepted_')
# (The field theorems are now `meetsObligations_*`; `Obligations.accepted_*` keeps the block-acceptance
# lemmas `accepted_child_decodes` and `accepted_slotTime_le`; the audited root is `ROOT` below.)


def renamed(name, current):
    """The current name of a historical declaration: itself if it is current, else the one current
    declaration the renames made of it (a `Refinement.*` name in any of the namespaces the split made of it),
    else itself."""
    if name in current:
        return name
    rest = '.'.join(RENAMED_COMPONENTS.get(c, c) for c in name.split('.'))
    if rest.startswith(STEP1_OLD):
        found = [p + rest[len(STEP1_OLD):] for p in STEP1_NEW if p + rest[len(STEP1_OLD):] in current]
    else:
        found = [rest] if rest in current else []
    return found[0] if len(found) == 1 else name


def closure(seeds, edges):
    seen = set()
    todo = list(seeds)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(edges.get(name, []))
    return seen


# Former direct sorry owners retired by a reviewed refactor. Their prior rows are kept
# under 'retired'; retirement is not proof closure.
RETIRED = {
    'final_inherited_progress': ('route A',
        'Only consumer was the retired first-crossing assembly; no route-A caller.'),
    'final_row_signers': ('route A',
        'Content moved into final_window_extract as the AnchorSteps conjunct. Reusable signer '
        'results landed in Healing/Outcome/Service.lean (row_of_report, row_signers_of_reports).'),
    'healthy_old_inventory_initialize': ('R0 decomposition replacement',
        'Replaced by healthy_preparation_initialize, which produces only the joint (E) tuple. '
        'Nothing outside healthy_preserve\'s own preservation plumbing read the old-entry inventory '
        'or the caches, and those HealthyStateFacts fields were removed. Removal is not proof '
        'closure: the inventory gap stays '
        'documented at the outside leaf healthy_vote_row_replacement.'),
}


# The fields of a row (and, with the three retirement fields, of a retired row); anything else a prior ledger
# carries is dropped.
ROW_FIELDS = ('name', 'file:line', 'status', 'blocked-by', 'in_obligations_closure', 'direct_sorry',
              'lean-status', 'evidence', 'obstruction')
RETIRED_FIELDS = (*ROW_FIELDS, 'status-before-retirement', 'retired-by', 'retirement-note')


def retired_rows(previous, current):
    """Keep the rows of retired former owners; never mark them proved."""
    kept = {row['name']: row for row in previous.get('retired', [])}
    for row in previous['rows']:
        short = row['name'].rsplit('.', 1)[-1]
        if row['name'] not in current and short in RETIRED and row['name'] not in kept:
            by, reason = RETIRED[short]
            kept[row['name']] = {**row, 'status-before-retirement': row.get('status'),
                                 'status': 'retired (not proved)', 'lean-status': 'removed',
                                 'in_obligations_closure': False, 'direct_sorry': False,
                                 'blocked-by': [], 'retired-by': by, 'retirement-note': reason}
    unexpected = sorted(n for n in kept if n in current)
    if unexpected:
        raise ValueError(f'Retired declarations still present: {unexpected}')
    return [{k: kept[n][k] for k in RETIRED_FIELDS if k in kept[n]} for n in sorted(kept)]


# The obligations endpoint whose closure the ledger audits, and its module.
ROOT = 'Consensus.Goldilocks.Obligations.Growing.meetsObligations_growing'
ROOT_MODULE = 'ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Endpoint'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    root = ROOT
    scope = 'ConsensusLean/Instances/Goldilocks/Lemmas'
    # The ledger's first audit.
    baseline = run('git', 'rev-parse', 'eed6d0b5').strip()
    head = run('git', 'rev-parse', 'HEAD').strip()
    path = Path('docs/notes/obligations-status.json')
    previous = json.loads(path.read_text()) if path.exists() else {'rows': []}
    old = {row['name']: row for row in previous['rows']}
    historical = set()
    for entry in run('git', 'ls-tree', '-r', baseline, '--', scope).splitlines():
        metadata, filename = entry.split('\t')
        if filename.endswith('.lean'):
            historical.update(n for n, _, sorry in declarations(
                run('git', 'cat-file', 'blob', metadata.split()[2])) if sorry)
    objects = run('git', 'rev-list', '--objects', baseline + '^..HEAD', '--', scope)
    for line in objects.splitlines():
        oid, _, filename = line.partition(' ')
        if filename.endswith('.lean'):
            historical.update(n for n, _, sorry in declarations(run('git', 'cat-file', 'blob', oid))
                              if sorry)
    # Source declarations by user name; `located` keeps each module's copy, since private declarations of
    # several modules may share one user name.
    current, located = {}, {}
    for source in sorted(Path(scope).rglob('*.lean')):
        for name, line, sorry in declarations(source.read_text()):
            current[name] = (str(source), line, sorry)
            located[(str(source)[:-5].replace('/', '.'), name)] = current[name]
            if sorry:
                historical.add(name)
    historical = {renamed(n, current) for n in historical}
    seeds = sorted(historical & current.keys())
    modules = sorted({m for m, n in located if n in seeds})
    subprocess.run(['lake', 'build', '--no-build', 'spec-surface', *modules], check=True)
    with tempfile.TemporaryDirectory() as directory:
        helper = Path(directory) / 'Names.lean'
        helper.write_text('''import Lean
open Lean
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let mods := #[''' + ','.join('`' + m for m in modules) + ''']
  let env ← importModules (mods.map ({module := ·})) {} (loadExts := false) (level := .private)
  for (name, _) in env.constants.toList do
    if isPrivateName name then
      IO.println s!"{privateToUserName name}\t{name}"
''')
        aliases = {}
        for line in run('lake', 'env', 'lean', '--run', str(helper)).splitlines():
            public, private = line.split('\t')
            aliases.setdefault(public, []).append(private)
    # A private name `_private.<Module>.0.<user name>` takes the source line of its own module's declaration, and
    # each scanned module's copy of a seed is a seed of its own.
    owned = {}
    for public, privates in aliases.items():
        for private in privates:
            module = re.match(r'_private\.(.*?)\.0\.', private)[1]
            if (module, public) in located:
                current[private] = located[(module, public)]
                owned.setdefault(public, []).append(private)
            elif public in current:
                current[private] = current[public]
    seeds = sorted({p for n in seeds for p in owned.get(n) or aliases.get(n, [n])})
    records = [json.loads(line) for line in run(
        'lake', 'exe', 'spec-surface', 'dependencies', '--from', root, *seeds,
        '--modules', ROOT_MODULE,
        *modules).splitlines()]
    missing = [r for r in records if 'missing' in r]
    if missing:
        raise ValueError(f'Historical declaration resolution failed: {missing}')
    edges = {r['declaration']: r['dependencies'] for r in records if 'declaration' in r}
    owners = {n for n, deps in edges.items() if 'sorryAx' in deps}
    accepted = closure([root], edges)
    # A row renamed between private and public (or moved to another module's private) keeps its
    # prior metadata: matched by the name without its `_private.<Module>.0.` prefix, only when
    # exactly one vanished prior row and exactly one new row have that name.
    user_name = lambda n: re.sub(r'^_private\..*?\.0\.', '', n)
    names = set(seeds) | owners
    vanished, fresh = {}, {}
    for group, side in ((vanished, set(old) - names), (fresh, names - set(old))):
        for n in side:
            group.setdefault(user_name(n), []).append(n)
    rows = []
    for name in sorted(names):
        if name not in current:
            raise ValueError(f'Missing source location: {name}')
        file, line, _ = current[name]
        dependencies = sorted((closure([name], edges) & owners) - {name})
        proved = not (closure([name], edges) & owners)
        short = name.rsplit('.', 1)[-1]
        prior = old.get(name)
        if prior is None:
            candidates = vanished.get(user_name(name), [])
            unique = len(candidates) == 1 and len(fresh[user_name(name)]) == 1
            prior = old[candidates[0]] if unique else {}
        # A 'lean-proved' rating describes a proof; it is not applied to a row whose closure has
        # regressed to a sorry.
        if short in RATINGS and ('status' not in prior or short in REFRESH) and (
                proved or RATINGS[short][0] != 'lean-proved'):
            rating, evidence = RATINGS[short]
            prior = {**prior, 'status': rating, 'evidence': evidence}
        status = 'lean-proved' if proved else prior.get('status', 'unknown')
        if not proved and status == 'lean-proved':
            status = 'unknown'
        row = {'name': name, 'file:line': f'{file}:{line}',
               'status': status, 'blocked-by': dependencies,
               'in_obligations_closure': name in accepted,
               'direct_sorry': name in owners,
               'lean-status': 'proved' if proved else 'direct-sorry' if name in owners else 'sorry-dependent'}
        for key in ('evidence', 'obstruction'):
            if key in prior:
                row[key] = prior[key]
        if short == 'final_duty_proposal' and name not in owners and dependencies == [
                'Consensus.Goldilocks.contract_heal']:
            row['status'] = 'unknown'
            row['evidence'] = ('Body proved by final_duty_proposal_run; full closure depends on '
                               'contract_heal only through the FinalQuery type (K S A). '
                               'Not a direct sorry in the proof body.')
        # A proved row's prose evidence predates the proof; outside REFRESH (curated texts) it is
        # replaced by the audit fact, recorded at the first audit that found the closure sorry-free.
        if proved and short not in REFRESH and not row.get('evidence', '').startswith(PROVED_EVIDENCE):
            row['evidence'] = f'{PROVED_EVIDENCE}{head[:8]}.'
        # A regressed row drops the proof text it carried from an earlier audit.
        if not proved and (row.get('evidence', '').startswith(PROVED_EVIDENCE) or (
                short in RATINGS and RATINGS[short][0] == 'lean-proved'
                and row.get('evidence') == RATINGS[short][1])):
            row.pop('evidence')
        rows.append(row)
    result = {'schema_version': 2, 'audit_commit': head, 'baseline_commit': baseline,
              'notes': ['blocked-by contains transitive compiled sorry owners, not speculative paper joins.',
                        'lean-proved means the full dependency closure is sorry-free.',
                        'Historical removed declarations are listed separately, not counted as proved.',
                        'retired keeps prior rows of retired former owners; retirement is not proof closure.',
                        'Zero compiled sorry owners is not zero outstanding statements: a statement can be stated '
                        'without a proof (docs/roadmap.md lists the stated, unproved ones).',
                        'Commit SHAs in evidence texts that are not in this repository\'s history (before its root '
                        '79cdddc8) do not resolve here.'],
              'historical_removed': sorted(historical - current.keys()),
              'fields': {n: sorted(closure([n], edges) & owners) for n in sorted(accepted)
                         if n == root or n.startswith(FIELD_PREFIXES)},
              'rows': rows,
              'retired': retired_rows(previous, current)}
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(accepted & owners)} obligations leaves; {len(owners - accepted)} outside leaves; {len(rows)} rows')


if __name__ == '__main__':
    main()
