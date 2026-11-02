#!/usr/bin/env python3
"""Regenerate the Accepted status ledger; paper classifications are preserved, never inferred.

Run after building ConsensusLean and spec-surface. Historical source scans select
former sorry declarations; compiled dependency edges determine their current status.
"""
import argparse
import datetime
import base64
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

# Whole-statement ratings supplied in this thread by the lead and healing paper owner,
# 2026-11-01. Later reviewed JSON ratings override these initial classifications.
LEAD = 'https://ampcode.com/threads/T-01a19205-229e-72c0-9a83-5119d88a0e27'
PAPER = 'https://ampcode.com/threads/T-01a18b7f-055c-74c7-ae28-91217f676dcd'
ROUTE_A = 'https://github.com/ethlabs-org/consensus-lean/issues/136'
RATINGS = {
    'accepted_catchUp': ('paper-partial', LEAD, 'Settled coefficient audit: simultaneous finite engine envelope and repaired transport remain; no arbitrary witness choice.'),
    'accepted_heal': ('paper-partial', LEAD, 'Settled coefficient audit: finite reset/preparation/retention and endpoint margins need joint synthesis.'),
    'accepted_latency': ('paper-partial', LEAD, 'Settled coefficient audit: joint nonfinal/four-anchor latency and actual carrier acceptance remain.'),
    'accepted_catchUp_ge_sleepy': ('paper-partial', LEAD, 'Settled coefficient audit: 37 is a verified constraint, not a proof about the opaque shared witness; enlargement needs monotonicity audit.'),
    'accepted_latency_ge_sleepy': ('paper-partial', LEAD, 'Settled coefficient audit: 8idx+12 is a verified constraint, not a jointly admissible selected witness.'),
    'final_window_extract': ('paper-partial', LEAD, 'Settled final-liveness audit: four-anchor combinatorics known; actual ready accepted chain, recurrence and endpoint carrier budget remain.'),
    # Route-A split of final_window_extract (#136): its body is final_window_extract_of'
    # from these two leaves (final_duty_proposal has a proved body); the rating is inherited
    # from final_window_extract.
    'final_reset_premises': ('paper-partial', ROUTE_A, "Open (H1)+(H3) of final_window_extract_of': (H1) reset premises through the horizon at Q.gst = Sol's M1′ reset; (H3) placement with u_min = finalSeedMin Q a = slot a + 2k + 5 (corrected, #145) = the heal coefficient. One leaf: (H3) depends on the reset a of (H1). Owners: Sol (H1), coefficients (H3)."),
    'final_duty_proposal': ('paper-partial', ROUTE_A, "(H2) of final_window_extract_of': duty → proposal adapter, bounded by 0 < s and ts s ≤ horizon; body proved by final_duty_proposal_run (FinalDutyProposal.lean, #143). Owner: Kev."),
    # Historical rating; the declaration is retired by route A (#141), see RETIRED.
    'final_inherited_progress': ('paper-open (research)', LEAD, 'Settled final-liveness audit: arbitrary dirty inherited permissions/held or credited rows must yield same-entry progress without a birth lower bound.'),
    'final_row_supply': ('paper-open (research)', LEAD, 'Research refinement: high same-entry/high-predecessor row algebra is proved conditionally; report_cover, inherited/low entries and carrier credit/acceptance remain. entry-rows-exact §§2,4–6.'),
    'final_cache_acceptance': ('paper-partial', LEAD, 'Settled final-liveness audit: actual last-carrier acceptance, retained lookup/cache for every reader and processing/read deadline budget remain.'),
    'healthy_old_inventory_initialize': ('paper-open (research)', PAPER, 'Whole-statement audit 6d6af170 §§27–28: global future first arrivals require upper coverage or strict below-hj, including equality; bounded actual reset production missing.'),
    'healthy_prepare': ('paper-partial', PAPER, 'Whole-statement audit 6d6af170 §§16–17,24,27–28: actual heal-cut stored record/cache/lock base production remains; inherited C above R not handled by R≤C.'),
    'healthy_preserve': ('paper-proved awaiting Lean', PAPER, 'Superseding §83 e8fc89c4: J quorum/inventory contradiction; F via F≤J; recent locks via lock_origin; retained records via archival tree/F monotonicity/restart. Adapter/J-entry elaboration remains.'),
    'healthy_cut_tips_comparable': ('paper-partial', PAPER, '103bfbd extracts actual stored-clock read-tip comparability; same equality-time pre-endCut gap. Engine output transport is proved.'),
    'healthy_cut_tips_ancestor': ('paper-partial', PAPER, '103bfbd extracts directed actual stored-clock read-tip ancestry; temporal/equality-time gap remains. Engine output transport is proved.'),
    'healthy_cut_agreement': ('paper-partial', PAPER, 'Whole-statement audit 6d6af170 §§17.2,25–28: old-row realization/replacement, origin comparability and actual engine read transport; heal-time cuts can precede endCut-heal.'),
    'healthy_cut_monotone': ('paper-partial', PAPER, 'Whole-statement audit 6d6af170 §§17.2–3: temporal DCA lower bound and equality-time/readiness transport; common-chain membership does not prevent backwards reads.'),
    'healthy_confirmed_supply': ('paper-partial', PAPER, 'Whole-statement audit 6d6af170 §§23–28,79–81: finite Healthy/service/preparation and fresh actual proposal with universal exact ReadyAt/CutAfter coverage remain.'),
    'outage_arm': ('paper-partial', PAPER, 'Whole-statement audit 6d6af170 §§10,14–19: inherited record/lookup and exact reader extraction; arming is not protection.'),
    'outage_repair': ('paper-open (research)', PAPER, 'Whole-statement audit 6d6af170 §§10,17–19: covering nonvetoed renewal, pool bound/resolutions, RESULT compatibility, persistence and both reader branches remain.'),
    'outage_pre_service': ('paper-partial', LEAD, 'Revision update 4d69fdd: old duplicate-fresh signature obstruction retired by migration; replacement engine service unproved. #128 Outage applicability not established.'),
    'clean_result_next_votes': ('paper-open (research)', PAPER, 'Outside audit 649f0286 §§73,77,82: raw-result induction after repair does not cover arbitrary early sub-fast/vetoed ResultAt without Catch/base.'),
    'reset_inv': ('paper-partial', PAPER, 'Outside audit 649f0286 §§74–81: full Protected/P3, arbitrary admissions/root/frame retention and uniform Tb remain beyond P1/P2.'),
    'vote_old_live_lock_below_parent': ('paper-proved awaiting Lean', PAPER, 'Outside audit 649f0286 §§80–81: provenance+l+2 transfer and separate optimistic u−1 branch; non-vote full-tree domain/service integration remains.'),
    'ready_unanimous': ('paper-partial', PAPER, 'Outside audit 649f0286 §§23,79–81: actual first-deviation head/walk/payload equality remains, not merely parent extension.'),
    'voter_unlock_keeps_lock': ('paper-open (research)', PAPER, 'Outside audit 649f0286: voter-only opponents and proposer s−1 lock defeat simple view bound; new pivot bypasses this leaf; no full-run counterexample asserted.'),
    'healthy_old_row_realize': ('paper-partial', PAPER, 'Superseding exact audit 732a1b6: older validAtt branch does not constrain target; receiver-held target/replay-height bridge missing. No full-run counterexample. J-specific preservation has target membership.'),
    'healthy_vote_row_replacement': ('paper-partial', PAPER, 'Outside audit 649f0286: realization/inventory give eventual coverage but still need l≤s; OldEntryCovered has no label upper bound.'),
    'weak_base_until': ('paper-open (research)', PAPER, 'Outside audit 649f0286 §§16–19,27–28,82: exact records/cache/global old-row base is not supplied by pivot seed.'),
    'weak_base_extend': ('paper-open (research)', PAPER, 'Outside audit 649f0286: held rows through T do not cover future first arrivals/new cache roots; event/restart continuation needed.'),
    'weak_base_locks': ('paper-partial', PAPER, 'Outside audit 649f0286: expiry confines cases, but finite Healthy drain/support against later origins remains.'),
    'healed_safe_until': ('paper-partial', PAPER, 'Outside audit 649f0286: weak-base production/preservation and actual ReadySafeOn reads remain; no extra progress premise.'),
    'include_healed_until': ('paper-partial', PAPER, 'Outside audit 649f0286: given unanimity, covering nonvetoed update and preserved records at exact post-T Sleepy reads remain.'),
    'grow_healed_until': ('paper-partial', PAPER, 'Outside audit 649f0286: fresh actual ready proposal plus inclusion and temporal safety joins remain.'),
    'outage_statements': ('paper-open (research)', PAPER, 'Outside audit 649f0286 §§10,17–19,82: full arming/lifetime/source compatibility and covering repair for both reader classes remain.'),
    'higher_report_window_origin': ('paper-proved awaiting Lean', LEAD, 'Four outside audits 649f0286: reset_origin_below and same-store high_of_anc establish high C, then high_report_origin; no unheld receiver height. entry-rows-exact §3.'),
    'update_window_kept': ('paper-partial', LEAD, 'Four outside audits 649f0286: actual update-frame viable-or-higher-origin dichotomy remains; hsrc can be vacuous; no reverse raw→stored ancestry.'),
    'ready_update': ('paper-partial', LEAD, 'Four outside audits 649f0286: exact result, veto, fast selection and source at actual update or higher report by deadline remain.'),
    'report_cover': ('paper-open (research)', LEAD, 'Four outside audits 649f0286: actual acToFG report existence under fgReported suppression, candidate survival/normalization and higher source remains; entry-rows-exact §§2,6.'),
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
            name = namespace[1] + '.' + name
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result.append((name, text.count('\n', 0, match.start()) + 1,
                       bool(re.search(r'\bsorry\b', text[match.end():end]))))
    return result


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
# under 'retired' with their provenance; retirement is not proof closure.
RETIRED = {
    'final_inherited_progress': ('route A (#136, #141)',
        'Only consumer was the retired first-crossing assembly; no route-A caller.'),
    'final_row_signers': ('route A (#136, #141)',
        'Content moved into final_window_extract as the AnchorSteps conjunct. Reusable signer '
        'results landed in Healing/Outcome/Service.lean (row_of_report, row_signers_of_reports); '
        'paper handoff workbench b386900 notes/cards/final_row_signers.md.'),
}


def retired_rows(previous, current):
    """Keep provenance of retired former owners; never mark them proved."""
    kept = {row['name']: row for row in previous.get('retired', [])}
    for row in previous['rows']:
        short = row['name'].rsplit('.', 1)[-1]
        if row['name'] not in current and short in RETIRED and row['name'] not in kept:
            by, reason = RETIRED[short]
            kept[row['name']] = {**row, 'status-before-retirement': row.get('status'),
                                 'status': 'retired (not proved)', 'lean-status': 'removed',
                                 'in_accepted_closure': False, 'direct_sorry': False,
                                 'blocked-by': [], 'retired-by': by, 'retirement-note': reason}
    unexpected = sorted(n for n in kept if n in current)
    if unexpected:
        raise ValueError(f'Retired declarations still present: {unexpected}')
    return [kept[n] for n in sorted(kept)]


def card_repositories(document):
    """Make legacy archive locators explicit without repointing existing pins."""
    for row in document['rows']:
        row.setdefault('card-repo', 'fradamt-agent/workbench' if row.get('card-path') else None)
    cards = document.get('shared-cards', [])
    if 'research-cores' in document:
        cards = [*cards, document['research-cores']]
    for card in cards:
        card.setdefault('card-repo', 'fradamt-agent/workbench')


def ingest_cards(document, repository):
    """Pinned owner-reviewed cards; shared audits are links, not synthetic leaves."""
    sources = [
        ('fb40eb4c7dfb235493d97837533f2fc402026675',
         'accepted_catchUp accepted_catchUp_ge_sleepy accepted_heal accepted_latency accepted_latency_ge_sleepy final_cache_acceptance final_inherited_progress final_row_supply final_window_extract ready_update report_cover sleepy_query_sync sleepy_safety_inputs update_window_kept vote_old_live_lock_below_parent'),
        ('013e11ace8151bf5525ef3a1c6a7f6fd44eac1d5',
         'clean_result_next_votes healthy_confirmed_supply healthy_cut_tips_ancestor healthy_cut_tips_comparable healthy_old_inventory_initialize healthy_old_row_realize healthy_prepare ready_unanimous reset_inv voter_unlock_keeps_lock weak_base_extend weak_base_locks weak_base_until'),
        ('af61e7b436f950709d0046a552a25ac1f3123134', 'outage_pre_service outage_repair'),
    ]
    directory = 'repos/goldilocks/notes/derisk/'
    for commit, names in sources:
        for name in names.split():
            locator = directory + name + '.md'
            response = json.loads(run('gh', 'api',
                f'repos/{repository}/contents/{locator}?ref={commit}'))
            card = base64.b64decode(response['content']).decode()
            if not re.search(r'\bresearch\b', card, re.I):
                raise ValueError(f'Expected reviewed research verdict in {locator}')
            adversarial = bool(re.search(r'adversarial', card, re.I))
            for row in document['rows']:
                if row['name'].rsplit('.', 1)[-1] == name:
                    row.update({'card-path': locator, 'card-commit': commit,
                                'card-repo': repository,
                                'derisk-verdict': 'research',
                                'adversarial-pass-done': 'y' if adversarial else 'n',
                                'last-changed': datetime.date.today().isoformat()})
    document['research-cores'] = {
        'card-repo': repository,
        'path': directory + 'research-cores.md', 'commit': sources[0][0],
        'note': 'Overlapping producer-gap groups; counts must not be added as leaves.'}
    document['shared-cards'] = [
        {'card-repo': repository, 'path': directory + 'joint-envelope.md', 'commit': sources[0][0]},
        {'card-repo': repository, 'path': directory + 'postReset_families.md', 'commit': sources[1][0]},
        {'card-repo': repository, 'path': directory + 'outage_tips.md', 'commit': sources[2][0]}]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ingest-cards', action='store_true')
    parser.add_argument('--metadata-only', action='store_true')
    parser.add_argument('--card-repo', default='fradamt-agent/workbench',
                        help='owner/repo containing the reviewed ingestion source commits')
    args = parser.parse_args()
    root = 'Consensus.Goldilocks.Refinement.accepted'
    scope = 'ConsensusLean/Instances/Goldilocks/Lemmas'
    baseline = run('git', 'rev-parse', 'fd7f498').strip()
    head = run('git', 'rev-parse', 'HEAD').strip()
    path = Path('docs/accepted-status.json')
    previous = json.loads(path.read_text()) if path.exists() else {'rows': []}
    card_repositories(previous)
    if args.ingest_cards:
        ingest_cards(previous, args.card_repo)
        path.write_text(json.dumps(previous, indent=2) + '\n')
        return
    if args.metadata_only:
        for row in previous['rows']:
            row.setdefault('card-path', None)
            row.setdefault('derisk-verdict', 'none yet')
            row.setdefault('adversarial-pass-done', 'n')
        path.write_text(json.dumps(previous, indent=2) + '\n')
        return
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
    current = {}
    for source in sorted(Path(scope).rglob('*.lean')):
        for name, line, sorry in declarations(source.read_text()):
            current[name] = (str(source), line, sorry)
            if sorry:
                historical.add(name)
    seeds = sorted(historical & current.keys())
    modules = sorted({current[n][0][:-5].replace('/', '.') for n in seeds})
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
        aliases = dict(line.split('\t') for line in run('lake', 'env', 'lean', '--run', str(helper)).splitlines())
    for public, private in aliases.items():
        if public in current:
            current[private] = current[public]
    seeds = [aliases.get(n, n) for n in seeds]
    records = [json.loads(line) for line in run(
        'lake', 'exe', 'spec-surface', 'dependencies', '--from', root, *seeds,
        '--modules', 'ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted',
        *modules).splitlines()]
    missing = [r for r in records if 'missing' in r]
    if missing:
        raise ValueError(f'Historical declaration resolution failed: {missing}')
    edges = {r['declaration']: r['dependencies'] for r in records if 'declaration' in r}
    owners = {n for n, deps in edges.items() if 'sorryAx' in deps}
    accepted = closure([root], edges)
    today = datetime.date.today().isoformat()
    rows = []
    for name in sorted(set(seeds) | owners):
        if name not in current:
            raise ValueError(f'Missing source location: {name}')
        file, line, _ = current[name]
        dependencies = sorted((closure([name], edges) & owners) - {name})
        proved = not (closure([name], edges) & owners)
        short = name.rsplit('.', 1)[-1]
        if short in ('accepted_catchUp', 'accepted_heal', 'accepted_latency',
                     'accepted_catchUp_ge_sleepy', 'accepted_latency_ge_sleepy'):
            area = 'coefficients'
        elif short.startswith('final_'):
            area = 'final liveness'
        elif 'outage' in name.lower() or 'persist' in short:
            area = 'outage+persist'
        elif any(x in name for x in ('Healing.', 'healthy_', 'healed_', 'Weak.')):
            area = 'healing'
        else:
            area = 'network+Sleepy'
        owner = {
            'coefficients': 'T-01a18ff0-1a20-744c-a2f0-a27048f42a3c',
            'final liveness': 'T-01a188b7-1c55-7594-9ad6-81a9b156211c',
            'healing': 'T-01a18b7f-055c-74c7-ae28-91217f676dcd',
            'network+Sleepy': 'T-01a18fec-6e1e-7342-9ca9-8562977d7347',
            'outage+persist': 'T-01a18fec-6e1e-7342-9ca9-8562977d7347',
        }[area]
        prior = old.get(name, {})
        if short in RATINGS and (prior.get('status-source') is None or short in ('healthy_preserve', 'healthy_old_row_realize')):
            rating, source, evidence = RATINGS[short]
            prior = {**prior, 'status': rating, 'status-source': source,
                     'evidence': evidence}
        status = 'lean-proved' if proved else prior.get('status', 'unknown')
        if not proved and status == 'lean-proved':
            status = 'unknown'
        row = {'name': name, 'file:line': f'{file}:{line}',
               'owner-thread': prior.get('owner-thread', owner), 'area': area,
               'status': status, 'blocked-by': dependencies,
               'in_accepted_closure': name in accepted,
               'direct_sorry': name in owners,
               'lean-status': 'proved' if proved else 'direct-sorry' if name in owners else 'sorry-dependent',
               'status-source': 'compiled dependency audit' if proved else prior.get('status-source'),
               'last-changed': today}
        for key in ('evidence', 'obstruction', 'card-commit'):
            if key in prior:
                row[key] = prior[key]
        for key, default in (('card-path', None), ('card-repo', None), ('derisk-verdict', 'none yet'),
                             ('adversarial-pass-done', 'n')):
            row[key] = prior.get(key, default)
        if short in ('outage_arm', 'healthy_preserve') and name not in owners:
            row['status'] = 'unknown'
            row['status-source'] = 'compiled dependency audit'
            row['evidence'] = ('Body proved at 649f0286; shared coefficient type dependencies remain. Exact endCut(T), both lookup alternatives and actual read prefix; arming is not protection.' if short == 'outage_arm' else
                               'Body proved at ed329627 from the existing base; J-specific target membership avoids healthy_old_row_realize. Shared coefficient type dependencies remain, not a direct sorry.')
        if short in ('sleepy_query_sync', 'sleepy_safety_inputs'):
            row.pop('obstruction', None)
            if name not in owners and dependencies == [
                    'Consensus.Goldilocks.Refinement.accepted_heal']:
                row['status'] = 'unknown'
                row['status-source'] = 'compiled dependency audit'
                row['evidence'] = ('Body proved; full closure depends on accepted_heal through '
                                   'K S A = acceptanceContract A (accepted_coefficients S A). '
                                   'The query and Sleepy premise types include the sorry definition; '
                                   'this is not a direct sorry in the proof body.')
        if short == 'final_duty_proposal' and name not in owners and dependencies == [
                'Consensus.Goldilocks.Refinement.accepted_heal']:
            row['status'] = 'unknown'
            row['status-source'] = 'compiled dependency audit'
            row['evidence'] = ('Body proved by final_duty_proposal_run (#143); full closure depends on '
                               'accepted_heal only through the FinalQuery type (K S A). '
                               'Not a direct sorry in the proof body.')
        comparison = {k: v for k, v in row.items() if k not in ('last-changed', 'file:line')}
        if comparison == {k: v for k, v in prior.items() if k not in ('last-changed', 'file:line')}:
            row['last-changed'] = prior['last-changed']
        rows.append(row)
    result = {'schema_version': 1, 'audit_commit': head, 'baseline_commit': baseline,
              'generated_on': today,
              'notes': ['blocked-by contains transitive compiled sorry owners, not speculative paper joins.',
                        'lean-proved means the full dependency closure is sorry-free.',
                        'Owner threads are area routing defaults; authoritative overrides are preserved.',
                        'Historical removed declarations are listed separately, not counted as proved.',
                        'retired keeps prior rows of retired former owners; retirement is not proof closure.'],
              'historical_removed': sorted(historical - current.keys()),
              'fields': {n: sorted(closure([n], edges) & owners) for n in sorted(accepted)
                         if n.startswith('Consensus.Goldilocks.Refinement.accepted_')},
              'rows': rows,
              'retired': retired_rows(previous, current)}
    for key in ('research-cores', 'shared-cards'):
        if key in previous:
            result[key] = previous[key]
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(accepted & owners)} Accepted leaves; {len(owners - accepted)} outside leaves; {len(rows)} rows')


if __name__ == '__main__':
    main()
