# G9 review: Task 9, reconcile facts (K3, K1)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Commit: `a339fd8` on `fgsa-composition` (worktree
`~/worktrees/available-chain-fgsa`). File: `AvailableChainFGSA/Proofs/Reconcile.lean`.

## Verdict

**PASS WITH FIXES.** There is no blocking finding and no major finding. The
three minor findings are docstring and report-line items. They do not change a
statement or a proof.

## Sources

- Plan: `docs/plans/2026-09-29-fgsa-model-store.md`, Task 9 (lines 1943–2031),
  Global Constraints, Review gates (G7–G12) and the blocking list.
- Blueprint: `blueprint/00-outline.md:477–484` (`bp.reconcile.v1`, K1, K3),
  `00-outline.md:498–503` (`bp.frame.v1`), `00-outline.md:105–137` (§2.2),
  `blueprint/01-foundations.md:288–361` (§6.1–6.3).
- K ids: `codex/lean-composition-plan.md:393–401` (K1, K3).
- Spec: `spec/archive/fgsa-protocol-2e884811.tex:444–450`, `474–484`,
  `734–741`, `874–894`.
- Model: `Model/Store.lean:43–71` (`activeCompatible`, `normalizeS`,
  `reconcile`), `Statements/Invariants.lean:32–47` (`SACompat`, `FastOrigin`),
  `Proofs/Fields.lean:94–104`.

## Check 1: statements against the plan and the blueprint

A script compared the twelve planned statements with the file, with
whitespace normalized and docstrings and proofs removed. All twelve are the
same text. The file adds four helpers (`reconcile_eq`, `preceq_normal`,
`stable_preceq_normal`, `mem_genuine_of_saved`). Each helper has a `[helper]`
docstring, and no planned statement has a new premise.

```text
┌────────────────────────────┬──────────────────────────────────────┬──────────┐
│ Lean (Reconcile.lean line) │ Blueprint clause                     │ Result   │
├────────────────────────────┼──────────────────────────────────────┼──────────┤
│ reconcile_obligations :28  │ §6.2 post.lease(B)=pre if B∥F, else  │ exact    │
│                            │ absent                               │          │
│ reconcile_fastWrite :43    │ §6.2 filter, same label domain       │ exact    │
│ reconcile_genuine :32      │ §6.2 missing/empty/body C kept or    │ exact    │
│ reconcile_savedGenuine :37 │ emptied; "preserves evaluated labels"│          │
│ reconcile_stable :47       │ §6.2 post.S                          │ exact    │
│ reconcile_frame :55        │ §6.2 last item; K3 (F,J,h_j,hmax,Σ.T)│ complete │
│ storeControls_reconcile:70 │ bp.frame.v1 "Reconcile does not      │ exact    │
│                            │ change" controls and D_Σ(X)          │          │
│ reconcile_idem :82         │ "idempotent for fixed F"             │ exact    │
│ reconcile_saCompat :90     │ §6.2 "every remaining target and     │ exact    │
│                            │ body is compatible with F"           │          │
│ reconcile_fastOrigin :162  │ §6.3 historical case                 │ exact    │
│ reconcile_harmless_origin  │ K1: leases, nonempty bodies, S       │ stronger │
│ :205                       │ compatible ⇒ no deletion, S extended │ concl.   │
│ reconcile_harmless :128    │ helper (has fastWrite premise)       │ helper   │
└────────────────────────────┴──────────────────────────────────────┴──────────┘
```

Notes:

- `reconcile_frame` names every field of `GridCO.State` except the four that
  reconcile writes (`obligations`, `genuine`, `stableRecord`, and the
  composite `fastWrite`), plus `fg`, `proposals` and `rowPool`. So the frame
  is complete. `reconcile_eq` (line 16) gives the full record equation in
  addition. D_Σ(X) (bp00 §2.2, line 114) reads only T, F, J and H, which are
  in `fg`. Λ and σ are not fields (DQ4; σ is `derive`), so K3 has no gap.
- "The output extends F" (bp01 §6.2) is `reconcile_nest`
  (`Proofs/Nesting.lean:28`, Task 8). It is correctly not in this task.
- K1 (`reconcile_harmless_origin`, line 205). The premises `hL`, `hG`, `hS`
  are the three blueprint premises. `hO : FastOrigin F₀ st` and
  `hF : F₀ ⪯ F` are the local forms of the blueprint premise "actual
  origins" (bp00 line 482) and of "local F monotonicity" (bp01 §6.3). The
  conclusion is a full state equation (only S changes) plus `S ⪯ S'`. This is
  stronger than "deletes no target or body and only extends S". There is NO
  fastWrite premise, as the plan requires (Opus M3).

## Check 2: the "filter form" of `reconcile_harmless`

`reconcile_harmless` (line 128) takes `hC : SACompat st`. Its third clause is
"every fastWrite member is compatible with F". The blueprint K1 does NOT
have this premise: bp01 §6.3 derives the fastWrite preservation from the
origin witnesses. So the filter form is a WEAKER statement than K1. It is
acceptable because:

- its docstring (lines 124–127) calls it a helper and says "do not cite this
  lemma as K1";
- the K1 of the plan is `reconcile_harmless_origin`, and the Task 13 K table
  (plan line 2402) maps K1 to `reconcile_harmless_origin` and
  `admitBlock_reconcile_harmless`, with `reconcile_harmless` as a helper;
- `reconcile_harmless_origin` builds the fastWrite clause from `hO`, `hG` and
  `hF` (lines 214–218), with the two cases of bp01 §6.3.

The filter form is not a restatement of the blueprint harmlessness. It is the
last step of the K1 proof. G13 must check that no later file cites it as K1.

## Check 3: premises that later tasks must discharge

```text
┌──────────────────────────┬───────────────────────────────┬──────────────────┐
│ Premise                  │ Discharge (Task 11, plan      │ Status           │
│                          │ 2166–2240)                    │                  │
├──────────────────────────┼───────────────────────────────┼──────────────────┤
│ hO : FastOrigin F₀ st1   │ h.fastOrigin on st, F₀ :=     │ checked: the     │
│ (reconcile_fastOrigin,   │ eraseFG st.fg.F; FastOrigin   │ transport is a   │
│ reconcile_harmless_      │ reads only fastWrite and      │ 4-line proof     │
│ origin)                  │ genuine, which st1 shares     │ (scratch test)   │
│ hF : F₀ ⪯ F              │ on_block_F_mono, eraseFG_     │ planned          │
│                          │ preceq                        │                  │
│ hL, hG, hS               │ premises of admitBlock_       │ passed through   │
│                          │ reconcile_harmless (the run   │ unchanged        │
│                          │ discharges them: T8+, K7)     │                  │
│ SACompat (filter form)   │ not needed downstream for K1  │ n/a              │
└──────────────────────────┴───────────────────────────────┴──────────────────┘
```

A scratch test compiled `FastOrigin Fb st → FastOrigin Fb st1` from
`st1.fastWrite = st.fastWrite` and `st1.base.genuine = st.base.genuine`, and
`FastOrigin` on `initial 4`. So `hO` is not a hidden hard premise.

## Check 4: lease instance and imports

- `Reconcile.lean` uses no lease-dependent GridCO lemma. The one GridCO name
  is `GridCO.savedGenuine`; `#check @GridCO.savedGenuine` shows no
  `[LeasePolicy]` argument. The `@… GridCO.slowLeasePolicy` rule does not
  apply.
- The one import is `AvailableChainFGSA.Proofs.ActView` (line 2). It is the
  smallest one: `block_compatible_of_preceq` (used at lines 185 and 218) is in
  `Proofs/ActView.lean:19`. A test with `Statements.Invariants` and
  `Proofs.Fields` only fails on that name.
- The root file imports the module (`AvailableChainFGSA.lean:14`). The file
  header and footer follow the Global Constraints. There is no free `n` next
  to `p : Params` (`storeControls_reconcile`, line 70, uses `State p.n`).

## Check 5: build and axioms

Scratch worktree `/Users/francesco/.claude/jobs/22f59f85/tmp/g9wt` at
`a339fd8`, `.lake/packages` linked, `.lake/build` copied from the
implementation worktree.

- `bash scripts/check-fgsa.sh`: exit 0. "Build completed successfully (3344
  jobs)"; root imports, native evaluation, direct imports, import closure and
  Q1/Q5 boundary pass; "checked 577 constants, 252 theorems"; "all FGSA
  checks pass". The Lake traces were replayed from the copied build (same
  source). So a direct compile was also run:
- `lake env lean AvailableChainFGSA/Proofs/Reconcile.lean`: no error, no
  warning.
- `#print axioms` on the twelve planned theorems: `propext`, `Quot.sound`;
  `storeControls_reconcile` and `reconcile_fastOrigin` also use
  `Classical.choice`. No other axiom, no `sorryAx`.

The scratch worktree was removed after the review.

## Findings

### BLOCKING

None.

### MAJOR

None.

### MINOR

1. **Missing blueprint and K tags on four planned theorems.**
   `Reconcile.lean:32` (`reconcile_genuine`), `:43` (`reconcile_fastWrite`),
   `:47` (`reconcile_stable`) and `:70` (`storeControls_reconcile`) have no
   docstring. `:36` (`reconcile_savedGenuine`) has a docstring without a
   blueprint id. The Global Constraints (Faithfulness) require that a proof
   docstring names its blueprint id and K id. `storeControls_reconcile` is a
   K3 theorem in the Task 13 table, but its source does not say so. The cause
   is in the plan: the Task 9 statement block (plan lines 1961–1990) has the
   same gaps, and the implementer copied it exactly. Fix: add
   `[bp bp.reconcile.v1] (§6.2, exact effects)` to lines 32, 36, 43 and 47,
   and `[bp bp.frame.v1, bp.reconcile.v1; K3]` to line 70. This changes no
   statement.

2. **The reading of "live lease" needs a report line.** K1 in the blueprint
   says "every live lease". `hL` (line 207) quantifies over every row of
   `obligations`, that is, every `Σ.lease[B] ≠ ⊥` (spec 446–447). A lease
   with a deadline at or before the current time stays in the store until
   the next tick (spec 447–448, 736–741), and reconcile deletes it when it
   conflicts with F (spec 878–880). So the Lean premise is the only correct
   form of K1: with "live" read as "deadline in the future", the blueprint
   claim "deletes no target" is false for such a row. This is not a weakening
   of a true statement. But the run layer (theorem (b), K7) must then show
   compatibility also for leases that are due but not yet expired. Add one
   line to the Task 13 report: "K1 `hL`: live = present in `Σ.lease`
   (`obligations`), including due leases that the next tick expires."

3. **The filter-form helper is weaker than K1 (report line, no code
   change).** `reconcile_harmless` (line 128) has the fastWrite premise that
   the blueprint K1 does not have. Its docstring already says this. G13 must
   check that no later file cites `reconcile_harmless` where K1 is needed, and
   the Task 13 K table must keep it in the "helper" column.

Observation (no action): two theorems are not separated by a blank line
(`Reconcile.lean:31–32`, `:35–36`, `:42–43`, `:46–47`, `:69–70`). This is only
layout.
