# Async-session review of the FG plan filtered-base edit (fg-module-filtered.md), 2026-09-28

Verbatim from the async-resilience session (cross-session message; read-only Opus review against bd942ca0 and the registry at HEAD).

Verdict: APPROVE WITH FIXES, 0 BLOCKING, 2 MAJOR, 6 MINOR. These are correct: Store.init, update_finality order, TF writes, activeView (both directions), the StoreInv fields, the pair-preservation argument, Tasks 12–13 (no raw-tree assumptions left), the DC line citations, the ported-text claim, and the pin-check inputs.

MAJOR
M1. on_block leaves out refusal conditions of spec 794–801 / DC 1722: the future-slot bound B.slot > Σ.s, the parent-slot order, and the proposer signature. The docstring (P:941–942) and the pin (P:1860) call them "AP". But they are FG admission conditions: each can refuse a block that the Lean accepts, and that block changes TF, hmax, the contest and J. The lemmas stay sound, because they quantify over StoreInv stores. Fix: list all of them as an explicit FG input contract, as the row-round check already is, or test B.parent.slot < B.slot in Lean. Align P:147 and P:1858; they drop the slot bound. Your Astra audit (P… in docs/audit) accepted the AP boundary; I side with the reviewer here.
M2. The Trees clause of the fj.frame.v3 pin (P:1854–1855) claims "one cumulative, parent-closed Σ.T" with .leanHyp [Store, activeView, activeView_subset], but no listed name proves closure or cumulativity. Fix: add on_block_TF_subset : st.TF ⊆ (on_block st B).TF and update_finality_TF : (update_finality st B).TF = st.TF, and cite storeInv_init / storeInv_on_block (closed). Mark S:366–367 (a block outside the view above h_F needs a slashable conflict) as .external "fg.finalLock.v1", and S:369–371 (the walk from genesis) as .ap. Task 13's hmono uses cumulativity, so it needs the lemma.

MINOR
1. P:8 still says "raw and FG-admitted trees".
2. The Store docstring (P:897–898) says "every B in TF had F ⪯ B when accepted", but no invariant carries it. Say that it is not formalized, or add a ghost history. No lemma needs it.
3. The Task 7 example stores (P:1145, P:1147) fail pair/Fcar. Build them with on_block, or call them arbitrary literals.
4. headReachesLo.v5 is described as "clauses 1–3 unchanged" (P:41, 1998, 2152, ~2125). Say "the conclusions are unchanged; the hypotheses are v5's".
5. P:1065–1066 attributes filteredFrom_Z_mem to a registry discharge that does not exist. Mark it as the plan's own reading.
6. storeControls_eq_fjControls: the prose, the pin and the registry say "under StoreInv and ViewRootInj", but the Lean statement takes only StoreInv (a stronger result). Align the prose and the pin, and note that ViewRootInj is used only by storeInv_on_block.
Small: registry HEAD now also has 8bb4ac9 and f7af9b2 (dated r162 lines only; no id, pin or status change). createRow lines: 1334–1401 at P:1981 vs 1334–1403 at P:21.
Also re-check the audit's P01 (the compact id:="…" syntax escapes the SUPERSEDED check); I did not verify it.
