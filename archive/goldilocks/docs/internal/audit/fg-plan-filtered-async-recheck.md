# Async-session re-review of the final FG filtered-base edit, 2026-09-28

Verbatim from the async-resilience session (cross-session message).

Re-review of the final filtered-base plan edit: APPROVE WITH FIXES, 0 BLOCKING, 0 MAJOR, 4 MINOR. Nothing blocks execution. The reviewer regenerated the diff against 195d31a, and it matches your .diff. M1, M2 and MINOR 1–6 are applied (one leftover of MINOR 4, below). Task 7 matches bd942ca0: the refusal order (duplicate, parent, F ⋠ B, parent slot) comes before update_finality and before insertion; update_finality_TF and on_block_TF_subset are correct; the on_block examples [B1′, B1, B2, B3] give F = B1, pair (2, B1), hmax = 4, and B1′ in TF but not in activeView. The Task 14 clauses cover every fj.frame.v3 block with correct ranges. The 8 active and 9 historical ids resolve, none is SUPERSEDED, and the expected pin output is consistent.

MINOR
1. Wrong DC citation for the parent-slot refusal (P:945, P:1174, P:149). DC:1722 is the slot/duplicate/parent guard. DC has no parent-slot refusal in on_block; it has `assert B.parent.slot < B.slot` in state_transition (consensus.tex 791, 2220). Cite that assert, and say that the spec (S:798) makes it a refusal.
2. The on_block defPin (P:2027) says "refusals 794–796". Make it 794–796 and 798.
3. The head-reaches-H labels (P:1994–1997) state the converse of v5 clause 1. v5 clause 1 is an "if". Write: "reaches H if A is in D_V or has an eligible child in D_V; otherwise the HEAD is A (clause 2), which can be below H". Also mark the FG-action-head use ("Σ.T in place of V", P:1996–1997) as the plan's reading, because v5 is stated only for a HEAD duty's frozen voter tree.
4. Leftovers. P:2240 still says "Clauses 1–3 are those of v2, v3 and v4"; write "the conclusions of clauses 1–3 are those of v2–v4; the hypotheses are v5's". The docstrings of activeView_subset (P:1150), update_finality_TF (P:1154) and on_block_TF_subset (P:1160) start with [helper], but these are pin coverage for fj.frame.v3; storeInv_init (P:999) has no docstring. They should start with "[pin fj.frame.v3] (Trees: …)". Optional: Task 13's cumulativity remark (P:1620 area) can cite on_block_TF_subset.
The reviewer did not run the pin-check script.
