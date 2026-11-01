# C8 ARM-healthy and C10 slow P1: no open hypotheses

`pcsa_armHealthyClaim` (C8, ARM-healthy) and `pcsa_slowP1Claim` (C10, slow
P1) in `Proofs/Assembly/Outage.lean` take no OPEN hypothesis. The versions
with the HEAD cone as a hypothesis, `pcsa_armHealthy_of_claims` and
`pcsa_slowP1_of_claims`, stay; the closed versions supply the cone records
(`Outage/CleanBridge.lean`):

- `CleanVoteConeItems`, for C8: for `0 < i` with `v_i ≤ b₀`, a block below
  every honest HEAD of label `i − 1` is below every honest HEAD of label `i`.
  `pcsa_cleanVoteConeItems` proves it from `pcsa_clean_heads_cone_at_vote`.
- `CleanConeItems`, for C10: the same with `e_{i−1} ≤ b₀` (the full cone).
  `pcsa_cleanConeItems` proves it from `pcsa_clean_heads_cone_past_cut`.

The cone is from tip-stability `spec/drafts/pending/pending-cone-repair.md`,
with its review fixes; the Clean lane proves it (`Clean/OPEN.md`, HeadCone).
C10 needs the full cone at the pending HEAD (`pcsa_cut_pendingHead`); the ARM
consumers use only the vote-time form.

The other fields of `CutChain` and `CutFacts` are proved
(`pcsa_cleanCutItems_of_cone`): `nonempty`, `chain` and `dis` (M1, M2, M3),
`same` (CI (i)), `rows` (`pcsa_clean_lock_below_record_cut`) and `bridge` (the
clean-gate successor: for `d_j ≤ b₀`, every honest HEAD of label `j + 1`
extends the honest result of label `j`). C8 uses `dis` at the label after the
PC slot and does not use `CutFacts`.

The cone and the bridge replace the former fields `CutChain.heads` (a HEAD of
label `i` with `v_i ≤ b₀` extends every honest result of `i − 1`) and
`CutFacts.pastCut` (the same with `e_{i−1} ≤ b₀`). A counterexample run refutes
the former fields in the boundary case `v_r ≤ b₀ < d_{r−1}` of pcsa34-r4.3
§5.5 step 2: the HEAD of label 2 of honest node 3 at `t = 18` does not extend
the result of label 1 of honest node 0 at `t = 20` (cuts 12 and 18). The run
does not refute the cone.
