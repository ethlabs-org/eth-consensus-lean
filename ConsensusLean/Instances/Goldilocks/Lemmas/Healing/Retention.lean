module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction

/-! # Goldilocks Healing: HR.4, height-scoped retention

(R1)–(R4) for the reset `a_z` over a Goldilocks run under `Healthy(g)` and `NoColl`. The
paper results (claims HR.4, status M: R4, R5, HBoot, JointRet and the high records; T1 §9
(the base case)): C1.1's first-violating-event induction over the run's cut index, with G1.10 at
the height-scoped scope (`𝓔_B` the entries of height `≥ H_z + 1` that conflict with `B`,
`T₀ = a_z − Δ`, every attestation signed at `a_z` covered by HR.1 (c)). It is not an instance of
C1.1: (K0) and (K1) need not hold at `a_z`.

**The induction** (JointRet §13, over the cut index of the fixed run, as C1.1's `persist_inv`).
The invariant at cut `k` has two parts:

* `VoteInv k`: (R3) at the honest votes cast at cut `k`, for **every** high origin of the run
  (a pending regular origin is activated before its first-transfer votes, which precede its
  write; JointRet's activation);
* `CacheInv k`: (R2) after an honest call at cut `k` at a time `≥ a_z`, for every high origin
  active at `k`: written at a cut `≤ k`, or of a label `j` with `t_{j+1} ≤` the time of `k`.

The base case is HBoot (§11, `boot_caches`: before `a_z` the honest `Σ.F` are compatible with
every high origin and no honest `Σ.J` is high) with the activation of pending origins
(`activation_caches`). The vote step (`retention_vote_step`) is C1.1's vote step: the caches at
the vote (`vote_state_caches`), (K2) by R5 (`vote_height_lead`), the fork-choice root compatible
with the origin (`vote_root_compatible`), then C1.1 (i) (`vote_viable_of_root`) and (ii)
(`high_vote_extends`, C1.1's `vote_extends` without the window `(s, m]` and without `Clean`). The
cut step (`retention_cut_step`) is G1.10 at the height-scoped scope. (R1)'s comparability is
`origins_compatible` (A1.9's counting: `fastLock_compatible_of_votes`, `fastLock_same_slot`) over
the votes of the invariant; (R1)'s attestations are the provenance of the sources (`high_rows`, HR.1
(a)); (R4) is the high-record lemma (`high_records`, §16). -/
