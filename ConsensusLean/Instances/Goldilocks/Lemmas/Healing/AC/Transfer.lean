module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalTransfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Votes

public section

/-! # Goldilocks Healing: three steps of H.1 (statements fixed)

Three step lemmas of H.1 (healing-simple `t1-proof.md`) over a `StandaloneRun`, used by the
assembly in `Steps.lean`; their statements are fixed (the assembly depends on them as stated):

* `origin_transfer_proposals`, T1 §3 at the proposal duty: a good origin is extended by the head
  of every honest `ac_proposal` of a later slot;
* `slow_origin_transfer_votes`, T1 §4 (slow origins): a slow origin whose window is `≥ r` is
  extended by every honest vote of a later slot;
* `proposal_votes`, T1 §6 (unanimity): with the locks settled from `t_{p−1}`, every honest vote of
  slot `p` is the honest proposal `P`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **T1 §4, a slow origin transfers to the votes** (A3/A5): for an honest slow lock of slot
`s` on `D` with `s − k + 1 ≥ r`, every honest vote of a slot after `s` extends `D`. At a
slot-`(s+1)` vote, every live lock of a label `j < s` has `j ≥ s − k + 1 ≥ r`, so its origin
result is compatible with the writer's saved result of label `j` (T1 §2), which extends `D`;
labels `s`, `s + 1` as in §3; then A1.8 for the ancestor `D` of the result, and
`votes_continue`. -/
theorem slow_origin_transfer_votes (hS : StandaloneRun tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) : VotesExtendAfter tr H U s D := by
  sorry

/-- **T1 §3–§4 at the proposal duty** ("The same argument applies at a proposal"; T1 §6, "Every
good lock from an older evidence slot has transferred"): the head of every honest proposal of a
slot after the label of a good origin extends its block: its votes do (T1 §3, §4), then
`proposals_extend_of_origin` (ProposalTransfer). -/
theorem origin_transfer_proposals (hS : StandaloneRun tr H U proposer g)
    {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) : ProposalsExtendAfter tr H U j B := by
  refine proposals_extend_of_origin hS hB ?_
  rcases goodOrigin_iff.1 hB with ⟨x, hx, i, CV, hfl, hs⟩ | ⟨x, hx, i, hsl, hs⟩
  · exact fast_origin_transfer_votes hS hx hfl hs
  · exact slow_origin_transfer_votes hS hx hsl hs

/-- **T1 §6, unanimity**: for an honest proposal `P` of slot `p` (with its parent the head of
its `ac_proposal`) at `t_p ≥ ḡ + 2Θ + 8Δ`, with the locks settled from `t_{p−1}`, every honest
vote of slot `p` is `P`. Proved over the canonical walk in `Unanimity/Votes`
(`proposal_votes_of_setting`; see that module's docstring). -/
theorem proposal_votes (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  obtain ⟨k, ℓp, d, pay, hk, hkc, hpay, htk, hPd, hPs, hPq, hPa, hacc⟩ := hP
  exact proposal_votes_of_setting
    ⟨hS, hpH, hk, hkc, hpay, htk, hPd, hPs, hPq, hPa, hacc, hp, hset⟩

end Consensus.Goldilocks.SA

end
