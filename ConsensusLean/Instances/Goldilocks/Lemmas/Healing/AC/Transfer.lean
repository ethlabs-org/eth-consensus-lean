module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalTransfer

public section

/-! # Goldilocks Healing: three open steps of H.1 (statements fixed)

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
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}

/-- **T1 §4, a slow origin transfers to the votes** (A3/A5): for an honest slow lock of slot
`s` on `D` with `s − k + 1 ≥ r`, every honest vote of a slot after `s` extends `D`. At a
slot-`(s+1)` vote, every live lock of a label `j < s` has `j ≥ s − k + 1 ≥ r`, so its origin
result is compatible with the writer's saved result of label `j` (T1 §2), which extends `D`;
labels `s`, `s + 1` as in §3; then A1.8 for the ancestor `D` of the result, and
`votes_continue`. -/
theorem slow_origin_transfer_votes (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) : VotesExtendAfter tr H U s D := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓX, C, hupd, hconf, -, hdeep, -⟩ := id hsl
  have hΦXU := (frameIn_of_callAt hr hx hupd.1).2
  have hDC : Anc U D C := Anc.mono hΦXU (deepest_mem hdeep).1.1.2.2
  have hres : ResultAt tr x i₀ s C (fastCounted sp (tr.state x i₀) ℓX.frame s C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  have hk := sp.two_le_k
  have hs' : gbar g + 4 * sp.Δ ≤ sp.ts s := hs.trans ((ts_le_iff sp).2 (by omega))
  have hcarry := trivial_carry_update hS hx hupd hs' C
  -- the result has a counted vote, whose head extends `C`
  obtain ⟨v₀, hv₀⟩ : (fastCounted sp (tr.state x i₀) ℓX.frame s C).Nonempty := by
    have hmaj := result_majority hres
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne] at hmaj
  have hnext : ∀ i, ∀ y ∈ H, ∀ e, VoteAt tr y i e → e.msg.slot = s + 1 →
      VoteExtends U e.msg D := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro y hy e ⟨ℓ, hc, he⟩ hes
      have hca : CastAt tr y i ℓ e := ⟨hc, he⟩
      have hCy := hcarry y hy i e ⟨ℓ, hc, he⟩ hes
      -- `D`, below the head of a counted vote, was accepted before the freeze
      have hacc : AcceptedBefore tr y D (sp.ts s + 3 * sp.Δ) := by
        obtain ⟨Hv, hHv, hHvr, hall⟩ := hCy.heads v₀ hv₀
        obtain ⟨-, -, -, R, hR, hRr, hCR⟩ := hv₀
        obtain rfl : R = Hv := hU.1 (hΦXU hR) hHv (hRr.trans hHvr.symm)
        exact hall D (hDC.trans (Anc.mono hΦXU hCR))
      exact result_transfer_anc sp hrun hx hres hDC hy hca hes hCy
        (viable_of_accepted hS hy hca hes hs' (hΦXU (deepest_mem hdeep).1.1.1) hacc)
        (slow_live_locks hS hx hsl hs hy hca hes
          fun z hz j hj e' hv' hs'' => ih j hj z hz e' hv' hs'')
        (writer_merged hrun hx hupd hy hca hes (hS.syncAC (by linarith) _))
  have hs1 : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) :=
    hs'.trans ((ts_le_iff sp).2 (by push_cast; omega))
  have hcont := votes_continue hS hs1 fun y hy i e hv hs => hnext i y hy e hv hs
  rw [votesExtendAfter_iff]
  intro y hy i e hv hlt
  rcases Nat.lt_or_ge (s + 1) e.msg.slot with h | h
  · exact votesExtendAfter_iff.1 hcont y hy i e hv h
  · exact hnext i y hy e hv (by omega)

/-- **T1 §3–§4 at the proposal duty** ("The same argument applies at a proposal"; T1 §6, "Every
good lock from an older evidence slot has transferred"): the head of every honest proposal of a
slot after the label of a good origin extends its block: its votes do (T1 §3, §4), then
`proposals_extend_of_origin` (ProposalTransfer). -/
theorem origin_transfer_proposals (hS : StandaloneRun tr H U g) {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) : ProposalsExtendAfter tr H U j B := by
  refine proposals_extend_of_origin hS hB ?_
  rcases goodOrigin_iff.1 hB with ⟨x, hx, i, CV, hfl, hs⟩ | ⟨x, hx, i, hsl, hs⟩
  · exact fast_origin_transfer_votes hS hx hfl hs
  · exact slow_origin_transfer_votes hS hx hsl hs

/-- **T1 §6, unanimity**: for an honest proposal `P` of slot `p` (with its parent the head of
its `ac_proposal`) at `t_p ≥ ḡ + 2Θ + 8Δ`, with the locks settled from `t_{p−1}`, every honest
vote of slot `p` is `P`: every lock live at the proposer or a voter is carried by the proposal
head `parent(P)`; the voter's tree is contained in the proposer's, the scores agree, so the
walks agree, and `P` is the only (eligible) slot-`p` child of `parent(P)`; a label-`p` lock
conflicting with `P` needs an earlier bad honest vote. -/
theorem proposal_votes (hS : StandaloneRun tr H U g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  sorry

end Consensus.Goldilocks.SA

end
