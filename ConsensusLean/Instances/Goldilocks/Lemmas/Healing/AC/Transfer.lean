module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SettledFrom
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalTransfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Votes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: three steps of H.1 (statements fixed)

Three step lemmas of H.1 over a `StandaloneRun`, used by the assembly in `Steps.lean`; their
statements are fixed (the assembly depends on them as stated):

* `origin_transfer_proposals`, the transfer at the proposal duty: a good origin is extended by
  the head of every honest `ac_proposal` of a later slot;
* `slow_origin_transfer_votes`, slow origins: a slow origin whose window is `≥ r` is extended by
  every honest vote of a later slot;
* `proposal_votes`, unanimity: with the locks settled from `t_{p−1}`, every honest vote of slot
  `p` is the honest proposal `P`. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- `slow_origin_transfer_votes` with the unlock given. -/
theorem slow_origin_transfer_votesU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) : VotesExtendAfter tr H U s D := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := id hsl
  have hΦXU := (frameIn_of_callAtU hr hx hupd.1).2
  have hDC : Anc U D C := Anc.mono hΦXU (deepest_mem hdeep).1.1.2.2
  have hres : ResultAt tr x i₀ s C (fastCounted sp (tr.state x i₀) ℓX.frame s C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  have hk := sp.two_le_k
  have hs' : gbar g + 4 * sp.Δ ≤ sp.ts s := hs.trans ((ts_le_iff sp).2 (by omega))
  have hcarry := trivial_carry_updateU hS hx hupd hs' C
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
      exact result_transfer_ancU sp hrun hx hres hDC hy hca hes hCy
        (viable_of_acceptedU hS hy hca hes hs' (hΦXU (deepest_mem hdeep).1.1.1) hacc)
        (slow_live_locksU hS.toHealthyBaseU hx hsl hs hy hca hes
          fun z hz j hj e' hv' hs'' => ih j hj z hz e' hv' hs'')
        (writer_mergedU hrun hx hupd hy hca hes (hS.syncAC (by linarith) _))
  have hs1 : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) :=
    hs'.trans ((ts_le_iff sp).2 (by push_cast; omega))
  have hcont := votes_continueU hS hs1 fun y hy i e hv hs => hnext i y hy e hv hs
  rw [votesExtendAfter_iff]
  intro y hy i e hv hlt
  rcases Nat.lt_or_ge (s + 1) e.msg.slot with h | h
  · exact votesExtendAfter_iff.1 hcont y hy i e hv h
  · exact hnext i y hy e hv (by omega)

/-- **A slow origin transfers to the votes**: for an honest slow lock of slot
`s` on `D` with `s − k + 1 ≥ r`, every honest vote of a slot after `s` extends `D`. At a
slot-`(s+1)` vote, every live lock of a label `j < s` has `j ≥ s − k + 1 ≥ r`, so its origin
result is compatible with the writer's saved result of label `j` (same-slot compatibility),
which extends `D`; labels `s`, `s + 1` as for a fast origin; then A1.8 for the ancestor `D` of
the result, and `votes_continue`. -/
theorem slow_origin_transfer_votes (hS : StandaloneRun tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) : VotesExtendAfter tr H U s D :=
  slow_origin_transfer_votesU (hS := hS.toU) (x := x) (hx := hx) (i₀ := i₀) (s := s) (D := D)
      (hsl := hsl) (hs := hs)

/-- `origin_transfer_proposals` with the unlock given. -/
theorem origin_transfer_proposalsU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g)
    {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) : ProposalsExtendAfterU u tr H U j B := by
  refine proposals_extend_of_originU hS hB ?_
  rcases goodOrigin_iff.1 hB with ⟨x, hx, i, CV, hfl, hs⟩ | ⟨x, hx, i, hsl, hs⟩
  · exact fast_origin_transfer_votesU hS hx hfl hs
  · exact slow_origin_transfer_votesU hS hx hsl hs

/-- **The transfer at the proposal duty** (the argument at the votes applies at a proposal, and
every good lock from an older evidence slot has transferred): the head of every honest proposal
of a slot after the label of a good origin extends its block: its votes do
(`fast_origin_transfer_votes`, `slow_origin_transfer_votes`), then `proposals_extend_of_origin`
(ProposalTransfer). -/
theorem origin_transfer_proposals (hS : StandaloneRun tr H U proposer g)
    {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) : ProposalsExtendAfter tr H U j B :=
  proposalsExtendAfterU_parent_iff.1 (origin_transfer_proposalsU hS.toU hB)

/-- `proposal_votes_coreU` with the locks settled above the floor `p` only. -/
theorem proposal_votes_core_fromU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H) (hP : HonestProposalU u tr (proposer p) p P)
    (hp : gbar g + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledFromU u tr H U p (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  obtain ⟨k, ℓp, d, pay, hk, hkc, hpay, htk, hPd, hPs, hPq, hPa, hacc⟩ := hP
  exact proposal_votes_of_setting_coreU
    ⟨hS, hpH, hk, hkc, hpay, htk, hPd, hPs, hPq, hPa, hacc, hp, hset⟩

/-- `proposal_votes_core` with the unlock given. -/
theorem proposal_votes_coreU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H) (hP : HonestProposalU u tr (proposer p) p P)
    (hp : gbar g + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledU u tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root :=
  proposal_votes_core_fromU hS hpH hP hp (hset.toFrom p)

/-- **Unanimity from `t_p ≥ ḡ + 8Δ`**: `proposal_votes` needs of the slot only
`t_{p−1} ≥ ḡ + 4Δ` (and `p > 0`); the margin for the locks is all in `hset`. -/
theorem proposal_votes_core (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root :=
  proposal_votes_coreU (hS := hS.toU) (p := p) (P := P) (hpH := hpH) (hP := hP.toU) (hp := hp)
      (hset := hset.toU)

/-- **Unanimity**: for an honest proposal `P` of slot `p` (with its parent the head of
its `ac_proposal`) at `t_p ≥ ḡ + 2Θ + 8Δ`, with the locks settled from `t_{p−1}`, every honest
vote of slot `p` is `P`. Proved over the canonical walk in `Unanimity/Votes`
(`proposal_votes_of_setting`; see that module's docstring). -/
theorem proposal_votes (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root :=
  proposal_votes_core hS hpH hP (by linarith [Θ_nonneg sp]) hset

end Consensus.Goldilocks.SA

end
