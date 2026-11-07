module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const

public section

/-! # The growing-fault ACBase and ACSteps statements imply the static ones

At `H := fun _ => H₀` the AC trace contract, `ACRun`, `SyncACAt`, `Carry`, the counts and every
honesty test at a time are the static ones (`Lemmas/Growing/Run/Const`), so each statement of
`Statements/AC/Growing` implies its static counterpart. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams}

/-- With a constant honest set, the votes of nodes honest at their votes are the honest votes. -/
private theorem honestVotes_const {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
    {H : Set (Fin sp.n)} (m : Nat) :
    {v | ∃ x j e', x ∈ (fun _ : Time => H) (tr.time j) ∧ VoteAt tr x j e' ∧ e'.msg = v ∧
        v.slot = m} =
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} := by
  ext v
  exact ⟨fun ⟨x, j, e', hx, h⟩ => ⟨x, hx, j, e', h⟩, fun ⟨x, hx, j, e', h⟩ => ⟨x, j, e', hx, h⟩⟩

theorem joinedAwake_of_growing (h : Growing.JoinedAwake sp) : JoinedAwake sp :=
  fun FGP ro H U tr hrun y hy i ℓ hc hj =>
    h FGP ro (fun _ => H) U tr (Goldilocks.Growing.ACLocalRun.const_iff.mpr hrun) y i ℓ hy hc hj

theorem joinedKeepsVotes_of_growing (h : Growing.JoinedKeepsVotes sp) : JoinedKeepsVotes sp :=
  fun FGP ro H U tr hrun y hy i ℓ hc hj =>
    h FGP ro (fun _ => H) U tr (Goldilocks.Growing.ACLocalRun.const_iff.mpr hrun) y i ℓ hy hc hj

theorem oneVotePerSlot_of_growing (h : Growing.OneVotePerSlot sp) : OneVotePerSlot sp :=
  fun FGP ro H U tr hrun y hy i j e e' =>
    h FGP ro (fun _ => H) U tr (Goldilocks.Growing.ACLocalRun.const_iff.mpr hrun) y i j e e' hy

theorem proposerVotersAgree_of_growing (h : Growing.ProposerVotersAgree sp) :
    ProposerVotersAgree sp :=
  fun FGP ro H U tr proposer hrun s p y i j ℓp ℓy pay e hp hy hpp hP ht hc hs hpay hsync =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s p y i j ℓp ℓy pay e hp hy hpp hP
      ht hc hs hpay (syncACAt_const.mpr hsync)

theorem firstTransfer_of_growing (h : Growing.FirstTransfer sp) : FirstTransfer sp :=
  fun FGP ro H U tr proposer hrun s x y i₀ i B CV ℓ e hx hl hy hc hs hsync hcarry hf hv he =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s x y i₀ i B CV ℓ e hx hl hy hc hs
      (syncACAt_const.mpr hsync) hcarry hf hv ((earlierVotesExtendAt_const _ _ _).mpr he)

theorem nextTransfer_of_growing (h : Growing.NextTransfer sp) : NextTransfer sp := by
  intro FGP ro H U tr proposer hrun m y i B ℓ e hy hc hs hall hhalf hcarry hf hv he
  refine h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) m y i B ℓ e hy hc hs
    (fun x j e' hx hv' hs' => hall x hx j e' hv' hs') ?_ ?_ hf hv
    ((earlierVotesExtendAt_const _ _ _).mpr he)
  · convert hhalf using 4
    ext x
    exact ⟨fun ⟨hx, j, e', _, h⟩ => ⟨hx, j, e', h⟩, fun ⟨hx, j, e', h⟩ => ⟨hx, j, e', hx, h⟩⟩
  · rw [honestVotes_const]
    exact hcarry

theorem optimisticTransfer_of_growing (h : Growing.OptimisticTransfer sp) :
    OptimisticTransfer sp :=
  fun FGP ro H U tr proposer hrun s x y i₀ i B CV ℓ e hx hl hf hy hc hs hcarry hv he =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s x y i₀ i B CV ℓ e hx hl hf hy hc hs
      hcarry hv ((earlierVotesExtendAt_const _ _ _).mpr he)

theorem optimisticNextUpdate_of_growing (h : Growing.OptimisticNextUpdate sp) :
    OptimisticNextUpdate sp :=
  fun FGP ro H U tr proposer hrun s z k B ℓ hf hall hz hu hhalf hres =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s z k B ℓ hf
      (fun x' j e hx hv hs => hall x' hx j e hv hs) hz hu hhalf hres

theorem sourceAge_of_growing (h : Growing.SourceAge sp) : SourceAge sp :=
  fun FGP ro H U tr hrun τ x i ℓ C hx ht hs =>
    h FGP ro (fun _ => H) U tr (Goldilocks.Growing.ACLocalRun.const_iff.mpr hrun) τ x i ℓ C hx ht hs

theorem resultTransfer_of_growing (h : Growing.ResultTransfer sp) : ResultTransfer sp :=
  fun FGP ro H U tr proposer hrun s X y i₀ i C CV ℓ e hX hr hy hc hs hcarry hv hl hw =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s X y i₀ i C CV ℓ e hX hr hy hc hs
      hcarry hv hl hw

theorem sourceCompatible_of_growing (h : Growing.SourceCompatible sp) : SourceCompatible sp :=
  fun FGP ro H U tr proposer hrun s m w x i₀ i B CV ℓ C hw hl hsync hcarry hf hx ht h1 h2 hall
      hcase =>
    h FGP ro (fun _ => H) U tr proposer (acRun_const.mpr hrun) s m w x i₀ i B CV ℓ C hw hl
      (syncACAt_const.mpr hsync) ((carry_const _ _).mpr hcarry) hf hx ht h1 h2
      (fun z j hj hz e hv hs1 hs2 => hall z hz j hj e hv hs1 hs2) hcase

/-- The growing-fault ACSteps milestone implies the static one. -/
theorem acSteps_of_growing (h : Growing.ACSteps) : ACSteps := fun sp =>
  { proposerVotersAgree := proposerVotersAgree_of_growing (h sp).proposerVotersAgree
    firstTransfer := firstTransfer_of_growing (h sp).firstTransfer
    nextTransfer := nextTransfer_of_growing (h sp).nextTransfer
    optimisticTransfer := optimisticTransfer_of_growing (h sp).optimisticTransfer
    optimisticNextUpdate := optimisticNextUpdate_of_growing (h sp).optimisticNextUpdate
    sourceAge := sourceAge_of_growing (h sp).sourceAge
    resultTransfer := resultTransfer_of_growing (h sp).resultTransfer
    sourceCompatible := sourceCompatible_of_growing (h sp).sourceCompatible }

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks

/-- The growing-fault `LocalRunReachable` implies the static one. -/
theorem localRunReachable_of_growing (h : Growing.LocalRunReachable) : LocalRunReachable :=
  fun P FGP A H U tr hrun y hy i ℓ hc =>
    h P FGP A (fun _ => H) U tr (Growing.ACLocalRun.const_iff.mpr hrun) y i ℓ hy hc

end Consensus.Goldilocks

end
