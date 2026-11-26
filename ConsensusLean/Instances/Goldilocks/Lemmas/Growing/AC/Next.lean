module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next transfer with participation counted at the vote

The counted votes must have been cast while honest. Their earlier slot then puts them before
the consuming vote, and retention preserves the participation count exactly.
-/

namespace Consensus.Goldilocks.AC.Growing

/-- `next_transfer` at any node start. -/
theorem next_transfer_from {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro}
    {proposer : Nat → Fin sp.n} {ini} (hrun : ACRun proposer tr H U ini) (K : CommitteeDict sp.n)
    (hP : CommitteePAt K tr H) (hT : CommitteeTAt K tr H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {m : Nat} {y : Fin sp.n} {i : Nat}
    {B : Blk sp.n FGP} {ℓ : ACLabel (goldilocksAC sp FGP ro)} {e : Em sp FGP}
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hall : ∀ x j e', x ∈ H (tr.time j) → VoteAt tr x j e' → e'.msg.slot = m →
      VoteExtends U e'.msg B)
    (hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧
      ∃ j e', x ∈ H (tr.time j) ∧ VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ x j e', x ∈ H (tr.time j) ∧ VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m})
    (hf : FaultBoundK K m tr (H (tr.time i)) (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (m + 1) B) (hearlier : EarlierVotesExtendAt tr H U i (m + 1) B) :
    VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hm := hr.time_mono
  have hry := hrun.upTo (hr.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : e.msg.slot = sp.slot (tr.time i) := (castAt_specU hry.localRun.toU hy hc').2.1
  have before : ∀ {x j e'}, x ∈ H (tr.time j) → VoteAt tr x j e' → e'.msg.slot = m → j < i := by
    intro x j e' hx hv hvs
    obtain ⟨ℓ', hv⟩ := hv
    have hs' : e'.msg.slot = sp.slot (tr.time j) := (castAt_specU (hr.upTo (hr.time_nonneg j)).toU
      hx (upTo_castAt.mpr ⟨le_rfl, hv⟩)).2.1
    by_contra h
    have hmono := slot_mono sp (hr.time_nonneg i) (hm (Nat.le_of_not_gt h))
    rw [← hslot, ← hs', hvs, hs] at hmono
    omega
  have hbefore : sp.ts m + 3 * sp.Δ ≤ tr.time i := by
    have h := (ts_le_iff_le_slot sp (hr.time_nonneg i) (m + 1 : Nat)).mpr
      (by rw [← hslot, hs])
    simp only [ACParams.ts] at h ⊢
    push_cast at h
    have := sp.toParams.hΔ
    linarith
  have hbatch : {x | x ∈ H (tr.time i) ∧ ∃ j e', x ∈ H (tr.time j) ∧
      VoteAt tr x j e' ∧ e'.msg.slot = m} =
      {x | x ∈ H (tr.time i) ∧ ∃ j e', VoteAt (tr.upTo (tr.time i)) x j e' ∧
        e'.msg.slot = m} := by
    ext x
    constructor
    · rintro ⟨hx, j, e', hxj, hv, hvs⟩
      exact ⟨hx, j, e', upTo_voteAt.mpr ⟨hm (before hxj hv hvs).le, hv⟩, hvs⟩
    · rintro ⟨hx, j, e', hv, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact ⟨hx, j, e', hr.antitone hji hx, hv, hvs⟩
  rw [hbatch] at hhalf
  apply AC.next_transfer_of_carry sp hry K (hP.upTo hm hr.antitone (tr.time i))
    (hT.upTo hr.antitone (tr.time i)) hsize hy hc' hs
  · intro x hx j e' hv hvs
    obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
    exact hall x j e' (hr.antitone hji hx) hv hvs
  · exact hhalf
  · have h := carryAt_upTo (d := tr.time i) le_rfl hbefore hcarry
    refine ⟨h.awake, h.joined, ?_, ?_⟩
    · rintro v ⟨x, hx, j, e', hv, he, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact h.heads v ⟨x, j, e', hr.antitone hji hx, hv, he, hvs⟩
    · rintro v ⟨x, hx, j, e', hv, he, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact h.holds v ⟨x, j, e', hr.antitone hji hx, hv, he, hvs⟩
  · have hset : {x | x ∈ H (tr.time i) ∧ (tr.upTo (tr.time i)).awake x (tr.time i) ∧
        JoinedAt (tr.upTo (tr.time i)) x (tr.time i)} =
        {x | x ∈ H (tr.time i) ∧ tr.awake x (tr.time i) ∧ JoinedAt tr x (tr.time i)} := by
      ext x
      simp only [Trace.upTo_awake, upTo_joinedAt le_rfl, le_refl, and_true]
    change (K.committee m ∩ (H (tr.time i))ᶜ).ncard < (K.committee m ∩
      {x | x ∈ H (tr.time i) ∧ (tr.upTo (tr.time i)).awake x (tr.time i) ∧
        JoinedAt (tr.upTo (tr.time i)) x (tr.time i)}).ncard
    rw [hset]
    exact hf
  · exact hf1
  · exact hviab
  · intro x hx j hji e' hv hvs
    obtain ⟨hjt, hv⟩ := upTo_voteAt.mp hv
    exact hearlier x j hji (hr.antitone hjt hx) e' hv hvs

theorem next_transfer (sp : ACParams) : NextTransfer sp :=
  fun _ _ _ _ _ _ hrun K hP hT hsize _ _ _ _ _ _ hy hc hs hall hhalf hcarry hf hf1 hviab hearlier =>
    next_transfer_from hrun K hP hT hsize hy hc hs hall hhalf hcarry hf hf1 hviab hearlier

end Consensus.Goldilocks.AC.Growing

end
