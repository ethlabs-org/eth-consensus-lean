module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic transfer charged at the consuming vote

The writer may be compromised before the vote. Its historical pool is read at the writer's
cut, but the shared validator is chosen outside the faulty set at the consuming vote.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

theorem optimistic_transfer_stored
    {ini} (hrun : ACRun proposer tr H U ini) (K : CommitteeDict sp.n)
    (hP : ∀ t, CommitteeP K (tr.upTo t) (H t)) (hT : ∀ t, CommitteeT K (tr.upTo t) (H t))
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (K.committee s ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hf1 : 2 * (K.committee (s + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtendAt tr H U i (s + 1) B) : VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have htime := hr.time_mono
  have hry := hrun.upTo (hr.time_nonneg i)
  have hrx := hrun.upTo (hr.time_nonneg i₀)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  obtain ⟨ℓx, A, hpt, hslx, hsel, rfl⟩ := hopt
  have hpt' := (upTo_optimisticPoint htime).mpr ⟨le_rfl, hpt⟩
  obtain ⟨_, _, _, hhead⟩ := castAt_spec hry.localRun hy hc'
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hry.localRun hy hc'.1
  obtain ⟨_, hΦxU⟩ := frameIn_of_call hrx.localRun hx hpt'.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc_from hry.localRun hry.vstart hy hc'
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  set SX := optimisticVoters sp A ℓx.frame s D
  have h34 : 3 * sp.committeeSize ≤ 4 * SX.ncard := by
    have h := hsel
    unfold optimisticSelect at h
    dsimp only at h
    split_ifs at h
    have := (deepest_mem h).1.2.1
    rwa [hslx] at this
  have hSX : SX ⊆ K.committee s := by
    rintro u ⟨v, hv, rfl, -⟩
    exact (hP (tr.time i₀)).2 x hx i₀ ℓx A hpt' s v hv
  have hf2 : 2 * (K.committee s ∩ (H (tr.time i))ᶜ).ncard < (K.committee s).ncard := by
    rw [hsize s]; exact hf
  have hxi : tr.time i₀ ≤ tr.time i := by
    have hslt : tr.time i₀ < sp.ts s + 2 * sp.Δ := by
      have h := hsel
      unfold optimisticSelect at h
      dsimp only at h
      split_ifs at h with hh
      · rw [hslx] at hh
        exact not_le.mp (not_or.mp (not_or.mp hh).2).2
    have hsv : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hry.localRun hy hc').2.1
    have ht := (ts_le_iff_le_slot sp (hr.time_nonneg i) (s + 1 : Nat)).mpr
      (by rw [← hsv, hs])
    simp only [SAParams.ts] at ht hslt
    push_cast at ht
    have := sp.toParams.hΔ
    linarith
  have hfreeze : sp.ts s + 3 * sp.Δ ≤ tr.time i := by
    have hsv : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hry.localRun hy hc').2.1
    have ht := (ts_le_iff_le_slot sp (hr.time_nonneg i) (s + 1 : Nat)).mpr
      (by rw [← hsv, hs])
    simp only [SAParams.ts] at ht ⊢
    push_cast at ht
    have := sp.toParams.hΔ
    linarith
  have hcarry' := carryAt_upTo (d := tr.time i) le_rfl hfreeze hcarry
  set V := mergedVoteView sp e.readPoint ℓ.frame (s + 1)
  have hcover : SX ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R, hR, hRr, hDR⟩
    exact carried_cover hry hy hc' hs hBt hcarry'
      ⟨hv, R, hR, hRr, hDR⟩
      (optimisticPoint_pool_slot_from hrx.localRun hrx.vstart hx hpt' hv) ⟨R, hΦxU hR, hRr,
        (frame_slot_le sp hrx.localRun hx hpt'.1 R hR).trans hslx.le,
        hBD.trans (Anc.mono hΦxU hDR)⟩
  have hW : voters V.votes ⊆ K.committee s := by
    rintro u ⟨v, hv, rfl⟩
    have hK := (hT (tr.time i)) y hy i ℓ e hc' s v hv
    rwa [merged_vote_slot hry.localRun hry.vstart hy hc' v hv] at hK
  have hE : equivocators V.votes ⊆ K.committee s ∩ (H (tr.time i))ᶜ := by
    intro w hw
    refine ⟨?_, fun hwH => honest_not_equivocator hry hy hc' hwH hw⟩
    obtain ⟨a, ha, -, -, -, rfl, -⟩ := hw
    exact hW ⟨a, ha, rfl⟩
  have hm : ∀ (Φ' : Frm sp.n FGP) (A' : SAState sp.n) (D' : Blk sp.n FGP), FrameOK Φ' →
      Φ'.tree ⊆ U → D' ∈ Φ'.tree →
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A' Φ' s D').ncard →
      (∀ v ∈ A'.pool s, v.val ∈ H (tr.time i) → v.slot = s ∧
        ∃ j < i, ∃ e', VoteAt (tr.upTo (tr.time i)) v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A'.pool s ⊆ ((tr.upTo (tr.time i)).state y (k + 1)).pool s) →
      Compatible U D' B := by
    rintro Φ' A' D' _ hΦ'U _ h34' hpool ⟨k, -, hsub⟩
    have hO' : optimisticVoters sp A' Φ' s D' ⊆ K.committee s := by
      rintro u ⟨v, hv, rfl, -⟩
      exact (hP (tr.time i)).1 y hy (k + 1) s v (hsub hv)
    obtain ⟨w, ⟨⟨v₁, hv₁, rfl, R₁, hR₁, hR₁r, hBR₁⟩, v₂, hv₂, hv₂w, R₂, hR₂, hR₂r, hDR₂⟩, hwH⟩ :=
      quorums_meet (K.committee s) (hsize s) hSX hO' h34 h34' hf2
    have hwH : v₁.val ∈ H (tr.time i) := not_not.mp hwH
    obtain ⟨_, j₁, hj₁, e₁, hvote₁, rfl⟩ := optimisticPoint_pool_vote hrx hx hpt' hv₁
      (hr.antitone hxi hwH)
    obtain ⟨hs₂, j₂, hj₂, e₂, hvote₂, rfl⟩ := hpool v₂ hv₂ (hv₂w ▸ hwH)
    have hvote₁' := (upTo_voteAt).mp hvote₁
    have hvote₁'' := upTo_voteAt.mpr ⟨hvote₁'.1.trans hxi, hvote₁'.2⟩
    obtain ⟨_, rfl⟩ := SA.one_vote_per_slotU sp FGP ro (H (tr.time i)) U
      (tr.upTo (tr.time i)) hry.localRun.toU _ hwH j₁ j₂ e₁ e₂ hvote₁''
      (hv₂w ▸ hvote₂)
      (by rw [optimisticPoint_pool_slot_from hrx.localRun hrx.vstart hx hpt' hv₁, hs₂])
    obtain rfl : R₂ = R₁ := hU.1 (hΦ'U hR₂) (hΦxU hR₁) (hR₂r.trans hR₁r.symm)
    exact anc_total hU (Anc.mono hΦ'U hDR₂) (hBD.trans (Anc.mono hΦxU hBR₁))
  have hearlier' : EarlierVotesExtend (tr.upTo (tr.time i)) (H (tr.time i)) U i (s + 1) B := by
    intro x hx j hji e' hv hvs
    obtain ⟨hjt, hv⟩ := upTo_voteAt.mp hv
    exact hearlier x j hji (hr.antitone hjt hx) e' hv hvs
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard :=
    cover_count (K.committee s) (hsize s) hSX hW hE h34 hf2
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i) V (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (locks_compatible hry K (hP (tr.time i)) hy hc' hs hBt
      (S := SX) (fun w hw => by
        rcases hcover hw with ⟨_, x, hx, hxv, hxs, hxa⟩ | h
        · exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩
        · exact Or.inl h)
      (by omega) hf1 hearlier' hm)
    fun X' Cx hCx hp hCxC =>
      isBest_of_cover hΦ (merged_support_subset hry.localRun hy hc' (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1) hcover h3 hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1))) V (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

theorem optimistic_transfer (sp : SAParams) :
    OptimisticTransfer sp := by
  intro FGP ro H U tr proposer hrun K hP hT hsize s x y i₀ i B CV ℓ e hx hopt hf hf1 hy hc hs
    hcarry hv he
  exact optimistic_transfer_stored hrun K (hP.upTo hrun.localRun.time_mono hrun.localRun.antitone)
    (hT.upTo hrun.localRun.antitone) hsize hx hopt .refl hf hf1 hy hc hs hcarry hv he

end Consensus.Goldilocks.SA.Growing

end
