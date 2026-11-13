module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.CountedSupporters
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee

public section

/-! # Result transfer across a compromise

The writer and voter are honest at their own cuts. The writer-pool premise connects their
views without requiring either node to remain honest at the other's cut.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Result transfer needs no cross-time honesty or fault count: each node obeys its own cut. -/
theorem result_transfer (hrun : ACRun proposer tr H U)
    {s : Nat} {X y : Fin sp.n} {i₀ i : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hX : X ∈ H (tr.time i₀)) (hres : ResultAt tr X i₀ s C CV)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) C)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L C)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg C := by
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hr := hry.localRun
  obtain ⟨_, _, _, hhead⟩ := castAt_spec hr hy hc'
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hy hc'.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc hr hy hc'
  rw [hs] at hdomA
  have hCt : C ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hr hy hc' (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1)
        (by
          obtain ⟨ℓX, hupd, _, rfl⟩ := hres
          exact carried_counted_supporters hrun hX hy hupd.1 hc hs .refl hcarry hviab hd)
        (merged_voters_subset hr hy hc' hd) (result_majority hres) hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : C = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hCt
  · exact (Anc.mem hcore he).2

/-- A result also transfers any viable ancestor compatible with the reader's live locks. -/
theorem result_transfer_anc (hrun : ACRun proposer tr H U)
    {s : Nat} {X y : Fin sp.n} {i₀ i : Nat} {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hX : X ∈ H (tr.time i₀)) (hres : ResultAt tr X i₀ s C CV) (hDC : Anc U D C)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) D)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg D := by
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hr := hry.localRun
  obtain ⟨_, _, _, hhead⟩ := castAt_spec hr hy hc'
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hy hc'.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc hr hy hc'
  rw [hs] at hdomA
  have hDt : D ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxD =>
      isBest_of_majority hΦ (merged_support_subset hr hy hc' (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1)
        (by
          obtain ⟨ℓX, hupd, _, rfl⟩ := hres
          exact carried_counted_supporters hrun hX hy hupd.1 hc hs hDC hcarry hviab hd)
        (merged_voters_subset hr hy hc' hd) (result_majority hres) hCx hp hCxD
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : D = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hDt
  · exact (Anc.mem hcore he).2

/-- **CS2 at the full committee from the growing fault bound**: `f < h ≤ n − f` gives
`2f < n`, which is CS2 at `K = full` with `committeeSize = n` (the stock callers' `hf1`). -/
theorem cs2_full_of_faultBoundAt (hc : sp.committeeSize = sp.n) {t d : Time}
    (hfault : FaultBoundAt tr H t d) {s : Nat} :
    2 * ((CommitteeDict.full sp.n).committee s ∩ (H d)ᶜ).ncard < sp.committeeSize :=
  cs2_full hc (by
    have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have : {y | y ∈ H d ∧ tr.awake y t ∧ JoinedAt tr y t}.ncard ≤ (H d).ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    unfold FaultBoundAt at hfault
    omega)

/-- Transfer also holds for an ancestor of the block stored by the fast lock. -/
theorem first_transfer_stored
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hP : ∀ t, CommitteeP K (tr.upTo t) (H t)) (hT : ∀ t, CommitteeT K (tr.upTo t) (H t))
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    (hcarry : CarryAt tr U y i e s CV)
    (hfault : FaultBoundK K s tr (H (tr.time i)) (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtendAt tr H U i (s + 1) B) : VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hry := hrun.upTo (hr.time_nonneg i)
  have hrx := hrun.upTo (hr.time_nonneg i₀)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  -- CS at the slot-`s` committee gives CS2 there
  have hf2 := cs2_of_cs (K.committee s) (H := H (tr.time i))
    (J := {y | y ∈ H (tr.time i) ∧ tr.awake y (tr.time i) ∧ JoinedAt tr y (tr.time i)})
    (fun _ h => h.1) hfault
  have hf : 2 * (K.committee s ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize := hsize s ▸ hf2
  rcases hfl with ⟨ℓX, C, hupd, hconf, hfs, rfl⟩ | hopt
  swap
  · exact optimistic_transfer_stored hrun K hP hT hsize hx hopt hBD hf hf1 hy hc hs hcarry hviab
      hearlier
  have hupd' := (upTo_updateAt hr.time_mono).mpr ⟨le_rfl, hupd⟩
  obtain ⟨_, _, _, hhead⟩ := castAt_spec hry.localRun hy hc'
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hry.localRun hy hc'.1
  have hΦxU := (frameIn_of_call hrx.localRun hx hupd'.1).2
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc hry.localRun hy hc'
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  obtain ⟨⟨_, _, hBC⟩, _, hfast⟩ := (deepest_mem hfs).1
  set P := tr.state x i₀
  set SX := {w | ∃ v ∈ fastCounted sp P ℓX.frame s D, v.val = w}
  have hd := writer_merged hrun hx hupd hy hc hs hsync
  have hsupp := carried_counted_supporters hrun hx hy hupd.1 hc hs hBD hcarry hviab hd
  have hhalf : sp.committeeSize ≤ 2 * SX.ncard := by
    unfold FastTest confirmationScore at hfast
    refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨hw, v, ⟨hv, hres⟩, hval, _, hanc⟩
    exact ⟨v, ⟨hv, hval ▸ hw, hres, hanc⟩, hval⟩
  have hSX : SX ⊆ K.committee s := by
    rintro w ⟨v, ⟨hv, -⟩, rfl⟩
    have hst : (tr.upTo (tr.time i₀)).state x i₀ = tr.state x i₀ :=
      Trace.upTo_state tr x fun _ hk => hr.time_mono hk.le
    exact (hP (tr.time i₀)).1 x hx i₀ s v (by rw [hst]; exact hv)
  have hmaj : (voters {v | v ∈ P.pool s}).ncard < 2 * SX.ncard := by
    refine lt_of_lt_of_le (result_majority (C := C) ⟨ℓX, hupd, hconf, rfl⟩)
      (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hCR⟩, hval⟩
    exact ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hBC.trans hCR⟩, hval⟩
  have hm : ∀ (Φ' : Frm sp.n FGP) (A' : SAState sp.n) (D' : Blk sp.n FGP), FrameOK Φ' →
      Φ'.tree ⊆ U → D' ∈ Φ'.tree →
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A' Φ' s D').ncard →
      (∀ v ∈ A'.pool s, v.val ∈ H (tr.time i) → v.slot = s ∧
        ∃ j < i, ∃ e', VoteAt (tr.upTo (tr.time i)) v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A'.pool s ⊆ ((tr.upTo (tr.time i)).state y (k + 1)).pool s) →
      Compatible U D' B := by
    rintro Φ' A' D' _ hΦ'U _ h34' _ ⟨k, hk, hsub⟩
    have hO' : optimisticVoters sp A' Φ' s D' ⊆ K.committee s := by
      rintro u ⟨v, hv, rfl, -⟩
      exact (hP (tr.time i)).1 y hy (k + 1) s v (hsub hv)
    obtain ⟨w, ⟨v₁, ⟨hv₁, hneq, _, R₁, hR₁, hR₁r, hBR₁⟩, rfl⟩,
      v₂, hv₂, hv₂w, R₂, hR₂, hR₂r, hDR₂⟩ :=
      inter_nonempty_of_half_quorum (K.committee s) (hsize s) hSX hO' hf2 hhalf h34'
    have hstate : (tr.upTo (tr.time i)).state y (k + 1) = tr.state y (k + 1) :=
      Trace.upTo_state tr y fun j hj => hr.time_mono ((Nat.le_of_lt_succ hj).trans hk)
    have hv₂p := hsub hv₂
    rw [hstate] at hv₂p
    obtain rfl : v₂ = v₁ := by
      rcases writer_pool hrun hx hupd hy hc hs hsync hk v₂ hv₂p with h | h
      · by_contra hne
        exact hneq ⟨v₂, h, v₁, hv₁, hne, hv₂w, rfl⟩
      · exact absurd (hv₂w ▸ h) hneq
    obtain rfl : R₂ = R₁ := hU.1 (hΦ'U hR₂) (hΦxU hR₁) (hR₂r.trans hR₁r.symm)
    exact anc_total hU (Anc.mono hΦ'U hDR₂) (hBD.trans (Anc.mono hΦxU hBR₁))
  have hearlier' : EarlierVotesExtend (tr.upTo (tr.time i)) (H (tr.time i)) U i (s + 1) B := by
    intro x hx j hji e' hv hvs
    obtain ⟨hjt, hv⟩ := upTo_voteAt.mp hv
    exact hearlier x j hji (hr.antitone hjt hx) e' hv hvs
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (locks_compatible hry K (hP (tr.time i)) hy hc' hs hBt (S := SX) (fun w hw => by
        obtain ⟨_, x, hx, hxv, hxs, hxa⟩ := hsupp hw
        exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩)
      hhalf hf1 hearlier' hm)
    fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hry.localRun hy hc' (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1) hsupp
        (merged_voters_subset hry.localRun hy hc' hd) hmaj hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

theorem first_transfer (sp : SAParams) : FirstTransfer sp := by
  intro FGP ro H U tr proposer hrun K hP hT hsize s x y i₀ i B CV ℓ e hx hfl hy hc hs hsync
    hcarry hf hf1 hv he
  exact first_transfer_stored hrun K (hP.upTo hrun.localRun.time_mono hrun.localRun.antitone)
    (hT.upTo hrun.localRun.antitone) hsize hx hfl .refl hy hc hs hsync hcarry hf hf1 hv he

end Consensus.Goldilocks.SA.Growing

end
