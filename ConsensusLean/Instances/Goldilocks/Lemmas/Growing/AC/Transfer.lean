module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Result transfer across a compromise

The writer and voter are honest at their own cuts. The writer-pool premise connects their
views without requiring either node to remain honest at the other's cut.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

private theorem state_eq (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    (y : Fin sp.n) (i : Nat) : (tr.upTo (tr.time i)).state y i = tr.state y i :=
  Trace.upTo_state tr y fun _ hk => hr.time_mono hk.le

private theorem counted_supporters (hrun : ACRun proposer tr H U)
    {X y : Fin sp.n} {i₀ i s : Nat} (hX : X ∈ H (tr.time i₀)) (hy : y ∈ H (tr.time i))
    {B C : Blk sp.n FGP} {ℓX ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hcX : tr.CallAt X i₀ ℓX) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hBC : Anc U B C)
    (hcarry : CarryAt tr U y i e s (fastCounted sp (tr.state X i₀) ℓX.frame s C))
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame s C, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
  have hrX := hrun.localRun.upTo (hrun.localRun.time_nonneg i₀)
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hcX' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hcX⟩
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hU := hrun.localRun.coherent
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_call hrX hX hcX'
  obtain ⟨hΦ, _⟩ := frameIn_of_call hry.localRun hy hc'.1
  have hCt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hone : ∀ w ∉ equivocators {x | x ∈ (tr.state X i₀).pool s}, ∀ v₁ v₂,
      v₁ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₂ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₁.val = w → v₂.val = w → v₁ = v₂ := by
    intro w hw v₁ v₂ h₁ h₂ hv₁ hv₂
    by_contra hne
    rcases hd v₁ h₁ (merged_vote_slot hry.localRun hy hc' v₁ h₁) with h₁' | h₁'
    · rcases hd v₂ h₂ (merged_vote_slot hry.localRun hy hc' v₂ h₂) with h₂' | h₂'
      · exact hw ⟨v₁, h₁', v₂, h₂', hne, hv₁, hv₂⟩
      · exact hw (hv₂ ▸ h₂')
    · exact hw (hv₁ ▸ h₁')
  rintro w ⟨v, ⟨hvp, hvw, hvres, hvanc⟩, rfl⟩
  have hvp' : v ∈ ((tr.upTo (tr.time i₀)).state X i₀).pool s :=
    state_eq hrun.localRun X i₀ ▸ hvp
  have hvs := state_pool_slot sp hrX hX i₀ s v hvp'
  obtain ⟨Hd, hHd, hHdr, hHds⟩ : ∃ Hd ∈ ℓX.frame.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
    unfold resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [ETime.of])
    · rename_i Hd hl
      obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
      split_ifs at hvres with hlt
      · exact absurd hvres (by simp [ETime.of])
      · exact ⟨Hd, hHd, hHdr, Nat.le_of_not_lt hlt⟩
  have hCHd : Anc U C Hd := by
    obtain ⟨R, hR, hRr, hCR⟩ := hvanc
    obtain rfl : R = Hd := hU.1 (hΦXU hR) (hΦXU hHd) (hRr.trans hHdr.symm)
    exact Anc.mono hΦXU hCR
  have hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ) := by
    rcases hcarry.holds v ⟨hvp, hvw, hvres, hvanc⟩ with h |
      ⟨v₁, v₂, h12, _, _, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
    · exact h
    · exfalso
      have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
          u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
        intro u hus hu
        refine Or.inl (List.mem_filter.mpr ⟨?_, ?_⟩)
        · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
          simpa [hus] using hu.1
        · simpa [freeze] using hu.2
      exact h12 (hone _ hvw v₁ v₂ (hm v₁ hs₁ hh₁) (hm v₂ hs₂ hh₂) hv₁ hv₂)
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨hvp, hvw, hvres, hvanc⟩
  have hEq : Hd = Hv := hU.1 (hΦXU hHd) hHv (hHdr.trans hHvr.symm)
  subst Hd
  have hacc' : AcceptedBefore (tr.upTo (tr.time i)) y Hv (sp.ts s + 3 * sp.Δ) := by
    have hT : sp.ts s + 3 * sp.Δ < tr.time i := by
      have hslot : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hry.localRun hy hc').2.1
      have h := (ts_le_iff_le_slot sp (hrun.localRun.time_nonneg i) ((s : Int) + 1)).mpr
        (by rw [← hslot, hs]; push_cast; rfl)
      have hΔ := sp.toParams.hΔ
      simp only [SAParams.ts] at h ⊢
      linarith
    rcases hacc Hv Relation.ReflTransGen.refl with hg | ⟨k, hk, ht⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mpr
        ⟨ht.le.trans hT.le, hk⟩, ht⟩
  refine carried_supporter hry hy hc' hs hCt hvs hheld
    ⟨Hv, hHv, hHvr, hvs ▸ hHds, hBC.trans hCHd, hacc'⟩ fun hq => ?_
  obtain ⟨x, hx, x', hx', hne, hxv, hx'v⟩ := hq
  exact hne (hone _ hvw x x' hx hx' hxv hx'v)

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
          exact counted_supporters hrun hX hy hupd.1 hc hs .refl hcarry hviab hd)
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
          exact counted_supporters hrun hX hy hupd.1 hc hs hDC hcarry hviab hd)
        (merged_voters_subset hr hy hc' hd) (result_majority hres) hCx hp hCxD
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : D = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hDt
  · exact (Anc.mem hcore he).2

/-- Transfer also holds for an ancestor of the block stored by the fast lock. -/
theorem first_transfer_stored (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundAt tr H (tr.time i) (tr.time i))
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtendAt tr H U i (s + 1) B) : VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hry := hrun.upTo (hr.time_nonneg i)
  have hrx := hrun.upTo (hr.time_nonneg i₀)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have hn : (H (tr.time i)).ncard + (H (tr.time i))ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have : honestAwakeJoined tr (H (tr.time i)) (tr.time i) ≤ (H (tr.time i)).ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    unfold FaultBoundAt at hfault
    unfold honestAwakeJoined at this
    omega
  rcases hfl with ⟨ℓX, C, hupd, hconf, hfs, rfl⟩ | hopt
  swap
  · exact optimistic_transfer_stored hrun hx hopt hBD hf hy hc hs hcarry hviab hearlier
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
  have hsupp := counted_supporters hrun hx hy hupd.1 hc hs hBD hcarry hviab hd
  have hhalf : sp.n ≤ 2 * SX.ncard := by
    refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨hw, v, ⟨hv, hres⟩, hval, _, hanc⟩
    exact ⟨v, ⟨hv, hval ▸ hw, hres, hanc⟩, hval⟩
  have hmaj : (voters {v | v ∈ P.pool s}).ncard < 2 * SX.ncard := by
    refine lt_of_lt_of_le (result_majority (C := C) ⟨ℓX, hupd, hconf, rfl⟩)
      (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hCR⟩, hval⟩
    exact ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hBC.trans hCR⟩, hval⟩
  have hm : ∀ (Φ' : Frm sp.n FGP) (A' : SAState sp.n) (D' : Blk sp.n FGP), FrameOK Φ' →
      Φ'.tree ⊆ U → D' ∈ Φ'.tree → 3 * sp.n ≤ 4 * (optimisticVoters sp A' Φ' s D').ncard →
      (∀ v ∈ A'.pool s, v.val ∈ H (tr.time i) → v.slot = s ∧
        ∃ j < i, ∃ e', VoteAt (tr.upTo (tr.time i)) v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A'.pool s ⊆ ((tr.upTo (tr.time i)).state y (k + 1)).pool s) →
      Compatible U D' B := by
    rintro Φ' A' D' _ hΦ'U _ h34' _ ⟨k, hk, hsub⟩
    have hint : (∅ : Set (Fin sp.n)).ncard < (SX ∩ optimisticVoters sp A' Φ' s D').ncard := by
      have := Set.ncard_inter_add_ncard_union SX (optimisticVoters sp A' Φ' s D')
      have := Set.ncard_le_ncard (Set.subset_univ (SX ∪ optimisticVoters sp A' Φ' s D'))
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      rw [Set.ncard_empty]
      omega
    obtain ⟨w, ⟨⟨v₁, ⟨hv₁, hneq, _, R₁, hR₁, hR₁r, hBR₁⟩, rfl⟩,
      v₂, hv₂, hv₂w, R₂, hR₂, hR₂r, hDR₂⟩, _⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hint
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
    (locks_compatible hry hy hc' hs hBt (S := SX) (fun w hw => by
        obtain ⟨_, x, hx, hxv, hxs, hxa⟩ := hsupp hw
        exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩)
      hhalf hf hearlier' hm)
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
  intro FGP ro H U tr proposer hrun s x y i₀ i B CV ℓ e hx hfl hy hc hs hsync hcarry hf hv he
  exact first_transfer_stored hrun hx hfl .refl hy hc hs hsync hcarry hf hv he

end Consensus.Goldilocks.SA.Growing

end
