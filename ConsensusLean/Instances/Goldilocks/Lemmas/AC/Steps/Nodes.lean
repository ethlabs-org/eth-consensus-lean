module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: the step lemmas (A1.1–A1.5, A1.8, A1.9)

The per-vote transfer lemmas over SA traces. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable (sp : SAParams)

section Stock

/-- **CS2 at the full committee from the stock fault bound**: `f < h ≤ n − f` gives `2f < n`,
which is CS2 at `K = full` with `committeeSize = n` (the stock callers' `hf1`). -/
theorem cs2_full_of_faultBound {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
    {H : Set (Fin sp.n)} {t : Time} (hc : sp.committeeSize = sp.n) (hfault : FaultBound tr H t)
    {s : Nat} : 2 * ((CommitteeDict.full sp.n).committee s ∩ Hᶜ).ncard < sp.committeeSize :=
  cs2_full hc (by
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have : honestAwakeJoined tr H t ≤ H.ncard := Set.ncard_le_ncard fun x hx => hx.1
    unfold FaultBound at hfault
    omega)

/-- `next_transfer_of_carry` with the unlock given. -/
theorem next_transfer_of_carryU
    {uL : Nat → Set Lock} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRunU wm uL proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    {m : Nat} {y : Fin sp.n} {i : Nat}
    {B : Blk sp.n FGP} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B)
    (hhalf : sp.committeeSize ≤
      2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m})
    (hfault : FaultBoundK K m tr H (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (m + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B) : VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hr hy hc
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_ancU hr (fun _ => voteStart_initial _) hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  -- the honest voters of slot `m` are supporters of `B` at `y`
  set SX : Set (Fin sp.n) := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}
  have hsupp : SX ⊆ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) m B := by
    rintro w ⟨hw, j, e', hv, hvs⟩
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (castAt_specU hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} :=
      ⟨w, hw, j, e', hv, rfl, hvs⟩
    -- `y` holds `e'.msg` itself (an honest validator has one slot-`m` vote)
    have hheld : HeldBefore e.readPoint e'.msg (sp.ts m + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u, u.slot = m → HeldBefore e.readPoint u (sp.ts m + 3 * sp.Δ) →
            u ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes := by
          intro u hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SAState.poolAt, show ¬ (((m + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
            simpa [hus] using hu.1
          · simpa [freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          honest_merged_voteU hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := (one_vote_per_slotU sp) FGP ro H U tr hr w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := honest_headU hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hw j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := carried_supporterU hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (honest_not_equivocatorU hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  -- counting: the voters at `y` are honest slot-`m` voters or faulty members of the slot-`m`
  -- committee, and `f < |SX|`
  obtain ⟨hf2, h3⟩ := next_transfer_counts (K.committee m) (H := H)
    (J := {y | y ∈ H ∧ tr.awake y (tr.time i) ∧ JoinedAt tr y (tr.time i)}) (hsize m)
    (fun _ h => h.1) hfault hhalf
  have hfm : 2 * (K.committee m ∩ Hᶜ).ncard < sp.committeeSize := hsize m ▸ hf2
  have hvoters : voters (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes ⊆
      SX ∪ (K.committee m ∩ Hᶜ) := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e', hv', he'⟩ := honest_merged_voteU hrun hy hc hv hw
      exact Or.inl ⟨hw, j, e', hv', by
        rw [he']; exact merged_vote_slotU hr (fun _ => voteStart_initial _) hy hc v hv⟩
    · have hK := hT y hy i ℓ e hc m v hv
      rw [merged_vote_slotU hr (fun _ => voteStart_initial _) hy hc v hv] at hK
      exact Or.inr ⟨hK, hw⟩
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) (m : Int) (fun B hB => voteDomain_subset_tree
        hB) hdomA hviab.voteDomain
    (locks_compatibleU hrun K hP hy hc hs hBt (S := SX)
      (fun w hw => by
        obtain ⟨-, x, hx, hxv, hxs, hxa⟩ := hsupp hw
        exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩)
      hhalf hf1 hearlier fun Φ' A D _ hΦ'U _ h34 hpool hsub =>
        origin_compatible hU hΦ'U K h34 (fun u ⟨v, hv, hvu, _⟩ => by
            obtain ⟨k, -, hk⟩ := hsub
            exact hvu ▸ hP.1 y hy (k + 1) m v (hk hv)) hfm fun v hv hvH => by
          obtain ⟨hvs, j, -, e', hvote, rfl⟩ := hpool v hv hvH
          exact hall _ hvH j e' hvote hvs)
    fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subsetU hr hy hc (m + 1)) (fun B hB =>
          voteDomain_subset_tree hB.1)
        hsupp hvoters h3 hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (m + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) (m : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- The A1.3 transfer after delivery: synchronization is used to obtain CarryAt,
not by the local transfer itself. -/
theorem next_transfer_of_carry {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    {m : Nat} {y : Fin sp.n} {i : Nat}
    {B : Blk sp.n FGP} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B)
    (hhalf : sp.committeeSize ≤
      2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m})
    (hfault : FaultBoundK K m tr H (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (m + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B) : VoteExtends U e.msg B :=
  next_transfer_of_carryU (FGP := FGP) (ro := ro) (H := H) (U := U) (tr := tr)
      (proposer := proposer) (hrun := hrun.toU) (K := K) (hP := hP) (hT := hT) (hsize := hsize)
      (m := m) (y := y) (i := i)
          (B := B) (ℓ := ℓ) (e := e) (hy := hy) (hc := hc) (hs := hs) (hall := hall)
              (hhalf := hhalf) (hcarry := hcarry) (hfault := hfault) (hf1 := hf1)
                  (hviab := hviab) (hearlier := hearlier)

/-- **A1.3**, over a run with the unlock given. -/
theorem next_transferU (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) (K : CommitteeDict sp.n)
    (hP : CommitteeP K tr H) (hT : CommitteeT K tr H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) (m : Nat) (y : Fin sp.n) (i : Nat)
    (B : Blk sp.n FGP) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP)
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B)
    (hhalf : sp.committeeSize ≤
      2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m})
    (hfault : FaultBoundK K m tr H (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (m + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B) : VoteExtends U e.msg B :=
  next_transfer_of_carryU sp hrun K hP hT hsize hy hc hs hall hhalf hcarry hfault hf1 hviab
    hearlier

/-- **A1.3.** -/
theorem next_transfer : NextTransfer sp :=
  fun _ _ _ _ _ _ hrun K hP hT hsize _ _ _ _ _ _ hy hc hs hall hhalf hcarry hfault hf1 hviab
      hearlier =>
    next_transfer_of_carry sp hrun K hP hT hsize hy hc hs hall hhalf hcarry hfault hf1 hviab
      hearlier

/-- `optimistic_transfer_stored` with the unlock given. -/
theorem optimistic_transfer_storedU
    {u : Nat → Set Lock} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRunU wm u proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize)
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (s + 1) B) : VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨ℓx, A, hpt, hslx, hsel, rfl⟩ := hopt
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hr hy hc
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hΦxU : ℓx.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx i₀ ℓx hpt.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1.2
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_ancU hr (fun _ => voteStart_initial _) hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  -- the counted validators, three quarters of the committee, all of them members (P)
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
    exact hP.2 x hx i₀ ℓx A hpt s v hv
  have hf2 : 2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard := by rw [hsize s]; exact hf
  -- each of them supports `B` at `y` or equivocates there
  set V := mergedVoteView sp e.readPoint ℓ.frame (s + 1)
  have hcover : SX ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R, hR, hRr, hDR⟩
    exact carried_coverU hrun hy hc hs hBt hcarry
      ⟨hv, R, hR, hRr, hDR⟩
      (optimisticPoint_pool_slotU hr (fun _ => voteStart_initial _) hx hpt hv) ⟨R, hΦxU hR, hRr,
        (frame_slot_leU sp hr hx hpt.1 R hR).trans hslx.le, hBD.trans (Anc.mono hΦxU hDR)⟩
  have hW : voters V.votes ⊆ K.committee s := by
    rintro u ⟨v, hv, rfl⟩
    have hK := hT y hy i ℓ e hc s v hv
    rwa [merged_vote_slotU hr (fun _ => voteStart_initial _) hy hc v hv] at hK
  have hE : equivocators V.votes ⊆ K.committee s ∩ Hᶜ := by
    intro w hw
    refine ⟨?_, fun hwH => honest_not_equivocatorU hrun hy hc hwH
      hw⟩
    obtain ⟨a, ha, -, -, -, rfl, -⟩ := hw
    exact hW ⟨a, ha, rfl⟩
  -- an optimistic origin of slot `s` at `y` shares an honest voter with `SX`
  have hm : ∀ (Φ' : Frm sp.n FGP) (A' : SAState sp.n) (D' : Blk sp.n FGP), FrameOK Φ' →
      Φ'.tree ⊆ U → D' ∈ Φ'.tree →
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A' Φ' s D').ncard →
      (∀ v ∈ A'.pool s, v.val ∈ H → v.slot = s ∧
        ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A'.pool s ⊆ (tr.state y (k + 1)).pool s) → Compatible U D' B := by
    rintro Φ' A' D' - hΦ'U - h34' hpool ⟨k, -, hsub⟩
    have hO' : optimisticVoters sp A' Φ' s D' ⊆ K.committee s := by
      rintro u ⟨v, hv, rfl, -⟩
      exact hP.1 y hy (k + 1) s v (hsub hv)
    obtain ⟨w, ⟨⟨v₁, hv₁, rfl, R₁, hR₁, hR₁r, hBR₁⟩, v₂, hv₂, hv₂w, R₂, hR₂, hR₂r, hDR₂⟩, hwH⟩ :=
      quorums_meet (K.committee s) (hsize s) hSX hO' h34 h34' hf2
    have hwH : v₁.val ∈ H := not_not.1 hwH
    obtain ⟨-, j₁, -, e₁, hvote₁, rfl⟩ := optimisticPoint_pool_voteU hrun hx hpt hv₁ hwH
    obtain ⟨hs₂, j₂, -, e₂, hvote₂, rfl⟩ := hpool v₂ hv₂ (hv₂w ▸ hwH)
    obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hwH j₁ j₂ e₁ e₂ hvote₁
      (hv₂w ▸ hvote₂)
      (by rw [optimisticPoint_pool_slotU hr (fun _ => voteStart_initial _) hx hpt hv₁, hs₂])
    obtain rfl : R₂ = R₁ := hU.1 (hΦ'U hR₂) (hΦxU hR₁) (hR₂r.trans hR₁r.symm)
    exact anc_total hU (Anc.mono hΦ'U hDR₂) (hBD.trans (Anc.mono hΦxU hBR₁))
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard :=
    cover_count (K.committee s) (hsize s) hSX hW hE h34 hf2
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i) V (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (locks_compatibleU hrun K hP hy hc hs hBt (S := SX)
      (fun w hw => by
        rcases hcover hw with ⟨-, x, hx, hxv, hxs, hxa⟩ | h
        · exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩
        · exact Or.inl h)
      (by omega) hf1 hearlier hm)
    fun X' Cx hCx hp hCxC =>
      isBest_of_cover hΦ (merged_support_subsetU hr hy hc (s + 1)) (fun B hB =>
          voteDomain_subset_tree hB.1)
        hcover h3 hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1))) V (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- **A1.4 (a), for the stored block.** A1.4 (a) for a block `B ⪯ D` of an optimistic lock on
`D` (the block the lock stores after moving back): every hypothesis and the conclusion are about
`B`, with the counted votes `CV` of `D`. -/
theorem optimistic_transfer_stored {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize)
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (s + 1) B) : VoteExtends U e.msg B :=
  optimistic_transfer_storedU (FGP := FGP) (ro := ro) (H := H) (U := U) (tr := tr)
      (proposer := proposer) (hrun := hrun.toU) (K := K) (hP := hP) (hT := hT) (hsize := hsize)
      (s := s) (x := x) (y := y)
          (i₀ := i₀) (i := i) (B := B) (D := D) (CV := CV) (ℓ := ℓ) (e := e) (hx := hx)
              (hopt := hopt) (hBD := hBD) (hf := hf) (hf1 := hf1) (hy := hy) (hc := hc)
                  (hs := hs) (hcarry := hcarry) (hviab := hviab) (hearlier := hearlier)

/-- **A1.4 (a).** -/
theorem optimistic_transfer : OptimisticTransfer sp :=
  fun _ _ _ _ _ _ hrun K hP hT hsize _ _ _ _ _ _ _ _ _ hx hopt hf hf1 hy hc hs hcarry hviab
      hearlier =>
    optimistic_transfer_stored sp hrun K hP hT hsize hx hopt .refl hf hf1 hy hc hs hcarry hviab
      hearlier

/-- `first_transfer_stored_of_pool` with the unlock given. -/
theorem first_transfer_stored_of_poolU
    {u : Nat → Set Lock} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRunU wm u proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1)
    (hmerged : ∀ ℓX, UpdateAt tr x i₀ s ℓX →
      ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
        v ∈ (tr.state x i₀).pool s ∨
          v.val ∈ equivocators {w | w ∈ (tr.state x i₀).pool s})
    (hpool : ∀ ℓX, UpdateAt tr x i₀ s ℓX → ∀ k ≤ i,
      ∀ v ∈ (tr.state y (k + 1)).pool s,
        v ∈ (tr.state x i₀).pool s ∨
          v.val ∈ equivocators {w | w ∈ (tr.state x i₀).pool s})
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B) (hearlier : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  -- CS at the slot-`s` committee gives CS2 there
  have hf2 := cs2_of_cs (K.committee s) (H := H)
    (J := {y | y ∈ H ∧ tr.awake y (tr.time i) ∧ JoinedAt tr y (tr.time i)}) (fun _ h => h.1)
    hfault
  have hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize := hsize s ▸ hf2
  rcases hfl with ⟨ℓX, C, hupd, hconf, hfs, rfl⟩ | hopt
  swap
  · exact optimistic_transfer_storedU sp hrun K hP hT hsize hx hopt hBD hf hf1 hy hc hs hcarry
      hviab hearlier
  -- the fast test of `x`'s update: `D` on the result `C`'s path, with half of the committee
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hr hy hc
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hΦxU : ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx i₀ ℓX hupd.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1.2
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_ancU hr (fun _ => voteStart_initial _) hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  obtain ⟨⟨-, -, hBC⟩, -, hfast⟩ := (deepest_mem hfs).1
  set P := tr.state x i₀
  set SX := {w | ∃ v ∈ fastCounted sp P ℓX.frame s D, v.val = w}
  have hd := hmerged ℓX hupd
  have hsupp := counted_supportersU hrun hx hy hupd.1 hc hs hBD hcarry hviab hd
  -- half of the committee are counted for `B`, and a strict majority of `x`'s participants
  have hhalf : sp.committeeSize ≤ 2 * SX.ncard := by
    unfold FastTest confirmationScore at hfast
    refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨hw, v, ⟨hv, hres⟩, hval, -, hanc⟩
    exact ⟨v, ⟨hv, hval ▸ hw, hres, hanc⟩, hval⟩
  have hSX : SX ⊆ K.committee s := by
    rintro w ⟨v, ⟨hv, -⟩, rfl⟩
    exact hP.1 x hx i₀ s v hv
  have hmaj : (voters {v | v ∈ P.pool s}).ncard < 2 * SX.ncard := by
    refine lt_of_lt_of_le (result_majority (C := C) ⟨ℓX, hupd, hconf, rfl⟩)
      (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hCR⟩, hval⟩
    exact ⟨v, ⟨hv, hneq, hres, R, hR, hRr, hBC.trans hCR⟩, hval⟩
  -- an optimistic origin of slot `s` at `y` shares a counted validator, whose single vote at
  -- `x` is also the one `y` counted (forwarding)
  have hm : ∀ (Φ' : Frm sp.n FGP) (A' : SAState sp.n) (D' : Blk sp.n FGP), FrameOK Φ' →
      Φ'.tree ⊆ U → D' ∈ Φ'.tree →
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A' Φ' s D').ncard →
      (∀ v ∈ A'.pool s, v.val ∈ H → v.slot = s ∧
        ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A'.pool s ⊆ (tr.state y (k + 1)).pool s) → Compatible U D' B := by
    rintro Φ' A' D' - hΦ'U - h34' - ⟨k, hk, hsub⟩
    have hO' : optimisticVoters sp A' Φ' s D' ⊆ K.committee s := by
      rintro u ⟨v, hv, rfl, -⟩
      exact hP.1 y hy (k + 1) s v (hsub hv)
    obtain ⟨w, ⟨v₁, ⟨hv₁, hneq, -, R₁, hR₁, hR₁r, hBR₁⟩, rfl⟩, v₂, hv₂, hv₂w, R₂, hR₂, hR₂r,
      hDR₂⟩ := inter_nonempty_of_half_quorum (K.committee s) (hsize s) hSX hO' hf2 hhalf h34'
    obtain rfl : v₂ = v₁ := by
      rcases hpool ℓX hupd k hk v₂ (hsub hv₂) with h | h
      · by_contra hne
        exact hneq ⟨v₂, h, v₁, hv₁, hne, hv₂w, rfl⟩
      · exact absurd (hv₂w ▸ h) hneq
    obtain rfl : R₂ = R₁ := hU.1 (hΦ'U hR₂) (hΦxU hR₁) (hR₂r.trans hR₁r.symm)
    exact anc_total hU (Anc.mono hΦ'U hDR₂) (hBD.trans (Anc.mono hΦxU hBR₁))
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => voteDomain_subset_tree
        hB) hdomA hviab.voteDomain
    (locks_compatibleU hrun K hP hy hc hs hBt (S := SX)
      (fun w hw => by
        obtain ⟨-, x, hx, hxv, hxs, hxa⟩ := hsupp hw
        exact Or.inr ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩)
      hhalf hf1 hearlier hm)
    fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subsetU hr hy hc (s + 1)) (fun B hB =>
          voteDomain_subset_tree hB.1)
        hsupp (merged_voters_subsetU hr (fun _ => voteStart_initial _) hy hc hd) hmaj hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- **A1.2, for the stored block.** A1.2 for a block `B ⪯ D` of a fast lock on `D` (the block
the lock stores after moving back): every hypothesis and the conclusion are about `B`, with the
counted votes `CV` of `D`. -/
theorem first_transfer_stored_of_pool {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1)
    (hmerged : ∀ ℓX, UpdateAt tr x i₀ s ℓX →
      ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
        v ∈ (tr.state x i₀).pool s ∨
          v.val ∈ equivocators {w | w ∈ (tr.state x i₀).pool s})
    (hpool : ∀ ℓX, UpdateAt tr x i₀ s ℓX → ∀ k ≤ i,
      ∀ v ∈ (tr.state y (k + 1)).pool s,
        v ∈ (tr.state x i₀).pool s ∨
          v.val ∈ equivocators {w | w ∈ (tr.state x i₀).pool s})
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B) (hearlier : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B :=
  first_transfer_stored_of_poolU (FGP := FGP) (ro := ro) (H := H) (U := U) (tr := tr)
      (proposer := proposer) (hrun := hrun.toU) (K := K) (hP := hP) (hT := hT) (hsize := hsize)
      (s := s) (x := x) (y := y)
          (i₀ := i₀) (i := i) (B := B) (D := D) (CV := CV) (ℓ := ℓ) (e := e) (hx := hx)
              (hfl := hfl) (hBD := hBD) (hy := hy) (hc := hc) (hs := hs) (hmerged := hmerged)
                  (hpool := hpool) (hcarry := hcarry) (hfault := hfault) (hf1 := hf1)
                      (hviab := hviab) (hearlier := hearlier)

/-- `first_transfer_stored` with the unlock given. -/
theorem first_transfer_storedU
    {u : Nat → Set Lock} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRunU wm u proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B) (hearlier : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B :=
  first_transfer_stored_of_poolU sp hrun K hP hT hsize hx hfl hBD hy hc hs
    (fun _ hu => writer_mergedU hrun hx hu hy hc hs hsync)
    (fun _ hu _ hk => writer_poolU hrun hx hu hy hc hs hsync hk)
    hcarry hfault hf1 hviab hearlier

/-- A1.2 with source-window service supplying the writer pool interfaces. -/
theorem first_transfer_stored {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hfl : FastLockAt tr x i₀ s D CV) (hBD : Anc U B D) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B) (hearlier : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B :=
  first_transfer_storedU (FGP := FGP) (ro := ro) (H := H) (U := U) (tr := tr)
      (proposer := proposer) (hrun := hrun.toU) (K := K) (hP := hP) (hT := hT) (hsize := hsize)
      (s := s) (x := x) (y := y)
          (i₀ := i₀) (i := i) (B := B) (D := D) (CV := CV) (ℓ := ℓ) (e := e) (hx := hx)
              (hfl := hfl) (hBD := hBD) (hy := hy) (hc := hc) (hs := hs) (hsync := hsync)
                  (hcarry := hcarry) (hfault := hfault) (hf1 := hf1) (hviab := hviab)
                      (hearlier := hearlier)

/-- A1.2 on a finite service prefix. The update can occur after the receiving
vote; both pool inclusions use the actual writer's observation cutoff. -/
theorem first_transfer_stored_window_before {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hP : CommitteeP K tr H) (hT : CommitteeT K tr H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {a b : Time} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hfl : FastLockAt tr x i₀ s D CV) (hi₀ : tr.time i₀ ≤ b)
    (hBD : Anc U B D) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtend tr H U i (s + 1) B) : VoteExtends U e.msg B :=
  first_transfer_stored_of_pool sp hrun K hP hT hsize hx hfl hBD hy hc hs
    (fun _ hu => writer_merged_window_before hrun hsync hx ha hu hi₀ hy hc hs)
    (fun _ hu _ hk => writer_pool_window_before hrun hsync hx ha hu hi₀ hy hc hs hk)
    hcarry hfault hf1 hviab hearlier

/-- **A1.2**, over a run with the unlock given. -/
theorem first_transferU (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) (K : CommitteeDict sp.n)
    (hP : CommitteeP K tr H) (hT : CommitteeT K tr H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) (s : Nat) (x y : Fin sp.n)
    (i₀ i : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro))
    (e : Em sp FGP) (hx : x ∈ H) (hfl : FastLockAt tr x i₀ s B CV) (hy : y ∈ H)
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    (hcarry : CarryAt tr U y i e s CV) (hfault : FaultBoundK K s tr H (tr.time i))
    (hf1 : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hviab : ViableAtVote ℓ e (s + 1) B) (hearlier : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B :=
  first_transfer_storedU sp hrun K hP hT hsize hx hfl .refl hy hc hs hsync hcarry hfault hf1
    hviab hearlier

/-- **A1.2.** -/
theorem first_transfer : FirstTransfer sp :=
  fun _ _ _ _ _ _ hrun K hP hT hsize _ _ _ _ _ _ _ _ _ hx hfl hy hc hs hsync hcarry hfault hf1
      hviab hearlier =>
    first_transfer_stored sp hrun K hP hT hsize hx hfl .refl hy hc hs hsync hcarry hfault hf1
      hviab hearlier

end Stock

/-- A block that `ac_to_fg` returns is a candidate. -/
private theorem mem_toFGCandidates {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2 = some C) : C ∈ toFGCandidates sp A Φ t := by
  unfold acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (deepest_mem hC').1

/-- **A1.5.** -/
theorem source_age : SourceAge sp := by
  intro FGP ro H U tr hrun τ x i ℓ C hx hto hslot
  obtain ⟨hc, -, hC⟩ := hto
  obtain ⟨hCv, l, hl, hlb, hlf, hls⟩ := mem_toFGCandidates sp hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨j, hj, B', CV', hfl, L, hL, hLr, hLB'⟩ :=
    fast_lock_provenance hrun hx i l₀ hl₀ hlf
  have hU := hrun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  refine ⟨j, hj.le, l₀.slot, B', CV', hfl, ?_, hls, ?_⟩
  · -- the lock was written in a slot after `τ`'s
    have h1 : sp.slot τ + 1 ≤ l₀.slot := by simp only at hls; omega
    have hτ : τ < sp.ts (l₀.slot : Int) := by
      rcases le_or_gt 0 τ with h0 | h0
      · refine lt_of_lt_of_le (not_le.1 fun h => ?_)
          ((ts_le_iff sp (a := (sp.slot τ : Int) + 1) (b := l₀.slot)).2 (by omega))
        have := ((ts_le_iff_le_slot sp h0) _).1 h
        omega
      · refine lt_of_lt_of_le h0 ?_
        simp only [SAParams.ts]
        have := sp.toParams.hΔ
        positivity
    rcases hfl with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hs, -⟩
    · rw [ht]
      have := sp.toParams.hΔ
      linarith
    · refine lt_of_lt_of_le hτ ?_
      rw [← hs]
      exact ((ts_le_iff_le_slot sp (hrun.time_nonneg j)) _).2 le_rfl
  · -- `C` is the viable ancestor of the lock's block, which is `L`
    have hCt : C ∈ ℓ.frame.tree := hCv.1
    obtain ⟨hvat, hva⟩ := viableAncestor_anc hΦ hB₀
    have hCe : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
    have hLe : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    subst hCe hLe
    exact (Anc.mono hΦU hva).trans hLB'

/-- **A1.8.** -/
theorem result_transfer : ResultTransfer sp := by
  intro FGP ro H U tr proposer hrun s X y i₀ i C CV ℓ e hX hres hy hc hs hcarry hviab hlocks hd
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hrun.localRun hy hc
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc hrun.localRun hy hc
  rw [hs] at hdomA
  have hCt : C ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => voteDomain_subset_tree
        hB) hdomA hviab.voteDomain
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hrun.localRun hy hc (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1)
        (by
          obtain ⟨ℓX, hupd, -, rfl⟩ := hres
          exact counted_supporters hrun hX hy hupd.1 hc hs .refl hcarry hviab hd)
        (merged_voters_subset hrun.localRun (fun _ => voteStart_initial _) hy hc hd)
        (result_majority hres) hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : C = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hCt
  · exact (Anc.mem hcore he).2


end Consensus.Goldilocks.SA

end
