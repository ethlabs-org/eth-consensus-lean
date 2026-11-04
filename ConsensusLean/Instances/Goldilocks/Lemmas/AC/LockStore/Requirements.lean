module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: the interface requirements 1–4 (A0.6)

The heads of the duties extend `fc_root` (the anchor does, and the walk only descends) and end in
`viable_heads` when they start in the viable tree of their domain (a walk inside a viable tree
whose domain is closed under ancestors stops only at a viable head: below any other block of it,
the child towards a viable head is eligible, so there is a best child); the block for the FG is a
candidate below the anchor; the confirmed tip is between `Φ.F` and the head; and the parent of a
proposal is the head of `ac_head` at the state the proposal leaves (at a slot start the latest
view is the proposal's view of the previous slot). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- A nonempty set of blocks of the tree has a best block for any score. -/
private theorem exists_isBest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hne : S.Nonempty) (score : Blk sp.n FGP → Nat) :
    ∃ C, IsBest sp score S C := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D, hD, hmax⟩ := hfin.exists_maximalFor score S hne
  obtain ⟨D', ⟨hD'S, hD'd⟩, hmin⟩ :=
    (hfin.subset (Set.sep_subset S fun C => score C = score D)).exists_minimalFor
      Block.root _ ⟨D, hD, rfl⟩
  refine ⟨D', hD'S, fun C hC hne => ?_⟩
  rcases lt_or_ge (score C) (score D') with h | h
  · exact Or.inl h
  have hCd : score C = score D' := le_antisymm (hD'd ▸ hmax hC (hD'd ▸ h)) h
  refine Or.inr ⟨hCd, lt_of_le_of_ne ?_ fun hr => hne (hΦ.coherent.1 (hS hC) (hS hD'S) hr.symm)⟩
  exact le_of_not_gt fun hlt => (hmin ⟨hC, hCd.trans hD'd⟩ hlt.le).not_gt hlt

/-- **A walk inside a viable tree stops at a viable head**, when its domain is closed under
ancestors and the fuel covers the blocks below its start. -/
private theorem ghost_viableHead {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {dom : Set (Blk sp.n FGP)}
    (hdom : dom ⊆ Φ.tree) (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) (t : Time)
    (V : View sp.n) (σ : Int) :
    ∀ (fuel : Nat) (H : Blk sp.n FGP), H ∈ Φ.viableTree dom →
      {X | X ∈ Φ.viableTree dom ∧ Φ.Anc H X ∧ X ≠ H}.ncard ≤ fuel →
      ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ) (goldfishEligible sp Φ t V σ) fuel H ∈
        Φ.viableHeads := by
  have hfin : ∀ H : Blk sp.n FGP, {X | X ∈ Φ.viableTree dom ∧ Φ.Anc H X ∧ X ≠ H}.Finite :=
    fun H => hΦ.finite.subset fun X hX => hdom hX.1.1
  -- below a block of the viable tree that is not a viable head, there is a viable head
  have below : ∀ H, H ∈ Φ.viableTree dom → H ∉ Φ.viableHeads →
      ∃ W ∈ Φ.viableTree dom, Φ.Anc H W ∧ W ≠ H ∧ W ∈ Φ.viableHeads := by
    rintro H ⟨hHd, hfH, W, hWd, hWv, hHW⟩ hnv
    exact ⟨W, ⟨hWd, hfH.trans hHW, W, hWd, hWv, .refl⟩, hHW, fun h => hnv (h ▸ hWv), hWv⟩
  intro fuel
  induction fuel with
  | zero =>
    intro H hH hD
    rw [ghost]
    by_contra hnv
    obtain ⟨W, hW, hHW, hWH, -⟩ := below H hH hnv
    have := (Set.ncard_pos (hfin H)).2 ⟨W, hW, hHW, hWH⟩
    omega
  | succ f ih =>
    intro H hH hD
    rw [ghost]
    split_ifs with hb
    · obtain ⟨⟨hCv, hCp, -⟩, -⟩ := hb.choose_spec
      have hHt : H ∈ Φ.tree := hdom hH.1
      have hHC : Φ.Anc H hb.choose := Relation.ReflTransGen.single ⟨hHt, hdom hCv.1, hCp⟩
      have hCH : hb.choose ≠ H := by
        intro h
        have := hΦ.coherent.2 H hHt hb.choose (hdom hCv.1) hCp
        rw [h] at this
        exact lt_irrefl _ this
      refine ih _ hCv (Nat.le_of_lt_succ (lt_of_lt_of_le ?_ hD))
      refine Set.ncard_lt_ncard ⟨fun X ⟨hX, hCX, hXC⟩ => ⟨hX, hHC.trans hCX, fun hXH => ?_⟩,
        fun hsub => (hsub ⟨hCv, hHC, hCH⟩).2.2 rfl⟩ (hfin H)
      subst hXH
      exact hCH (Anc.antisymm hΦ.coherent hHC hCX).symm
    · by_contra hnv
      obtain ⟨W, ⟨hWd, -, -⟩, hHW, hWH, hWv⟩ := below H hH hnv
      rcases Relation.ReflTransGen.cases_head hHW with h | ⟨c, hHc, hcW⟩
      · exact hWH h.symm
      refine hb (exists_isBest hΦ (S := {B | B ∈ Φ.viableTree dom ∧ B.parent = some H.root ∧
        goldfishEligible sp Φ t V σ B}) (fun B hB => hdom hB.1.1) ⟨c, ?_, hHc.2.2, ?_⟩ _)
      · exact ⟨hdomA W hWd c hcW, hH.2.1.trans (Relation.ReflTransGen.single hHc), W, hWd,
          hWv, hcW⟩
      · refine Or.inl fun ⟨W', hW', hp⟩ => hnv ?_
        have : W' = H := hΦ.coherent.1 (hΦ.viableHeads_subset hW') hHc.1
          (Option.some.inj (hp.symm.trans hHc.2.2))
        exact this ▸ hW'

/-- The finite viable-tree walk reaches a viable head in its domain if its anchor has
a viable descendant there; otherwise it stays at the anchor. -/
theorem ghost_viable_dichotomy {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom)
    {A : Blk sp.n FGP} (hA : A ∈ Φ.tree) (hroot : Φ.Anc Φ.fcRoot A)
    (t : Time) (V : View sp.n) (σ : Int) {fuel : Nat} (hf : Φ.tree.ncard ≤ fuel) :
    let E := ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ)
      (goldfishEligible sp Φ t V σ) fuel A
    ((∃ W ∈ dom, W ∈ Φ.viableHeads ∧ Φ.Anc A W) → E ∈ dom ∧ E ∈ Φ.viableHeads) ∧
    ((¬ ∃ W ∈ dom, W ∈ Φ.viableHeads ∧ Φ.Anc A W) → E = A) := by
  dsimp only
  constructor
  · intro hdesc
    have hAv : A ∈ Φ.viableTree dom := by
      obtain ⟨W, hW, hv, ha⟩ := hdesc
      exact ⟨hdomA W hW A ha, hroot, W, hW, hv, ha⟩
    have hv := ghost_viableHead hΦ hdom hdomA t V σ fuel A hAv
      ((Set.ncard_le_ncard (fun X hX => hdom hX.1.1) hΦ.finite).trans hf)
    refine ⟨?_, hv⟩
    suffices hm : ∀ f B, B ∈ dom → ghost sp (Φ.viableTree dom)
        (goldfishScore sp Φ V σ) (goldfishEligible sp Φ t V σ) f B ∈ dom from
      hm fuel A hAv.1
    intro f
    induction f with
    | zero => exact fun B hB => hB
    | succ f ih =>
      intro B hB
      rw [ghost]
      split_ifs with hb
      · exact ih _ hb.choose_spec.1.1.1
      · exact hB
  · intro hnone
    have hn : ¬ ∃ C, IsBest sp (goldfishScore sp Φ V σ)
        {B | B ∈ Φ.viableTree dom ∧ B.parent = some A.root ∧
          goldfishEligible sp Φ t V σ B} C := by
      rintro ⟨C, ⟨⟨hCd, -, W, hW, hv, hCW⟩, hp, -⟩, -⟩
      exact hnone ⟨W, hW, hv,
        (Relation.ReflTransGen.single ⟨hA, hdom hCd, hp⟩).trans hCW⟩
    cases fuel with
    | zero => rfl
    | succ f => simp only [ghost, dite_eq_right hn]

/-- The same dichotomy for `getHead`, with its frame-cardinality fuel. -/
theorem getHead_viable_dichotomy {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom)
    (A : SAState sp.n) (t : Time) (V : View sp.n) (σ : Int)
    (ha : getAnchor sp A Φ t ∈ Φ.tree) (hroot : Φ.Anc Φ.fcRoot (getAnchor sp A Φ t)) :
    let hasDesc := ∃ W ∈ dom, W ∈ Φ.viableHeads ∧ Φ.Anc (getAnchor sp A Φ t) W
    (hasDesc → getHead sp A Φ t (Φ.viableTree dom) V σ ∈ dom ∧
      getHead sp A Φ t (Φ.viableTree dom) V σ ∈ Φ.viableHeads) ∧
    (¬hasDesc → getHead sp A Φ t (Φ.viableTree dom) V σ = getAnchor sp A Φ t) :=
  ghost_viable_dichotomy hΦ hdom hdomA ha hroot t V σ le_rfl

/-- The walk only descends. -/
private theorem anc_ghost' {Φ : Frm sp.n FGP} {tree : Set (Blk sp.n FGP)} (hT : tree ⊆ Φ.tree)
    {score : Blk sp.n FGP → Nat} {eligible : Blk sp.n FGP → Prop} (fuel : Nat) {a : Blk sp.n FGP}
    (ha : a ∈ Φ.tree) : Φ.Anc a (ghost sp tree score eligible fuel a) := by
  induction fuel generalizing a with
  | zero => exact Relation.ReflTransGen.refl
  | succ f ih =>
    rw [ghost]
    split
    · rename_i h
      have hc := h.choose_spec.1
      exact Relation.ReflTransGen.head ⟨ha, hT hc.1, hc.2.1⟩ (ih (hT hc.1))
    · exact Relation.ReflTransGen.refl

/-- The head of a walk from the anchor over the viable tree of a domain closed under ancestors:
in the tree, above the anchor, and a viable head when the anchor is in that viable tree. -/
private theorem getHead_spec {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {A : SAState sp.n} {t : Time}
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) (V : View sp.n) (σ : Int)
    (ha : getAnchor sp A Φ t ∈ Φ.tree) :
    getHead sp A Φ t (Φ.viableTree dom) V σ ∈ Φ.tree ∧
      Φ.Anc (getAnchor sp A Φ t) (getHead sp A Φ t (Φ.viableTree dom) V σ) ∧
      (getAnchor sp A Φ t ∈ Φ.viableTree dom →
        getHead sp A Φ t (Φ.viableTree dom) V σ ∈ Φ.viableHeads) := by
  have hT : Φ.viableTree dom ⊆ Φ.tree := fun B hB => hdom hB.1
  unfold getHead
  have hanc := anc_ghost' (score := goldfishScore sp Φ V σ)
    (eligible := goldfishEligible sp Φ t V σ) hT Φ.tree.ncard ha
  refine ⟨?_, hanc, fun hav => ghost_viableHead hΦ hdom hdomA t V σ _ _ hav
    (Set.ncard_le_ncard (fun X hX => hT hX.1) hΦ.finite)⟩
  by_cases he : getAnchor sp A Φ t = ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ)
    (goldfishEligible sp Φ t V σ) Φ.tree.ncard (getAnchor sp A Φ t)
  · exact he ▸ ha
  · exact (Anc.mem hanc he).2

/-- **A duty head is good** (requirement 1) when its walk starts at the anchor of a state with
the lock invariant and runs over the viable tree of a domain closed under ancestors. -/
private theorem headOK_of {ro : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)} (hU : Coherent U)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {A : SAState sp.n}
    (h : LockInv U A Φ) {t : Time} {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) (V : View sp.n) (σ : Int) :
    (goldilocksSA sp FGP ro).HeadOK Φ
      ⟨getHead sp A Φ t (Φ.viableTree dom) V σ, getAnchor sp A Φ t, dom⟩ := by
  obtain ⟨ha, hanc⟩ := anc_getAnchor hΦ (h.liveBlocks_chain hU hΦ hΦU (t := t))
  obtain ⟨-, hah, hv⟩ := getHead_spec hΦ hdom hdomA V σ ha
  exact ⟨(hanc Φ.fcRoot (Or.inr rfl)).trans hah, hv⟩

/-- A block that `ac_to_fg` returns is a candidate. -/
theorem toFG_candidate {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2 = some C) : C ∈ toFGCandidates sp A Φ t := by
  unfold acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (deepest_mem hC').1

/-- The voter block tree is closed under ancestors when block stamps grow along parent edges. -/
private theorem voterBlockTree_closed {A : SAState sp.n} {Φ : Frm sp.n FGP}
    (hsp : ∀ B ∈ Φ.tree, ∀ Pa ∈ Φ.tree, B.parent = some Pa.root →
      A.blockStamp Pa.root ≤ A.blockStamp B.root) (s : Nat) :
    ∀ B ∈ voterBlockTree sp A Φ s, ∀ X, Φ.Anc X B → X ∈ voterBlockTree sp A Φ s := by
  intro B hB X hX
  have hle : A.blockStamp X.root ≤ A.blockStamp B.root := by
    clear hB
    induction hX with
    | refl => exact le_rfl
    | tail _ hp ih => exact ih.trans (hsp _ hp.2.1 _ hp.1 hp.2.2)
  exact ⟨mem_of_anc hX hB.1, hB.2.imp hle.trans_lt
    fun ⟨P, hP, hPs, hBP⟩ => ⟨P, hP, hPs, hX.trans hBP⟩⟩

variable (sp)

/-- **A0.6.** -/
theorem interface_requirements : InterfaceRequirements sp := by
  intro FGP ro
  have hall : ∀ (Φ : Frm sp.n FGP), ∀ B ∈ Φ.tree, ∀ X, Φ.Anc X B → X ∈ Φ.tree :=
    fun Φ B hB X hX => mem_of_anc hX hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- requirement 1: the heads of the duties
    intro x U hU A Φ t₀ hr
    obtain ⟨⟨hΦ, hΦU⟩, ht₀, h⟩ := lockInv_of_reachable hU hr
    refine ⟨fun σ _ d p hp => ?_, fun t c Φ' ht hok e he d hd => ?_⟩
    · change (acProposal sp A Φ _).2 = _ at hp
      unfold acProposal at hp
      dsimp only at hp
      split_ifs at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      exact headOK_of hU hΦ hΦU (h.unlock hU hΦ hΦU _ _ _) (fun _ h => h) (hall Φ) _ _
    · obtain ⟨A₁, V, σ, h1, h2, rfl⟩ := (h.callOK hU ⟨hΦ, hΦU⟩ hok).step_emits hU hok.1.1
        hok.1.2 x t (ht₀.trans ht) c e he d hd
      have hsp := stamp_parent sp FGP ro x U hU _ _ _ (ACInterface.ReachableAt.step c hr ht hok)
      beta_reduce at hsp
      rw [← h2] at hsp
      exact headOK_of hU hok.1.1 hok.1.2 h1 (fun B hB => voteDomain_subset_tree hB)
        (voteDomain_anc_closed (voterBlockTree_closed hsp _)) V σ
  · -- requirement 2: the block for the FG
    intro x U hU A Φ t₀ hr t ht C hC
    change (acToFG sp A Φ t).2 = some C at hC
    exact (toFG_candidate hC).1
  · -- requirement 3: the head and the confirmed tip
    intro x U hU A Φ t₀ hr t _
    obtain ⟨⟨hΦ, hΦU⟩, -, h⟩ := lockInv_of_reachable hU hr
    change Φ.Anc Φ.fcRoot (acHead sp A Φ t) ∧ Φ.Anc Φ.F (acConfirmed sp A Φ t) ∧
      Φ.Anc (acConfirmed sp A Φ t) (acHead sp A Φ t)
    obtain ⟨ha, -⟩ := anc_getAnchor hΦ (h.liveBlocks_chain hU hΦ hΦU (t := t))
    have hHt := (getHead_spec hΦ (fun _ h => h) (hall Φ) (latestView sp A Φ t).1
      (latestView sp A Φ t).2 ha).1
    have hOK := (headOK_of (ro := ro) hU hΦ hΦU h (t := t) (fun _ h => h) (hall Φ)
      (latestView sp A Φ t).1 (latestView sp A Φ t).2).1
    refine ⟨hOK, ?_⟩
    unfold acConfirmed
    dsimp only
    rcases hd : deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
        Φ.Anc X (acHead sp A Φ t)} with _ | D
    · exact ⟨.refl, hΦ.rooted.2 _ hHt⟩
    · obtain ⟨⟨hDt, -, hDH⟩, -⟩ := deepest_mem hd
      exact ⟨hΦ.rooted.2 D hDt, hDH⟩
  · -- requirement 4: the parent of a proposal is the head
    intro x U hU A Φ t₀ hr σ _ s' d p hp
    change acProposal sp A Φ (sp.toParams.slotTime σ) = (s', some (d, p)) at hp
    unfold acProposal at hp
    dsimp only at hp
    split_ifs at hp
    swap
    · simp at hp
    simp only [Prod.mk.injEq, Option.some.injEq] at hp
    obtain ⟨rfl, ⟨rfl, -⟩, -⟩ := hp
    change _ = acHead sp _ Φ _
    have hts : sp.toParams.slotTime σ = sp.ts σ := by
      rw [sp.slotTime_eq]; simp [SAParams.ts]
    have hsl : sp.slot (sp.toParams.slotTime σ) = σ := by
      rw [hts]; exact slot_of_mem sp σ le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
    have hlt : ¬ (sp.ts (σ : Int) + 2 * sp.Δ ≤ sp.toParams.slotTime σ) := by
      rw [hts]; have := sp.toParams.hΔ; linarith
    unfold acHead latestView
    simp only [hsl, hlt, ↓reduceIte]
    rfl

end Consensus.Goldilocks.SA

end
