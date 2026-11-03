module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

/-! # Goldilocks Healing: H.2's canonical walk in a general frame

The proposal walk stops at its returned parent head. Settled locks bound its anchor, and a
reader below the proposer root reaches that root before branching. Walk comparison transfers
winning children only on the shared ancestral suffix.
-/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- The unextended proposal walk stops at its returned parent head. -/
theorem h2_parent_walkEnd {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (acProposal sp A Φ t).2 = some (d, pay)) :
    d.start ∈ Φ.tree ∧ Φ.Anc Φ.fcRoot d.start ∧
      WalkEnd (Φ.viableTree Φ.tree) (goldfishScore sp Φ (View.ofLists pay)
        ((sp.slot t : Int) - 1))
        (goldfishEligible sp Φ t (View.ofLists pay) ((sp.slot t : Int) - 1)) d.start d.head := by
  unfold acProposal at hpay
  split_ifs at hpay
  simp only [Option.some.injEq, Prod.mk.injEq] at hpay
  obtain ⟨rfl, rfl⟩ := hpay
  have hfa := fcRoot_anc_getAnchor hΦ
    { A with locks := (unlock sp A.locks Φ t ((sp.slot t : Int) - 1)
      (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))) } t
  refine ⟨?_, hfa, ?_⟩
  · rcases Relation.ReflTransGen.cases_tail hfa with he | ⟨B, _, hB⟩
    · exact he.symm ▸ hΦ.fcRoot_mem
    · exact hB.2.1
  · exact walkEnd_ghost hΦ.coherent (fun _ h => h.1)
      (hΦ.finite.subset (fun _ h => h.1))
      (Set.ncard_le_ncard (fun _ h => h.1) hΦ.finite) _

/-- A proposal anchor is the frame root, or every honest vote of the proposal's slot extends
it. Settled older locks suffice; normalization and unlocking only move their blocks back. -/
theorem h2_proposal_anchor (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {p k : Nat}
    (hpH : proposer p ∈ H) {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt (proposer p) k ℓ) (ht : tr.time k = sp.ts p)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (acProposal sp (tr.state (proposer p) k) ℓ.frame (tr.time k)).2 =
      some (d, pay))
    (hbelow : ∀ l ∈ (tr.state (proposer p) k).locks, l.slot < p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    d.start = ℓ.frame.fcRoot ∨
      ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = p → VoteExtends U e.msg d.start := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hpH hc
  have hΔ := sp.toParams.hΔ
  have hslot : sp.slot (tr.time k) = p := by
    rw [ht]; exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  unfold acProposal at hpay
  split_ifs at hpay
  simp only [Option.some.injEq, Prod.mk.injEq, hslot] at hpay
  obtain ⟨hd, -⟩ := hpay
  suffices h : ∀ (A : SAState sp.n) (V : View sp.n),
      A.locks = unlock sp (tr.state (proposer p) k).locks ℓ.frame (tr.time k)
        ((p : Int) - 1) V →
      getAnchor sp A ℓ.frame (tr.time k) = ℓ.frame.fcRoot ∨
        ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = p →
          VoteExtends U e.msg (getAnchor sp A ℓ.frame (tr.time k)) by
    rw [← hd]; exact h _ _ rfl
  intro A V hA
  unfold getAnchor
  cases hD : deepest ℓ.frame (liveLockBlocks sp A.locks ℓ.frame (tr.time k) ∪
      {ℓ.frame.fcRoot}) with
  | none => exact Or.inl rfl
  | some D =>
    simp only [Option.getD_some]
    rcases (deepest_mem hD).1 with hDlock | hDroot
    swap
    · exact Or.inl (Set.mem_singleton_iff.1 hDroot)
    right
    obtain ⟨hDt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hDr⟩ := hDlock
    obtain rfl : D = ℓ.frame.viableAncestor B :=
      hΦ.coherent.1 hDt (mem_of_anc (anc_viableAncestor ℓ.frame B) hB) hDr.symm
    rw [hA] at hl
    replace hlive : sp.slot (tr.time k) ≤ l.slot + sp.k :=
      hlive.trans (((locksWF_state hr hpH k).unlock _ _ _ _).cap hl)
    obtain ⟨l₀, hl₀, hslots, -, -, B₀, hB₀, hB₀r, B', hB', hB'r, hBB₀⟩ :=
      ((locks_move_back sp) FGP ℓ.frame (tr.state (proposer p) k).locks
        (tr.time k) hΦ).2.2 _ _ l hl
    obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
    obtain ⟨hvotes, -⟩ := locksSettled_iff.1 hset _ hpH k (by rw [ht]; linarith)
      l₀ hl₀ (by rw [← hslots]; exact hlive) B₀ (hΦU hB₀) hB₀r
    intro x hx i e hv hes
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hvotes x hx i e hv
      (by rw [hes]; exact hbelow l₀ hl₀)
    exact ⟨Hd, hHd, hHdr,
      (Anc.mono hΦU ((anc_viableAncestor ℓ.frame B').trans hBB₀)).trans hBHd⟩

/-- If all viable witnesses extend `R`, a walk starting below `R` must reach it. Before `R`
there is only one viable child and its parent is not a viable head, so scores are irrelevant. -/
theorem h2_walk_reaches_root {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hclosed : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ Φ.tree → X ∈ dom)
    {R a : Blk sp.n FGP} (hR : R ∈ Φ.viableTree dom) (haR : Φ.Anc a R)
    (hfa : Φ.Anc Φ.fcRoot a)
    (hwitness : ∀ W ∈ dom, W ∈ Φ.viableHeads → Φ.Anc R W)
    (V : View sp.n) (t : Time) (σ : Int) :
    Φ.Anc R (ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ)
      (goldfishEligible sp Φ t V σ) Φ.tree.ncard a) := by
  have hT : Φ.viableTree dom ⊆ Φ.tree := fun _ h => hdom h.1
  refine anc_ghost_of_best hΦ.coherent hT (hΦ.finite.subset hT) (hdom hR.1) _ haR
    (Set.ncard_le_ncard (fun X hX => hT hX.1) hΦ.finite) fun X haX hXR hne => ?_
  obtain rfl | ⟨C, hXC, hCR⟩ := Relation.ReflTransGen.cases_head_iff.1 hXR
  · exact absurd rfl hne
  have hCv : C ∈ Φ.viableTree dom :=
    ⟨hclosed R hR.1 C hCR hXC.2.1, (hfa.trans haX).tail hXC,
      hR.2.2.choose, hR.2.2.choose_spec.1, hR.2.2.choose_spec.2.1,
      hCR.trans hR.2.2.choose_spec.2.2⟩
  have hXdom : X ∈ dom := hclosed R hR.1 X hXR hXC.1
  have hel : goldfishEligible sp Φ t V σ C := by
    left
    rintro ⟨W, hW, hCW⟩
    obtain rfl : W = X := hΦ.coherent.1 (hΦ.viableHeads_subset hW) hXC.1
      (Option.some.inj (hCW.symm.trans hXC.2.2))
    exact hne (Anc.antisymm hΦ.coherent hXR (hwitness W hXdom hW))
  refine ⟨C, ⟨⟨hCv, hXC.2.2, hel⟩, ?_⟩, hCR⟩
  rintro D ⟨hD, hDX, -⟩ hDC
  obtain ⟨W, hW, hWv, hDW⟩ := hD.2.2
  have hDR : Φ.Anc D R := by
    rcases anc_total hΦ.coherent hDW (hwitness W hW hWv) with h | h
    · exact h
    · rcases Relation.ReflTransGen.cases_tail h with he | ⟨Z, hRZ, hZD⟩
      · exact he ▸ .refl
      · obtain rfl : Z = X := hΦ.coherent.1 hZD.1 hXC.1
          (Option.some.inj (hZD.2.2.symm.trans hDX))
        exact False.elim (hne (Anc.antisymm hΦ.coherent hXR hRZ))
  have hnot : ∀ Y Z, Φ.Anc Y Z → Z.parent = some X.root →
      X.slot < Y.slot → Y = Z := by
    intro Y Z hYZ hZX hlt
    rcases Relation.ReflTransGen.cases_tail hYZ with he | ⟨Q, hYQ, hQZ⟩
    · exact he.symm
    · obtain rfl : Q = X := hΦ.coherent.1 hQZ.1 hXC.1
        (Option.some.inj (hQZ.2.2.symm.trans hZX))
      have := (Anc.slot_le hΦ.coherent hYQ).1
      omega
  rcases anc_total hΦ.coherent hCR hDR with h | h
  · exact False.elim (hDC (hnot C D h hDX (hΦ.coherent.2 X hXC.1 C hXC.2.1 hXC.2.2)).symm)
  · exact False.elim (hDC (hnot D C h hXC.2.2 (hΦ.coherent.2 X hXC.1 D (hT hD) hDX)))

/-- Transferring the winner along the traversed interval suffices; extra eligible competitors
in the reader's frame need not be eligible in the proposer's frame. -/
theorem h2_walk_transfer {T T' : Set (Blk sp.n FGP)} {sc sc' : Blk sp.n FGP → Nat}
    {el el' : Blk sp.n FGP → Prop} {a E E' : Blk sp.n FGP}
    (hT : T ⊆ U) (ha : a ∈ U) (hw : WalkEnd (sp := sp) T sc el a E)
    (hstep : ∀ X, Anc U a X → Anc U X E → X ≠ E →
      ∀ C, IsBest sp sc (eligibleChildren T el X) C →
        IsBest sp sc' (eligibleChildren T' el' X) C)
    (hend : WalkEnd (sp := sp) T' sc' el' E E') :
    WalkEnd (sp := sp) T' sc' el' a E' := by
  obtain ⟨f, hf, hs⟩ := walkEnd_iff.1 hw
  clear hw
  induction f generalizing a with
  | zero =>
    change a = E at hf
    exact hf ▸ hend
  | succ f ih =>
    by_cases he : a = E
    · exact he ▸ hend
    have haE : Anc U a E := hf ▸ anc_ghost hT (f + 1) ha
    rw [ghost] at hf
    split at hf
    · rename_i hb
      have hC := hb.choose_spec
      have haC : Anc U a hb.choose := .single ⟨ha, hT hC.1.1, hC.1.2.1⟩
      exact (ih (hT hC.1.1) (fun X hCX hXE hne C hbest =>
        hstep X (haC.trans hCX) hXE hne C hbest) hf).step (hstep a .refl haE he _ hC)
    · exact False.elim (he hf)

end Consensus.Goldilocks.SA

end
