module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild

public section

/-! # Goldilocks Healing: the canonical walk from the proposal's anchor ends at `P` (H.1 (i))

The proposer's walk from `d.start` has one step per block of its tree, so it stops, at
`d.head = parent(P)`: no child of `d.head` in the proposer's tree is eligible, and `P` is not
in that tree (it would be an eligible child, of the current slot). With `P` added, the walk
takes the same steps up to `d.head` (`P` is a child of `d.head` only), then `P`, the only
eligible child there, and stops (no block of the tree has a slot above `p`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n} {schedule : Nat → Fin sp.n}

/-- The anchor is in the frame tree. -/
private theorem getAnchor_mem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SAState sp.n)
    (t : Time) : getAnchor sp A Φ t ∈ Φ.tree := by
  unfold getAnchor
  cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
  | none => exact hΦ.fcRoot_mem
  | some D =>
    rcases (deepest_mem hd).1 with h | h
    · exact h.1
    · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem

/-- `proposal_walkEnd_core` with the unlock given. -/
theorem proposal_walkEnd_coreU
    {u : Nat → Set Lock} (hs : UnanimitySettingCoreU u tr H U schedule g p P k ℓp d pay) :
    WalkEnd (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) d.start P ∧
      P ∈ U ∧ ℓp.frame.tree ⊆ U ∧ Anc U d.start d.head ∧ Anc U d.head P := by
  have hr := hs.standalone.run.localRun
  have hU := hr.coherent
  have hq := hs.proposer_mem
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hq hs.call
  have hslot : sp.slot (sp.ts p) = p :=
    slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  have hpay := hs.payload
  rw [hs.time] at hpay
  unfold acProposalWith at hpay
  split_ifs at hpay
  simp only [Option.some.injEq, Prod.mk.injEq, hslot] at hpay
  obtain ⟨hd, rfl⟩ := hpay
  set V := View.ofLists (voteViewList (tr.state (schedule p) k) ℓp.frame
    ((p : Int) - 1) ⊤)
  set T := ℓp.frame.viableTree ℓp.frame.tree
  set sc := goldfishScore sp ℓp.frame V ((p : Int) - 1)
  set el := goldfishEligible sp ℓp.frame (sp.ts p) V ((p : Int) - 1)
  have hT : T ⊆ ℓp.frame.tree := fun B hB => hB.1
  have hTU : T ⊆ U := hT.trans hΦU
  have hstart : d.start ∈ ℓp.frame.tree := by rw [← hd]; exact getAnchor_mem hΦ _ _
  have hhead : ghost sp T sc el ℓp.frame.tree.ncard d.start = d.head := by rw [← hd]; rfl
  have hw := walkEnd_ghost (sp := sp) (sc := sc) (el := el) hU hTU (hΦ.finite.subset hT)
    (Set.ncard_le_ncard hT hΦ.finite) d.start
  rw [hhead] at hw
  have hheadU : d.head ∈ U := by
    by_cases he : d.start = d.head
    · exact he ▸ hΦU hstart
    · exact (Anc.mem (hw.anc hTU (hΦU hstart)) he).2
  -- the walk stopped at `d.head`: no child of `d.head` in `T` is eligible
  have hstop : ∀ B ∈ T, B.parent = some d.head.root → ¬ el B := fun B hB hp hel =>
    (walkEnd_iff.1 hw).choose_spec.2 (exists_isBest hΦ (S := eligibleChildren T el d.head)
      (fun C hC => hT hC.1) ⟨B, hB, hp, hel⟩ sc)
  have hPel : el P := Or.inr (Or.inl (by rw [hs.slot, hslot]))
  have hPU : P ∈ U := by
    obtain ⟨j, -, hacc, -⟩ := hs.accepted
    obtain ⟨ℓ₁, hc₁, -⟩ := id hacc
    exact (frameIn_of_callAtU hr hq hc₁).2 ((accept_newU sp hr hq hacc).1 ℓ₁ hc₁)
  -- no block of the tree has a slot above `p`
  have hslot_le : ∀ C ∈ ℓp.frame.tree, C.slot ≤ p := fun C hC => by
    have := frame_slot_leU sp hr hq hs.call C hC
    rw [hs.time, hslot] at this
    exact this
  have hP₂ : WalkEnd (insert P T) sc el d.head P := by
    refine WalkEnd.step (C := P) ⟨⟨Set.mem_insert _ _, hs.parent, hPel⟩, fun D hD hne => ?_⟩
      (walkEnd_self ?_)
    · rcases hD.1 with h | h
      · exact absurd h hne
      · exact absurd hD.2.2 (hstop D h hD.2.1)
    · rintro ⟨C, hC, -⟩
      have hCU : C ∈ U := by
        rcases hC.1 with h | h
        · exact h ▸ hPU
        · exact hTU h
      have := hU.2 P hPU C hCU hC.2.1
      rcases hC.1 with h | h
      · rw [h] at this; omega
      · have := hslot_le C (hT h); have := hs.slot; omega
  refine ⟨hw.congr hU hTU (hΦU hstart) hheadU (fun X hX => ⟨Set.ext fun B => ?_, fun _ _ => rfl⟩)
    hP₂, hPU, hΦU, hw.anc hTU (hΦU hstart),
    Relation.ReflTransGen.single ⟨hheadU, hPU, hs.parent⟩⟩
  refine ⟨fun h => ⟨Set.mem_insert_of_mem _ h.1, h.2⟩, fun h => ⟨h.1.resolve_left ?_, h.2⟩⟩
  rintro rfl
  exact hX (Option.some.inj (h.2.1.symm.trans hs.parent))

/-- **The canonical walk from the proposal's anchor ends at `P`**, through `d.head`. -/
theorem proposal_walkEnd_core (hs : UnanimitySettingCore tr H U schedule g p P k ℓp d pay) :
    WalkEnd (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) d.start P ∧
      P ∈ U ∧ ℓp.frame.tree ⊆ U ∧ Anc U d.start d.head ∧ Anc U d.head P :=
  proposal_walkEnd_coreU (hs := hs.toU)

/-! ## In the setting of unanimity -/

/-- `proposal_walkEnd_core` in the setting of unanimity. -/
theorem proposal_walkEnd (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) :
    WalkEnd (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) d.start P ∧
      P ∈ U ∧ ℓp.frame.tree ⊆ U ∧ Anc U d.start d.head ∧ Anc U d.head P :=
  proposal_walkEnd_core hs.toCore

end Consensus.Goldilocks.SA

end
