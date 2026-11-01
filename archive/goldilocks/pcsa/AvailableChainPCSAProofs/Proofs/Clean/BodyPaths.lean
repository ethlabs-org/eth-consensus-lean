module
public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt

public section

/-! C6 BodyPaths: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private theorem body_prefix_parent (B C : Block) (h : Block.Preceq C B) :
    C = B ∨ Block.Preceq C B.parent := by
  cases B with
  | genesis => exact Or.inl (of_decide_eq_true h)
  | node P s r v =>
    change (decide (C = .node P s r v) || Block.preceq C P) = true at h
    rcases Bool.or_eq_true_iff.mp h with he | hp
    · exact Or.inl (of_decide_eq_true he)
    · exact Or.inr hp
/-- Every reachable body pool contains all prefixes of its bodies. -/
theorem pcsa_body_prefix_mem (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ B ∈ st.base.blocks, ∀ C, Block.Preceq C B → C ∈ st.base.blocks := by
  induction h with
  | init =>
    intro B hB C hC
    have hB' : B = .genesis := List.mem_singleton.mp hB
    subst B
    have hC' : C = .genesis := of_decide_eq_true hC
    subst C
    exact List.mem_singleton_self _
  | tick t h ih =>
    rw [pcsa_clock_blocks]
    exact ih
  | @deliver st o h ih =>
    intro B hB C hC
    have htree := pcsa_tree_correspondence p st h
    have hpred := pcsa_c3_process_body_pred p
      (fun B => ∀ C, Block.Preceq C B → C = B ∨ C ∈ st.base.blocks) st o
      (fun B hB C hC => Or.inr (ih B hB C hC)) (by
        intro s N P _ hp _ C hC
        rcases body_prefix_parent N.erase C hC with he | hparent
        · exact Or.inl he
        · have hlook := FGSA.pickPair_some_spec st.fg.TF _ hp
          have hm : N.erase.parent ∈ st.base.blocks :=
            (htree _).mpr ⟨P, hlook.1, of_decide_eq_true hlook.2⟩
          exact Or.inr (ih _ hm C hparent)) B hB C hC
    rcases hpred with rfl | hm
    · exact hB
    · exact pcsa_body_process_keep p st o h hm
/-- A vacuous frame retains every member of any supplied block subset. -/
theorem pcsa_frame_subset_of_frame (p : Params) (st : State p.n)
    (blocks : Finset (SimplexFG.FGBlock (Fin p.n))) (h : Run.FrameVacuous p st) :
    KitFG.storeFrameView (FGSA.heightView p) st.fg blocks = blocks := by
  apply Finset.ext
  intro B
  rw [KitFG.storeFrameView_def]
  change B ∈ KitFG.filteredFromView (FGSA.heightView p) (controls p st) blocks ↔ B ∈ blocks
  rw [KitFG.mem_filteredFromView]
  constructor
  · exact fun hb => hb.1
  · intro hb
    have hF : (controls p st).F = .genesis := h.1
    rw [hF, h.2.1, h.2.2]
    exact ⟨hb, KitFG.genesis_preceq B, KitFG.genesis_preceq B,
      B, hb, KitFG.preceq_refl B, Nat.zero_le _⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem paths_clock_frame (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (u : Time) :
    FrameVacuous p (clock p (V2.D.Run.stateBefore E rho k x).st u) := by
  change (clock p _ u).fg.F = .genesis ∧
    (KitFG.storeControlsView (FGSA.heightView p) (clock p _ u).fg).Z = .genesis ∧
    (KitFG.storeControlsView (FGSA.heightView p) (clock p _ u).fg).lo = 0
  rw [pcsa_body_clock_fg]
  exact hF x hx k
/-- Every prefix of a held body is in the full stage-1 walk tree. -/
theorem pcsa_full_read_prefix_mem (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (u : Time) (B C : Block)
    (hB : B ∈ (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blocks)
    (hC : Block.Preceq C B) :
    C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k x).st u)
      (fullTree p (clock p (V2.D.Run.stateBefore E rho k x).st u)) := by
  have hreach := Reachable.tick u (pcsa_reachable_stateBefore E rho k x)
  have hm := pcsa_body_prefix_mem p _ hreach B hB C hC
  obtain ⟨D, hD, he⟩ := (pcsa_tree_correspondence p _ hreach C).mp hm
  apply List.mem_filter.mpr
  refine ⟨hm, decide_eq_true ?_⟩
  rw [pcsa_fullTree_of_frame p _ (paths_clock_frame E rho hF k x hx u)]
  exact ⟨D, hD, he⟩
/-- A pre-freeze body retains every prefix in the later voter walk tree. -/
theorem pcsa_frozen_read_prefix_mem (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (a k : Nat) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (u : Time) (B C : Block)
    (ha : a ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) (hak : a ≤ k)
    (hB : B ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks)
    (hC : Block.Preceq C B) :
    C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k x).st u)
      (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho k x).st u).fg
        (voterBlocks p (clock p (V2.D.Run.stateBefore E rho k x).st u) (s + 1))) := by
  have hm := pcsa_body_prefix_mem p _ (pcsa_reachable_stateBefore E rho a x) B hB C hC
  have hlate := pcsa_body_stateBefore_mono E rho h.noRestart x hak hm
  have hclock : C ∈ (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blocks := by
    rw [pcsa_clock_blocks]
    exact hlate
  have hstamp : GridCO.stampBlock (V2.D.Run.stateBefore E rho a x).st.base C <
      SA.freezeTime p.toParams s := by
    by_cases hg : C = .genesis
    · subst C
      rw [(pcsa_genesis_body_stamp E rho h.noRestart a x).2]
      have hp := p.deltaPos
      change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
      positivity
    · exact pcsa_body_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
        a x C _ ha hg hm
  obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho a x C hm
  have hp : (V2.D.Run.stateBefore E rho a x).st.base.blockStamp <+:
      (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blockStamp := by
    rw [pcsa_clock_bodyStamps]
    exact pcsa_bodyStamps_stateBefore_prefix E rho h.noRestart x hak
  have hs := pcsa_stampBlock_eq_of_prefix _ _ C row hp hr
  have hreach := Reachable.tick u (pcsa_reachable_stateBefore E rho k x)
  obtain ⟨D, hD, he⟩ := (pcsa_tree_correspondence p _ hreach C).mp hclock
  apply List.mem_filter.mpr
  refine ⟨hclock, decide_eq_true ?_⟩
  rw [pcsa_frame_subset_of_frame p _ _ (paths_clock_frame E rho hF k x hx u)]
  refine ⟨D, Finset.mem_filter.mpr ⟨hD, ?_⟩, he⟩
  apply Bool.or_eq_true_iff.mpr
  left
  apply decide_eq_true
  rw [he, Nat.add_sub_cancel, hs]
  exact hstamp
end AvailableChain.PCSA.Run

end
