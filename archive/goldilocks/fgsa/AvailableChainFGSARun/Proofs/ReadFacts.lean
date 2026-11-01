module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.Head.Walk -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- Strict event cuts are below inclusive event cuts. -/
theorem idxBefore_le_timeIdx (rho : V2.D.Run V (fgsa p c)) (t : Time) :
    V2.D.Run.idxBefore rho t ≤ (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  rw [V2.D.Run.idxBefore_def]
  exact (List.monotone_filter_right _
    (fun e h => decide_eq_true (le_of_lt (of_decide_eq_true h)))).length_le

omit [DecidableEq V] in
/-- Strict event cuts preserve time order. -/
theorem fgsa_idxBefore_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le hab))

/-- A named immutable parent equals the parent field. -/
theorem fgsa_parent_eq_of_some {C X : Block} (hp : C.parent? = some X) : C.parent = X := by
  cases C with
  | genesis => cases hp
  | node P s root r => exact Option.some.inj hp

/-- A child extends the parent named by its immutable field. -/
theorem fgsa_parent_preceq_of_some {C X : Block} (hp : C.parent? = some X) :
    Block.Preceq X C := by
  cases C with
  | genesis => cases hp
  | node P s root r =>
    cases Option.some.inj hp
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

/-- Every block extends its parent. -/
theorem fgsa_parent_preceq (b : Block) : Block.Preceq b.parent b := by
  cases b with
  | genesis => exact block_preceq_refl _
  | node P s root r => exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

/-- The active floor Z extends the finalized root. -/
theorem fgsa_F_preceq_Z (p : Params) (st : State p.n) (h : CStoreInv p st) :
    FGBlock.Preceq st.fg.F (controls p st).Z := by
  unfold Controls.Z
  split
  · exact h.fg.FJ
  · exact KitFG.preceq_refl _

/-- A label's HEAD duty is before its gate. -/
theorem fgsa_vote_lt_gate (p : Params) (s : Slot) :
    SA.voteTime p.toParams s < SA.gateTime p.toParams s := by
  change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith [p.deltaPos]

theorem fgsa_clock_block_stamp
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (y : V)
    (t : Time) (B : Block) (hm : B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks) :
    GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho k y).st t).base B =
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base B := by
  rw [← (metaInv_stateBefore E rho k y).stampKeys] at hm
  obtain ⟨⟨b, u⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  unfold GridCO.stampBlock
  rw [(clock_cumulative p _ _).2.2.1]
  cases hf : (V2.D.Run.stateBefore E rho k y).st.base.blockStamp.find?
      (fun row => row.1 == B) with
  | none =>
    have hn := List.find?_eq_none.mp hf (B, u) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

end AvailableChain.FGSA.Run
end
