module
public import ConsensusShape.Run
public import ConsensusModelProofs.Canonical.Unforgeable
@[expose] public section
namespace Consensus.Shape
open Model
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}
namespace Run
variable (rho : Model.Run (compiled F) E)

omit [Nonempty V] in
/-- Every item candidate is a proposal carrying the post-clock mempool. -/
theorem candidate_payload (st : (compile (protoOf F E)).State) (v : V) (t : Time)
    {h : Header} {a cs}
    (ho : (Model.Obj.mk a (.item h) cs) ∈ rho.candidates st v t) :
    h.input = encodeTxs st.2 := by
  unfold Model.Run.candidates at ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp ho
    cases d with
    | inl d =>
      simp only [Model.protoOf, compiled, compile] at hd
      cases ha : (protoOf F E).act st.1 d with
      | none => simp only [ha, Option.map_none] at hd; cases hd
      | some mc =>
        simp only [ha, Option.map_some] at hd
        obtain ⟨i, _, he⟩ := List.mem_map.mp hd
        cases he
    | inr s =>
      simp only [Model.protoOf, compiled, compile] at hd
      cases ha : (protoOf F E).propose st.1 s.val with
      | none => simp only [ha, Option.map_none] at hd; cases hd
      | some mc =>
        simp only [ha, Option.map_some] at hd
        obtain ⟨i, _, he⟩ := List.mem_map.mp hd
        cases he
        rfl
  · obtain ⟨bc, _, he⟩ := List.mem_map.mp ho
    cases he

/-- Release filtering cannot change a proposal payload. In particular, restarting
before the tick does not affect the cumulative input supplied by the clock. -/
theorem honestProposal_payload {s h} (hp : HonestProposal rho s h) :
    h.input = encodeTxs (Model.mempool rho.submit (proposerOf rho s)
      ((protoOf F E).proposalTime s)) := by
  obtain ⟨_, _, cs, i, hi, ho⟩ := hp
  simp only [Model.Run.releasesAt, hi] at ho
  unfold Model.Run.tick at ho
  split at ho
  · have hc := Model.releaseAll_subset _ _ _ _ ho
    exact candidate_payload rho _ _ _ hc
  · simp at ho
omit [DecidableEq V] [Nonempty V] in
theorem submitted_mem_mempool {x : Tx} {v : V} {t p : Time}
    (hv : v ∈ rho.honest) (hs : rho.point.SubmittedToAll x t) (htp : t ≤ p) :
    x ∈ Model.mempool rho.submit v p := by
  obtain ⟨τ, hτ, hτt, hx⟩ := hs v hv
  have hτp : τ ≤ p := le_trans hτt htp
  have hp : 0 ≤ p := le_trans hτ hτp
  rw [Model.mempool, ite_eq_right (not_lt.mpr hp)]
  apply List.mem_flatMap.mpr
  refine ⟨τ, ?_, hx⟩
  rw [List.bind_eq_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨τ.toNat, List.mem_range.mpr ?_, ?_⟩
  · have := Int.toNat_le_toNat hτp
    omega
  · change τ ∈ [(τ.toNat : Int)]
    simp [Int.toNat_of_nonneg hτ]

end Run
end Consensus.Shape
end
