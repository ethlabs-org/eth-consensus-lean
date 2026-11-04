module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Refinement: the simulating trace

Facts about the canonical trace in `Lemmas/Refinement/TraceDefs`, whose non-exposed
definitions have their characterising lemmas beside them. The proof that this trace is a
`GoldilocksRun` and agrees with the engine is split into `Shape`, `Steps`, `Run` and
assembled in `Simulation`. -/

namespace Consensus.Goldilocks

open Blocks

namespace Node

variable {P : Params} {A : NodeAC P}

/-- The cut law's successor is `cutPost`. -/
theorem cutPost_of_cutStep {self : Fin P.n} {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') : cutPost self t st c = st' := by
  rw [cutPost_eq]
  obtain ⟨fg', ac', r'⟩ := st'
  cases c with
  | ac ℓ =>
    obtain ⟨-, e, hfg, hr⟩ := h
    simp only at hfg hr
    subst hfg hr
    simp only [e]
  | fg ℓ =>
    rcases ℓ with ⟨B, acc⟩ | a | ⟨C, signed⟩
    · cases acc with
      | true =>
        obtain ⟨-, e, hac, hr⟩ := h
        simp only at hac hr
        subst hac hr
        simp only [e, Option.getD_some]
      | false =>
        obtain ⟨-, e⟩ := h
        simp only [e]
    · obtain ⟨hfg, hac, hr⟩ := h
      simp only at hfg hac hr
      subst hfg hac hr
      rfl
    · cases signed with
      | none =>
        obtain ⟨-, e⟩ := h
        simp only [e]
      | some a =>
        obtain ⟨e, hfg, hac⟩ := h
        simp only at hfg hac
        subst hfg hac
        simp only [e, Option.map_some, Option.getD_some]

/-- A cut chain ends at the fold of `cutPost` over its cuts. -/
theorem foldl_cutPost_of_cutChain {self : Fin P.n} {t : Time} {st st' : NodeState A}
    {cs : List (Cut A)} (h : CutChain self t st cs st') : cs.foldl (cutPost self t) st = st' := by
  induction h with
  | nil => rfl
  | cons hc _ ih => simp only [List.foldl_cons, cutPost_of_cutStep hc, ih]

/-- The handler's result state is the fold of `cutPost` over its cuts (C0.5). -/
theorem foldl_cutPost_exec (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) :
    (exec proposer dg self st t e).2.foldl (cutPost self t) st = (exec proposer dg self st t e).1 :=
  foldl_cutPost_of_cutChain (Compose.exec_is_cut_chain proposer dg self st t e)

end Node

namespace Refinement

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The trace's horizon is `awakeAt`'s clamp. -/
theorem simTrace_inHorizon_iff (t : Time) :
    (simTrace S rho hn).InHorizon t ↔
      ∃ k, (cutLabel S rho hn k ≠ none ∨ t ≤ rho.horizon) ∧ t ≤ cutTime S rho hn k := by
  simp [RunTrace.InHorizon, simTrace_label, simTrace_time, simTrace_observationHorizon,
    cutLabel_eq, cutTime_eq]

/-- An honest node is awake only within the run's horizon. -/
theorem simTrace_awake_in_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      (simTrace S rho hn).InHorizon t := by
  intro y _ t h
  rw [simTrace_awake_iff, awakeAt_iff] at h
  refine (simTrace_inHorizon_iff S rho hn t).mpr
    ⟨(allCuts S rho hn).length, Or.inr h.2.2, ?_⟩
  simp only [cutTime_eq, List.getElem?_length, Option.elim_none]
  linarith [h.2.2]

/-- An honest node awake in the environment within the horizon is awake in the trace. -/
theorem simTrace_awake_before_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, E.awake (rho.key y) t = true → 0 ≤ t →
      t ≤ rho.horizon → (simTrace S rho hn).awake y t := by
  intro y _ t hw h0 hh
  exact (simTrace_awake_iff S rho hn y t).mpr ((awakeAt_iff S rho hn y t).mpr ⟨hw, h0, hh⟩)

/-- The cut map is monotone. -/
theorem cutMap_mono : Monotone (cutMap S rho hn) :=
  monotone_nat_of_le_succ fun i => by
    rw [cutMap_succ]
    exact Nat.le_add_right _ _

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A canonical message in a recursive receipt has an actual AC message cut,
even when its vote is already present or rejected by the pool cap. -/
theorem deliverRecs_message_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (m : Vote sp.n) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.message m)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ ℓ, r.label = .ac ℓ ∧ ℓ.call = .message m := by
  intro os
  induction os with
  | nil => intro st sub h; simp at h
  | cons o os ih =>
    intro st sub ⟨x, hx, he⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
      simp only [groupRecs_eq, exec, onMessage, acCall, cutPosts_cons, cutPosts_nil]
      simp
    · cases ho : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
        exact ih st (sub + 1) ⟨x, hx, he⟩
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
        obtain ⟨r, hr, ℓ, hl, hm⟩ := ih (exec proposer dg self st t e).1
          (sub + 1) ⟨x, hx, he⟩
        exact ⟨r, List.mem_append_right _ hr, ℓ, hl, hm⟩

end Refinement
end Consensus.Goldilocks
