module
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Simulation: the simulating trace

Facts about the canonical trace in `Lemmas/Simulation/TraceDefs`, whose non-exposed
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

/-- The `k`-th post-state of a cut list is the fold of its first `k + 1` cuts. -/
theorem cutPosts_getElem (self : Fin P.n) (t : Time) (cs : List (Cut A)) (st : NodeState A)
    (k : Nat) (hk : k < (cutPosts self t cs st).length) :
    (cutPosts self t cs st)[k] = (cs.take (k + 1)).foldl (cutPost self t) st := by
  induction cs generalizing st k with
  | nil => simp [cutPosts_nil] at hk
  | cons c cs ih =>
    rw [List.getElem_of_eq (cutPosts_cons self t c cs st) hk]
    cases k with
    | zero => simp
    | succ k =>
      rw [cutPosts_cons, List.length_cons] at hk
      rw [List.getElem_cons_succ, ih _ _ (by omega), List.take_succ_cons, List.foldl_cons]

end Node

namespace Simulation
open AsChainShape

open Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The trace's horizon is `awakeAt`'s clamp. -/
theorem simTrace_inHorizon_iff (t : Time) :
    (simTrace S rho hn).InHorizon t ↔
      ∃ k, (cutLabel S rho hn k ≠ none ∨ t ≤ rho.horizon) ∧ t ≤ cutTime S rho hn k := by
  simp [RunTrace.InHorizon, simTrace_label, simTrace_time, simTrace_observationHorizon,
    cutLabel_eq, cutTime_eq]

/-- Every time up to the run's horizon is in the trace's horizon. -/
theorem simTrace_inHorizon_of_le {t : Time} (ht : t ≤ rho.horizon) :
    (simTrace S rho hn).InHorizon t := by
  rw [(simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.inHorizon_of_le (traceEncoding S hn) rho ht

/-- An honest node is awake only within the run's horizon. -/
theorem simTrace_awake_in_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      (simTrace S rho hn).InHorizon t := by
  intro y _ t h
  rw [(simTrace_encoding S rho hn).1] at h ⊢
  exact NodeAsChainShape.CanonicalTrace.awake_in_horizon (traceEncoding S hn) rho h

/-- The cut map is monotone. -/
theorem cutMap_mono : Monotone (cutMap S rho hn) := by
  rw [(simTrace_encoding S rho hn).2]
  exact NodeAsChainShape.CanonicalTrace.cutMap_mono (traceEncoding S hn) rho

/-- A cut at or after event `i`'s first cut and at or before event `i'`'s last cut has `i ≤ i'`. -/
theorem cutMap_index_le {i i' k k' : Nat} (hk : cutMap S rho hn i ≤ k)
    (hk' : k' < cutMap S rho hn (i' + 1)) (h : k ≤ k') : i ≤ i' := by
  rw [(simTrace_encoding S rho hn).2] at hk hk'
  exact NodeAsChainShape.CanonicalTrace.cutMap_index_le (traceEncoding S hn) rho hk hk' h

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A canonical message in a recursive receipt has an actual AC message cut,
even when its vote is already present or rejected by the pool cap. -/
theorem deliverRecs_message_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (m : Vote sp.n) :
    ∀ (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.message m)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ ℓ, r.label = .ac ℓ ∧ ℓ.call = .message m := by
  intro os st sub hm
  obtain ⟨r, hr, l, hl, hm⟩ := NodeAsChainShape.CanonicalTrace.deliverRecs_message_call
    (wireCodec sp ro binding) hs proposer dg self t i m os st sub hm
  obtain ⟨q, hq, hlabel⟩ := deliverRecs_label proposer dg hs self t i os st sub hr
  exact ⟨q, hq, l, hlabel.trans hl, hm⟩

end Simulation
end Consensus.Goldilocks
