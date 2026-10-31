module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
@[expose] public section

/-! # The tick run of a one-validator node (generic part of the Goldilocks witness)

For any node AC `A` with `n = 1` and `Δ = 1`, the run in which the validator ticks at every time
`t ≥ 0` and nothing else happens (`tickRun`), its states, groups and cut law, and that it is a
`Node.LocalRun` (`tickRun_localRun`); the shape of a tick's cuts; the attestation pool and (for the
Goldilocks SA) the vote pool lemmas. Used by `ConsensusLeanTest/GoldilocksWitness` (consensus-lean
#69); see its docstring. -/

namespace Consensus.Goldilocks.Witness

open Node

variable {P : Params} (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)

/-- The validator `0`. -/
def v0 : Fin P.n := ⟨0, P.hn⟩

/-- The node state before the tick of time `t`. -/
noncomputable def tickState : Nat → NodeState A
  | 0 => Node.init A
  | t + 1 => (exec (fun _ => v0) dg v0 (tickState t) (t : Int) (.tick 0)).1

/-- The cuts of the tick of time `t`. -/
noncomputable def tickCuts (t : Nat) : List (Cut A) :=
  (exec (fun _ => v0) dg v0 (tickState A dg t) (t : Int) (.tick 0)).2

/-- The node state after the first `k` cuts of the tick of time `t`. -/
noncomputable def tickMid (t k : Nat) : NodeState A :=
  ((tickCuts A dg t).take k).foldl (cutPost v0 (t : Int)) (tickState A dg t)

/-- The tick run. -/
noncomputable def tickRun : RunTrace A where
  init _ := Node.init A
  node _ := v0
  time i := ((i / 8 : Nat) : Int)
  event i := if i % 8 < (tickCuts A dg (i / 8)).length then 2 * (i / 8) else 2 * i + 1
  pos i := i % 8
  label i := (tickCuts A dg (i / 8))[i % 8]?
  post i := tickMid A dg (i / 8) (i % 8 + 1)
  awake _ t := 0 ≤ t

/-! ## The cuts of a tick -/

/-- An `attest` step makes at most two cuts. -/
theorem attest_length (self : Fin P.n) (st : NodeState A) (C : A.Blk) :
    (attest self st C).2.length ≤ 2 := by
  simp only [attest]
  split <;> simp [onAttestation]

/-- An `on_block` makes at most two cuts. -/
theorem onBlock_length (self : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    (onBlock self st t B).2.length ≤ 2 := by
  simp only [onBlock]
  split_ifs
  · simp
  · split <;> simp

/-- A tick makes at most seven cuts. -/
theorem onTick_length (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    (onTick (fun _ => v0) dg self st t x).2.length ≤ 7 := by
  have h1 : ∀ st', (tickStep (fun _ => v0) dg self st' t x .acTick).2.length = 1 := fun _ => rfl
  have h2 : ∀ st', (tickStep (fun _ => v0) dg self st' t x .proposal).2.length ≤ 3 := by
    intro st'
    simp only [tickStep]
    split_ifs
    · split
      · simp
      · simp only [proposeBlock, List.length_cons]
        exact le_trans (Nat.add_le_add_right (onBlock_length A _ _ _ _) 1) (by norm_num)
    · simp
  have h3 : ∀ st', (tickStep (fun _ => v0) dg self st' t x .fgUpdate).2.length ≤ 3 := by
    intro st'
    simp only [tickStep]
    split
    · simp
    · simp only [List.length_cons]
      exact le_trans (Nat.add_le_add_right (attest_length A _ _ _) 1) (by norm_num)
  simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil, List.nil_append,
    List.length_append]
  have := h1 st
  have := h2 (tickStep (fun _ => v0) dg self st t x .acTick).1
  have := h3 (tickStep (fun _ => v0) dg self
    (tickStep (fun _ => v0) dg self st t x .acTick).1 t x .proposal).1
  omega

theorem tickCuts_length (t : Nat) : (tickCuts A dg t).length ≤ 7 :=
  onTick_length A dg v0 _ _ 0

/-- The first cut of a tick is its `ac_on_tick`. -/
theorem tickCuts_head (t : Nat) :
    (tickCuts A dg t)[0]? = some (acCall v0 (tickState A dg t) (t : Int) .tick).2 := by
  simp [tickCuts, exec, onTick, runSteps, tickSteps, tickStep]

theorem tickCuts_ne_nil (t : Nat) : tickCuts A dg t ≠ [] := by
  intro h
  have := tickCuts_head A dg t
  rw [h] at this
  simp at this

/-! ## What a tick's cuts are -/

/-- The AC calls of a tick: `ac_on_tick`, `ac_proposal`, the own block's `ac_on_block`,
`ac_to_fg`. -/
theorem onTick_ac_call (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {ℓ : ACLabel A}
    (hm : Cut.ac ℓ ∈ (onTick (fun _ => v0) dg self st t x).2) :
    ℓ.call = .tick ∨ ℓ.call = .proposal ∨ (∃ B, ℓ.call = .block B) ∨ ℓ.call = .toFG := by
  rw [Healing.onTick_eq] at hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · simp only [tickStep, acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm; exact Or.inl rfl
  · simp only [tickStep] at hm
    split_ifs at hm
    · split at hm
      · simp only [acProposal, List.mem_singleton, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.1 hm with hm | hm
        · simp only [acProposal, Cut.ac.injEq] at hm
          subst hm; exact Or.inr (Or.inl rfl)
        · simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp at hm
          · split at hm
            · simp at hm
            · simp only [acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
                List.not_mem_nil, or_false] at hm
              subst hm; exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp only [acToFG, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm; exact Or.inr (Or.inr (Or.inr rfl))
    · rcases List.mem_cons.1 hm with hm | hm
      · simp only [acToFG, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inr (Or.inr rfl))
      · simp only [attest] at hm
        split at hm <;> simp [onAttestation] at hm

/-- The FG-relevant shape of a tick's cuts: the `ac_on_tick` cut, the proposal step's cuts (no
signing and no attestation cut; an own block carries attestations of the pool at the tick's
start), the `ac_to_fg` cut, then nothing, a silent `attest`, or a signing `attest` followed by its
`on_attestation`. -/
theorem onTick_shape (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    ∃ L2 ct L3, (onTick (fun _ => v0) dg self st t x).2 =
      (acCall self st t .tick).2 :: (L2 ++ ct :: L3) ∧
      L2 = (tickStep (fun _ => v0) dg self (acCall self st t .tick).1 t x .proposal).2 ∧
      (∃ ℓ : ACLabel A, ct = Cut.ac ℓ ∧ ℓ.call = .toFG) ∧
      (∀ c ∈ L2, (∀ a, c ≠ .fg (.attestation a)) ∧ (∀ C sa, c ≠ .fg (.attest C sa)) ∧
        ∀ B acc, c = .fg (.block B acc) → ∀ a ∈ B.fgPayload, a ∈ st.fg.atts) ∧
      (L3 = [] ∨ (∃ C, L3 = [.fg (.attest C none)]) ∨
        ∃ C a, L3 = [.fg (.attest C (some a)), .fg (.attestation a)]) := by
  have h0 : (tickStep (fun _ => v0) dg self st t x .acTick).2 =
      [(acCall self st t .tick).2] := rfl
  -- the proposal step
  have h2 : ∀ st' : NodeState A, st'.fg = st.fg →
      ∀ c ∈ (tickStep (fun _ => v0) dg self st' t x .proposal).2,
      (∀ a, c ≠ .fg (.attestation a)) ∧ (∀ C sa, c ≠ .fg (.attest C sa)) ∧
        ∀ B acc, c = .fg (.block B acc) → ∀ a ∈ B.fgPayload, a ∈ st.fg.atts := by
    intro st' hfg c hc
    simp only [tickStep] at hc
    split_ifs at hc
    · split at hc
      · simp only [acProposal, List.mem_singleton] at hc
        subst hc
        exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => by cases h⟩
      · rcases List.mem_cons.1 hc with hc | hc
        · subst hc
          exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => by cases h⟩
        · simp only [proposeBlock, onBlock] at hc
          split_ifs at hc
          · simp at hc
          · split at hc
            · simp only [List.mem_singleton] at hc
              subst hc
              refine ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun B acc h a ha => ?_⟩
              simp only [Cut.fg.injEq, FGLabel.block.injEq] at h
              obtain ⟨rfl, -⟩ := h
              simp only [mkBlock, Store.proposalAttestations, List.mem_filter] at ha
              simpa [acProposal, hfg] using ha.1
            · simp only [acCall, List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with hc | hc
              · subst hc
                refine ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun B acc h a ha => ?_⟩
                simp only [Cut.fg.injEq, FGLabel.block.injEq] at h
                obtain ⟨rfl, -⟩ := h
                simp only [mkBlock, Store.proposalAttestations, List.mem_filter] at ha
                simpa [acProposal, hfg] using ha.1
              · subst hc
                exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => by cases h⟩
    · simp at hc
  -- the FG update
  have h3 : ∀ st' : NodeState A, ∃ ct L3,
      (tickStep (fun _ => v0) dg self st' t x .fgUpdate).2 = ct :: L3 ∧
      (∃ ℓ : ACLabel A, ct = Cut.ac ℓ ∧ ℓ.call = .toFG) ∧ (L3 = [] ∨
        (∃ C, L3 = [.fg (.attest C none)]) ∨
        ∃ C a, L3 = [.fg (.attest C (some a)), .fg (.attestation a)]) := by
    intro st'
    simp only [tickStep]
    split
    · exact ⟨_, [], rfl, ⟨_, rfl, rfl⟩, Or.inl rfl⟩
    · refine ⟨_, _, rfl, ⟨_, rfl, rfl⟩, ?_⟩
      simp only [attest]
      split
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  obtain ⟨ct, L3, h3e, hct, hL3⟩ :=
    h3 (tickStep (fun _ => v0) dg self
      (tickStep (fun _ => v0) dg self st t x .acTick).1 t x .proposal).1
  refine ⟨(tickStep (fun _ => v0) dg self
    (tickStep (fun _ => v0) dg self st t x .acTick).1 t x .proposal).2, ct, L3, ?_, rfl,
    hct, h2 _ rfl, hL3⟩
  rw [Healing.onTick_eq, h0, h3e]
  rfl

/-- In a tick's cuts, an FG cut is not the first. -/
theorem onTick_fg_pos (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {k : Nat}
    {ℓ : FGLabel P A.Payload}
    (hk : (onTick (fun _ => v0) dg self st t x).2[k]? = some (.fg ℓ)) : 1 ≤ k := by
  obtain ⟨L2, ct, L3, he, -⟩ := onTick_shape A dg self st t x
  rw [he] at hk
  rcases k with _ | k
  · simp [acCall] at hk
  · omega

/-- In a tick's cuts, an `on_attestation(a)` cut directly follows the `attest` cut that signs
`a`. -/
theorem onTick_att_pos (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {k : Nat}
    {a : FG.Att P.n}
    (hk : (onTick (fun _ => v0) dg self st t x).2[k]? = some (.fg (.attestation a))) :
    ∃ k' C, k = k' + 1 ∧
      (onTick (fun _ => v0) dg self st t x).2[k']? = some (.fg (.attest C (some a))) := by
  obtain ⟨L2, ct, L3, he, -, ⟨ℓ, rfl, -⟩, hL2, hL3⟩ := onTick_shape A dg self st t x
  rw [he] at hk ⊢
  rcases k with _ | k
  · simp [acCall] at hk
  rw [List.getElem?_cons_succ] at hk
  by_cases hlt : k < L2.length
  · rw [List.getElem?_append_left hlt] at hk
    exact absurd rfl ((hL2 _ (List.mem_of_getElem? hk)).1 a)
  rw [List.getElem?_append_right (by omega)] at hk
  obtain ⟨m, rfl⟩ : ∃ m, k = L2.length + m := ⟨k - L2.length, by omega⟩
  rw [Nat.add_sub_cancel_left] at hk
  rcases m with _ | _ | _ | m
  · simp at hk
  · rcases hL3 with rfl | ⟨C, rfl⟩ | ⟨C, a', rfl⟩ <;> simp at hk
  · rcases hL3 with rfl | ⟨C, rfl⟩ | ⟨C, a', rfl⟩
    · simp at hk
    · simp at hk
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Cut.fg.injEq, FGLabel.attestation.injEq] at hk
      subst hk
      refine ⟨L2.length + 2, C, rfl, ?_⟩
      rw [List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
      simp
  · rcases hL3 with rfl | ⟨C, rfl⟩ | ⟨C, a', rfl⟩ <;> simp at hk

/-- An own block of a tick carries attestations of the pool at the tick's start. -/
theorem onTick_block_payload (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {k : Nat}
    {B : A.Blk} {acc : Bool}
    (hk : (onTick (fun _ => v0) dg self st t x).2[k]? = some (.fg (.block B acc))) :
    ∀ a ∈ B.fgPayload, a ∈ st.fg.atts := by
  obtain ⟨L2, ct, L3, he, -, ⟨ℓ, rfl, -⟩, hL2, hL3⟩ := onTick_shape A dg self st t x
  rw [he] at hk
  rcases k with _ | k
  · simp [acCall] at hk
  rw [List.getElem?_cons_succ] at hk
  by_cases hlt : k < L2.length
  · rw [List.getElem?_append_left hlt] at hk
    exact (hL2 _ (List.mem_of_getElem? hk)).2.2 B acc rfl
  rw [List.getElem?_append_right (by omega)] at hk
  have hm := List.mem_of_getElem? hk
  rcases List.mem_cons.1 hm with hm | hm
  · cases hm
  · rcases hL3 with rfl | ⟨C, rfl⟩ | ⟨C, a', rfl⟩ <;> simp at hm

/-- An own block of the tick of time `t` carries attestations of the pool at its start. -/
theorem onBlock_tick_payload_aux (t k : Nat) {B : A.Blk} {acc : Bool}
    (hk : (tickCuts A dg t)[k]? = some (.fg (.block B acc))) :
    ∀ a ∈ B.fgPayload, a ∈ (tickState A dg t).fg.atts :=
  onTick_block_payload A dg v0 _ _ 0 hk

/-- A block named by a cut of a tick (its FG `on_block` or its `ac_on_block`) is the tick's own
proposal, made from `ac_proposal`'s result on the state after `ac_on_tick`. -/
theorem onTick_block_made (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {c : Cut A}
    (hc : c ∈ (onTick (fun _ => v0) dg self st t x).2) {B : A.Blk}
    (hB : (∃ acc, c = .fg (.block B acc)) ∨ ∃ ℓ : ACLabel A, c = .ac ℓ ∧ ℓ.call = .block B) :
    ∃ d p, (Node.acProposal (acCall self st t .tick).1 t).2.2 = some (d, p) ∧
      B = mkBlock dg self (Node.acProposal (acCall self st t .tick).1 t).1.fg t x d.head p := by
  obtain ⟨L2, ct, L3, he, hL2e, ⟨ℓt, rfl, hℓt⟩, -, hL3⟩ := onTick_shape A dg self st t x
  rw [he] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exfalso
    rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
    · simp [acCall] at h
    · simp only [acCall, Cut.ac.injEq] at h
      subst h; cases hcall
  rcases List.mem_append.1 hc with hc | hc
  · rw [hL2e] at hc
    simp only [tickStep] at hc
    split_ifs at hc
    · split at hc
      · exfalso
        simp only [Node.acProposal, List.mem_singleton] at hc
        subst hc
        rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
        · cases h
        · simp only [Cut.ac.injEq] at h; subst h; cases hcall
      · rename_i d p hr
        refine ⟨d, p, hr, ?_⟩
        rcases List.mem_cons.1 hc with hc | hc
        · exfalso
          subst hc
          rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
          · simp [Node.acProposal] at h
          · simp only [Node.acProposal, Cut.ac.injEq] at h; subst h; cases hcall
        · simp only [proposeBlock, onBlock] at hc
          split_ifs at hc
          · simp at hc
          · split at hc
            · simp only [List.mem_singleton] at hc
              subst hc
              rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
              · simp only [Cut.fg.injEq, FGLabel.block.injEq] at h; exact h.1.symm
              · cases h
            · simp only [acCall, List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl
              · rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
                · simp only [Cut.fg.injEq, FGLabel.block.injEq] at h; exact h.1.symm
                · cases h
              · rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
                · cases h
                · simp only [Cut.ac.injEq] at h; subst h
                  simp only [ACInterface.Call.block.injEq] at hcall; exact hcall.symm
    · simp at hc
  · exfalso
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩
      · cases h
      · simp only [Cut.ac.injEq] at h; subst h; rw [hℓt] at hcall; cases hcall
    · rcases hL3 with rfl | ⟨C, rfl⟩ | ⟨C, a', rfl⟩ <;>
        rcases hB with ⟨acc, h⟩ | ⟨ℓ, h, hcall⟩ <;> simp_all

/-- In a tick's cuts, a signing `attest` cut is directly followed by its `on_attestation`. -/
theorem onTick_sign_next (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {k : Nat}
    {C : A.Blk} {a : FG.Att P.n}
    (hk : (onTick (fun _ => v0) dg self st t x).2[k]? = some (.fg (.attest C (some a)))) :
    (onTick (fun _ => v0) dg self st t x).2[k + 1]? = some (.fg (.attestation a)) := by
  obtain ⟨L2, ct, L3, he, -, ⟨ℓ, rfl, -⟩, hL2, hL3⟩ := onTick_shape A dg self st t x
  rw [he] at hk ⊢
  rcases k with _ | k
  · simp [acCall] at hk
  rw [List.getElem?_cons_succ] at hk
  rw [List.getElem?_cons_succ]
  by_cases hlt : k < L2.length
  · rw [List.getElem?_append_left hlt] at hk
    exact absurd rfl ((hL2 _ (List.mem_of_getElem? hk)).2.1 C (some a))
  rw [List.getElem?_append_right (by omega)] at hk
  rw [List.getElem?_append_right (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, k = L2.length + m := ⟨k - L2.length, by omega⟩
  rw [Nat.add_sub_cancel_left] at hk
  rw [show L2.length + m + 1 - L2.length = m + 1 by omega]
  rcases m with _ | _ | m
  · simp at hk
  · rcases hL3 with rfl | ⟨C', rfl⟩ | ⟨C', a', rfl⟩
    · simp at hk
    · simp at hk
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Cut.fg.injEq, FGLabel.attest.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      simp
  · rcases hL3 with rfl | ⟨C', rfl⟩ | ⟨C', a', rfl⟩ <;> (rcases m with _ | m <;> simp at hk)

/-! ## The post-states -/

/-- The fold over all the cuts of a tick is the next tick's state. -/
theorem foldl_tickCuts (t : Nat) :
    (tickCuts A dg t).foldl (cutPost v0 (t : Int)) (tickState A dg t) = tickState A dg (t + 1) :=
  foldl_cutPost_exec (fun _ => v0) dg v0 _ _ _

/-- After all the cuts of a tick, the next tick's state. -/
theorem tickMid_of_le {t k : Nat} (hk : (tickCuts A dg t).length ≤ k) :
    tickMid A dg t k = tickState A dg (t + 1) := by
  unfold tickMid
  rw [List.take_of_length_le hk, foldl_tickCuts]

theorem tickMid_zero (t : Nat) : tickMid A dg t 0 = tickState A dg t := rfl

/-! ## The attestation pool -/

theorem onAttestation_atts {ACP : Type} (st : Store P ACP) (a a' : FG.Att P.n)
    (h : a' ∈ (st.onAttestation a).atts) : a' ∈ st.atts ∨ a' = a := by
  unfold Store.onAttestation at h
  split_ifs at h
  · exact Or.inl h
  · simpa using h

theorem addAtts_atts {ACP : Type} : ∀ (l : List (FG.Att P.n)) (st : Store P ACP) (a' : FG.Att P.n),
    a' ∈ (st.addAtts l).atts → a' ∈ st.atts ∨ a' ∈ l
  | [], st, a', h => Or.inl h
  | a :: l, st, a', h => by
    simp only [Store.addAtts, List.foldl_cons] at h
    rcases addAtts_atts l _ a' h with h | h
    · rcases onAttestation_atts st a a' h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem updateFinality_atts {ACP : Type} (st : Store P ACP) (σ : FG.ChainState P.n) :
    (st.updateFinality σ).atts = st.atts := by
  unfold Store.updateFinality
  dsimp only
  split <;> (try split_ifs) <;> split <;> (try split_ifs) <;> rfl

theorem onBlock_atts {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock B = some st') (a : FG.Att P.n) (ha : a ∈ st'.atts) :
    a ∈ st.atts ∨ a ∈ B.fgPayload := by
  unfold Store.onBlock at h
  split at h
  · cases h
  · split_ifs at h
    split at h
    · cases h
    · cases h
      rcases addAtts_atts _ _ a ha with h | h
      · erw [updateFinality_atts] at h
        exact Or.inl h
      · exact Or.inr h

/-- An attestation enters the pool only from an accepted block or an `on_attestation` cut. -/
theorem cutStep_atts {self : Fin P.n} {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') (a : FG.Att P.n) (ha : a ∈ st'.fg.atts) :
    a ∈ st.fg.atts ∨ (∃ B, c = .fg (.block B true) ∧ a ∈ B.fgPayload) ∨
      c = .fg (.attestation a) := by
  match c, h with
  | .ac ℓ, h => exact Or.inl (h.2.2.1 ▸ ha)
  | .fg (.block B true), h =>
    rcases onBlock_atts h.2.1 a ha with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨B, rfl, h'⟩)
  | .fg (.block B false), h => exact Or.inl (h.2 ▸ ha)
  | .fg (.attestation a'), h =>
    rw [h.1] at ha
    rcases onAttestation_atts _ a' a ha with h' | rfl
    · exact Or.inl h'
    · exact Or.inr (Or.inr rfl)
  | .fg (.attest C none), h => exact Or.inl (h.2 ▸ ha)
  | .fg (.attest C (some a')), h => exact Or.inl (h.2.1 ▸ ha)

/-! ## The SA's vote pool -/

namespace SAPool

open SA

variable (sp : SAParams) {FGP : Type}

theorem updateLatestConfirmed_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (C : Blk sp.n FGP) :
    (updateLatestConfirmed sp A Φ C).pool = A.pool := by
  unfold updateLatestConfirmed; split_ifs <;> rfl

theorem optimisticConfirmation_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation
  split
  · rfl
  · rw [updateLatestConfirmed_pool]

theorem updateConfirmation_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).pool = A.pool := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs
    · rfl
    · change (updateLatestConfirmed sp _ Φ _).pool = A.pool
      rw [updateLatestConfirmed_pool]

theorem admitVote_pool (A : SAState sp.n) (t : Time) (v : Vote sp.n) (σ : Nat) (w : Vote sp.n)
    (h : w ∈ (admitVote sp A t v).pool σ) : w ∈ A.pool σ ∨ w = v := by
  unfold admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hσ
    · rcases List.mem_append.1 h with h | h
      · exact Or.inl (hσ ▸ h)
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl h

theorem blockReceipt_pool (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) (σ : Nat)
    (w : Vote sp.n) (h : w ∈ (blockReceipt sp A t B).pool σ) : w ∈ A.pool σ ∨ w ∈ blockVotes B := by
  unfold blockReceipt at h
  have key : ∀ (l : List (Vote sp.n)) (A' : SAState sp.n),
      w ∈ (l.foldl (fun A v => admitVote sp A t v) A').pool σ → w ∈ A'.pool σ ∨ w ∈ l := by
    intro l
    induction l with
    | nil => exact fun A' h => Or.inl h
    | cons v l ih =>
      intro A' h
      rcases ih _ h with h | h
      · rcases admitVote_pool sp A' t v σ w h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases key _ _ h with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem tryVote_pool (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (σ : Nat)
    (w : Vote sp.n) (h : w ∈ (tryVote sp self A Φ t).1.pool σ) :
    w ∈ A.pool σ ∨ ∃ e ∈ (tryVote sp self A Φ t).2, e.msg = w := by
  unfold tryVote at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with h₁ h₂
  · exact Or.inl h
  · exact Or.inl h
  all_goals
    rw [optimisticConfirmation_pool] at h
    rcases admitVote_pool sp _ t _ σ w h with h | rfl
    · exact Or.inl h
    · exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩

theorem acOnTick_pool (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (σ : Nat) (w : Vote sp.n) (h : w ∈ (acOnTick sp self A Φ t).1.pool σ) :
    w ∈ A.pool σ ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg = w := by
  unfold acOnTick at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> (try simp only at h ⊢) <;> first
    | exact Or.inl h
    | exact tryVote_pool sp self A Φ t σ w h
    | (rw [updateConfirmation_pool] at h; first
        | exact Or.inl h
        | exact tryVote_pool sp self A Φ t σ w h)

theorem acProposal_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (SA.acProposal sp A Φ t).1.pool = A.pool := by
  unfold SA.acProposal; split_ifs <;> rfl

theorem acToFG_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (SA.acToFG sp A Φ t).1.pool = A.pool := by
  unfold SA.acToFG
  dsimp only
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

theorem acOnBlock_pool (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) (σ : Nat) (w : Vote sp.n) (h : w ∈ (acOnBlock sp self A Φ t B).1.pool σ) :
    w ∈ A.pool σ ∨ w ∈ blockVotes B ∨ ∃ e ∈ (acOnBlock sp self A Φ t B).2, e.msg = w := by
  unfold acOnBlock at h ⊢
  rcases tryVote_pool sp self _ Φ t σ w h with h | h
  · rw [optimisticConfirmation_pool] at h
    rcases blockReceipt_pool sp A t B σ w h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem admitVote_pool_mono (A : SAState sp.n) (t : Time) (v : Vote sp.n) (σ : Nat) :
    A.pool σ ⊆ (admitVote sp A t v).pool σ := by
  intro w hw
  unfold admitVote
  split_ifs
  · exact hw
  · exact hw
  · simp only [Function.update_apply]
    split_ifs with hσ
    · subst hσ; exact List.mem_append_left _ hw
    · exact hw

theorem blockReceipt_pool_mono (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) (σ : Nat) :
    A.pool σ ⊆ (blockReceipt sp A t B).pool σ := by
  unfold blockReceipt
  have key : ∀ (l : List (Vote sp.n)) (A' : SAState sp.n),
      A'.pool σ ⊆ (l.foldl (fun A v => admitVote sp A t v) A').pool σ := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons v l ih => exact fun A' => List.Subset.trans (admitVote_pool_mono sp A' t v σ) (ih _)
  exact fun w hw => key _ _ hw

theorem tryVote_pool_mono (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (σ : Nat) : A.pool σ ⊆ (tryVote sp self A Φ t).1.pool σ := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact fun _ h => h
  · exact fun _ h => h
  all_goals
    rw [optimisticConfirmation_pool]
    exact fun w hw => admitVote_pool_mono sp _ t _ σ hw

theorem acOnTick_pool_mono (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (σ : Nat) : A.pool σ ⊆ (acOnTick sp self A Φ t).1.pool σ := by
  unfold acOnTick
  dsimp only
  split_ifs <;> (try simp only) <;> first
    | exact fun _ h => h
    | exact tryVote_pool_mono sp self A Φ t σ
    | (rw [updateConfirmation_pool]; exact tryVote_pool_mono sp self A Φ t σ)
    | rw [updateConfirmation_pool]

theorem acOnBlock_pool_mono (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) (σ : Nat) : A.pool σ ⊆ (acOnBlock sp self A Φ t B).1.pool σ := by
  unfold acOnBlock
  refine List.Subset.trans (blockReceipt_pool_mono sp A t B σ) ?_
  rw [← optimisticConfirmation_pool sp _ Φ t]
  exact tryVote_pool_mono sp self _ Φ t σ

/-- Pool `σ` holds votes of slot `σ`. -/
def SlotOK (A : SAState sp.n) : Prop := ∀ σ, ∀ w ∈ A.pool σ, w.slot = σ

theorem admitVote_slot (A : SAState sp.n) (t : Time) (v : Vote sp.n) (h : SlotOK sp A) :
    SlotOK sp (admitVote sp A t v) := by
  intro σ w hw
  unfold admitVote at hw
  split_ifs at hw
  · exact h σ w hw
  · exact h σ w hw
  · simp only [Function.update_apply] at hw
    split_ifs at hw with hσ
    · rcases List.mem_append.1 hw with hw | hw
      · exact h σ w (hσ ▸ hw)
      · rw [List.mem_singleton.1 hw, hσ]
    · exact h σ w hw

theorem slot_of_pool_eq {A A' : SAState sp.n} (he : A'.pool = A.pool) (h : SlotOK sp A) :
    SlotOK sp A' := fun σ w hw => h σ w (he ▸ hw)

theorem blockReceipt_slot (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) (h : SlotOK sp A) :
    SlotOK sp (blockReceipt sp A t B) := by
  unfold blockReceipt
  have key : ∀ (l : List (Vote sp.n)) (A' : SAState sp.n), SlotOK sp A' →
      SlotOK sp (l.foldl (fun A v => admitVote sp A t v) A') := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons v l ih => exact fun A' h => ih _ (admitVote_slot sp A' t v h)
  exact key _ _ (fun σ w hw => h σ w hw)

theorem tryVote_slot (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (h : SlotOK sp A) : SlotOK sp (tryVote sp self A Φ t).1 := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact h
  · exact h
  all_goals
    refine slot_of_pool_eq sp (optimisticConfirmation_pool sp _ Φ t) ?_
    exact admitVote_slot sp _ t _ (fun σ w hw => h σ w hw)

theorem acOnTick_slot (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (h : SlotOK sp A) : SlotOK sp (acOnTick sp self A Φ t).1 := by
  unfold acOnTick
  dsimp only
  split_ifs <;> (try simp only) <;> first
    | exact h
    | exact tryVote_slot sp self A Φ t h
    | exact slot_of_pool_eq sp (updateConfirmation_pool sp _ Φ t _) (tryVote_slot sp self A Φ t h)
    | exact slot_of_pool_eq sp (updateConfirmation_pool sp _ Φ t _) h

theorem acOnBlock_slot (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) (h : SlotOK sp A) : SlotOK sp (acOnBlock sp self A Φ t B).1 := by
  unfold acOnBlock
  exact tryVote_slot sp self _ Φ t (slot_of_pool_eq sp (optimisticConfirmation_pool sp _ Φ t)
    (blockReceipt_slot sp A t B h))

end SAPool

/-! ## The tick run: indices, states, groups -/

section Run

variable {A dg}

theorem tickRun_time (i : Nat) : (tickRun A dg).time i = ((i / 8 : Nat) : Int) := rfl

theorem tickRun_label (i : Nat) : (tickRun A dg).label i = (tickCuts A dg (i / 8))[i % 8]? := rfl

theorem tickRun_node (i : Nat) : (tickRun A dg).node i = v0 := rfl

/-- With one validator, every validator is `v0`. -/
theorem eq_v0 (h1 : P.n = 1) (y : Fin P.n) : y = v0 := Fin.ext (by have := y.isLt; simp [v0]; omega)

/-- The state before cut `i` is the state after the first `i mod 8` cuts of the tick of time
`⌊i/8⌋`. -/
theorem tickRun_state (h1 : P.n = 1) (y : Fin P.n) :
    ∀ i, (tickRun A dg).state y i = tickMid A dg (i / 8) (i % 8)
  | 0 => rfl
  | i + 1 => by
    have ih := tickRun_state h1 y i
    have hy := eq_v0 h1 y
    have hlen := tickCuts_length A dg (i / 8)
    simp only [Trace.state]
    by_cases h7 : i % 8 = 7
    · have hq : (i + 1) / 8 = i / 8 + 1 := by omega
      have hr : (i + 1) % 8 = 0 := by omega
      have hl : (tickRun A dg).label i = none := by
        rw [tickRun_label, h7]; exact List.getElem?_eq_none (by omega)
      have hn : ¬ ((tickRun A dg).node i = y ∧ (tickRun A dg).label i ≠ none) := fun h => h.2 hl
      simp only [hn, ↓reduceIte]
      rw [ih, hq, hr, tickMid_zero, h7, tickMid_of_le A dg (by omega)]
    · have hq : (i + 1) / 8 = i / 8 := by omega
      have hr : (i + 1) % 8 = i % 8 + 1 := by omega
      rw [hq, hr]
      split_ifs with h
      · rfl
      · rw [ih]
        have hl : (tickCuts A dg (i / 8)).length ≤ i % 8 := by
          by_contra hc
          have hlt : i % 8 < (tickCuts A dg (i / 8)).length := by omega
          exact h ⟨hy.symm, by rw [tickRun_label, List.getElem?_eq_getElem hlt]; simp⟩
        rw [tickMid_of_le A dg hl, tickMid_of_le A dg (by omega)]

theorem tickRun_state_tick (h1 : P.n = 1) (y : Fin P.n) (t : Nat) :
    (tickRun A dg).state y (8 * t) = tickState A dg t := by
  rw [tickRun_state h1, show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]; rfl

/-- The tick of time `t` is a group at cut `8t`. -/
theorem tickRun_groupAt (h1 : P.n = 1) (t : Nat) :
    (tickRun A dg).GroupAt (fun _ => v0) dg v0 (8 * t) (t : Int) (.tick 0) := by
  have hcs : (exec (fun _ => v0) dg v0
      ((tickRun A dg).state v0 (8 * t)) (t : Int) (.tick 0)).2 =
      tickCuts A dg t := by rw [tickRun_state_tick h1]; rfl
  have hlen := tickCuts_length A dg t
  have hpos := List.length_pos_of_ne_nil (tickCuts_ne_nil A dg t)
  have hev : (tickRun A dg).event (8 * t) = 2 * t := by
    change (if 8 * t % 8 < (tickCuts A dg (8 * t / 8)).length then 2 * (8 * t / 8)
      else 2 * (8 * t) + 1) = _
    rw [show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]
    simp only [hpos, ↓reduceIte]
  refine ⟨by rw [hcs]; exact tickCuts_ne_nil A dg t, fun k hk0 => ?_, fun i hi => ?_⟩
  · have hk : k < (tickCuts A dg t).length := hcs ▸ hk0
    have hq : (8 * t + k) / 8 = t := by omega
    have hr : (8 * t + k) % 8 = k := by omega
    refine ⟨rfl, by rw [tickRun_time, hq], ?_, hr, ?_⟩
    · rw [hev]
      change (if (8 * t + k) % 8 < (tickCuts A dg ((8 * t + k) / 8)).length then
        2 * ((8 * t + k) / 8) else 2 * (8 * t + k) + 1) = _
      rw [hq, hr]
      simp only [hk, ↓reduceIte]
    · rw [tickRun_label, hq, hr, List.getElem_of_eq hcs hk0]
      exact List.getElem?_eq_getElem hk
  · rw [hev] at hi
    change (if i % 8 < (tickCuts A dg (i / 8)).length then 2 * (i / 8) else 2 * i + 1) =
      2 * t at hi
    rw [hcs]
    split_ifs at hi with h
    · have : i / 8 = t := by omega
      subst this
      omega
    · omega

/-- An event whose first cut is an `ac_on_tick` is a tick. -/
theorem exec_head_tick (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) {ℓ : ACLabel A}
    (hh : (exec (fun _ => v0) dg y st t e).2.head? = some (.ac ℓ))
    (hc : ℓ.call = .tick) : ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | block B =>
    exfalso
    simp only [exec, onBlock] at hh
    split_ifs at hh
    · simp at hh
    · split at hh <;> simp at hh
  | message m =>
    exfalso
    simp only [exec, onMessage, acCall, List.head?_cons, Option.some.injEq, Cut.ac.injEq] at hh
    subst hh; cases hc
  | attestation a => simp [exec, onAttestation] at hh
  | restart =>
    exfalso
    simp only [exec, restart, acCall, List.head?_cons, Option.some.injEq, Cut.ac.injEq] at hh
    subst hh; cases hc

/-- A group of the tick run is a tick, at a cut `8t'` and time `t'`. -/
theorem tickRun_groupAt_inv {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (h : (tickRun A dg).GroupAt (fun _ => v0) dg y j t e) :
    j % 8 = 0 ∧ t = ((j / 8 : Nat) : Int) ∧ ∃ x, e = .tick x := by
  obtain ⟨hne, hk, hev⟩ := h
  have hlen : 0 < (exec (fun _ => v0) dg y ((tickRun A dg).state y j) t e).2.length :=
    List.length_pos_of_ne_nil hne
  obtain ⟨-, ht, -, -, hl⟩ := hk 0 hlen
  rw [Nat.add_zero] at hl ht
  have hlab : j % 8 < (tickCuts A dg (j / 8)).length := by
    by_contra hc
    rw [tickRun_label, List.getElem?_eq_none (by omega)] at hl
    cases hl
  have hpos := List.length_pos_of_ne_nil (tickCuts_ne_nil A dg (j / 8))
  have hevj : (tickRun A dg).event j = 2 * (j / 8) := by
    change (if j % 8 < (tickCuts A dg (j / 8)).length then 2 * (j / 8) else 2 * j + 1) = _
    simp only [hlab, ↓reduceIte]
  have hev0 : (tickRun A dg).event (8 * (j / 8)) = 2 * (j / 8) := by
    change (if 8 * (j / 8) % 8 < (tickCuts A dg (8 * (j / 8) / 8)).length then
      2 * (8 * (j / 8) / 8) else 2 * (8 * (j / 8)) + 1) = _
    rw [show 8 * (j / 8) / 8 = j / 8 by omega, show 8 * (j / 8) % 8 = 0 by omega]
    simp only [hpos, ↓reduceIte]
  have hj := (hev (8 * (j / 8)) (hev0.trans hevj.symm)).1
  have hmod : j % 8 = 0 := by omega
  refine ⟨hmod, ht.symm, ?_⟩
  rw [tickRun_label, hmod, tickCuts_head] at hl
  have hh : (exec (fun _ => v0) dg y ((tickRun A dg).state y j) t e).2.head? =
      some (acCall v0 (tickState A dg (j / 8)) ((j / 8 : Nat) : Int) .tick).2 := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen, ← hl]
  exact exec_head_tick y _ t e (ℓ := ⟨.tick, _, _⟩) hh rfl

/-- The cut law along a cut chain, cut by cut. -/
theorem chain_step {self : Fin P.n} {t : Time} {st st' : NodeState A} {cs : List (Cut A)}
    (h : CutChain self t st cs st') : ∀ k (hk : k < cs.length),
      CutStep self t ((cs.take k).foldl (cutPost self t) st) cs[k]
        ((cs.take (k + 1)).foldl (cutPost self t) st) := by
  induction h with
  | nil => intro k hk; simp at hk
  | @cons st st₁ st' c cs hs _ ih =>
    intro k hk
    cases k with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero, List.take_succ_cons,
        List.foldl_cons, cutPost_of_cutStep hs]
      exact hs
    | succ k =>
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ,
        cutPost_of_cutStep hs]
      exact ih k (by simpa using hk)

/-- A labelled cut of the tick run is a cut of the tick of time `⌊i/8⌋`. -/
theorem tickRun_label_mem {i : Nat} {c : Cut A} (h : (tickRun A dg).label i = some c) :
    c ∈ tickCuts A dg (i / 8) := List.mem_of_getElem? h

/-- No restart in the tick run. -/
theorem tickRun_no_restart (y : Fin P.n) (k : Nat) : ¬ (tickRun A dg).RestartAt y k := by
  rintro ⟨ℓ, hc, hr⟩
  rcases onTick_ac_call A dg _ _ _ _ (tickRun_label_mem hc.2) with h | h | ⟨B, h⟩ | h <;>
    rw [h] at hr <;> cases hr

/-- No AC message call in the tick run. -/
theorem tickRun_no_msg (y : Fin P.n) (k : Nat) (m : A.Msg) : ¬ (tickRun A dg).MsgCallAt y k m := by
  rintro ⟨ℓ, hc, hr⟩
  rcases onTick_ac_call A dg _ _ _ _ (tickRun_label_mem hc.2) with h | h | ⟨B, h⟩ | h <;>
    rw [h] at hr <;> cases hr

/-- A labelled cut of the tick run is its index's cut of the tick, below the tick's length. -/
theorem tickRun_label_get {i : Nat} {c : Cut A} (h : (tickRun A dg).label i = some c) :
    ∃ hk : i % 8 < (tickCuts A dg (i / 8)).length, (tickCuts A dg (i / 8))[i % 8] = c := by
  rw [tickRun_label] at h
  exact List.getElem?_eq_some_iff.1 h

/-- The cut law holds at every labelled cut of the tick run. -/
theorem tickRun_cutStep (h1 : P.n = 1) {y : Fin P.n} {i : Nat} {c : Cut A}
    (hc : (tickRun A dg).CallAt y i c) :
    CutStep y ((tickRun A dg).time i) ((tickRun A dg).state y i) c ((tickRun A dg).post i) := by
  obtain ⟨hk, rfl⟩ := tickRun_label_get hc.2
  rw [tickRun_state h1, eq_v0 h1 y]
  exact chain_step
    (Compose.exec_is_cut_chain (fun _ => v0) dg v0 (tickState A dg (i / 8)) _ (.tick 0)) _ hk

/-- Every attestation in the pool before cut `i` was signed by the validator at an earlier
cut. -/
theorem tickRun_pool (h1 : P.n = 1) :
    ∀ i, ∀ a ∈ ((tickRun A dg).state v0 i).fg.atts, ∃ j < i, (tickRun A dg).SignAt v0 j a := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro a ha
    rcases i with _ | i
    · simp [Trace.state, tickRun, Node.init, Store.init] at ha
    simp only [Trace.state] at ha
    split_ifs at ha with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun A dg).CallAt v0 i c := ⟨hl.1, hc⟩
      rcases cutStep_atts A (tickRun_cutStep h1 hcall) a ha with h | ⟨B, rfl, hB⟩ | rfl
      · obtain ⟨j, hj, hs⟩ := ih i (by omega) a h
        exact ⟨j, by omega, hs⟩
      · obtain ⟨hk, he⟩ := tickRun_label_get hc
        have hpay := onBlock_tick_payload_aux (A := A) (dg := dg) (i / 8) (i % 8) (by
          rw [List.getElem?_eq_getElem hk, he]) a hB
        rw [← tickRun_state_tick h1 v0] at hpay
        obtain ⟨j, hj, hs⟩ := ih (8 * (i / 8)) (by omega) a hpay
        exact ⟨j, by omega, hs⟩
      · obtain ⟨hk, he⟩ := tickRun_label_get hc
        obtain ⟨k', C, hk', hsig⟩ := onTick_att_pos (A := A) (dg := dg) v0 _ _ 0 (k := i % 8)
          (by change (tickCuts A dg (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
        refine ⟨8 * (i / 8) + k', by omega, C, rfl, ?_⟩
        rw [tickRun_label, show (8 * (i / 8) + k') / 8 = i / 8 by omega,
          show (8 * (i / 8) + k') % 8 = k' by omega]
        exact hsig
    · obtain ⟨j, hj, hs⟩ := ih i (by omega) a ha
      exact ⟨j, by omega, hs⟩

/-- A signing `attest` cut precedes every `on_attestation` cut of the tick run. -/
theorem tickRun_att_signed {y : Fin P.n} {i : Nat} {a : FG.Att P.n}
    (h : (tickRun A dg).AttCallAt y i a) : ∃ j < i, (tickRun A dg).SignAt v0 j a := by
  obtain ⟨hk, he⟩ := tickRun_label_get h.2
  obtain ⟨k', C, hk', hsig⟩ := onTick_att_pos (A := A) (dg := dg) v0 _ _ 0 (k := i % 8)
    (by change (tickCuts A dg (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
  refine ⟨8 * (i / 8) + k', by omega, C, rfl, ?_⟩
  rw [tickRun_label, show (8 * (i / 8) + k') / 8 = i / 8 by omega,
    show (8 * (i / 8) + k') % 8 = k' by omega]
  exact hsig

/-- Two groups of the tick run at one time start at the same cut. -/
theorem tickRun_groupAt_unique {y y' : Fin P.n} {j j' : Nat} {t : Time} {e e' : Event A}
    (h : (tickRun A dg).GroupAt (fun _ => v0) dg y j t e)
    (h' : (tickRun A dg).GroupAt (fun _ => v0) dg y' j' t e') :
    j = j' := by
  obtain ⟨hm, ht, -⟩ := tickRun_groupAt_inv h
  obtain ⟨hm', ht', -⟩ := tickRun_groupAt_inv h'
  have : j / 8 = j' / 8 := by rw [ht] at ht'; exact_mod_cast ht'
  omega

/-- **The tick run is a run of the node** (`Node.LocalRun`), for the honest set of all
validators and any signer map. -/
theorem tickRun_localRun (h1 : P.n = 1) (hΔ : P.Δ = 1) (sg : A.Msg → Fin P.n) :
    Node.LocalRun (fun _ => v0) dg Set.univ sg (tickRun A dg) where
  init _ _ := rfl
  grouped y _ i c hc := by
    obtain ⟨hk, -⟩ := tickRun_label_get hc.2
    refine ⟨8 * (i / 8), .tick 0, ?_, by omega, ?_⟩
    · rw [eq_v0 h1 y, tickRun_time]; exact tickRun_groupAt h1 (i / 8)
    · rw [eq_v0 h1 y, tickRun_state_tick h1]
      change i < 8 * (i / 8) + (tickCuts A dg (i / 8)).length
      omega
  cutLaw y _ i c hc := tickRun_cutStep h1 hc
  wire y _ j t e h := by
    obtain ⟨-, -, x, rfl⟩ := tickRun_groupAt_inv h
    trivial
  proposerCredential _ _ _ _ B _ := eq_v0 h1 B.proposer
  time_nonneg _ := Int.natCast_nonneg _
  time_mono _ _ h := Int.ofNat_le.mpr (Nat.div_le_div_right h)
  finite T := (Set.finite_Iio (8 * (T.toNat + 1))).subset fun i hi => by
    obtain ⟨-, hT⟩ := hi
    change ((i / 8 : Nat) : Int) ≤ T at hT
    have h0 : 0 ≤ T := le_trans (Int.natCast_nonneg _) hT
    have : i / 8 ≤ T.toNat := (Int.le_toNat h0).mpr hT
    change i < 8 * (T.toNat + 1)
    omega
  phase_order y _ y' _ j j' t e e' h h' hlt :=
    absurd (tickRun_groupAt_unique h h') (Nat.ne_of_lt hlt)
  tick_public y _ j t h := by
    obtain ⟨_, h⟩ := h
    obtain ⟨-, rfl, -⟩ := tickRun_groupAt_inv h
    change P.Δ ∣ _
    rw [hΔ]; exact one_dvd _
  tick_unique y _ j j' t h h' := by
    obtain ⟨_, h⟩ := h
    obtain ⟨_, h'⟩ := h'
    exact tickRun_groupAt_unique h h'
  tick_of_awake y _ t h0 _ _ := by
    have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg h0
    refine ⟨8 * t.toNat, 0, ?_⟩
    rw [eq_v0 h1 y, ← htt]
    exact tickRun_groupAt h1 t.toNat
  awake_in_horizon y _ t ht := by
    have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
    refine ⟨8 * t.toNat, ?_, ?_⟩
    · left
      rw [tickRun_label, show 8 * t.toNat / 8 = t.toNat by omega,
        show 8 * t.toNat % 8 = 0 by omega, tickCuts_head]
      simp
    · rw [tickRun_time, show 8 * t.toNat / 8 = t.toNat by omega, htt]
  awake_of_call _ _ _ _ := Int.natCast_nonneg _
  restart_of_sleep _ _ _ u _ hu _ hnu _ := absurd hu hnu
  restart_at_wake _ _ u _ hu _ hnu _ := absurd hu hnu
  sleep_of_restart y _ i h := absurd h (tickRun_no_restart y i)
  block_unforgeable y _ i B h _ := by
    obtain ⟨acc, hc⟩ := h
    obtain ⟨hk, he⟩ := tickRun_label_get hc.2
    have hpos := onTick_fg_pos (A := A) (dg := dg) v0 _ _ 0 (k := i % 8)
      (by change (tickCuts A dg (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
    refine ⟨i, le_rfl, ⟨acc, ?_⟩, ?_⟩
    · rw [eq_v0 h1 B.proposer]; exact ⟨rfl, hc.2⟩
    · change i % 8 ≠ 0; omega
  att_unforgeable y _ i a h _ := by
    rw [eq_v0 h1 a.val]
    rcases h with h | ⟨B, ⟨acc, hc⟩, ha⟩
    · exact tickRun_att_signed h
    · obtain ⟨hk, he⟩ := tickRun_label_get hc.2
      have hpay := onBlock_tick_payload_aux (A := A) (dg := dg) (i / 8) (i % 8) (by
        rw [List.getElem?_eq_getElem hk, he]) a ha
      rw [← tickRun_state_tick h1 v0] at hpay
      obtain ⟨j, hj, hs⟩ := tickRun_pool h1 (8 * (i / 8)) a hpay
      exact ⟨j, by omega, hs⟩
  msg_unforgeable y _ i m h _ := absurd h (tickRun_no_msg y i m)

/-- After the first cut of a tick (its `ac_on_tick`), the state is `acCall`'s. -/
theorem tickMid_one (t : Nat) :
    tickMid A dg t 1 = (acCall v0 (tickState A dg t) (t : Int) .tick).1 := by
  have hpos := List.length_pos_of_ne_nil (tickCuts_ne_nil A dg t)
  have h0 : (tickCuts A dg t)[0] = (acCall v0 (tickState A dg t) (t : Int) .tick).2 :=
    Option.some.inj ((List.getElem?_eq_getElem hpos).symm.trans (tickCuts_head A dg t))
  have hs : CutStep v0 (t : Int) (tickState A dg t) (acCall v0 (tickState A dg t) (t : Int) .tick).2
      (tickMid A dg t 1) := by
    have := chain_step
      (Compose.exec_is_cut_chain (fun _ => v0) dg v0 (tickState A dg t) (t : Int) (.tick 0))
      0 hpos
    simp only [List.take_zero, List.foldl_nil] at this
    change CutStep v0 (t : Int) (tickState A dg t) (tickCuts A dg t)[0] (tickMid A dg t 1) at this
    rwa [h0] at this
  generalize tickMid A dg t 1 = st' at hs ⊢
  obtain ⟨fg', ac', r'⟩ := st'
  obtain ⟨-, hstep, hfg, hr⟩ := hs
  simp only [acCall] at hstep hfg hr ⊢
  rw [hfg, hr, (congrArg Prod.fst hstep : _ = ac')]

/-- An FG cut keeps the AC state; an AC cut writes the AC's step. -/
theorem cutStep_ac {self : Fin P.n} {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') :
    (∀ ℓ : FGLabel P A.Payload, c = .fg ℓ → st'.ac = st.ac) ∧
      ∀ ℓ : ACLabel A, c = .ac ℓ → A.step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) := by
  match c, h with
  | .ac ℓ, h => exact ⟨fun _ h' => (by cases h'), fun ℓ' h' => by cases h'; exact h.2.1⟩
  | .fg (.block B true), h => exact ⟨fun _ _ => h.2.2.1, fun _ h' => by cases h'⟩
  | .fg (.block B false), h => exact ⟨fun _ _ => by rw [h.2], fun _ h' => by cases h'⟩
  | .fg (.attestation a), h => exact ⟨fun _ _ => h.2.1, fun _ h' => by cases h'⟩
  | .fg (.attest C none), h => exact ⟨fun _ _ => by rw [h.2], fun _ h' => by cases h'⟩
  | .fg (.attest C (some a)), h => exact ⟨fun _ _ => h.2.2, fun _ h' => by cases h'⟩

/-- A cut of the tick run at position `0` is the tick's `ac_on_tick`. -/
theorem tickRun_label_zero {i : Nat} {c : Cut A} (h : (tickRun A dg).label i = some c)
    (h0 : i % 8 = 0) : c = (acCall v0 (tickState A dg (i / 8)) ((i / 8 : Nat) : Int) .tick).2 := by
  rw [tickRun_label, h0, tickCuts_head] at h
  exact (Option.some.inj h).symm

end Run

end Consensus.Goldilocks.Witness

end
