module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Ticks
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # The one-validator tick run: the reset and `Inv`

The remaining facts of the healing premises on the tick run of
`Goldilocks/Runs/OneValidator/Premises`, proved outright:

* **The run** (`good_tick`, `label_cases`): before every tick the state is `Good`; the labelled cuts
  of every tick are listed. So the validator signs exactly `att s` at `t_s` (`signAt_iff`), accepts
  exactly `blk s` at `t_s` (`blockCall_eq`), and votes only at `t = 1` and in `ac_on_block` of its
  own block (`emit_cases`); every pool vote of slot `σ` is `cv σ` (`pool_cv`).
* **The reset** (`tickRun_isReset`): `H_z = slot(ḡ) + 3` (`hz_eq`) and `a_z = t_{slot(ḡ)+4}`
  (`aZ`), the time of `att (slot(ḡ) + 4)`.
* **`Inv`** (`tickRun_inv`): every protected block of slot `j` is a chain block of slot `≤ j`
  (`protected_le`), so `Inv(t₀)` holds for every `t₀`. (`Geo` itself fails here for `p ≥ 4`: by
  `fgGood_frame`, the block of slot `p − 2` is a viable head of the proposer's frame and not of the
  voter's, and it is in the voter block tree.)
With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open AC Node ChainFrame

/-! ## The ticks of the run -/

theorem tickState_succ (t : Nat) :
    tickState N1 dg1 (t + 1) =
      (stockTick N1 dg1 v0 (tickState N1 dg1 t) (t : Int) 0).1 := rfl

theorem tickCuts_eq (t : Nat) :
    tickCuts N1 dg1 t =
      (stockTick N1 dg1 v0 (tickState N1 dg1 t) (t : Int) 0).2 := rfl

theorem tick_cases (t : Nat) : t = 1 ∨ (∃ k, t = 4 * (k + 1)) ∨ (t % 4 = 2 ∧ 4 ≤ t) ∨
    (t ≠ 1 ∧ ¬ (t % 4 = 0 ∧ 4 ≤ t) ∧ ¬ (t % 4 = 2 ∧ 4 ≤ t)) := by
  by_cases h1 : t = 1
  · exact Or.inl h1
  by_cases hA : t % 4 = 0 ∧ 4 ≤ t
  · exact Or.inr (Or.inl ⟨t / 4 - 1, by omega⟩)
  by_cases hC : t % 4 = 2 ∧ 4 ≤ t
  · exact Or.inr (Or.inr (Or.inl hC))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, hA, hC⟩))

theorem admitOwn_readCuts (st : NodeState N1) (t : Time) (c : Cut N1) :
    admitOwn (st, c :: readCuts st t) = (st, c :: readCuts st t) := by
  unfold readCuts
  split <;> rfl

/-- **The run invariant**: before every tick, the node state is `Good`. -/
theorem good_tick : ∀ t, Good (tickState N1 dg1 t) t
  | 0 => good_init
  | t + 1 => by
    have ih := good_tick t
    rw [tickState_succ]
    rcases tick_cases t with rfl | ⟨k, rfl⟩ | hC | ⟨h1, hA, hC⟩
    · obtain ⟨A', e, he, -, -, hg⟩ := tick_B0 ih
      rw [stockTick, he]; exact hg
    · obtain ⟨fg', e, st', -, -, he, -, -, hg⟩ := tick_A ih
      rw [he]; exact hg
    · obtain ⟨A', he, hg⟩ := tick_C ih hC
      rw [stockTick, he, show Node.frame (tickState N1 dg1 t) =
        Node.frame { (tickState N1 dg1 t) with ac := A' } from rfl,
        show [_] ++ readCuts _ _ = _ :: readCuts _ _ from rfl, admitOwn_readCuts]
      exact hg
    · rw [stockTick, (tick_noop ih h1 hA hC).1, show [_] ++ readCuts _ _ =
        _ :: readCuts _ _ from rfl, admitOwn_readCuts]
      exact (tick_noop ih h1 hA hC).2

/-! ## The cuts of the run -/

theorem tickCuts_A (k : Nat) : ∃ fg' e,
    (tickState N1 dg1 (4 * (k + 1))).fg.onBlock (blk (k + 1)) = some fg' ∧ FGGood fg' (k + 1) ∧
    tickCuts N1 dg1 (4 * (k + 1)) =
      [.ac ⟨.tick, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩,
        .ac ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩,
        .fg (.block (blk (k + 1)) true), .ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩,
        .ac ⟨.toFG, fg'.toFrame, []⟩, .fg (.attest (blk (k + 1)) (some (att (k + 1)))),
        .fg (.attestation (att (k + 1)))] ∧
    e.msg = cv (k + 1) ∧ e.readPoint.pool = (tickState N1 dg1 (4 * (k + 1))).ac.pool := by
  obtain ⟨fg', e, st', hob, hfg', he, hm, hp, -⟩ := tick_A (good_tick (4 * (k + 1)))
  exact ⟨fg', e, hob, hfg', by rw [tickCuts_eq, he], hm, hp⟩

theorem tickCuts_B0 : ∃ e, tickCuts N1 dg1 1 =
    [.ac ⟨.tick, Node.frame (tickState N1 dg1 1), [e]⟩,
      .ac ⟨.toFG, Node.frame (tickState N1 dg1 1), []⟩] ∧
    e.msg = cv 0 ∧ e.readPoint.pool = (tickState N1 dg1 1).ac.pool := by
  obtain ⟨A', e, he, hm, hp, -⟩ := tick_B0 (good_tick 1)
  exact ⟨e, by rw [tickCuts_eq, stockTick, he]; rfl, hm, hp⟩

theorem tickCuts_other {t : Nat} (h1 : t ≠ 1) (hA : ¬ (t % 4 = 0 ∧ 4 ≤ t)) :
    ∃ st, tickCuts N1 dg1 t = [.ac ⟨.tick, Node.frame (tickState N1 dg1 t), []⟩] ++
      readCuts st t ∧ Node.frame st = Node.frame (tickState N1 dg1 t) := by
  rw [tickCuts_eq, stockTick]
  by_cases hC : t % 4 = 2 ∧ 4 ≤ t
  · obtain ⟨A', he, -⟩ := tick_C (good_tick t) hC
    rw [he, show Node.frame (tickState N1 dg1 t) =
      Node.frame { (tickState N1 dg1 t) with ac := A' } from rfl,
      show [_] ++ readCuts _ _ = _ :: readCuts _ _ from rfl, admitOwn_readCuts]
    exact ⟨_, rfl, rfl⟩
  · rw [(tick_noop (good_tick t) h1 hA hC).1,
      show [_] ++ readCuts _ _ = _ :: readCuts _ _ from rfl, admitOwn_readCuts]
    exact ⟨_, rfl, rfl⟩

theorem get7 {α : Type} {a0 a1 a2 a3 a4 a5 a6 c : α} {k : Nat}
    (h : [a0, a1, a2, a3, a4, a5, a6][k]? = some c) :
    (k = 0 ∧ c = a0) ∨ (k = 1 ∧ c = a1) ∨ (k = 2 ∧ c = a2) ∨ (k = 3 ∧ c = a3) ∨
      (k = 4 ∧ c = a4) ∨ (k = 5 ∧ c = a5) ∨ (k = 6 ∧ c = a6) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp at h <;> simp [h]

theorem get2 {α : Type} {a0 a1 c : α} {k : Nat} (h : [a0, a1][k]? = some c) :
    (k = 0 ∧ c = a0) ∨ (k = 1 ∧ c = a1) := by
  rcases k with _ | _ | k <;> simp at h <;> simp [h]

theorem get_readCuts {st : NodeState N1} {t : Time} {a c : Cut N1} {k : Nat}
    (h : (a :: readCuts st t)[k]? = some c) :
    (k = 0 ∧ c = a) ∨ (k = 1 ∧ c = .ac ⟨.toFG, Node.frame st, []⟩) ∨
      (k = 2 ∧ ∃ C, c = .fg (.attest C none)) := by
  unfold readCuts at h
  split at h
  · exact (get2 h).imp_right Or.inl
  · rename_i C heq
    rcases k with _ | _ | _ | k <;> simp at h
    · exact Or.inl ⟨rfl, h.symm⟩
    · exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · exact Or.inr (Or.inr ⟨rfl, C, h.symm⟩)

/-- **The labelled cuts of the run.** -/
theorem label_cases {i : Nat} {c : Cut N1} (h : (tickRun N1 dg1).label i = some c) :
    (∃ k fg' e, i / 8 = 4 * (k + 1) ∧
      (tickState N1 dg1 (4 * (k + 1))).fg.onBlock (blk (k + 1)) = some fg' ∧ FGGood fg' (k + 1) ∧
      e.msg = cv (k + 1) ∧ e.readPoint.pool = (tickState N1 dg1 (4 * (k + 1))).ac.pool ∧
      ((i % 8 = 0 ∧ c = .ac ⟨.tick, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩) ∨
       (i % 8 = 1 ∧ c = .ac ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩) ∨
       (i % 8 = 2 ∧ c = .fg (.block (blk (k + 1)) true)) ∨
       (i % 8 = 3 ∧ c = .ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩) ∨
       (i % 8 = 4 ∧ c = .ac ⟨.toFG, fg'.toFrame, []⟩) ∨
       (i % 8 = 5 ∧ c = .fg (.attest (blk (k + 1)) (some (att (k + 1))))) ∨
       (i % 8 = 6 ∧ c = .fg (.attestation (att (k + 1)))))) ∨
    (i / 8 = 1 ∧ ∃ e, e.msg = cv 0 ∧ e.readPoint.pool = (tickState N1 dg1 1).ac.pool ∧
      ((i % 8 = 0 ∧ c = .ac ⟨.tick, Node.frame (tickState N1 dg1 1), [e]⟩) ∨
       (i % 8 = 1 ∧ c = .ac ⟨.toFG, Node.frame (tickState N1 dg1 1), []⟩))) ∨
    (i / 8 ≠ 1 ∧ ¬ (i / 8 % 4 = 0 ∧ 4 ≤ i / 8) ∧
      ((i % 8 = 0 ∧ c = .ac ⟨.tick, Node.frame (tickState N1 dg1 (i / 8)), []⟩) ∨
       (i % 8 = 1 ∧ c = .ac ⟨.toFG, Node.frame (tickState N1 dg1 (i / 8)), []⟩) ∨
       (i % 8 = 2 ∧ ∃ C, c = .fg (.attest C none)))) := by
  rw [tickRun_label] at h
  rcases tick_cases (i / 8) with h1 | ⟨k, hk⟩ | hC | ⟨h1, hA, -⟩
  · obtain ⟨e, he, hm, hp⟩ := tickCuts_B0
    rw [h1, he] at h
    exact Or.inr (Or.inl ⟨h1, e, hm, hp, get2 h⟩)
  · obtain ⟨fg', e, hob, hfg', he, hm, hp⟩ := tickCuts_A k
    rw [hk, he] at h
    exact Or.inl ⟨k, fg', e, hk, hob, hfg', hm, hp, get7 h⟩
  · obtain ⟨st, he, hf⟩ := tickCuts_other (t := i / 8) (by omega) (by omega)
    rw [he] at h
    have hc := get_readCuts h
    rw [hf] at hc
    exact Or.inr (Or.inr ⟨by omega, by omega, hc⟩)
  · obtain ⟨st, he, hf⟩ := tickCuts_other h1 hA
    rw [he] at h
    have hc := get_readCuts h
    rw [hf] at hc
    exact Or.inr (Or.inr ⟨h1, hA, hc⟩)

/-- The signings of the run: the attestation of slot `s ≥ 1`, at cut `8·t_s + 5`. -/
theorem signAt_iff {i : Nat} {a : FG.Att sp1.n} :
    (tickRun N1 dg1).SignAt v0 i a ↔ ∃ s, 1 ≤ s ∧ i = 8 * (4 * s) + 5 ∧ a = att s := by
  constructor
  · rintro ⟨C, -, hc⟩
    rcases label_cases hc with ⟨k, fg', e, hk, -, -, -, -, hcs⟩ | ⟨-, e, -, -, hcs⟩ | ⟨-, -, hcs⟩
    · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h5, h⟩ | ⟨-, h⟩ <;>
        try cases h
      exact ⟨k + 1, by omega, by omega, rfl⟩
    · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, C, h⟩ <;> cases h
  · rintro ⟨s, hs, rfl, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    obtain ⟨fg', e, -, -, he, -, -⟩ := tickCuts_A k
    refine ⟨blk (k + 1), rfl, ?_⟩
    rw [tickRun_label, show (8 * (4 * (k + 1)) + 5) / 8 = 4 * (k + 1) by omega,
      show (8 * (4 * (k + 1)) + 5) % 8 = 5 by omega, he]
    rfl

/-- The block calls of the run: the block of slot `s ≥ 1`, accepted at cut `8·t_s + 2`. -/
theorem blockCall_eq {i : Nat} {B : N1.Blk} {acc : Bool}
    (h : (tickRun N1 dg1).label i = some (.fg (.block B acc))) :
    ∃ s, 1 ≤ s ∧ i = 8 * (4 * s) + 2 ∧ B = blk s ∧ acc = true := by
  rcases label_cases h with ⟨k, fg', e, hk, -, -, -, -, hcs⟩ | ⟨-, e, -, -, hcs⟩ | ⟨-, -, hcs⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h2, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      try cases h
    exact ⟨k + 1, by omega, by omega, rfl, rfl⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, C, h⟩ <;> cases h

theorem blk_label (k : Nat) :
    (tickRun N1 dg1).label (8 * (4 * (k + 1)) + 2) = some (.fg (.block (blk (k + 1)) true)) := by
  obtain ⟨fg', e, -, -, he, -, -⟩ := tickCuts_A k
  rw [tickRun_label, show (8 * (4 * (k + 1)) + 2) / 8 = 4 * (k + 1) by omega,
    show (8 * (4 * (k + 1)) + 2) % 8 = 2 by omega, he]
  rfl

/-- An AC call of the run with an emission: the vote of slot `0` at cut `8`, or the vote of slot
`k + 1` at cut `8·t_{k+1} + 3`, inside `ac_on_block` of the own block. -/
theorem emit_cases {i : Nat} {ℓ : ACLabel N1} (h : (tickRun N1 dg1).label i = some (.ac ℓ))
    {e : N1.Em} (he : e ∈ ℓ.emits) :
    (i = 8 ∧ e.msg = cv 0 ∧ e.readPoint.pool = (tickState N1 dg1 1).ac.pool) ∨
    ∃ k fg', i = 8 * (4 * (k + 1)) + 3 ∧ ℓ.frame = fg'.toFrame ∧ FGGood fg' (k + 1) ∧
      ℓ.call = .block (blk (k + 1)) ∧ e.msg = cv (k + 1) ∧
      e.readPoint.pool = (tickState N1 dg1 (4 * (k + 1))).ac.pool := by
  rcases label_cases h with ⟨k, fg', e', hk, -, hfg', hm, hp, hcs⟩ | ⟨h1, e', hm, hp, hcs⟩ |
      ⟨-, -, hcs⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h3, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;>
      simp only [List.not_mem_nil, List.mem_singleton] at he
    subst he
    exact Or.inr ⟨k, fg', by omega, rfl, hfg', rfl, hm, hp⟩
  · rcases hcs with ⟨h0, h⟩ | ⟨-, h⟩ <;> simp only [Cut.ac.injEq] at h <;> subst h <;>
      simp only [List.not_mem_nil, List.mem_singleton] at he
    subst he
    exact Or.inl ⟨by omega, hm, hp⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, C, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;>
      simp at he

/-- An `ac_on_block(B)` call of the run: the own block of slot `k + 1` at `8·t_{k+1} + 3`. -/
theorem acBlock_cases {i : Nat} {ℓ : ACLabel N1} (h : (tickRun N1 dg1).label i = some (.ac ℓ))
    {B : N1.Blk} (hB : ℓ.call = .block B) :
    ∃ k, i = 8 * (4 * (k + 1)) + 3 ∧ B = blk (k + 1) := by
  rcases label_cases h with ⟨k, fg', e', hk, -, -, -, -, hcs⟩ | ⟨-, e', -, -, hcs⟩ | ⟨-, -, hcs⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h3, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;> simp at hB
    exact ⟨k, by omega, hB.symm⟩
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ <;> simp only [Cut.ac.injEq] at h <;> subst h <;> simp at hB
  · rcases hcs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, C, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;> simp at hB

/-- An `ac_on_tick` call of the run is the first cut of its tick. -/
theorem acTick_pos {i : Nat} {ℓ : ACLabel N1} (h : (tickRun N1 dg1).label i = some (.ac ℓ))
    (hc : ℓ.call = .tick) : i % 8 = 0 := by
  rcases label_cases h with ⟨k, fg', e', hk, -, -, -, -, hcs⟩ | ⟨-, e', -, -, hcs⟩ | ⟨-, -, hcs⟩
  · rcases hcs with ⟨h0, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;> simp at hc
    exact h0
  · rcases hcs with ⟨h0, h⟩ | ⟨-, h⟩ <;> simp only [Cut.ac.injEq] at h <;> subst h <;> simp at hc
    exact h0
  · rcases hcs with ⟨h0, h⟩ | ⟨-, h⟩ | ⟨-, C, h⟩ <;>
      simp only [Cut.ac.injEq, reduceCtorEq] at h <;> subst h <;> simp at hc
    exact h0

/-! ## The states of the run -/

theorem mid_step {t j : Nat} {c : Cut N1} (h : (tickCuts N1 dg1 t)[j]? = some c) :
    CutStep v0 (t : Int) (tickMid N1 dg1 t j) c (tickMid N1 dg1 t (j + 1)) := by
  have hj : j < 8 := by
    have := (List.getElem?_eq_some_iff.1 h).1; have := tickCuts_length N1 dg1 t; omega
  have hl : (tickRun N1 dg1).label (8 * t + j) = some c := by
    rw [tickRun_label, show (8 * t + j) / 8 = t by omega, show (8 * t + j) % 8 = j by omega]
    exact h
  have := tickRun_cutStep (A := N1) (dg := dg1) rfl (y := v0) ⟨rfl, hl⟩
  rw [tickRun_state rfl, tickRun_time, show (8 * t + j) / 8 = t by omega,
    show (8 * t + j) % 8 = j by omega] at this
  change CutStep v0 (t : Int) (tickMid N1 dg1 t j) c
    (tickMid N1 dg1 ((8 * t + j) / 8) ((8 * t + j) % 8 + 1)) at this
  rwa [show (8 * t + j) / 8 = t by omega, show (8 * t + j) % 8 = j by omega] at this

theorem mid_ac {t j : Nat} {ℓ : ACLabel N1} (h : (tickCuts N1 dg1 t)[j]? = some (.ac ℓ)) :
    (tickMid N1 dg1 t (j + 1)).fg = (tickMid N1 dg1 t j).fg := (mid_step h).2.2.1

theorem fgGood_cutStep {t : Time} {st st' : NodeState N1} {c : Cut N1} (h : CutStep v0 t st c st')
    (hc : ∀ B, c ≠ .fg (.block B true)) {τ : Nat} (hg : FGGood st.fg τ) : FGGood st'.fg τ := by
  match c, h, hc with
  | .ac ℓ, h, _ => rw [h.2.2.1]; exact hg
  | .fg (.block B true), _, hc => exact absurd rfl (hc B)
  | .fg (.block B false), h, _ => rw [h.2]; exact hg
  | .fg (.attestation a), h, _ =>
    rw [h.1]
    unfold Store.onAttestation
    split_ifs
    · exact hg
    · exact ⟨hg.blocks, hg.sigma, hg.J, hg.hj, hg.hmax, hg.F⟩
  | .fg (.attest C none), h, _ => rw [h.2]; exact hg
  | .fg (.attest C (some a)), h, _ => rw [h.2.1]; exact hg

/-- The tip of the FG store before cut `i`: the next block is accepted at the cut `2` of its
tick. -/
def stTip (i : Nat) : Nat :=
  if i / 8 % 4 = 0 ∧ 4 ≤ i / 8 ∧ 3 ≤ i % 8 then tip (i / 8) + 1 else tip (i / 8)

theorem mid_fgGood (t j : Nat) :
    FGGood (tickMid N1 dg1 t j).fg (if t % 4 = 0 ∧ 4 ≤ t ∧ 3 ≤ j then tip t + 1 else tip t) := by
  have hg := (good_tick t).fg
  have hg' := (good_tick (t + 1)).fg
  rcases tick_cases t with ht | ⟨k, rfl⟩ | hC | ⟨h1, hA, -⟩
  rotate_left
  · obtain ⟨fg', e, hob, hfg', he, -, -⟩ := tickCuts_A k
    have hlen : (tickCuts N1 dg1 (4 * (k + 1))).length = 7 := by rw [he]; rfl
    have g : ∀ (j : Nat) (c : Cut N1),
        [Cut.ac ⟨.tick, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩,
        .ac ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩,
        .fg (.block (blk (k + 1)) true), .ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩,
        .ac ⟨.toFG, fg'.toFrame, []⟩, .fg (.attest (blk (k + 1)) (some (att (k + 1)))),
        .fg (.attestation (att (k + 1)))][j]? = some c →
          (tickCuts N1 dg1 (4 * (k + 1)))[j]? = some c :=
      fun j c h => by rw [he]; exact h
    have m1 := mid_ac (g 0 _ rfl)
    have m2 := mid_ac (g 1 _ rfl)
    have m3 := (mid_step (g 2 _ rfl)).2.1
    rw [m2, m1, tickMid_zero, hob, Option.some.injEq] at m3
    have h3 : FGGood (tickMid N1 dg1 (4 * (k + 1)) 3).fg (k + 1) := m3 ▸ hfg'
    have h4 := fgGood_cutStep (mid_step (g 3 _ rfl)) (by simp) h3
    have h5 := fgGood_cutStep (mid_step (g 4 _ rfl)) (by simp) h4
    have h6 := fgGood_cutStep (mid_step (g 5 _ rfl)) (by simp) h5
    rw [tip_A]
    rcases j with _ | _ | _ | _ | _ | _ | _ | j
    · rw [ite_neg (by omega), tickMid_zero]; rw [tip_A] at hg; exact hg
    · rw [ite_neg (by omega), m1, tickMid_zero]; rw [tip_A] at hg; exact hg
    · rw [ite_neg (by omega), m2, m1, tickMid_zero]; rw [tip_A] at hg; exact hg
    · rw [ite_pos ⟨by omega, by omega, by omega⟩]; exact h3
    · rw [ite_pos ⟨by omega, by omega, by omega⟩]; exact h4
    · rw [ite_pos ⟨by omega, by omega, by omega⟩]; exact h5
    · rw [ite_pos ⟨by omega, by omega, by omega⟩]; exact h6
    · rw [ite_pos ⟨by omega, by omega, by omega⟩, tickMid_of_le N1 dg1 (by omega)]
      rw [show tip (4 * (k + 1) + 1) = k + 1 from tip_A1 k] at hg'; exact hg'
  all_goals
    have htip : tip (t + 1) = tip t := by unfold tip; omega
    rw [ite_neg (by omega)]
    have hnoblock : ∀ (k : Nat) (c : Cut N1), (tickCuts N1 dg1 t)[k]? = some c →
        ∀ B, c ≠ Cut.fg (A := N1) (.block B true) := by
      intro k c hc B
      first
      | (obtain rfl := ht; obtain ⟨e, he, -, -⟩ := tickCuts_B0
         rw [he] at hc; rcases get2 hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp)
      | (obtain ⟨st, he, -⟩ := tickCuts_other (t := t) (by omega) (by omega)
         rw [he] at hc
         rcases get_readCuts hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, C, rfl⟩ <;> simp)
    clear hg'
    induction j with
    | zero => simpa only [tickMid_zero] using hg
    | succ j ih =>
      by_cases hj : j < (tickCuts N1 dg1 t).length
      · have hc : (tickCuts N1 dg1 t)[j]? = some ((tickCuts N1 dg1 t)[j]) :=
          List.getElem?_eq_getElem hj
        exact fgGood_cutStep (mid_step hc) (hnoblock j _ hc) ih
      · rw [tickMid_of_le N1 dg1 (by omega), ← htip]
        exact (good_tick (t + 1)).fg

theorem state_eq (i : Nat) : (tickRun N1 dg1).state v0 i = tickMid N1 dg1 (i / 8) (i % 8) :=
  tickRun_state rfl v0 i

theorem state_fgGood (i : Nat) : FGGood ((tickRun N1 dg1).state v0 i).fg (stTip i) := by
  rw [state_eq]; exact mid_fgGood _ _

theorem tip_le_stTip (i : Nat) : tip (i / 8) ≤ stTip i := by unfold stTip; split_ifs <;> omega

theorem state_frame (i : Nat) :
    ∃ f, ChainFrame (Node.frame ((tickRun N1 dg1).state v0 i)) f (jexp (stTip i)) (stTip i) :=
  fgGood_frame (state_fgGood i)

theorem state_tick (t : Nat) : (tickRun N1 dg1).state v0 (8 * t) = tickState N1 dg1 t :=
  tickRun_state_tick rfl v0 t

/-- Every chain block is an honest block. -/
theorem blk_mem_honest (m : Nat) : blk m ∈ (tickRun N1 dg1).HonestBlocks Set.univ := by
  refine ⟨v0, Set.mem_univ _, 8 * (4 * m + 1), ?_⟩
  rw [state_tick]
  have h := (good_tick (4 * m + 1)).fg
  rw [show tip (4 * m + 1) = m by unfold tip; omega] at h
  exact (mem_tree_iff h.blocks).2 ⟨m, le_rfl, rfl⟩

theorem anc_honest {a b : Nat} (h : a ≤ b) :
    Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (blk a) (blk b) :=
  anc_blk h fun k _ _ => blk_mem_honest k

/-- Every vote in a pool of slot `σ` is the vote of slot `σ`. -/
theorem pool_cv (i σ : Nat) : ∀ v ∈ ((tickRun N1 dg1).state v0 i).ac.pool σ, v = cv σ := by
  intro v hv
  obtain ⟨j, -, ℓ, hc, e, he, rfl⟩ := tickRun_votes i σ v hv
  have hs := tickRun_slotOK i σ e.msg hv
  rcases emit_cases hc.2 he with ⟨-, hm, -⟩ | ⟨k, fg', -, -, -, -, hm, -⟩
  · rw [hm] at hs ⊢; rw [← hs]; rfl
  · rw [hm] at hs ⊢; rw [← hs]; rfl

theorem tickState_pool_cv (t σ : Nat) : ∀ v ∈ (tickState N1 dg1 t).ac.pool σ, v = cv σ := by
  rw [← state_tick]; exact pool_cv _ σ

/-! ## The protected blocks are chain blocks of their slot or earlier -/

theorem ancR_blk_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {C : N1.Blk} {s : Nat}
    (hA : AncR Φ C (blk s).root) : ∃ c ≤ s, C = blk c := by
  obtain ⟨R, hR, hr, ha⟩ := hA
  obtain ⟨rfl, -, -⟩ := h.eq_of_root hR hr
  obtain ⟨c, hc, he, -⟩ := anc_blk_inv h.onChain ha
  exact ⟨c, hc, he⟩

theorem getConfirmation_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {A : ACState sp1.n}
    {s : Nat} (hpool : ∀ v ∈ A.pool s, v = cv s) {C : N1.Blk}
    (hC : getConfirmation sp1 A Φ s = some C) : ∃ c ≤ s, C = blk c := by
  obtain ⟨⟨-, -, hlt⟩, -⟩ := deepest_mem hC
  unfold confirmationScore at hlt
  dsimp only at hlt
  generalize hS : supporters Φ _ (s : Int) C = S at hlt
  obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
  rw [← hS] at hi
  obtain ⟨-, x, hx, -, -, hanc⟩ := hi
  rw [hpool x hx.1] at hanc
  exact ancR_blk_le h hanc

theorem optimisticSelect_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ)
    {A : ACState sp1.n} {t : Time}
    (hpool : ∀ v ∈ A.pool (sp1.slot t), ∃ σ ≤ sp1.slot t, v = cv σ) {B : N1.Blk}
    (hB : optimisticSelect sp1 A Φ t = some B) : ∃ m ≤ sp1.slot t, B = blk m := by
  unfold optimisticSelect at hB
  dsimp only at hB
  split_ifs at hB
  obtain ⟨⟨-, h3, -⟩, -⟩ := deepest_mem hB
  obtain ⟨i, x, hx, -, hanc⟩ := Set.nonempty_of_ncard_ne_zero (s :=
    optimisticVoters sp1 A Φ (sp1.slot t) B) (fun h0 => by
      rw [h0] at h3; change 3 * 1 ≤ 4 * 0 at h3; omega)
  obtain ⟨σ, hσ, rfl⟩ := hpool x hx
  obtain ⟨m, hm, rfl⟩ := ancR_blk_le h hanc
  exact ⟨m, le_trans hm hσ, rfl⟩

theorem projAC_state (i : Nat) :
    (tickRun N1 dg1).projAC.state v0 i = ((tickRun N1 dg1).state v0 i).ac :=
  Compose.projAC_state tickRun_goldilocksRun.toLocalRun (Set.mem_univ _) i

theorem projAC_call {y : Fin sp1.n} {i : Nat} {ℓ : ACLabel N1}
    (hc : (tickRun N1 dg1).projAC.CallAt y i ℓ) :
    y = v0 ∧ ℓ.frame = Node.frame ((tickRun N1 dg1).state v0 i) ∧
      (tickRun N1 dg1).label i = some (.ac ℓ) := by
  obtain rfl := eq_v0 rfl y
  exact ⟨rfl, Compose.frame_of_projAC tickRun_goldilocksRun (Set.mem_univ _) hc,
    (Compose.projAC_callAt.1 hc).2⟩

theorem time_eq (i : Nat) : (tickRun N1 dg1).projAC.time i = ((i / 8 : Nat) : Int) := rfl

/-- The pool of the slot of a cut at an optimistic check: chain votes of that slot or earlier. -/
theorem optPoint_pool {x : Fin sp1.n} {i : Nat} {ℓ : ACLabel N1} {A : ACState sp1.n}
    (hp : OptimisticPoint (tickRun N1 dg1).projAC x i ℓ A) :
    ∀ v ∈ A.pool (sp1.slot ((tickRun N1 dg1).projAC.time i)),
      ∃ σ ≤ sp1.slot ((tickRun N1 dg1).projAC.time i), v = cv σ := by
  obtain ⟨hc, hcase⟩ := hp
  obtain ⟨rfl, -, hl⟩ := projAC_call hc
  intro v hv
  rcases hcase with ⟨m, hm, -⟩ | ⟨B, hB, rfl⟩ | ⟨e, he, rfl⟩
  · exact absurd ⟨ℓ, ⟨rfl, hl⟩, hm⟩ (tickRun_no_msg v0 i m)
  · obtain ⟨k, rfl, rfl⟩ := acBlock_cases hl hB
    have hs : sp1.slot ((tickRun N1 dg1).projAC.time (8 * (4 * (k + 1)) + 3)) = k + 1 := by
      rw [time_eq, slot_nat]; omega
    rw [hs] at hv ⊢
    rcases ACPool.blockReceipt_pool sp1 _ _ _ _ v hv with hv | hv
    · rw [projAC_state] at hv; exact ⟨k + 1, le_rfl, pool_cv _ _ v hv⟩
    · rw [show declaredHeadVotes (blk (k + 1)) = [cv k] from rfl, List.mem_singleton] at hv
      exact ⟨k, by omega, hv⟩
  · rcases emit_cases hl he with ⟨rfl, hm, hrp⟩ | ⟨k, fg', rfl, -, -, -, hm, hrp⟩
    · have hs : sp1.slot ((tickRun N1 dg1).projAC.time 8) = 0 := by rw [time_eq, slot_nat]
      rw [hs] at hv ⊢
      rcases ACPool.admitVote_pool sp1 _ _ _ _ v hv with hv | hv
      · rw [hrp] at hv; exact ⟨0, le_rfl, tickState_pool_cv _ _ v hv⟩
      · rw [hm] at hv; exact ⟨0, le_rfl, hv⟩
    · have hs : sp1.slot ((tickRun N1 dg1).projAC.time (8 * (4 * (k + 1)) + 3)) = k + 1 := by
        rw [time_eq, slot_nat]; omega
      rw [hs] at hv ⊢
      rcases ACPool.admitVote_pool sp1 _ _ _ _ v hv with hv | hv
      · rw [hrp] at hv; exact ⟨k + 1, le_rfl, tickState_pool_cv _ _ v hv⟩
      · rw [hm] at hv; exact ⟨k + 1, le_rfl, hv⟩

theorem update_pool {x : Fin sp1.n} {i s : Nat} {ℓ : ACLabel N1}
    (hu : UpdateAt (tickRun N1 dg1).projAC x i s ℓ) :
    (∀ v ∈ ((tickRun N1 dg1).projAC.state x i).pool s, v = cv s) ∧
      ∃ f, ChainFrame ℓ.frame f (jexp (stTip i)) (stTip i) := by
  obtain ⟨rfl, hfr, -⟩ := projAC_call hu.1
  rw [projAC_state, hfr]
  exact ⟨pool_cv i s, state_frame i⟩

/-- **Every protected block of slot `j` is a chain block of slot `≤ j`.** -/
theorem protected_le {t₀ : Time} {B : N1.Blk} {j : Nat}
    (h : Protected (fun _ => v0) (tickRun N1 dg1).projAC Set.univ t₀ B j) :
    ∃ m ≤ j, B = blk m := by
  rcases h with ⟨x, -, i, CV, -, hfl, -⟩ | ⟨x, -, i, -, ⟨ℓ, C, hu, hC, hB⟩, -⟩ |
      ⟨-, ⟨k, ℓ, d, pay, -, -, -, -, -, hBs, -, -, i', -, ⟨ℓ', hc', hcall⟩, hti⟩, -, -⟩
  · rcases hfl with ⟨ℓ, C, hu, hC, hB, -⟩ | ⟨ℓ, A, hp, hs, hsel, -⟩
    · obtain ⟨hpool, f, hf⟩ := update_pool hu
      obtain ⟨c, hc, rfl⟩ := getConfirmation_le hf hpool hC
      obtain ⟨⟨⟨-, -, ha⟩, -⟩, -⟩ := deepest_mem hB
      obtain ⟨b, hb, he, -⟩ := anc_blk_inv hf.onChain ha
      exact ⟨b, le_trans hb hc, he⟩
    · obtain ⟨rfl, hfr, -⟩ := projAC_call hp.1
      obtain ⟨f, hf⟩ := state_frame i
      rw [← hfr] at hf
      obtain ⟨m, hm, rfl⟩ := optimisticSelect_le hf (optPoint_pool hp) hsel
      exact ⟨m, hs ▸ hm, rfl⟩
  · obtain ⟨hpool, f, hf⟩ := update_pool hu
    obtain ⟨c, hc, rfl⟩ := getConfirmation_le hf hpool hC
    obtain ⟨⟨⟨-, -, ha⟩, -⟩, -⟩ := deepest_mem hB
    obtain ⟨b, hb, he, -⟩ := anc_blk_inv hf.onChain ha
    exact ⟨b, le_trans hb hc, he⟩
  · obtain ⟨-, -, hl⟩ := projAC_call hc'
    obtain ⟨k', rfl, rfl⟩ := acBlock_cases hl hcall
    rw [time_eq, ts_nat] at hti
    refine ⟨k' + 1, ?_, rfl⟩
    have : (((8 * (4 * (k' + 1)) + 3) / 8 : Nat) : Int) = 4 * (k' + 1 : Nat) := by
      rw [show (8 * (4 * (k' + 1)) + 3) / 8 = 4 * (k' + 1) by omega]; push_cast; ring
    rw [this] at hti
    have h' : ((4 * (k' + 1 : Nat) : Int) : Int) = 4 * ((j : Nat) : Int) := hti
    omega

/-! ## `Inv` holds from every time -/

theorem tip_ge {j i : Nat} (h : 4 * (j + 1) ≤ i / 8) : j ≤ tip (i / 8) := by unfold tip; omega

/-- **`Inv(t₀)` holds on the AC projection of the tick run, for every `t₀`.** -/
theorem tickRun_inv (t₀ : Time) :
    Inv (fun _ => v0) (tickRun N1 dg1).projAC Set.univ
      ((tickRun N1 dg1).HonestBlocks Set.univ) t₀ := by
  intro B j hP y _ i ℓ hc ht
  obtain ⟨m, hm, rfl⟩ := protected_le hP
  obtain ⟨-, hfr, hl⟩ := projAC_call hc
  rw [time_eq, ts_nat] at ht
  have hji : 4 * (j + 1) ≤ i / 8 := by
    have h' : ((4 * ((j + 1 : Nat) : Int)) : Int) ≤ ((i / 8 : Nat) : Int) := ht
    omega
  refine ⟨?_, fun e he => ?_⟩
  · obtain ⟨f, hf⟩ := state_frame i
    rw [hfr]
    have hτ : j ≤ stTip i := le_trans (tip_ge hji) (tip_le_stTip i)
    rcases Nat.lt_or_ge m f with hmf | hmf
    · left; rw [hf.fcRoot]; exact anc_honest hmf.le
    · right
      exact hf.mem_viableTree' (hf.mem (le_trans hf.fj hf.jτ) le_rfl) hmf (by omega)
        (hf.mem hmf (by omega))
  · rcases emit_cases hl he with ⟨rfl, -, -⟩ | ⟨k, fg', rfl, hfr', hfg', -, hm', -⟩
    · omega
    · obtain ⟨f', hf'⟩ := fgGood_frame hfg'
      rw [hfr', hm']
      have hk : j ≤ k := by omega
      rcases Nat.lt_or_ge m f' with hmf | hmf
      · right; rw [hf'.fcRoot]; exact anc_honest hmf.le
      · left
        exact hf'.mem_viableTree' (mem_voterBlockTree hf' _ (le_trans hf'.fj (jexp_le _)) le_rfl)
          hmf (by omega) (mem_voterBlockTree hf' _ hmf (by omega))

theorem hmax_state (i : Nat) : ((tickRun N1 dg1).state v0 i).fg.hmax = hexp (stTip i) :=
  (state_fgGood i).hmax

/-! ## The reset -/

/-- The slot `slot(ḡ) + 3` of the cut `c_z`. -/
noncomputable def zN (g : Time) : Nat := sp1.toParams.slotOf (gbar g) + 3

/-- The reset `a_z = t_{slot(ḡ)+4}`: the attestation of slot `slot(ḡ) + 4` has height
`H_z + 1 = slot(ḡ) + 4`. -/
noncomputable def aZ (g : Time) : Time := 4 * ((zN g + 1 : Nat) : Int)

theorem cutZ_eq (g : Time) : Healing.cutZ sp1.toParams g = 4 * ((zN g : Nat) : Int) := rfl

theorem time_run (i : Nat) : ((tickRun N1 dg1).time i : Int) = ((i / 8 : Nat) : Int) := rfl

theorem firstCutAfter_iff (g : Time) (j : Nat) :
    Healing.FirstCutAfter (tickRun N1 dg1) j (Healing.cutZ sp1.toParams g) ↔
      j = 8 * (4 * zN g + 1) := by
  rw [cutZ_eq]
  constructor
  · rintro ⟨hlt, hgt⟩
    have h1 : 4 * zN g < j / 8 := by
      have h' : (4 * ((zN g : Nat) : Int) : Int) < ((j / 8 : Nat) : Int) := hgt
      omega
    have h2 : j ≤ 8 * (4 * zN g + 1) := by
      by_contra hc
      have h' : (((8 * (4 * zN g + 1)) / 8 : Nat) : Int) ≤ 4 * ((zN g : Nat) : Int) :=
        hlt _ (by omega)
      omega
    omega
  · rintro rfl
    refine ⟨fun k hk => ?_, ?_⟩
    · change ((k / 8 : Nat) : Int) ≤ 4 * ((zN g : Nat) : Int); omega
    · change 4 * ((zN g : Nat) : Int) < (((8 * (4 * zN g + 1)) / 8 : Nat) : Int); omega

/-- `H_z = slot(ḡ) + 3`: the tip after all events at `c_z = t_{slot(ḡ)+3}`. -/
theorem hz_eq (g : Time) : Healing.HZ (tickRun N1 dg1) Set.univ g = zN g := by
  have hset : {h | ∃ y ∈ (Set.univ : Set (Fin sp1.n)), ∃ j,
      Healing.FirstCutAfter (tickRun N1 dg1) j (Healing.cutZ sp1.toParams g) ∧
        ((tickRun N1 dg1).state y j).fg.hmax = h} = {zN g} := by
    have hmax : ((tickRun N1 dg1).state v0 (8 * (4 * zN g + 1))).fg.hmax = zN g := by
      rw [state_tick, (good_tick _).fg.hmax]
      unfold hexp tip zN; split_ifs <;> omega
    ext h
    simp only [Set.mem_univ, true_and, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, j, hj, rfl⟩
      rw [firstCutAfter_iff] at hj
      rw [eq_v0 rfl y, hj, hmax]
    · rintro rfl
      exact ⟨v0, _, (firstCutAfter_iff g _).2 rfl, hmax⟩
  unfold Healing.HZ
  rw [hset, csSup_singleton]

/-- **The reset `a_z` of the tick run** is `t_{slot(ḡ)+4}`. -/
theorem tickRun_isReset (g : Time) : Healing.IsReset (tickRun N1 dg1) Set.univ g (aZ g) := by
  rw [Healing.IsReset, hz_eq]
  refine ⟨⟨v0, Set.mem_univ _, 8 * (4 * (zN g + 1)) + 5, att (zN g + 1),
    signAt_iff.2 ⟨_, by omega, rfl, rfl⟩, att_h _ (by omega), ?_⟩, fun y _ k a hs ha => ?_⟩
  · change (((8 * (4 * (zN g + 1)) + 5) / 8 : Nat) : Int) = 4 * ((zN g + 1 : Nat) : Int)
    rw [show (8 * (4 * (zN g + 1)) + 5) / 8 = 4 * (zN g + 1) by omega]; push_cast; ring
  · rw [eq_v0 rfl y] at hs
    obtain ⟨s, hs1, rfl, rfl⟩ := signAt_iff.1 hs
    rw [att_h s hs1] at ha
    subst ha
    change 4 * ((zN g + 1 : Nat) : Int) ≤ (((8 * (4 * (zN g + 1)) + 5) / 8 : Nat) : Int)
    rw [show (8 * (4 * (zN g + 1)) + 5) / 8 = 4 * (zN g + 1) by omega]; push_cast; ring_nf; rfl

theorem aZ_nonneg (g : Time) : 0 ≤ aZ g := by unfold aZ; positivity

end Consensus.Goldilocks.Witness.One

end
