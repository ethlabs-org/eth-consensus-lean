module
public import ConsensusLeanTest.Goldilocks.AC.Optimistic
@[expose] public section

/-! # Witnesses for the premises of the Goldilocks ACSteps statement `SourceCompatible`

The hypotheses of A1.9 `SourceCompatible` (`Statements/AC/Steps.lean`) hold together of the run
`trW` of `Goldilocks/AC/Optimistic` (one validator `v0`, `Δ = 1`, `t_s = 4s`, `k = c = 2`,
frame `Φ₁` with tree `{g, B1}` and `F = fc_root = g`, coherent set `U₁ = {g, B1}`, honest set all
of `Fin 1`), so the proved milestone is not vacuous. It is taken at `s = 1`, `m = 3`: `v0`'s
optimistic fast lock of slot `1` on `B1` at cut 0, its slot-`2` vote at cut 1 (branch (i)), and
its `ac_to_fg` call at cut 2, time `12 ∈ (t_2 + Δ, t_3 + Δ] = (9, 13]`, which returns `B1`.

`sourceCompatible_premises_satisfiable` states, at `sp1`, `FGP := Unit`, `ro1`, that there are
values of all the statement's universally bound variables satisfying `ACRun` and every hypothesis
(copied from the statement); `sourceCompatible_on_witness` applies the proved milestone
(`acStepsAt`) to the run.

Limitations: `n = 1` and `f = 0`. The fast lock has the optimistic origin (the only update of
`trW` is of slot `2`, at cut 3, after the call). The returned block is `B` itself, so the
conclusion `Compatible U₁ B1 B1` is reflexive; indeed every two blocks of `U₁` are compatible
(`compatible_U₁`: `U₁` is a chain). A conclusion that could fail needs a block of `U`
incompatible with `B`, i.e. a second block on genesis, which this run does not have. -/

namespace Consensus.Goldilocks.SA.Test

/-! ## The premises -/

/-- `Carry(1, S, B1)`: the only honest slot-`2` vote is `v0`'s at cut 1 (`carry_W`). -/
theorem carryAll_W : Carry trW Set.univ U₁ 1 CV1 := fun y _ i e he hs => by
  obtain rfl : y = v0 := Subsingleton.elim _ _
  rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hs (by decide)
  · exact carry_W

/-- Every honest vote before cut 2 of a slot in `(1, 3]` extends `B1`: the only one is `vote2`,
on `B1`. -/
theorem earlierSlots_W : ∀ z ∈ (Set.univ : Set (Fin sp1.n)), ∀ j < 2, ∀ e, VoteAt trW z j e →
    1 < e.msg.slot → e.msg.slot ≤ 3 → VoteExtends U₁ e.msg B1 := fun _ _ j _ e he hs _ => by
  rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact absurd hs (by decide)
  · exact ⟨B1, B1_mem, rfl, Relation.ReflTransGen.refl⟩

/-- Branch (i): `v0` cast its slot-`2` vote at cut 1, with `F = g` compatible with `B1`. -/
theorem castBefore_W : ∃ j < 2, ∃ ℓ' e, CastAt trW v0 j ℓ' e ∧ e.msg.slot = 1 + 1 ∧
    Compatible U₁ ℓ'.frame.F B1 :=
  ⟨1, by decide, ℓ1, e1, castAt_W, rfl, compatible_U₁ g_mem B1_mem⟩

/-! ## The witness -/

/-- (a) **A1.9, `SourceCompatible`: the premises are satisfiable.** Every hypothesis of the
statement holds of the run at `s = 1`, `m = 3`, `C = B1`: `v0`'s fast lock of slot `1` on `B1` at
cut 0 (optimistic origin), its slot-`2` vote at cut 1, and its `ac_to_fg` call at cut 2, time
`12`, returning `B1`. -/
theorem sourceCompatible_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : SATrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (s m : Nat) (w x : Fin sp1.n) (i₀ i : Nat)
      (B : Blk sp1.n Unit) (CV : Set (Vote sp1.n)) (ℓ : ACLabel (goldilocksSA sp1 Unit ro1))
      (C : Blk sp1.n Unit),
    sp1.committeeSize = sp1.n ∧ ACRun proposer tr H U ∧
    w ∈ H ∧ FastLockAt tr w i₀ s B CV ∧
    SyncAC (goldilocksSA sp1 Unit ro1) H U (sp1.ts s) (sp1.ts (s + 1 : Nat) + sp1.Δ) tr ∧
    Carry tr H U s CV ∧ 2 * Hᶜ.ncard < sp1.n ∧
    x ∈ H ∧ ToFGAt tr x i ℓ C ∧
    sp1.ts (s + 1 : Nat) + sp1.Δ < tr.time i ∧ tr.time i ≤ sp1.ts m + sp1.Δ ∧
    (∀ z ∈ H, ∀ j < i, ∀ e, VoteAt tr z j e → s < e.msg.slot → e.msg.slot ≤ m →
      VoteExtends U e.msg B) ∧
    ((∃ j < i, ∃ ℓ' e, CastAt tr x j ℓ' e ∧ e.msg.slot = s + 1 ∧ Compatible U ℓ'.frame.F B) ∨
      (∃ k < i, tr.RestartAt x k ∧ sp1.ts s < tr.time k)) :=
  ⟨Set.univ, U₁, trW, fun _ => v0, 1, 3, v0, v0, 0, 2, B1, CV1, ℓ2, B1, rfl, acRun_W, trivial,
    Or.inr optimisticLock_W, sync_W (by decide), carryAll_W, faults_W, trivial, toFG_W,
    by decide, by decide, earlierSlots_W, Or.inl castBefore_W⟩

/-! ## The milestone on the witness -/

/-- (a) A1.9 on the run: the block `B1` that `ac_to_fg` returns at cut 2 is compatible with the
locked block `B1`. -/
theorem sourceCompatible_on_witness : Compatible U₁ B1 B1 :=
  (acStepsAt sp1).sourceCompatible Unit ro1 Set.univ U₁ trW (fun _ => v0) rfl acRun_W 1 3 v0 v0
    0 2 B1 CV1 ℓ2 B1 trivial (Or.inr optimisticLock_W) (sync_W (by decide)) carryAll_W faults_W
    trivial toFG_W (by decide) (by decide) earlierSlots_W (Or.inl castBefore_W)

end Consensus.Goldilocks.SA.Test

end
