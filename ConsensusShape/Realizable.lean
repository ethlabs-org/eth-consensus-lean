module
public import ConsensusShape.Regimes
public import ConsensusModelProofs.Canonical
public import Mathlib.Tactic

@[expose] public section
namespace Consensus.Shape
open Model Run

/-- The fully participating synchronous environment. -/
def realizableEnv (V : Type) : Env V := ⟨1, by decide, 0, fun _ _ => true⟩

/-- An injective hash with reserved zero unused. -/
def realizableHash (h : Header) : Nat := Encodable.encode h + 1

/-- All service guards we activate, including recovered and finalized service. -/
def serviceBounds (C : Constants) (k : Nat) : List Nat :=
  [C.D_c, C.D_s, C.D_f, C.growth.eval k, C.stableGrowth.eval k,
   C.recovery.eval k, C.recovery.eval k + C.recGrowth.eval k,
   C.finStart.eval k + C.finDelay.eval k]

/-- Active guards, independently of what a protocol outputs: a positive ready
proposal after recovery and finality startup, with every reported service
deadline in the horizon, ready readers there, a nonvacuous recurrence window,
and a transaction submitted strictly before the proposal. -/
def ActiveGuards {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {F : Family} {E : Env V} (r : Model.Run (compiled F) E) (C : Constants) (k : Nat) : Prop :=
  ∃ s, 0 < (protoOf F E).proposalTime s ∧
    E.gst + (C.recovery.eval k : Time) * E.Δ < (protoOf F E).proposalTime s ∧
    E.gst + (C.finStart.eval k : Time) * E.Δ < (protoOf F E).proposalTime s ∧
    (k : Time) * (protoOf F E).slotLen ≤ r.horizon ∧
    ReadyProposer r ((C.catchUp : Time) * E.Δ) s ∧
    r.point.SubmittedToAll 42 0 ∧
    ∀ d ∈ serviceBounds C k,
      (protoOf F E).proposalTime s + (d : Time) * E.Δ ≤ r.horizon ∧
      (r.point.readyAt ((C.catchUp : Time) * E.Δ)
        ((protoOf F E).proposalTime s + (d : Time) * E.Δ)).Nonempty

/-- Every regime is realizable for every family and valid constants. One
validator suffices. The same run realizes them all, with a nonempty outage,
a protected reader, and active inclusion and liveness deadlines. No conditions
on `C` beyond `Valid` are needed; in particular its positive budget permits
the nonempty outage. The family need not satisfy `ShapeClaims`. -/
theorem profile_realizable (F : Family) (C : Constants) (hC : C.Valid)
    (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (k : Nat) (hk : 1 ≤ k) :
    ∃ r : Model.Run (compiled F) (realizableEnv V),
      r.InjectiveHash ∧ ActiveGuards r C k ∧
      Sleepy r C ∧ StableSleepy r C ∧ Fast r C ∧ LiveSleepy r C k ∧
      Recovery r C k ∧ Finality r C k ∧
      ∃ T b₀ b₁, T < b₀ ∧ b₀ < b₁ ∧ Outage r C T b₀ b₁ ∧ FastOutage r C T b₀ b₁ ∧
        ∃ w ∈ r.honest, r.point.AwakeOnClosed w (max 0 (b₀ - (C.catchUp : Time) - 1)) b₀ := by
  classical
  dsimp only [Time] at *
  let E := realizableEnv V
  let P := protoOf F E
  let L := P.slotLen
  have hL : 0 < L := P.slotLen_pos
  let B := (serviceBounds C k).sum
  let T := P.proposalTime (B + 1)
  have hT : (B : Int) < T := by
    change (B : Int) < ((B + 1 : Nat) : Int) * L
    push_cast
    have : 1 ≤ L := by
      simp only [Time] at *
      omega
    nlinarith
  have hkL : 0 ≤ (k : Int) * L := mul_nonneg (by positivity) hL.le
  let H : Int := T + (B : Int) + (C.armingLag : Int) + (C.budget : Int) + (k : Int) * L + 2
  have hH : 0 ≤ H := by dsimp only [H, Time] at *; omega
  let holder : (ℓ : (Model.protoOf (compiled F) E).Label) →
      Fin ((Model.protoOf (compiled F) E).seats ℓ) ↪ V := fun ℓ =>
    match ℓ with
    | .inl _ => (Fintype.equivFin V).symm.toEmbedding
    | .inr _ => ⟨fun _ => Classical.choice inferInstance, fun a b _ => by
        have ha : a.val = 0 := by
          have := a.isLt
          change a.val < min 1 (Fintype.card V) at this
          omega
        have hb : b.val = 0 := by
          have := b.isLt
          change b.val < min 1 (Fintype.card V) at this
          omega
        exact Fin.ext (ha.trans hb.symm)⟩
  let submit : V → Time → List Tx := fun _ t => if t = 0 then [42] else []
  obtain ⟨es, valid, sync, healthy⟩ := Model.canonical_run (compiled F) V E
    Finset.univ H hH holder submit realizableHash
  let r := Model.mkRun (F := compiled F) (E := E) Finset.univ H holder submit realizableHash es
  have ready : ∀ c t, r.point.readyAt c t = Finset.univ := by
    intro c t; ext v
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, r, Model.mkRun, Model.Run.point,
      E, realizableEnv]
  have rp : ∀ c s, ReadyProposer r c s := by
    intro c s
    exact ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩
  have faulty : r.point.faulty = ∅ := by simp [EnvPoint.faulty, r, Model.mkRun, Model.Run.point]
  have majority : ∀ t, r.point.ReadyMajority ((C.catchUp : Int) * E.Δ) t := by
    intro t; simp [EnvPoint.ReadyMajority, ready, faulty, Fintype.card_pos]
  have full : ∀ start, r.point.FullParticipation start := by intro _ _ _ _ _ _; rfl
  have npos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have eta : ∀ t, r.point.EtaSleepy ((C.catchUp : Int) * E.Δ) C.θ ((C.η : Int) * E.Δ) t := by
    intro t
    have awake : r.point.awakeIn (t - (C.η : Int) * E.Δ) t = Finset.univ := by
      ext v
      simp only [EnvPoint.awakeIn, Finset.mem_filter, Finset.mem_univ]
      constructor
      · intro _; trivial
      · intro _
        exact ⟨Finset.mem_univ _, t, by simp [E, realizableEnv], le_rfl, rfl⟩
    unfold EnvPoint.EtaSleepy
    rw [awake, faulty, ready]
    simp only [Finset.union_empty, Finset.card_univ]
    have := hC.theta_upper
    nlinarith
  have recur : Recurrence r ((C.catchUp : Int) * E.Δ) 0 k := by
    intro t ht _
    have hq : 0 ≤ t / L + 1 := by
      have := Int.ediv_nonneg ht hL.le
      simp only [Time] at *
      omega
    refine ⟨(t / L + 1).toNat, ?_, ?_, rp _ _⟩
    · change t < ((t / L + 1).toNat : Int) * L
      rw [Int.toNat_of_nonneg hq]
      have := Int.emod_lt_of_pos t hL
      have := Int.mul_ediv_add_emod t L
      nlinarith
    · change ((t / L + 1).toNat : Int) * L ≤ t + (k : Int) * L
      rw [Int.toNat_of_nonneg hq]
      have := Int.emod_nonneg t hL.ne'
      have := Int.mul_ediv_add_emod t L
      have hk' : (1 : Int) ≤ k := by exact_mod_cast hk
      nlinarith
  have sleepy : Sleepy r C := ⟨valid, sync, rfl, fun t _ _ => majority t⟩
  have recovery : Recovery r C k := by
    refine ⟨valid, sync, ?_, fun _ => full _, ?_, recur, ?_⟩
    · intro t _ _; rw [ready, faulty]
      simp only [Finset.card_univ, Finset.card_empty, Nat.cast_zero, add_zero]
      have := hC.thetaRec_upper
      nlinarith
    · simp [Wakes, E, realizableEnv]
    · have hb : C.recovery.eval k ≤ B :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by simp [serviceBounds])
      change 0 + (C.recovery.eval k : Int) * 1 ≤ H
      simp only [zero_add, mul_one]
      dsimp only [H, Time] at *; omega
  have outage : Outage r C T (T + C.armingLag + 1) (T + C.armingLag + 2) := by
    refine ⟨valid, healthy _, ?_, ?_, ?_, fun t _ _ => majority t, fun t _ _ => eta t⟩
    · change 0 ≤ T ∧ T ≤ T + C.armingLag + 1 ∧
        T + C.armingLag + 1 ≤ T + C.armingLag + 2 ∧ T + C.armingLag + 2 ≤ H
      dsimp only [H, Time] at *; omega
    · change T + (C.armingLag : Int) * 1 ≤ T + C.armingLag + 1
      simp only [Time] at *
      omega
    · change T + C.armingLag + 2 - (T + C.armingLag + 1) ≤ (C.budget : Int) * 1
      have := hC.budget_pos; simp only [Time] at *; omega
  refine ⟨r, ?_, ?_, sleepy, ⟨sleepy, fun t _ _ => eta t⟩,
    ⟨sleepy, full 0, ?_⟩, ⟨sleepy, recur⟩, recovery, ⟨recovery, ?_, ?_⟩,
    T, T + C.armingLag + 1, T + C.armingLag + 2, by omega, by omega, outage, ?_, ?_⟩
  · constructor
    · intro a b h; exact Encodable.encode_injective (Nat.add_right_cancel h)
    · intro h; exact Nat.succ_ne_zero _
  · have hrec : C.recovery.eval k ≤ B :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by simp [serviceBounds])
    have hfin : C.finStart.eval k + C.finDelay.eval k ≤ B :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by simp [serviceBounds])
    refine ⟨B + 1, ?_, ?_, ?_, ?_, rp _ _, ?_, ?_⟩
    · exact lt_of_le_of_lt (by positivity : (0 : Int) ≤ B) hT
    · change 0 + (C.recovery.eval k : Int) * 1 < T
      omega
    · change 0 + (C.finStart.eval k : Int) * 1 < T
      omega
    · change (k : Int) * L ≤ H
      dsimp only [H, Time] at *
      omega
    · intro v _; exact ⟨0, le_rfl, le_rfl, by simp [r, Model.mkRun, Model.Run.point, submit]⟩
    · intro d hd
      have hb : d ≤ B := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hd
      constructor
      · change T + (d : Int) * 1 ≤ H
        dsimp only [H, Time] at *; omega
      · rw [ready]; exact Finset.univ_nonempty
  · simp [EnvPoint.BelowQuarter, faulty, Fintype.card_pos]
  · simp [EnvPoint.BelowOneThird, faulty, Fintype.card_pos]
  · intro t _ _; rw [ready]; simp only [Finset.card_univ]
    have := Fintype.card_pos (α := V); simp only [Time] at *; omega
  · refine ⟨?_, ?_⟩
    · refine ⟨valid, healthy _, outage.interval, ?_, outage.withinBudget,
        outage.readyBefore, outage.etaSleepyBefore⟩
      change T + (C.fastArmingLag : Int) * 1 ≤ T + C.armingLag + 1
      have := hC.fastArmingLag_le
      simp only [Time] at *; omega
    · intro t _ _; rw [ready]; simp only [Finset.card_univ]; simp only [Time] at *; omega
  · exact ⟨Classical.choice inferInstance, Finset.mem_univ _, fun _ _ _ => rfl⟩

end Consensus.Shape
end
