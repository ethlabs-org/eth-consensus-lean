module
public import ConsensusShape.Claims
@[expose] public section
namespace Consensus.Shape
open Run
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family}

def bounds (C : Constants) : System.Bounds where
  confirmedLive k := C.growth.eval k
  stableLive k := C.stableGrowth.eval k
  recovery k := C.recovery.eval k
  finStart k := C.finStart.eval k
  finLive k := C.finDelay.eval k

/-- The only exported interpretation of the L0 execution slots for this shape. -/
def profile (A : Assumptions) : System.ExecProfile (Model.sysOf (compiled F) V) where
  sync r := r.2.PartialSynchrony
  healthyUntil t r := r.2.HealthyPrefixDelivery t
  recurrent start k r := Recurrence r.2 ((A.catchUp : Time) * r.1.Δ) start k

theorem profile_congr {A A' : Assumptions} (hc : A.catchUp = A'.catchUp) :
    profile (F := F) (V := V) A = profile A' := by
  simp only [profile, hc]

def RefinementStatement (F : Family) (C : Constants) (A : Assumptions) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] : Prop :=
  ShapeClaims F A C → System.ProblemClaims (Model.sysOf (compiled F) V) A (bounds C) (profile A)

variable {E : Env V} (rho : Model.Run (compiled F) E) (A : Assumptions) (C : Constants)

abbrev Premise (q : System.ClaimKey) :=
  (Model.sysOf (compiled F) V).Premise A (bounds C) (profile A) q ⟨E, rho⟩

theorem sleepy_iff : Sleepy rho A ↔ rho.ExecutionValid ∧ Premise rho A C .sleepy := by
  constructor
  · intro h; exact ⟨h.valid, ⟨h.gst_zero, h.participation⟩, h.sync⟩
  · rintro ⟨hv, ⟨hg, hp⟩, hs⟩; exact ⟨hv, hs, hg, hp⟩

theorem stableInclusion_iff : StableSleepy rho A ↔
    rho.ExecutionValid ∧ Premise rho A C .stableInclusion := by
  constructor
  · intro h; exact ⟨h.valid, ⟨⟨h.gst_zero, h.participation⟩, h.etaSleepy⟩, h.sync⟩
  · rintro ⟨hv, ⟨⟨hg, hp⟩, he⟩, hs⟩; exact ⟨⟨hv, hs, hg, hp⟩, he⟩

theorem fastInclusion_iff : Fast rho A ↔
    rho.ExecutionValid ∧ Premise rho A C .fastInclusion := by
  constructor
  · intro h; exact ⟨h.valid, ⟨⟨h.gst_zero, h.participation⟩, h.full, h.belowQuarter⟩, h.sync⟩
  · rintro ⟨hv, ⟨⟨hg, hp⟩, hf, hb⟩, hs⟩; exact ⟨⟨hv, hs, hg, hp⟩, hf, hb⟩

theorem live_iff (k : Nat) : LiveSleepy rho A k ↔
    rho.ExecutionValid ∧ Premise rho A C (.live k) := by
  constructor
  · intro h; exact ⟨h.valid, ⟨h.gst_zero, h.participation⟩, h.sync, h.recurrence⟩
  · rintro ⟨hv, ⟨hg, hp⟩, hs, hr⟩; exact ⟨⟨hv, hs, hg, hp⟩, hr⟩

theorem outage_iff (T b₀ b₁ : Time) : Outage rho A T b₀ b₁ ↔
    rho.ExecutionValid ∧ Premise rho A C (.outage T b₀ b₁) := by
  constructor
  · intro h; exact ⟨h.valid, ⟨h.interval, h.armed, h.withinBudget, h.readyBefore,
      h.etaSleepyBefore⟩, h.healthy⟩
  · rintro ⟨hv, ⟨hi, ha, hb, hr, he⟩, hh⟩; exact ⟨hv, hh, hi, ha, hb, hr, he⟩

theorem fastOutage_iff (T b₀ b₁ : Time) : FastOutage rho A T b₀ b₁ ↔
    rho.ExecutionValid ∧ Premise rho A C (.fastOutage T b₀ b₁) := by
  constructor
  · intro h; exact ⟨h.valid, ⟨⟨h.interval, h.armed, h.withinBudget, h.readyBefore,
      h.etaSleepyBefore⟩, h.highParticipation⟩, h.healthy⟩
  · rintro ⟨hv, ⟨⟨hi, ha, hb, hr, he⟩, hp⟩, hh⟩
    exact ⟨⟨hv, hh, hi, ha, hb, hr, he⟩, hp⟩

theorem recovery_iff (k : Nat) : Recovery rho A C k ↔
    rho.ExecutionValid ∧ Premise rho A C (.recovery k) := by
  constructor
  · intro h; exact ⟨h.valid, ⟨h.participation, h.full, h.noWakeAfterGST, h.horizon⟩,
      h.sync, h.recurrence⟩
  · rintro ⟨hv, ⟨hp, hf, hn, hh⟩, hs, hr⟩; exact ⟨hv, hs, hp, hf, hn, hr, hh⟩

theorem finality_iff (k : Nat) : Finality rho A C k ↔
    rho.ExecutionValid ∧ Premise rho A C (.finality k) := by
  constructor
  · intro h; exact ⟨h.valid, ⟨⟨h.participation, h.full, h.noWakeAfterGST, h.horizon⟩,
      h.finParticipation⟩, h.sync, h.recurrence⟩
  · rintro ⟨hv, ⟨⟨hp, hf, hn, hh⟩, hfin⟩, hs, hr⟩
    exact ⟨⟨hv, hs, hp, hf, hn, hr, hh⟩, hfin⟩
end Consensus.Shape
end
