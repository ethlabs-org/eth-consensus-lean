module
public import ConsensusProblem.Properties

@[expose] public section

/-! # The consensus problem: claims (layer 0)

A claim says: on every valid run satisfying assumption `A`, property `P` holds,
or the system's excuse holds (`Holds`); unconditional claims have no excuse
(`HoldsAlways`). The assumptions are a `Profile`, fixed and reviewed by the
shape layer for a protocol family; this layer fixes what each property means
and which properties are promised. Bounds are coefficients of the run's `Δ`.

What this layer cannot check: that the profile is realistic and nonvacuous,
that the excuse is meaningful, that `convicts` means misbehaviour. The model
layer fixes the excuse and evidence (and proves every execution premise
satisfiable, `canonical_run`); the shape layer fixes the profile. Satisfiability
of the shape profiles is shown by positive controls (tests), not yet by a
general theorem. -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V]

/-- On valid runs satisfying `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r

/-- On valid runs, `P` holds. -/
def HoldsAlways (S : System V) (P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → P r

/-- The assumptions under which each property is promised. -/
structure Profile (S : System V) where
  /-- For safety of confirmed and stable. -/
  sleepy : S.Run → Prop
  /-- For transaction liveness, with recurrence gap `k`. -/
  live : Nat → S.Run → Prop
  /-- Outage `[b₀, b₁)` after a protected read at `T`, and its fast variant. -/
  outage : Time → Time → Time → S.Run → Prop
  outageFast : Time → Time → Time → S.Run → Prop
  /-- Recovery after GST, with recurrence gap `k`. -/
  recovery : Nat → S.Run → Prop
  /-- Finality after GST, with recurrence gap `k`. -/
  finality : Nat → S.Run → Prop

/-- The reported bounds, as coefficients of the run's `Δ`. -/
structure Bounds where
  catchUp : Nat
  /-- Transaction latency of confirmed and stable, for recurrence gap `k`. -/
  confirmedLive : Nat → Nat
  stableLive : Nat → Nat
  /-- After GST, when recovered safety starts. -/
  recovery : Nat → Nat
  /-- After GST, when finality liveness starts, and its latency. -/
  finStart : Nat → Nat
  finLive : Nat → Nat

/-- `c · Δ` in run `r`. -/
def dur (S : System V) (r : S.Run) (c : Nat) : Time := (c : Time) * (S.trace r).point.env.Δ

/-- The consensus problem for system `S`, profile `Prof` and bounds `B`. -/
structure ProblemClaims (S : System V) (Prof : Profile S) (B : Bounds) : Prop where
  laws : S.Laws
  /-- Unconditional, on valid runs. -/
  nested : S.HoldsAlways (fun r => (S.trace r).Nested .stable .confirmed)
  finalizedMonotone : S.HoldsAlways (fun r => (S.trace r).Monotone .finalized 0)
  nonFraming : S.HoldsAlways (fun r => S.NonFraming r)
  /-- Accountability, on valid runs. -/
  finalizedAccountable : S.Holds (fun _ => True) (fun r => S.AccountablySafe r .finalized 0)
  /-- Safety of the available outputs. -/
  confirmedSafe : S.Holds Prof.sleepy (fun r => (S.trace r).Safe .confirmed 0)
  stableSafe : S.Holds Prof.sleepy (fun r => (S.trace r).Safe .stable 0)
  /-- Transaction liveness. -/
  confirmedLive : ∀ k, S.Holds (Prof.live k)
    (fun r => (S.trace r).TxLive (S.dur r B.catchUp) .confirmed 0 (S.dur r (B.confirmedLive k)))
  stableLive : ∀ k, S.Holds (Prof.live k)
    (fun r => (S.trace r).TxLive (S.dur r B.catchUp) .stable 0 (S.dur r (B.stableLive k)))
  /-- Persistence through an outage. -/
  stablePersists : ∀ T b₀ b₁, S.Holds (Prof.outage T b₀ b₁)
    (fun r => (S.trace r).PersistsThrough (S.dur r B.catchUp) .stable T b₀ b₁)
  stablePersistsFast : ∀ T b₀ b₁, S.Holds (Prof.outageFast T b₀ b₁)
    (fun r => (S.trace r).PersistsThrough (S.dur r B.catchUp) .stable T b₀ b₁)
  /-- Recovered safety, for ready readers. -/
  recovered : ∀ k, S.Holds (Prof.recovery k)
    (fun r => (S.trace r).ReadySafe (S.dur r B.catchUp) .confirmed
        ((S.trace r).point.env.gst + S.dur r (B.recovery k)) ∧
      (S.trace r).ReadySafe (S.dur r B.catchUp) .stable
        ((S.trace r).point.env.gst + S.dur r (B.recovery k)))
  /-- Finality liveness. -/
  finalizedLive : ∀ k, S.Holds (Prof.finality k)
    (fun r => (S.trace r).TxLive (S.dur r B.catchUp) .finalized
      ((S.trace r).point.env.gst + S.dur r (B.finStart k)) (S.dur r (B.finLive k)))

/-- Accountable safety, non-framing and fewer than a third faulty give agreement
of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) {g : Out} {t₀ : Time}
    (hacc : S.AccountablySafe r g t₀) (hnf : S.NonFraming r)
    (hb : (S.trace r).point.BelowOneThird) : (S.trace r).Agree g t₀ := by
  classical
  intro u hu v hv i j hi hj
  rcases hacc u hu v hv i j hi hj with hc | hcard
  · exact hc
  · exfalso
    have hsub : S.convicted r (S.view r u i ∪ S.view r v j) ⊆ (S.trace r).point.faulty := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold convicted at hx; simpa using hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxh => hnf x hxh ?_⟩
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, hu, hL.view_mono r u i _ hi.2 ho⟩
      · exact ⟨v, hv, hL.view_mono r v j _ hj.2 ho⟩
    have := Finset.card_le_card hsub
    unfold EnvPoint.BelowOneThird at hb
    omega

/-- Under the claims, a valid run with fewer than a third faulty has agreeing
finalized reads, or the excuse holds. -/
theorem finalizedAgree_of_claims {S : System V} {Prof : Profile S} {B : Bounds}
    (hC : ProblemClaims S Prof B) (r : S.Run) (hv : S.Valid r)
    (hb : (S.trace r).point.BelowOneThird) :
    (S.trace r).Agree .finalized 0 ∨ S.Excuse r := by
  rcases hC.finalizedAccountable r hv trivial with hacc | hex
  · exact Or.inl (agree_of_accountable S hC.laws r hacc (hC.nonFraming r hv) hb)
  · exact Or.inr hex

end System

end Consensus

end
