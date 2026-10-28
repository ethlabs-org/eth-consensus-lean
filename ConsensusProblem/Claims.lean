module
public import ConsensusProblem.Properties

@[expose] public section

/-! # The consensus problem: claims (layer 0)

A claim is "under assumption `A`, property `P` holds, or the system's excuse
holds" (`Holds`), or, for unconditional claims, "under `A`, `P` holds"
(`HoldsAlways`). The assumptions are a `Profile`: a parameter, fixed by the
shape layer for a protocol family and reviewed there; this layer fixes what
each property means and which properties are promised. `ProblemClaims S Prof B`
is the whole problem for system `S`, profile `Prof` and bounds `B`.

What this layer cannot check: that the profile is realistic and nonvacuous,
that the excuse is meaningful, and that `convicts` means misbehaviour. The
model layer fixes the excuse (an observed hash collision) and evidence; the
shape layer fixes the profile and proves it realizable with active deadlines. -/

namespace Consensus

open AvailableChain (Time)

namespace System

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Under `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, A r → P r ∨ S.Excuse r

/-- Under `A`, `P` holds (no excuse). -/
def HoldsAlways (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, A r → P r

/-- The assumptions under which each property is promised. -/
structure Profile (S : System V) where
  /-- Validity, for the unconditional claims. -/
  valid : S.Run → Prop
  /-- Sleepy: for safety of confirmed and stable. -/
  sleepy : S.Run → Prop
  /-- Sleepy with recurrence gap `k`: for transaction liveness. -/
  live : Nat → S.Run → Prop
  /-- Outage `[b₀, b₁)` after a protected read at `T`, and its fast variant. -/
  outage : Time → Time → Time → S.Run → Prop
  outageFast : Time → Time → Time → S.Run → Prop
  /-- Recovery after GST with recurrence gap `k`. -/
  recovery : Nat → S.Run → Prop
  /-- Finality after GST with recurrence gap `k`. -/
  finality : Nat → S.Run → Prop

/-- The reported bounds (durations). -/
structure Bounds where
  catchUp : Time
  /-- Transaction latency of confirmed and stable for recurrence gap `k`. -/
  confirmedLive : Nat → Time
  stableLive : Nat → Time
  /-- Time after GST from which recovered safety holds. -/
  recovery : Nat → Time
  /-- Time after GST from which finality liveness holds, and its latency. -/
  finStart : Nat → Time
  finLive : Nat → Time

/-- The consensus problem for system `S`, profile `Prof` and bounds `B`. -/
structure ProblemClaims (S : System V) (Prof : Profile S) (B : Bounds) : Prop where
  laws : S.Laws
  /-- Unconditional (under validity). -/
  nested : S.HoldsAlways Prof.valid (fun r => S.Nested r .stable .confirmed)
  finalizedMonotone : S.HoldsAlways Prof.valid (fun r => S.Monotone r .finalized 0)
  nonFraming : S.HoldsAlways Prof.valid (fun r => S.NonFraming r)
  /-- Accountability. -/
  finalizedAccountable : S.Holds Prof.valid (fun r => S.AccountablySafe r .finalized 0)
  /-- Safety of the available outputs. -/
  confirmedSafe : S.Holds Prof.sleepy (fun r => S.Safe r .confirmed 0)
  stableSafe : S.Holds Prof.sleepy (fun r => S.Safe r .stable 0)
  /-- Transaction liveness. -/
  confirmedLive : ∀ k, S.Holds (Prof.live k)
    (fun r => S.TxLive r B.catchUp .confirmed 0 (B.confirmedLive k))
  stableLive : ∀ k, S.Holds (Prof.live k)
    (fun r => S.TxLive r B.catchUp .stable 0 (B.stableLive k))
  /-- Persistence through an outage. -/
  stablePersists : ∀ T b₀ b₁, S.Holds (Prof.outage T b₀ b₁)
    (fun r => S.PersistsThrough r B.catchUp .stable T b₀ b₁)
  stablePersistsFast : ∀ T b₀ b₁, S.Holds (Prof.outageFast T b₀ b₁)
    (fun r => S.PersistsThrough r B.catchUp .stable T b₀ b₁)
  /-- Recovered safety for ready readers. -/
  recovered : ∀ k, S.Holds (Prof.recovery k)
    (fun r => S.ReadySafe r B.catchUp .confirmed ((S.env r).gst + B.recovery k) ∧
      S.ReadySafe r B.catchUp .stable ((S.env r).gst + B.recovery k))
  /-- Finality liveness. -/
  finalizedLive : ∀ k, S.Holds (Prof.finality k)
    (fun r => S.TxLive r B.catchUp .finalized ((S.env r).gst + B.finStart k) (B.finLive k))

/-- Accountable safety, non-framing and fewer than a third faulty give
agreement of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) {g : Out} {t₀ : Time}
    (hacc : S.AccountablySafe r g t₀) (hnf : S.NonFraming r) (hb : S.BelowOneThird r) :
    S.Agree r g t₀ := by
  classical
  intro u hu v hv i j hi hj
  rcases hacc u hu v hv i j hi hj with hc | hcard
  · exact hc
  · exfalso
    have hsub : S.convicted r (S.view r u i ∪ S.view r v j) ⊆
        Finset.univ \ (S.env r).honest := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold convicted at hx; simpa using hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxh => hnf x hxh ?_⟩
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, hu, hL.view_mono r u i (S.cuts r) hi.2 ho⟩
      · exact ⟨v, hv, hL.view_mono r v j (S.cuts r) hj.2 ho⟩
    have := Finset.card_le_card hsub
    unfold BelowOneThird at hb
    omega

/-- Under the problem claims, a valid run with fewer than a third faulty has
agreeing finalized reads, or the excuse holds. -/
theorem finalizedAgree_of_claims {S : System V} {Prof : Profile S} {B : Bounds}
    (hC : ProblemClaims S Prof B) (r : S.Run) (hv : Prof.valid r) (hb : S.BelowOneThird r) :
    S.Agree r .finalized 0 ∨ S.Excuse r := by
  rcases hC.finalizedAccountable r hv with hacc | hex
  · exact Or.inl (agree_of_accountable S hC.laws r hacc (hC.nonFraming r hv) hb)
  · exact Or.inr hex

end System

end Consensus

end
