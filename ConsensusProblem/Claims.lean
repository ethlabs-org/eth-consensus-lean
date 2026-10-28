module
public import ConsensusProblem.Properties
public import ConsensusProblem.Assumptions

@[expose] public section

/-! L0 fixes the environment assumptions and the closed execution-slot
mapping per claim. L1 publishes A and instantiates the reviewed slots. Recovery
and accountability expose the accountable-fraction escape explicitly. -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V]

/-- On valid runs satisfying `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r

/-- On valid runs, `P` holds. -/
def HoldsAlways (S : System V) (P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → P r

/-- The reported bounds, as coefficients of the run's `Δ`. -/
structure Bounds where
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

/-- Reviewed execution slots, interpreted by the model and shape libraries. -/
structure ExecProfile (S : System V) where
  sync : S.Run → Prop
  healthyUntil : Time → S.Run → Prop
  recurrent : Time → Nat → S.Run → Prop

inductive ClaimKey where
  | sleepy | stableInclusion | fastInclusion
  | live (k : Nat)
  | outage (T b₀ b₁ : Time)
  | fastOutage (T b₀ b₁ : Time)
  | recovery (k : Nat)
  | finality (k : Nat)
  deriving DecidableEq

/-- The environment part of every reviewed claim. -/
def EnvAssumption (A : Assumptions) (B : Bounds) (q : ClaimKey)
    (p : EnvPoint V) : Prop :=
  let c := (A.catchUp : Time) * p.env.Δ
  let sleepy := p.env.gst = 0 ∧ EnvPoint.Throughout 0 p.horizon (p.ReadyAbove A.sleepyReadyAbove c)
  let eta := ∀ t, 0 ≤ t → t ≤ p.horizon →
    p.EtaSleepy A.stableEtaAbove ((A.eta : Time) * p.env.Δ) c t
  let outage := fun lag T b₀ b₁ =>
    (0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ p.horizon) ∧
    T + (lag : Time) * p.env.Δ ≤ b₀ ∧
    b₁ - b₀ ≤ (A.outageBudget : Time) * p.env.Δ ∧
    (∀ t, 0 ≤ t → t < b₀ → p.ReadyAbove A.sleepyReadyAbove c t) ∧
    (∀ t, 0 ≤ t → t < b₀ → p.EtaSleepy A.stableEtaAbove ((A.eta : Time) * p.env.Δ) c t)
  let recovery := fun k =>
    EnvPoint.Throughout p.env.gst p.horizon (p.ReadyAbove A.recovery.readyAbove c) ∧
    (A.recovery.requireFull = true → p.FullParticipation p.env.gst) ∧
    (A.recovery.noWakeAfterGST = true → p.NoWakeFrom p.env.gst) ∧
    p.env.gst + (B.recovery k : Time) * p.env.Δ ≤ p.horizon
  match q with
  | .sleepy | .live _ => sleepy
  | .stableInclusion => sleepy ∧ eta
  | .fastInclusion => sleepy ∧ p.FullParticipation 0 ∧ p.FaultsBelow A.fastFaultsBelow
  | .outage T b₀ b₁ => outage A.armingLag T b₀ b₁
  | .fastOutage T b₀ b₁ => outage A.fastArmingLag T b₀ b₁ ∧
      ∀ t, 0 ≤ t → t < b₀ → p.ReadyOfAllAtLeast A.fastOutageReadyAtLeast c t
  | .recovery k => recovery k
  | .finality k => recovery k ∧
      EnvPoint.Throughout p.env.gst p.horizon (p.ReadyOfAll A.finalityReadyOfAll c)

/-- The claim-to-slot mapping is fixed here, with paired outage branches. -/
def Exec (S : System V) (X : ExecProfile S) (q : ClaimKey) (r : S.Run) : Prop :=
  match q with
  | .sleepy | .stableInclusion | .fastInclusion => X.sync r
  | .live k => X.sync r ∧ X.recurrent 0 k r
  | .outage _ b₀ _ | .fastOutage _ b₀ _ => X.healthyUntil b₀ r
  | .recovery k | .finality k => X.sync r ∧ X.recurrent (S.trace r).point.env.gst k r

def Premise (S : System V) (A : Assumptions) (B : Bounds) (X : ExecProfile S)
    (q : ClaimKey) (r : S.Run) : Prop :=
  EnvAssumption A B q (S.trace r).point ∧ Exec S X q r

/-- Accountability escape for the whole honest evidence set. -/
def Slashed (S : System V) (α : ℚ) (r : S.Run) : Prop :=
  (Fintype.card V : ℚ) * α ≤ (S.convicted r (S.honestEvidence r)).card

def HoldsAccountable (S : System V) (α : ℚ) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r ∨ S.Slashed α r

structure ProblemClaims (S : System V) (A : Assumptions) (B : Bounds)
    (X : ExecProfile S) : Prop where
  laws : S.Laws
  nested : S.HoldsAlways (fun r => (S.trace r).Nested .finalized .stable ∧
    (S.trace r).Nested .stable .confirmed)
  finalizedMonotone : S.HoldsAlways (fun r => (S.trace r).Monotone .finalized 0)
  nonFraming : S.HoldsAlways (fun r => S.NonFraming r)
  finalizedAccountable : S.HoldsAccountable A.accFrac (fun _ => True)
    (fun r => S.AccountablySafe r A.accFrac .finalized 0)
  confirmedSafe : S.Holds (S.Premise A B X .sleepy) (fun r => (S.trace r).Safe .confirmed 0)
  stableSafe : S.Holds (S.Premise A B X .sleepy) (fun r => (S.trace r).Safe .stable 0)
  confirmedLive : ∀ k, S.Holds (S.Premise A B X (.live k))
    (fun r => (S.trace r).TxLive (S.dur r A.catchUp) .confirmed 0 (S.dur r (B.confirmedLive k)))
  stableLive : ∀ k, S.Holds (S.Premise A B X (.live k))
    (fun r => (S.trace r).TxLive (S.dur r A.catchUp) .stable 0 (S.dur r (B.stableLive k)))
  stablePersists : ∀ T b₀ b₁, S.Holds (S.Premise A B X (.outage T b₀ b₁))
    (fun r => (S.trace r).PersistsThrough (S.dur r A.catchUp) .stable T b₀ b₁)
  stablePersistsFast : ∀ T b₀ b₁, S.Holds (S.Premise A B X (.fastOutage T b₀ b₁))
    (fun r => (S.trace r).PersistsThrough (S.dur r A.catchUp) .stable T b₀ b₁)
  recovered : ∀ k, S.HoldsAccountable A.accFrac (S.Premise A B X (.recovery k))
    (fun r => (S.trace r).ReadySafe (S.dur r A.catchUp) .confirmed
        ((S.trace r).point.env.gst + S.dur r (B.recovery k)) ∧
      (S.trace r).ReadySafe (S.dur r A.catchUp) .stable
        ((S.trace r).point.env.gst + S.dur r (B.recovery k)))
  finalizedLive : ∀ k, S.Holds (S.Premise A B X (.finality k))
    (fun r => (S.trace r).TxLive (S.dur r A.catchUp) .finalized
      ((S.trace r).point.env.gst + S.dur r (B.finStart k)) (S.dur r (B.finLive k)))

/-- Accountable safety, non-framing and faults below the accountable fraction give agreement
of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) {g : Out} {t₀ : Time}
    {α : ℚ} (hacc : S.AccountablySafe r α g t₀) (hnf : S.NonFraming r)
    (hb : (S.trace r).point.FaultsBelow α) : (S.trace r).Agree g t₀ := by
  classical
  intro u hu v hv i j hi hj
  rcases hacc u hu v hv i j hi hj with hc | hcard
  · exact hc
  · exfalso
    have hsub : S.convicted r (S.view r u i ∪ S.view r v j) ⊆ (S.trace r).point.faulty := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold convicted Consensus.convicted at hx; simpa using hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxh => hnf x hxh ?_⟩
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, hu, hL.view_mono r u i _ hi.2 ho⟩
      · exact ⟨v, hv, hL.view_mono r v j _ hj.2 ho⟩
    change (Fintype.card V : ℚ) * α ≤
      (S.convicted r (S.view r u i ∪ S.view r v j)).card at hcard
    have hc : ((S.convicted r (S.view r u i ∪ S.view r v j)).card : ℚ) ≤
        (S.trace r).point.faulty.card := by exact_mod_cast Finset.card_le_card hsub
    unfold EnvPoint.FaultsBelow at hb
    linarith

/-- Non-framing and a strict fault cap exclude the global slashing escape. -/
theorem not_slashed_of_nonFraming (S : System V) (r : S.Run) {α : ℚ}
    (hnf : S.NonFraming r) (hb : (S.trace r).point.FaultsBelow α) : ¬ S.Slashed α r := by
  classical
  have hsub : S.convicted r (S.honestEvidence r) ⊆ (S.trace r).point.faulty := by
    intro v hv
    have hc : S.convicts r (S.honestEvidence r) v := (Finset.mem_filter.mp hv).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hnf v hh hc⟩
  have hc : ((S.convicted r (S.honestEvidence r)).card : ℚ) ≤
      (S.trace r).point.faulty.card := by exact_mod_cast Finset.card_le_card hsub
  unfold Slashed EnvPoint.FaultsBelow at *
  intro hs
  linarith

/-- The accountable fraction is also the strict fault cap needed to derive
finalized agreement, including elimination of the global slashing escape. -/
theorem finalizedAgree_of_claims {S : System V} {A : Assumptions} {B : Bounds}
    {X : ExecProfile S} (hc : ProblemClaims S A B X) (r : S.Run) (hv : S.Valid r)
    (hb : (S.trace r).point.FaultsBelow A.accFrac) :
    (S.trace r).Agree .finalized 0 ∨ S.Excuse r := by
  rcases hc.finalizedAccountable r hv trivial with ha | he | hs
  · exact Or.inl (agree_of_accountable S hc.laws r ha (hc.nonFraming r hv) hb)
  · exact Or.inr he
  · exact False.elim (not_slashed_of_nonFraming S r (hc.nonFraming r hv) hb hs)

end System

end Consensus

end
