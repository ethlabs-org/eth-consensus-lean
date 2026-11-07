module
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Spec.Shape.OnRuns
public import ConsensusLean.Examples.Shape.Bft
import ConsensusLean.Main
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLeanTest.Fixtures.Support
@[expose] public section

/-! # Positive controls

The regimes of the L0 table are met by concrete runs, so no refutation in the
other test modules comes from a regime that no run can meet, and `CorrectProtocol` is
not vacuous at concrete numbers. A family with a Goldilocks-like skeleton
(`ctrlSkeleton`: slots of `4Δ`, one proposer per slot) that does nothing (`ctrlFamily`),
at standard thresholds with catch-up, arming lag and outage budget `1`, outage look-back
`η = 2`, heal and latency `1`
(`ctrlParams`; arbitrary numbers that test the regimes only, not Goldilocks
performance bounds), index `k = 1`,
five validators (`key 0` faulty), `Δ = ΔF = 2` (realizability starts at `2`: delivery is
strictly before the bound), horizon `40`:

* `positive_controls`, for every capability:
  - sleepy: everyone awake, the synchronous canonical run; the progress
    requirement holds with a window inside the horizon (`ProgressActive`),
    liveness is active
    (transaction `42` submitted to `key 1` at `0`, read by `key 2`), and the
    transaction reaches `key 2` by network relay, never by submission;
  - healthy at GST `5`: everyone awake (the fixed healthy set is all the
    honest validators), a log with **no receipt before `5`**, progress from
    `ready` with a window inside the horizon, liveness and safety active
    after the heal point. The do-nothing family sends no protocol messages,
    so this control does not distinguish delayed from eager delivery of
    protocol messages; it shows the regime is met with nothing received
    before the GST.
* `outage_control`: `T = 2 < b₀ = 6 < b₁ = 8`, honest `key 2` always asleep,
  outage regime (η-sleepy with look-back `2`; no honest validator falls asleep
  in the no-sleep window `[2, 12]`; the cohort counts, with a faulty opponent)
  and active outage (a protected source, a sleeper inside the window, a ready
  reader from the recovery point `14`).

* The control contract tolerates arbitrary numbers of validators not ready.
* `ctrl_not_obligations` (rejection): the do-nothing family is realizable
  (`ctrl_realizable`) but not `ShapeObligations` at any contract, since acceptance gives active
  service (`ShapeObligations.activeService`: a relayed transaction in a read) and its reads are
  empty. Realizability of the regimes is not acceptance.
* `bftContract_admissible`: the numbers of the BFT contract shape shared by
  Streamlet and Tendermint (`Examples.Shape.Bft`) are admissible for a positive
  catch-up (in `Consensus.Shape`, as before its move out of the Spec).

All witnesses are the generic ones of `regimes_realizable`
(`sleepy_witness`, `healthy_witness`, `outage_witness`) at explicit
numbers. -/

namespace Consensus.Shape

open Blocks in
/-- The numbers of `bftContract` are admissible for a positive catch-up. -/
theorem bftContract_admissible (progress : Capability → ℕ+ → ProgressReq) {catchUp : Nat}
    (h : 1 ≤ catchUp) (heal latency : Affine) :
    (bftContract progress catchUp heal latency).params.Admissible :=
  Params.standard_admissible h le_rfl

end Consensus.Shape

namespace Consensus.Shape.Tests.Controls
open Consensus Blocks Shape
open Consensus.Model (Public pubOf sysOf)

/-- The control outputs: one for the available and stable capabilities, one for final. -/
inductive CtrlOut where
  | confirmed
  | finalized
  deriving DecidableEq, Repr

/-- The control schema: `confirmed` serves available and stable, `finalized` final. -/
def ctrlSchema : OutputSchema :=
  ⟨CtrlOut, fun
    | .available => some .confirmed
    | .stable => some .confirmed
    | .final => some .finalized⟩

/-- Two placeholder committee kinds. -/
inductive CtrlKind where
  | head
  | fin
  deriving DecidableEq, Repr

/-- The control skeleton: slots of `4·Δ`, one proposer per slot, polling disabled, the two
placeholder committee kinds at phases 1 and 2, every key in each. -/
def ctrlSkeleton (pub : Public) : Skeleton pub.n where
  grid := ⟨4 * pub.ΔAC, mul_pos (by decide) pub.ΔAC_pos⟩
  proposerSel := fun _ => .sized 1
  pollSel := .fixed ∅
  Kind := CtrlKind
  decKind := inferInstance
  kinds := [.head, .fin]
  phase := fun | .head => pub.ΔAC.toNat | .fin => 2 * pub.ΔAC.toNat
  kindSel := fun _ => .fixed Finset.univ

/-- A control-skeleton shape that does nothing. Any shape would do: the
canonical run (as in `coverage`) is valid whatever the protocol does. -/
def ctrlShape (pub : Public) : ChainShape pub CtrlOut Unit where
  skel := ctrlSkeleton pub
  State := Unit
  Body := Unit
  Durable := Unit
  decBody := inferInstance
  init := fun _ => ()
  clock := fun s _ => s
  propose := fun s _ => (s, none)
  act := fun s _ _ => (s, none)
  pollPropose := fun s _ => (s, none)
  poll := fun s _ => (s, none)
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s
  durable := fun s => s
  restore := fun _ d _ => d
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The control family. -/
def ctrlFamily : ChainShapeFamily ctrlSchema Unit := ctrlShape

/-- Standard thresholds; catch-up, arming lag and outage budget `1`; outage
look-back `η = 2`, no-sleep margin `2` and recovery delay `3`; heal and
latency `1` for every capability and index. -/
def ctrlParams : Params ℕ+ :=
  { Params.standard 1 1 1 (fun _ _ => 1) (fun _ _ => 1) with
    η := 2, noSleep := 2, recovery := 3 }

/-- The control contract over the control schema: `ctrlParams`, index the
gap `k`, one honest ready proposer per window of `k` slots (available,
stable), the pattern `range 2` per window of `k` slots (final). -/
abbrev ctrlK : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := ctrlParams
  progress
    | .final, k => .recur ⟨Pattern.range 2, k, 0⟩
    | _, k => .recur ⟨Pattern.single, k, 0⟩

theorem ctrlK_admissible : ctrlK.params.Admissible := by
  have h := Params.standard_admissible (Idx := ℕ+) (catchUp := 1) (lag := 1) (budget := 1)
    (heal := fun _ _ => 1) (latency := fun _ _ => 1) le_rfl le_rfl
  exact ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

theorem ctrlK_progressFits : ProgressFits ctrlK ctrlFamily := by
  intro cap k pub
  cases cap <;> intro _ <;> rfl

/-- The control recurrences tolerate any number of validators not ready and a
bad proposer slot in every window (gap `2` for one proposer, `3` for two
consecutive ones). -/
theorem ctrlK_progressTolerant : ProgressTolerant ctrlSchema ctrlK := by
  intro cap ho N
  cases cap
  · exact ⟨2, show (⟨Pattern.single, 2, 0⟩ : Recurrence).BadSlotSlack by decide⟩
  · exact ⟨2, show (⟨Pattern.single, 2, 0⟩ : Recurrence).BadSlotSlack by decide⟩
  · exact ⟨3, show (⟨Pattern.range 2, 3, 0⟩ : Recurrence).BadSlotSlack by decide⟩

/-- The control system: five validators. -/
abbrev S : System (Fin 5) := sysOf ctrlSchema (compiled ctrlFamily) (Fin 5)

/-- The control progress reader. -/
abbrev X : Progress S ProgressReq := shapeProgress ctrlFamily (Fin 5)

/-- The PKI. -/
def key5 : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := extremalKey 4

theorem card5 : 5 ≤ Fintype.card (Fin 5) := by simp

/-- The concrete index `k = 1`. -/
def k1 : ctrlK.Idx := (1 : ℕ+)

/-- The everyone-awake point: `Δ = ΔF = 2`, horizon `40`. -/
abbrev ptA : EnvPoint (Fin 5) := realPoint key5 card5 2 two_pos 2 two_pos allAwake 40

/-- The sleeper point: `key 2` always asleep, `Δ = ΔF = 2`, horizon `40`. -/
abbrev ptS : EnvPoint (Fin 5) :=
  realPoint key5 card5 2 two_pos 2 two_pos (asleepAlways (kv key5 card5 2 (by decide))) 40

/-- One window of every control progress requirement is at most `16` long. -/
theorem progLen_le (cap : Capability) :
    progLen ctrlFamily ctrlK cap k1 (⟨2, two_pos, 2, two_pos, allAwake⟩ : Env (Fin 5)) ≤ 16 := by
  cases cap <;> decide

theorem progLen_nonneg' (cap : Capability) :
    0 ≤ progLen ctrlFamily ctrlK cap k1 (⟨2, two_pos, 2, two_pos, allAwake⟩ : Env (Fin 5)) :=
  progLen_nonneg _ _ _ _ _

/-- **Positive controls** (sleepy, and healthy at GST `5` with a log silent
before `5`), for every capability at index `1`. -/
theorem positive_controls (cap : Capability) :
    (∃ r : S.Run, S.pt r = ptA ∧ S.Witness r ∧ S.Sleepy ctrlK r ∧
      S.prog X ctrlK cap k1 0 (S.pt r).horizon r ∧ ProgressActive ctrlFamily ctrlK cap k1 0 r.2 ∧
      (S.pt r).TxLiveActive (S.cDur ctrlK r) 0 (S.lat ctrlK cap k1 r) ∧
      ∃ x, ∃ w ∈ r.2.point.honestAt 0, (∀ τ, x ∉ r.2.submit w τ) ∧
        ∃ τ, 0 ≤ τ ∧ x ∈ r.2.relay w τ) ∧
    (∃ r : S.Run, S.pt r = ptA ∧ S.Witness r ∧
      (∀ w m t, (S.log r).recv w m t → 5 ≤ t) ∧ (S.log r).EagerFrom (S.pt r) 5 ∧
      S.Healthy ctrlK 5 r ∧ S.prog X ctrlK cap k1 (S.ready ctrlK 5 r) (S.pt r).horizon r ∧
      ProgressActive ctrlFamily ctrlK cap k1 (S.ready ctrlK 5 r) r.2 ∧
      (S.pt r).TxLiveActive (S.cDur ctrlK r) (S.heal ctrlK cap k1 5 r) (S.lat ctrlK cap k1 r) ∧
      SafeActive (S.cDur ctrlK r) (S.heal ctrlK cap k1 5 r) (S.pt r)) := by
  have hL := progLen_le cap
  have hL0 := progLen_nonneg' cap
  have hlat : (ctrlK.params.latency cap k1 : Time) * 2 = 2 := by cases cap <;> rfl
  constructor
  · obtain ⟨rho, hpt, -, hw, hs, hp, hpa, ht⟩ :=
      sleepy_witness (F := ctrlFamily) key5 card5 two_pos two_pos 40 ctrlK_admissible
        (by norm_num) (by norm_num) ctrlK_progressFits cap k1 (by rw [hlat]; linarith)
    refine ⟨⟨_, rho⟩, hpt, hw, hs, hp, hpa, ht, ?_⟩
    have hps : CommLog.PSync rho.point rho.log 0 :=
      (Model.sysOf_delivers_iff (O := ctrlSchema) rho _ _ _).mp hs.1
    exact active_relay rho hps le_rfl (mul_nonneg (Nat.cast_nonneg _) (Env.ΔAC_pos _).le)
      (fun _ _ => by rw [realPoint_env]; exact allAwake_apply _ _) ht
  · have hheal : max (5 : Time) 0 + (ctrlK.params.heal cap k1 : Time) * 2 = 7 := by
      cases cap <;> rfl
    have hrdy : max (5 : Time) 0 + (ctrlK.params.catchUp : Time) * 2 + 1 = 8 := by decide
    obtain ⟨rho, hpt, -, hw, he, hH, hp, hpa, ht, hsa⟩ :=
      healthy_witness (F := ctrlFamily) key5 card5 two_pos two_pos 40 ctrlK_admissible
        (by norm_num) (by norm_num) ctrlK_progressFits cap k1 5
        (le_mul_of_one_le_left zero_le_two (by exact_mod_cast ctrlK.params.fgDelay.pos))
        (by rw [hheal, hlat]; norm_num) (by rw [hheal]; norm_num)
        (by rw [hrdy]; linarith)
    exact ⟨⟨_, rho⟩, hpt, hw, he.quiet, he, hH, hp, hpa, ht, hsa⟩

/-- The control family meets L0 `Realizable` at the control contract (the
generic theorem at concrete numbers). -/
theorem ctrl_realizable : Realizable S X ctrlK :=
  (regimes_realizable ctrlFamily ctrlK ctrlK_admissible ctrlK_progressFits ctrlK_progressTolerant
    (Fin 5) card5).toRealizable

/-- **The do-nothing family is not accepted** (rejection): at every contract.
`ShapeObligations` gives active service (`ShapeObligations.activeService`), a transaction relayed
into the read of an honest node; the control family's reads are empty. So `ctrl_realizable`, a
realizability certificate, is not acceptance. -/
theorem ctrl_not_obligations (K : Contract ProgressReq) :
    ¬ ShapeObligationsOn ctrlFamily K (fun _ p => p.ConstantFaults) := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  have hc := h.correct _ (Fin 5)
  have hrat : (2 : Time) ≤ (K.params.fgDelay : Time) * 2 :=
    le_mul_of_one_le_left (by norm_num) (by exact_mod_cast K.params.fgDelay.pos)
  obtain ⟨r, ⟨hw, _, _⟩, ⟨_, hH, hp, ha⟩, _⟩ :=
    (hc.realizable (by simp)).healthy .available i 2 2 0
      (by norm_num) (by norm_num) hrat le_rfl
  rcases hc.behaviour.healthyLive .available _ rfl i 0 r
      ⟨hw.1, hw.2.2.1⟩ ⟨hH, hp⟩ with hl | he
  · obtain ⟨x, u, w, t, t', _, _, _, _, _, _, hx⟩ := hl.served ha
    simp [Trace.readAt, sysOf, Model.Run.readIdx, Model.protoOf, compiled, ctrlFamily,
      ctrlShape, compile, ledgerOf, System.restrict] at hx
  · exact hw.2.1 he

/-- **Outage control**: `T = 2 < b₀ = 6 < b₁ = 8` (at `Δ = 2`), honest `key 2` always
asleep, a faulty `key 0`: the outage regime holds (its no-sleep window is
`[2, 12]` and its recovery point `14`) and the outage is active, with a ready
reader at the horizon `40 ≥ 14`. -/
theorem outage_control :
    ∃ r : S.Run, S.pt r = ptS ∧ S.Witness r ∧ S.Outage ctrlK 2 6 8 r ∧
      OutageActive (S.cDur ctrlK r) 6 2 6 8 (S.pt r) ∧
      S.outageStart ctrlK 6 r = 2 ∧ S.outageEnd ctrlK 8 r = 12 ∧ S.recoveryAt ctrlK 8 r = 14 ∧
      (S.pt r).HonestAt (kv key5 card5 2 (by decide)) 0 ∧
      (∀ t, (S.pt r).env.awake (kv key5 card5 2 (by decide)) t = false) ∧
      ((S.pt r).faultyAt 0).Nonempty := by
  obtain ⟨rho, hpt, -, hw, ho, hoa⟩ :=
    outage_witness (F := ctrlFamily) key5 card5 two_pos two_pos 40 ctrlK_admissible
      (by norm_num) (by norm_num) (T := 2) (b₀ := 6) (b₁ := 8)
      ⟨by norm_num, by decide, by norm_num, by decide⟩ (by norm_num) (by norm_num) (by decide)
  have hC : ctrlK.params.noSleep = 2 := rfl
  have hR : ctrlK.params.recovery = 3 := rfl
  have hD : ((ctrlK.params.recovery : Nat) : Time) * 2 = 6 := by rw [hR]; norm_num
  rw [hD] at hoa
  refine ⟨⟨_, rho⟩, hpt, hw, ho, hoa, ?_, ?_, ?_, ?_, ?_, hw.2.2.2.1⟩
  · change min (max 0 (6 - ((ctrlK.params.noSleep : Nat) : Time) * rho.point.env.ΔAC))
      rho.point.horizon = 2
    rw [hpt, realPoint_env, realPoint_horizon, hC]
    norm_num
  · change min (8 + ((ctrlK.params.noSleep : Nat) : Time) * rho.point.env.ΔAC)
      rho.point.horizon = 12
    rw [hpt, realPoint_env, realPoint_horizon, hC]
    norm_num
  · change 8 + ((ctrlK.params.recovery : Nat) : Time) * rho.point.env.ΔAC = 14
    rw [hpt, realPoint_env, hR]
    norm_num
  · change rho.point.HonestAt _ 0
    rw [hpt]
    exact realPoint_honest key5 card5 two_pos two_pos _ 40 (j := 2) (by decide) (by decide)
  · intro t
    change rho.point.env.awake _ t = false
    rw [hpt, realPoint_env]
    simp [asleepAlways_apply]

end Consensus.Shape.Tests.Controls

end
