module
public import ConsensusProofs
public import ConsensusInstances
public import ConsensusTests.Support
public import Mathlib.Tactic
@[expose] public section

/-! # Positive controls

The regimes of the L0 table are met by concrete runs, so no refutation in the
other test modules comes from a regime that no run can meet, and `Good` is
not vacuous at concrete numbers. A family with the Goldilocks skeleton that
does nothing (`ctrlFamily`), at standard thresholds with catch-up, arming lag
and outage budget `1`, outage look-back `η = 2`, heal and latency `1`
(`ctrlParams`; arbitrary numbers that test the regimes only, not Goldilocks
performance bounds), index `k = 1`,
five validators (`key 0` faulty), `Δ = 1`, horizon `20`:

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
* `outage_control`: `T = 1 < b₀ = 3 < b₁ = 4`, honest `key 2` asleep at `3`,
  outage regime (η-sleepy with look-back `2`) and active outage (a protected
  source, a sleeper inside the window, an eligible reader).

* The control contract tolerates arbitrary numbers of validators not ready.

All witnesses are the generic ones of `regimes_realizable`
(`sleepy_witness`, `healthy_witness`, `outage_witness`) at explicit
numbers. -/

namespace Consensus.Shape.Tests.Controls
open Consensus Blocks Shape
open Consensus.Model (Public pubOf sysOf)

/-- A Goldilocks-skeleton shape that does nothing. Any shape would do: the
canonical run (as in `coverage`) is valid whatever the protocol does. -/
def ctrlShape (pub : Public) : ChainShape pub GOut Unit where
  skel := goldilocksSkeleton pub.n
  State := Unit
  Body := Unit
  Durable := Unit
  decBody := inferInstance
  init := fun _ => ()
  clock := fun s _ => s
  propose := fun _ _ => none
  act := fun _ _ _ => none
  pollPropose := fun _ _ => none
  poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s
  durable := fun s => s
  restore := fun _ d _ => d
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The control family. -/
def ctrlFamily : ShapeFamily goldilocksSchema Unit := ctrlShape

/-- Standard thresholds; catch-up, arming lag and outage budget `1`; outage
look-back `η = 2`; heal and latency `1` for every capability and index. -/
def ctrlParams : Params ℕ+ :=
  { Params.standard 1 1 1 (fun _ _ => 1) (fun _ _ => 1) with η := 2 }

/-- The control contract over the Goldilocks schema: `ctrlParams`, index the
gap `k`, one honest ready proposer per window of `k` slots (available,
stable), the pattern `range 2` per window of `k` slots (final). Not the
pinned Goldilocks contract (`goldilocksContract`). -/
abbrev ctrlK : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := ctrlParams
  progress
    | .final, k => .recur ⟨Pattern.range 2, k⟩
    | _, k => .recur ⟨Pattern.single, k⟩

theorem ctrlK_admissible : ctrlK.params.Admissible := by
  have h := Params.standard_admissible (Idx := ℕ+) (catchUp := 1) (lag := 1) (budget := 1)
    (heal := fun _ _ => 1) (latency := fun _ _ => 1) le_rfl le_rfl
  exact ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

theorem ctrlK_progressFits : ProgressFits ctrlK ctrlFamily := by
  intro cap k pub
  cases cap <;> rfl

/-- The control recurrences tolerate any number of validators not ready and a
bad proposer slot in every window (gap `2` for one proposer, `3` for two
consecutive ones). -/
theorem ctrlK_progressTolerant : ProgressTolerant goldilocksSchema ctrlK := by
  intro cap ho N
  cases cap
  · exact ⟨2, show (⟨Pattern.single, 2⟩ : Recurrence).BadSlotSlack by decide⟩
  · exact ⟨2, show (⟨Pattern.single, 2⟩ : Recurrence).BadSlotSlack by decide⟩
  · exact ⟨3, show (⟨Pattern.range 2, 3⟩ : Recurrence).BadSlotSlack by decide⟩

/-- The control system: five validators. -/
abbrev S : System (Fin 5) := sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)

/-- The control progress reader. -/
abbrev X : Progress S ProgressReq := shapeProgress ctrlFamily (Fin 5)

/-- The PKI. -/
def key5 : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := extremalKey 4

theorem card5 : 5 ≤ Fintype.card (Fin 5) := by simp

/-- The concrete index `k = 1`. -/
def k1 : ctrlK.Idx := (1 : ℕ+)

/-- The everyone-awake point: `Δ = 1`, horizon `20`. -/
abbrev ptA : EnvPoint (Fin 5) := realPoint key5 card5 1 one_pos allAwake 20

/-- The sleeper point: `key 2` asleep at `3`, `Δ = 1`, horizon `20`. -/
abbrev ptS : EnvPoint (Fin 5) :=
  realPoint key5 card5 1 one_pos (sleepAt (kv key5 card5 2 (by decide)) 3) 20

/-- One window of every control progress requirement is at most `8` long. -/
theorem progLen_le (cap : Capability) :
    progLen ctrlFamily ctrlK cap k1 (⟨1, one_pos, allAwake⟩ : Env (Fin 5)) ≤ 8 := by
  cases cap <;> decide

theorem progLen_nonneg' (cap : Capability) :
    0 ≤ progLen ctrlFamily ctrlK cap k1 (⟨1, one_pos, allAwake⟩ : Env (Fin 5)) :=
  progLen_nonneg _ _ _ _ _

/-- **Positive controls** (sleepy, and healthy at GST `5` with a log silent
before `5`), for every capability at index `1`. -/
theorem positive_controls (cap : Capability) :
    (∃ r : S.Run, S.pt r = ptA ∧ S.Witness r ∧ S.Sleepy ctrlK r ∧
      S.prog X ctrlK cap k1 0 (S.pt r).horizon r ∧ ProgressActive ctrlFamily ctrlK cap k1 0 r.2 ∧
      (S.pt r).TxLiveActive (S.cDur ctrlK r) 0 (S.lat ctrlK cap k1 r) ∧
      ∃ x, ∃ w ∈ r.2.honest, (∀ τ, x ∉ r.2.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ r.2.relay w τ) ∧
    (∃ r : S.Run, S.pt r = ptA ∧ S.Witness r ∧
      (∀ w m t, (S.log r).recv w m t → 5 ≤ t) ∧ (S.log r).EagerFrom (S.pt r) 5 ∧
      S.Healthy ctrlK 5 r ∧ S.prog X ctrlK cap k1 (S.ready ctrlK 5 r) (S.pt r).horizon r ∧
      ProgressActive ctrlFamily ctrlK cap k1 (S.ready ctrlK 5 r) r.2 ∧
      (S.pt r).TxLiveActive (S.cDur ctrlK r) (S.heal ctrlK cap k1 5 r) (S.lat ctrlK cap k1 r) ∧
      SafeActive (S.cDur ctrlK r) (S.heal ctrlK cap k1 5 r) (S.pt r)) := by
  have hL := progLen_le cap
  have hL0 := progLen_nonneg' cap
  have hlat : (ctrlK.params.latency cap k1 : Time) * 1 = 1 := by cases cap <;> rfl
  constructor
  · obtain ⟨rho, hpt, -, hw, hs, hp, hpa, ht⟩ :=
      sleepy_witness (F := ctrlFamily) key5 card5 one_pos 20 ctrlK_admissible ctrlK_progressFits
        cap k1 (by rw [hlat]; linarith)
    refine ⟨⟨_, rho⟩, hpt, hw, hs, hp, hpa, ht, ?_⟩
    have hps : CommLog.PSync rho.point rho.log 0 :=
      (Model.sysOf_delivers_iff (O := goldilocksSchema) rho _ _).mp hs.1
    exact active_relay rho hps le_rfl (mul_nonneg (Nat.cast_nonneg _) (Env.Δ_pos _).le)
      (fun _ _ => rfl) ht
  · have hheal : max (5 : Time) 0 + (ctrlK.params.heal cap k1 : Time) * 1 = 6 := by
      cases cap <;> rfl
    have hrdy : max (5 : Time) 0 + (ctrlK.params.catchUp : Time) * 1 + 1 = 7 := by decide
    obtain ⟨rho, hpt, -, hw, he, hH, hp, hpa, ht, hsa⟩ :=
      healthy_witness (F := ctrlFamily) key5 card5 one_pos 20 ctrlK_admissible
        ctrlK_progressFits cap k1 5 (by rw [hheal, hlat]; norm_num) (by rw [hheal]; norm_num)
        (by rw [hrdy]; linarith)
    exact ⟨⟨_, rho⟩, hpt, hw, he.quiet, he, hH, hp, hpa, ht, hsa⟩

/-- The control family meets L0 `Realizable` at the control contract (the
generic theorem at concrete numbers). -/
theorem ctrl_realizable : Realizable S X ctrlK :=
  (regimes_realizable ctrlFamily ctrlK ctrlK_admissible ctrlK_progressFits ctrlK_progressTolerant
    (Fin 5) card5).toRealizable

/-- **Outage control**: `T = 1 < b₀ = 3 < b₁ = 4`, honest `key 2` asleep at
`3`: the outage regime holds and the outage is active. -/
theorem outage_control :
    ∃ r : S.Run, S.pt r = ptS ∧ S.Witness r ∧ S.Outage ctrlK 1 3 4 r ∧
      OutageActive (S.cDur ctrlK r) 1 3 4 (S.pt r) ∧
      kv key5 card5 2 (by decide) ∈ (S.pt r).honest ∧
      (S.pt r).env.awake (kv key5 card5 2 (by decide)) 3 = false := by
  obtain ⟨rho, hpt, -, hw, ho, hoa⟩ :=
    outage_witness (F := ctrlFamily) key5 card5 one_pos 20 ctrlK_admissible
      (T := 1) (b₀ := 3) (b₁ := 4)
      ⟨by norm_num, by decide, by norm_num, by decide⟩ (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨_, rho⟩, hpt, hw, ho, hoa, ?_, ?_⟩
  · change _ ∈ rho.point.honest
    rw [hpt]
    exact realPoint_honest key5 card5 one_pos _ 20 (j := 2) (by decide) (by decide)
  · change sleepAt (kv key5 card5 2 (by decide)) 3 (kv key5 card5 2 (by decide)) 3 = false
    simp [sleepAt]

end Consensus.Shape.Tests.Controls

end
