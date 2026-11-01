module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep (own-library route)
public meta import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep (engine execution)

@[expose] public section

/-! Short corruption-growth regime candidate. This is not a bounded strong
source witness. Five validators are honest in the source. The continuation
retains three. Its two faults are strictly above one-third and below one-half.
Delta is two. The strict suffix ends at time one, before the next public tick.
The executable checks use the real duty engine. No compile-time evaluation runs. -/
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate

def params : Params where
  Δ := 2
  n := 5
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin 5
abbrev Event := V2.Event Validator (fgsa params unitCodec).Object
abbrev World := V2.D.World Validator (fgsa params unitCodec)

def env : Generic.Env Validator where
  Δ := 2
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

def source : V2.D.Run Validator (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := 0
  events := (List.finRange 5).map (fun v => .tick v 0)
  seatOf := seatOf
  input _ _ := ()

def continuation : V2.D.Run Validator (fgsa params unitCodec) :=
  { source with
    honest := {0, 1, 2}
    horizon := 1
    events := source.events.filter (fun e => e.node.val < 3) }

/-- Strictly above one-third, not only above the rounded source cap. -/
theorem fault_counts :
    (Finset.univ \ source.honest).card = 0 ∧
    (Finset.univ \ continuation.honest).card = 2 ∧
    params.n < 3 * (Finset.univ \ continuation.honest).card ∧
    (Finset.univ \ continuation.honest).card < continuation.honest.card := by decide

/-- The short candidate has an actual strict suffix. -/
theorem candidate_endpoint : source.horizon < continuation.horizon := by decide

/-- Check only finite regime premises on a short real execution.
The missing bounded-source and whole-regime proofs are listed in OPEN.md. -/
def runCandidate : IO Unit := do
  for run in [source, continuation] do
    unless decide (run.events.Pairwise (fun e f => e.key ≤ f.key)) do
      throw (IO.userError "event keys are not sorted")
    unless decide run.events.Nodup do
      throw (IO.userError "duplicate event")
    unless run.events.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ run.horizon)) do
      throw (IO.userError "event outside the horizon")
    unless run.events.all (fun e => decide (e.node ∈ run.honest)) do
      throw (IO.userError "event at a faulty node")
    for v in ((List.finRange 5).filter (fun v => decide (v ∈ run.honest))) do
      for t in [:run.horizon.toNat + 1] do
        if (t : Time) % env.Δ == 0 then
          unless run.events.any (fun e => e == .tick v (t : Time)) do
            throw (IO.userError "public tick is missing")
    let mut world : World := V2.D.World.init
    for e in run.events do
      match e with
      | .tick v t =>
        let result := V2.D.tick env run (world v) v t
        unless result.2.isEmpty do
          throw (IO.userError "unexpected emission before the first HEAD time")
        world := Function.update world v result.1
      | _ => throw (IO.userError "unexpected non-tick event")
      for v in ((List.finRange 5).filter (fun v => decide (v ∈ run.honest))) do
        unless (world v).st.namedBodies == [.genesis] do
          throw (IO.userError "non-genesis named body in the short run")
  for v in ([0, 1, 2] : List Validator) do
    let localPrefix := fun (es : List Event) =>
      es.filter (fun e => decide (e.node = v ∧ e.time ≤ source.horizon))
    unless localPrefix continuation.events == localPrefix source.events do
      throw (IO.userError "retained local prefix differs")
  unless decide ((Finset.univ \ continuation.honest).card < continuation.honest.card) do
    throw (IO.userError "retained majority is missing")
  IO.println "short candidate PASS: 5 validators, source horizon 0, continuation horizon 1"
  IO.println "5 source ticks, 3 retained ticks; faults 2/5, retained honest 3/5"
  IO.println "checked schedules, real ticks, empty emissions, and genesis-only scope"
  IO.println "checked retained local replay and majority"
  IO.println "Full bounded-source and whole-regime non-vacuity proofs remain open."

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate

def main : IO Unit := AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate.runCandidate
end
