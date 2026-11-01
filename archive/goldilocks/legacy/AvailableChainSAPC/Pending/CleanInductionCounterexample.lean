module
public import AvailableChainSAPC.Pending.RejectedCleanInduction
public import AvailableChainSAPC.Tests.CleanInvariantCounterexample

@[expose] public section
namespace AvailableChain.SAPC.Pending

/-- The round-9 universal event obligation fails at early label 1.
The witness satisfies the exact Sleepy regime, even with the fault cap.
No contract definition or protocol rule is changed. -/
theorem cleanEventObligations_false :
    ¬ Rejected.CleanEventObligations Tests.CleanInvariantCounterexample.p
      Tests.CleanInvariantCounterexample.env := by
  intro h
  have step := (h rfl Tests.CleanInvariantCounterexample.run 0
    Tests.CleanInvariantCounterexample.sleepy).1 0 1
  exact Tests.CleanInvariantCounterexample.no_extension
    (step 42 Tests.CleanInvariantCounterexample.next_save.1
      Tests.CleanInvariantCounterexample.rejectedPath
      Tests.CleanInvariantCounterexample.before_cutoff)

#print axioms cleanEventObligations_false

end AvailableChain.SAPC.Pending
end
