module
public import AvailableChainFGSAInhabit.WitnessPositive -- shake: keep (type checks)

/-! P4: positive emissions, timed receipts, acceptance, and row admission.

These tests use P1–P3 directly. Event indices start at zero; the store index
is one greater than the delivery index. Both full runs reuse the short prefixes.
-/

open AvailableChain AvailableChain.FGSA AvailableChain.FGSA.Run
open AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
open AvailableChain.FGSA.Run.Tests.WitnessPositive

#check positivePrefix
#check firstHead
#check firstProposal
#check positive_head_tick
#check positive_head_output
#check positive_head_receive_zero
#check positive_head_receive_one
#check positive_head_receive_two
#check positive_head_receive_three
#check positive_proposal_tick
#check positive_proposal_output
#check positive_proposal_receive_zero
#check positive_proposal_receive_one
#check positive_proposal_receive_two
#check positive_proposal_receive_three
#check positive_proposal_accepted
#check firstRow
#check positive_row_tick
#check positive_row_output
#check positive_row_receive
#check positive_row_admitted
#check positive_six_zero
#check positive_six_one
#check positive_six_two
#check positive_six_three
#check positive_head_length
#check positive_proposal_length
#check positive_accept_length
#check positive_row_length
#check positive_source_prefix
#check positive_get_extend
#check positive_source_get
#check positive_continuation_get
#check positive_source_state
#check positive_continuation_state
#check positive_source_output
#check positive_continuation_output
#check positive_source_head
#check positive_continuation_head
#check positive_source_proposal
#check positive_continuation_proposal
#check positive_source_accepted
#check positive_continuation_accepted
#check positive_source_row
#check positive_continuation_row
#check positive_source_pool
#check positive_continuation_pool
#check positive_signer_honest
#check positive_early_row_time
#check positive_no_earlier_row
#check positive_source_first_row
#check positive_source_head_receipts
#check positive_continuation_head_receipts
#check positive_source_proposal_receipts
#check positive_continuation_proposal_receipts
#check positive_source_row_receipt
#check positive_continuation_row_receipt

example : V2.D.Run.emits strongEnv source 0 (firstHead) 1 :=
  ⟨4, positive_source_head⟩

example : (source.events[4]?).map V2.Event.time = some 1 := by
  rw [positive_source_head.1]
  rfl

example : V2.D.Run.emits strongEnv source 0 (firstProposal) 4 :=
  ⟨32, positive_source_proposal⟩

example : (source.events[32]?).map V2.Event.time = some 4 := by
  rw [positive_source_proposal.1]
  rfl

example : V2.D.Run.emits strongEnv source 0 (ofRow params firstRow) 14 :=
  ⟨132, positive_source_row⟩

example : (source.events[132]?).map V2.Event.time = some 14 := by
  rw [positive_source_row.1]
  rfl

example (v : Validator) :
    source.events[8 + v.val]? = some (.deliver v firstHead 1) :=
  positive_source_head_receipts v

example (v : Validator) :
    source.events[36 + v.val]? = some (.deliver v firstProposal 4) :=
  positive_source_proposal_receipts v

example : source.events[136]? = some (.deliver 0 (ofRow params firstRow) 14) :=
  positive_source_row_receipt

example : toWire params firstProposal ∈
    (V2.D.Run.stateBefore strongEnv source 37 0).st.proposals := positive_source_accepted

example : firstRow ∈ (V2.D.Run.stateBefore strongEnv source 137 0).st.rowPool :=
  positive_source_pool

example : V2.D.Run.emits weakEnv continuation 0 (firstHead) 1 :=
  ⟨4, positive_continuation_head⟩

example : (continuation.events[4]?).map V2.Event.time = some 1 := by
  rw [positive_continuation_head.1]
  rfl

example : V2.D.Run.emits weakEnv continuation 0 (firstProposal) 4 :=
  ⟨32, positive_continuation_proposal⟩

example : (continuation.events[32]?).map V2.Event.time = some 4 := by
  rw [positive_continuation_proposal.1]
  rfl

example : V2.D.Run.emits weakEnv continuation 0 (ofRow params firstRow) 14 :=
  ⟨132, positive_continuation_row⟩

example : (continuation.events[132]?).map V2.Event.time = some 14 := by
  rw [positive_continuation_row.1]
  rfl

example (v : Validator) :
    continuation.events[8 + v.val]? = some (.deliver v firstHead 1) :=
  positive_continuation_head_receipts v

example (v : Validator) :
    continuation.events[36 + v.val]? = some (.deliver v firstProposal 4) :=
  positive_continuation_proposal_receipts v

example : continuation.events[136]? = some (.deliver 0 (ofRow params firstRow) 14) :=
  positive_continuation_row_receipt

example : toWire params firstProposal ∈
    (V2.D.Run.stateBefore weakEnv continuation 37 0).st.proposals := positive_continuation_accepted

example : firstRow ∈ (V2.D.Run.stateBefore weakEnv continuation 137 0).st.rowPool :=
  positive_continuation_pool

example : (0 : Validator) ∈ source.honest ∧ (0 : Validator) ∈ continuation.honest :=
  positive_signer_honest

example (v : Validator) (o : Obj params) (t : Time) (body : RowPayload)
    (hp : o.payload = .row body) (he : V2.D.Run.emits strongEnv source v o t) : 14 ≤ t :=
  positive_source_first_row v o t body hp he

example : (positivePrefix 2 12).events.length = 12 := positive_head_length
example : (positivePrefix 5 40).events.length = 40 := positive_proposal_length
example : (positivePrefix 5 37).events.length = 37 := positive_accept_length
example : (positivePrefix 15 137).events.length = 137 := positive_row_length
