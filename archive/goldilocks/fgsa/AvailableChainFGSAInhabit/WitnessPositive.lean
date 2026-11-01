module
public import AvailableChainFGSAInhabit.WeakContinuationW1
public import AvailableChainFGSAInhabit.SleepPositive -- shake: keep (sleep witness)

@[expose] public section

/-! Positive execution on short prefixes of the W1 witness.

Event indices start at zero. A store at index `i + 1` includes event `i`.
The HEAD prefix ends after its fourth receipt (12 events, time 1).
The proposal prefix ends after its fourth receipt (40 events, time 4).
The acceptance prefix ends after the first proposal receipt (37 events).
-/

namespace AvailableChain.FGSA.Run.Tests.WitnessPositive
open WeakContinuationWitness

/-- Take an event prefix of the same generator, with its original parameters. -/
def positivePrefix (steps count : Nat) : V2.D.Run Validator (fgsa params unitCodec) :=
  runData (steps : Time) ((buildPrefix steps).2.take count)

/-- Node zero's first HEAD votes for genesis in slot zero. -/
def firstHead : Obj params := ⟨.seat (.base (.head 0)) ⟨0, by decide⟩, .head genesisRoot⟩

/-- ROOT-DIGEST W3e. The first proposal has no rows and carries four slot-zero HEADs. -/
def firstProposal : Obj params :=
  let heads := nodes.map fun i => (⟨.seat (.head 0) i, genesisRoot⟩ : HeadWire params.n)
  ⟨.seat (.prop 1) ⟨0, by decide⟩,
    .proposal (.node .genesis 1 (params.digest ⟨genesisRoot, 1, 0, [], heads, heads⟩)
      (packBody (n := params.n) 0 []) heads heads [])⟩

/-- P1: the tick that emits node zero's first HEAD. -/
theorem positive_head_tick :
    (positivePrefix 2 12).events[4]? = some (.tick 0 1) := by decide +kernel

/-- P1: the HEAD is in the output of its named tick. -/
theorem positive_head_output :
    firstHead ∈ V2.D.Run.emitsAt weakEnv (positivePrefix 2 12) 4 := by
  have h : V2.D.Run.emitsAt weakEnv (positivePrefix 2 12) 4 = [firstHead] := by
    exact @of_decide_eq_true _
      ((inferInstance : DecidableEq (List (Obj params))) _ _) (by decide +kernel)
  rw [h]
  exact List.mem_singleton_self _

/-- P1: node zero receives this HEAD. -/
theorem positive_head_receive_zero :
    (positivePrefix 2 12).events[8]? = some (.deliver 0 firstHead 1) := by decide +kernel

/-- P1: node one receives this HEAD. -/
theorem positive_head_receive_one :
    (positivePrefix 2 12).events[9]? = some (.deliver 1 firstHead 1) := by decide +kernel

/-- P1: node two receives this HEAD. -/
theorem positive_head_receive_two :
    (positivePrefix 2 12).events[10]? = some (.deliver 2 firstHead 1) := by decide +kernel

/-- P1: node three receives this HEAD. -/
theorem positive_head_receive_three :
    (positivePrefix 2 12).events[11]? = some (.deliver 3 firstHead 1) := by decide +kernel

/-- P1: the tick that emits node zero's first proposal. -/
theorem positive_proposal_tick :
    (positivePrefix 5 40).events[32]? = some (.tick 0 4) := by decide +kernel

/-- P1: the proposal is in the output of its named tick. -/
theorem positive_proposal_output :
    firstProposal ∈ V2.D.Run.emitsAt weakEnv (positivePrefix 5 40) 32 := by
  have h : V2.D.Run.emitsAt weakEnv (positivePrefix 5 40) 32 = [firstProposal] := by
    exact @of_decide_eq_true _
      ((inferInstance : DecidableEq (List (Obj params))) _ _) (by decide +kernel)
  rw [h]
  exact List.mem_singleton_self _

/-- P1: node zero receives this proposal. -/
theorem positive_proposal_receive_zero :
    (positivePrefix 5 40).events[36]? = some (.deliver 0 firstProposal 4) := by decide +kernel

/-- P1: node one receives this proposal. -/
theorem positive_proposal_receive_one :
    (positivePrefix 5 40).events[37]? = some (.deliver 1 firstProposal 4) := by decide +kernel

/-- P1: node two receives this proposal. -/
theorem positive_proposal_receive_two :
    (positivePrefix 5 40).events[38]? = some (.deliver 2 firstProposal 4) := by decide +kernel

/-- P1: node three receives this proposal. -/
theorem positive_proposal_receive_three :
    (positivePrefix 5 40).events[39]? = some (.deliver 3 firstProposal 4) := by decide +kernel

/-- P2: the real delivery handler stores the proposal at node zero. -/
theorem positive_proposal_accepted :
    toWire params firstProposal ∈
      (V2.D.Run.stateBefore weakEnv (positivePrefix 5 37) 37 0).st.proposals := by
  decide +kernel

/-- P2: node one stores the same proposal after its delivery. -/
example : toWire params firstProposal ∈
    (V2.D.Run.stateBefore weakEnv (positivePrefix 5 38) 38 1).st.proposals := by
  decide +kernel

/-- The first row is a height-one target for genesis, signed by node zero. -/
def firstRow : RowWire params.n :=
  ⟨.seat .fg ⟨0, by decide⟩, .vote ⟨.vote 1 genesisRoot false, none⟩⟩

/-- P3: the first successful FG tick is at time 14. -/
theorem positive_row_tick :
    (positivePrefix 15 137).events[132]? = some (.tick 0 14) := by decide +kernel

/-- P3: node zero releases the named full row. -/
theorem positive_row_output :
    ofRow params firstRow ∈ V2.D.Run.emitsAt weakEnv (positivePrefix 15 137) 132 := by
  have h : V2.D.Run.emitsAt weakEnv (positivePrefix 15 137) 132 = [ofRow params firstRow] := by
    exact @of_decide_eq_true _
      ((inferInstance : DecidableEq (List (Obj params))) _ _) (by decide +kernel)
  rw [h]
  exact List.mem_singleton_self _

/-- P3: the row is delivered to node zero at the same time. -/
theorem positive_row_receive :
    (positivePrefix 15 137).events[136]? = some (.deliver 0 (ofRow params firstRow) 14) := by
  decide +kernel

/-- P3: the real handler admits this row to node zero's pool. -/
theorem positive_row_admitted :
    firstRow ∈ (V2.D.Run.stateBefore weakEnv (positivePrefix 15 137) 137 0).st.rowPool := by
  decide +kernel

/-- P3: node one's pool contains node zero's row after the next delivery. -/
example : firstRow ∈
    (V2.D.Run.stateBefore weakEnv (positivePrefix 15 138) 138 1).st.rowPool := by
  decide +kernel

/-- The only earlier FG duty emits nothing at node zero. -/
theorem positive_six_zero :
    (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 0) 0 6).2 = [] := by
  decide +kernel

/-- The only earlier FG duty emits nothing at node one. -/
theorem positive_six_one :
    (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 1) 1 6).2 = [] := by
  decide +kernel

/-- The only earlier FG duty emits nothing at node two. -/
theorem positive_six_two :
    (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 2) 2 6).2 = [] := by
  decide +kernel

/-- The only earlier FG duty emits nothing at node three. -/
theorem positive_six_three :
    (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 3) 3 6).2 = [] := by
  decide +kernel

/-- The HEAD prefix ends at its last named receipt. -/
theorem positive_head_length : (positivePrefix 2 12).events.length = 12 := by decide +kernel

/-- The proposal prefix ends at its last named receipt. -/
theorem positive_proposal_length : (positivePrefix 5 40).events.length = 40 := by decide +kernel

/-- The acceptance prefix ends immediately after node zero's receipt. -/
theorem positive_accept_length : (positivePrefix 5 37).events.length = 37 := by decide +kernel

/-- The row prefix ends immediately after node zero's receipt. -/
theorem positive_row_length : (positivePrefix 15 137).events.length = 137 := by decide +kernel

attribute [local irreducible] buildPrefix

/-- A short prefix is a literal prefix of the source run. -/
theorem positive_source_prefix (steps count : Nat) (hs : steps ≤ 254) :
    (positivePrefix steps count).events.IsPrefix source.events :=
  (List.take_prefix count _).trans (w1_prefix_prefix steps 254 hs)

/-- A prefix event keeps its index when events are appended. -/
theorem positive_get_extend {xs ys : List Event} (hp : xs.IsPrefix ys)
    {i : Nat} {e : Event} (he : xs[i]? = some e) : ys[i]? = some e := by
  obtain ⟨zs, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]
  exact he

/-- Each named prefix event is a source event at the same index and time. -/
theorem positive_source_get {steps count i : Nat} (hs : steps ≤ 254) {e : Event}
    (he : (positivePrefix steps count).events[i]? = some e) : source.events[i]? = some e :=
  positive_get_extend (positive_source_prefix steps count hs) he

/-- Each named prefix event is also a continuation event. -/
theorem positive_continuation_get {steps count i : Nat} (hs : steps ≤ 254) {e : Event}
    (he : (positivePrefix steps count).events[i]? = some e) :
    continuation.events[i]? = some e :=
  positive_get_extend ⟨(buildSuffix 16).2, rfl⟩ (positive_source_get hs he)

/-- Short-prefix replay is the source replay, in the source environment. -/
theorem positive_source_state (steps count i : Nat) (hs : steps ≤ 254)
    (hi : i ≤ (positivePrefix steps count).events.length) :
    V2.D.Run.stateBefore strongEnv source i =
      V2.D.Run.stateBefore weakEnv (positivePrefix steps count) i := by
  have hp := positive_source_prefix steps count hs
  rw [← w1_source_state i (hi.trans hp.length_le)]
  change genFold V2.D.World.init (source.events.take i) =
    genFold V2.D.World.init ((positivePrefix steps count).events.take i)
  obtain ⟨zs, he⟩ := hp
  rw [← he, List.take_append_of_le_length hi]

/-- Short-prefix replay is also the continuation replay. -/
theorem positive_continuation_state (steps count i : Nat) (hs : steps ≤ 254)
    (hi : i ≤ (positivePrefix steps count).events.length) :
    V2.D.Run.stateBefore weakEnv continuation i =
      V2.D.Run.stateBefore weakEnv (positivePrefix steps count) i := by
  rw [source_replay (hi.trans (positive_source_prefix steps count hs).length_le)]
  exact positive_source_state steps count i hs hi

/-- An indexed prefix output is a source output at the same tick. -/
theorem positive_source_output {steps count i : Nat} (hs : steps ≤ 254)
    {v : Validator} {t : Time} {o : Obj params}
    (he : (positivePrefix steps count).events[i]? = some (.tick v t))
    (ho : o ∈ V2.D.Run.emitsAt weakEnv (positivePrefix steps count) i) :
    o ∈ V2.D.Run.emitsAt strongEnv source i := by
  have hget := positive_source_get hs he
  have ht : t ≤ source.horizon := (source_in_horizon _ (List.mem_of_getElem? hget)).2
  rw [V2.D.Run.emitsAt, hget,
    positive_source_state steps count i hs (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)]
  rw [V2.D.Run.emitsAt, he] at ho
  have htick (st : Node params) :
      (V2.D.tick weakEnv (positivePrefix steps count) st v t).2 =
        (V2.D.tick strongEnv source st v t).2 := by
    unfold V2.D.tick
    rw [awake_agreement v t ht]
    rfl
  exact (congrArg (fun xs : List (Obj params) => o ∈ xs)
    (htick (V2.D.Run.stateBefore weakEnv (positivePrefix steps count) i v))).mp ho

/-- An indexed prefix output is a continuation output at the same tick. -/
theorem positive_continuation_output {steps count i : Nat} (hs : steps ≤ 254)
    {v : Validator} {t : Time} {o : Obj params}
    (he : (positivePrefix steps count).events[i]? = some (.tick v t))
    (ho : o ∈ V2.D.Run.emitsAt weakEnv (positivePrefix steps count) i) :
    o ∈ V2.D.Run.emitsAt weakEnv continuation i := by
  rw [V2.D.Run.emitsAt, positive_continuation_get hs he,
    positive_continuation_state steps count i hs
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)]
  rw [V2.D.Run.emitsAt, he] at ho
  exact ho

/-- P1 on the source: node zero emits the HEAD at index 4, time 1. -/
theorem positive_source_head : source.events[4]? = some (.tick 0 1) ∧
    firstHead ∈ V2.D.Run.emitsAt strongEnv source 4 :=
  ⟨positive_source_get (by decide) positive_head_tick,
    positive_source_output (by decide) positive_head_tick positive_head_output⟩

/-- P1 on the continuation: the same HEAD emission. -/
theorem positive_continuation_head : continuation.events[4]? = some (.tick 0 1) ∧
    firstHead ∈ V2.D.Run.emitsAt weakEnv continuation 4 :=
  ⟨positive_continuation_get (by decide) positive_head_tick,
    positive_continuation_output (by decide) positive_head_tick positive_head_output⟩

/-- P1 on the source: node zero emits the proposal at index 32, time 4. -/
theorem positive_source_proposal : source.events[32]? = some (.tick 0 4) ∧
    firstProposal ∈ V2.D.Run.emitsAt strongEnv source 32 :=
  ⟨positive_source_get (by decide) positive_proposal_tick,
    positive_source_output (by decide) positive_proposal_tick positive_proposal_output⟩

/-- P1 on the continuation: the same proposal emission. -/
theorem positive_continuation_proposal : continuation.events[32]? = some (.tick 0 4) ∧
    firstProposal ∈ V2.D.Run.emitsAt weakEnv continuation 32 :=
  ⟨positive_continuation_get (by decide) positive_proposal_tick,
    positive_continuation_output (by decide) positive_proposal_tick positive_proposal_output⟩

/-- P2 on the source: node zero has accepted the proposal after event 36. -/
theorem positive_source_accepted :
    toWire params firstProposal ∈ (V2.D.Run.stateBefore strongEnv source 37 0).st.proposals := by
  rw [positive_source_state 5 37 37 (by decide) (by rw [positive_accept_length])]
  exact positive_proposal_accepted

/-- P2 on the continuation: the same accepted proposal. -/
theorem positive_continuation_accepted :
    toWire params firstProposal ∈
      (V2.D.Run.stateBefore weakEnv continuation 37 0).st.proposals := by
  rw [positive_continuation_state 5 37 37 (by decide) (by rw [positive_accept_length])]
  exact positive_proposal_accepted

/-- P3 on the source: node zero emits the row at index 132, time 14. -/
theorem positive_source_row : source.events[132]? = some (.tick 0 14) ∧
    ofRow params firstRow ∈ V2.D.Run.emitsAt strongEnv source 132 :=
  ⟨positive_source_get (by decide) positive_row_tick,
    positive_source_output (by decide) positive_row_tick positive_row_output⟩

/-- P3 on the continuation: the same row emission. -/
theorem positive_continuation_row : continuation.events[132]? = some (.tick 0 14) ∧
    ofRow params firstRow ∈ V2.D.Run.emitsAt weakEnv continuation 132 :=
  ⟨positive_continuation_get (by decide) positive_row_tick,
    positive_continuation_output (by decide) positive_row_tick positive_row_output⟩

/-- P3 on the source: node zero has pooled the row after event 136. -/
theorem positive_source_pool :
    firstRow ∈ (V2.D.Run.stateBefore strongEnv source 137 0).st.rowPool := by
  rw [positive_source_state 15 137 137 (by decide) (by rw [positive_row_length])]
  exact positive_row_admitted

/-- P3 on the continuation: the same pooled row. -/
theorem positive_continuation_pool :
    firstRow ∈ (V2.D.Run.stateBefore weakEnv continuation 137 0).st.rowPool := by
  rw [positive_continuation_state 15 137 137 (by decide) (by rw [positive_row_length])]
  exact positive_row_admitted

/-- The row signer is honest in both runs. -/
theorem positive_signer_honest : (0 : Validator) ∈ source.honest ∧
    (0 : Validator) ∈ continuation.honest := by
  rw [honest_sets.1, honest_sets.2]
  exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- A row before time 14 can only come from the FG duty at time 6. -/
theorem positive_early_row_time (st : Node params) (v : Validator) (t : Time)
    (o : Obj params) (body : RowPayload) (ht : t < 14)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2)
    (hp : o.payload = .row body) : t = 6 := by
  obtain ⟨d, j, m, rfl, hd, ha⟩ := gen_tick_seat st v t o ho
  have htime := (duties_spec params d t).mp hd
  cases d with
  | headAction s =>
      have ha := w1_head_action (c := unitCodec) (x := ()) ha
      change some (.head (headVote params (FGSA.clock params st.st t) s).root) = some m at ha
      cases ha
      cases hp
  | propAction s =>
      have ha := w1_proposal_action (c := unitCodec) (x := ()) ha
      change (propose params (FGSA.clock params st.st t) s).map (withApp params 0) = some m at ha
      unfold propose at ha
      split at ha
      · cases ha
      · simp only [Option.map_map] at ha
        obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
        cases hp
  | fgAction r =>
      change 4 * (↑(r * 2) : Int) + 6 = t at htime
      push_cast at htime
      simp only [Time] at ht htime ⊢
      omega

/-- Every earlier time has no released row, checked separately at each node of time 6. -/
theorem positive_no_earlier_row (steps : Nat) (ht : steps < 14) (o : Obj params)
    (body : RowPayload) (hp : o.payload = .row body) :
    o ∉ (tickBatch steps (buildPrefix steps).1).2 := by
  intro ho
  obtain ⟨v, hv⟩ := (w1_tickBatch_emits steps (buildPrefix steps).1 o).mp ho
  have hs := positive_early_row_time ((buildPrefix steps).1 v) v steps o body
    (by exact_mod_cast ht) hv hp
  have hs' : steps = 6 := by exact_mod_cast hs
  subst steps
  fin_cases v
  · change o ∈ (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 0) 0 6).2 at hv
    rw [positive_six_zero] at hv
    exact List.not_mem_nil hv
  · change o ∈ (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 1) 1 6).2 at hv
    rw [positive_six_one] at hv
    exact List.not_mem_nil hv
  · change o ∈ (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 2) 2 6).2 at hv
    rw [positive_six_two] at hv
    exact List.not_mem_nil hv
  · change o ∈ (V2.D.tick weakEnv (runData 269 []) ((buildPrefix 6).1 3) 3 6).2 at hv
    rw [positive_six_three] at hv
    exact List.not_mem_nil hv

/-- P3 is the earliest row time in the source, not merely an arbitrary later row. -/
theorem positive_source_first_row (v : Validator) (o : Obj params) (t : Time)
    (body : RowPayload) (hp : o.payload = .row body)
    (he : V2.D.Run.emits strongEnv source v o t) : 14 ≤ t := by
  obtain ⟨i, hi, ho⟩ := w1_source_emits v o t he
  rw [(V2.D.Run.step_tick_eq weakEnv source hi).2] at ho
  obtain ⟨n, _, rfl, hn⟩ := w1_locate_emission 254 i v t o hi ho
  by_contra ht
  have hn' : n < 14 := by exact_mod_cast (lt_of_not_ge ht)
  exact positive_no_earlier_row n hn' o body hp hn

/-- The continuation also has no row emission before time 14. -/
example (v : Validator) (o : Obj params) (t : Time) (body : RowPayload)
    (hp : o.payload = .row body) (he : V2.D.Run.emits weakEnv continuation v o t) :
    14 ≤ t := by
  obtain ⟨i, hi, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq weakEnv continuation hi).2] at ho
  rw [w1_continuation_eq] at hi ho
  obtain ⟨n, _, rfl, hn⟩ := w1_locate_emission 270 i v t o hi ho
  by_contra ht
  have hn' : n < 14 := by exact_mod_cast (lt_of_not_ge ht)
  exact positive_no_earlier_row n hn' o body hp hn

/-- P1 receipts of node zero's HEAD in the source, indexed by receiver. -/
theorem positive_source_head_receipts (v : Validator) :
    source.events[8 + v.val]? = some (.deliver v firstHead 1) := by
  fin_cases v
  · exact positive_source_get (by decide) positive_head_receive_zero
  · exact positive_source_get (by decide) positive_head_receive_one
  · exact positive_source_get (by decide) positive_head_receive_two
  · exact positive_source_get (by decide) positive_head_receive_three

/-- P1 receipts of node zero's HEAD in the continuation. -/
theorem positive_continuation_head_receipts (v : Validator) :
    continuation.events[8 + v.val]? = some (.deliver v firstHead 1) := by
  fin_cases v
  · exact positive_continuation_get (by decide) positive_head_receive_zero
  · exact positive_continuation_get (by decide) positive_head_receive_one
  · exact positive_continuation_get (by decide) positive_head_receive_two
  · exact positive_continuation_get (by decide) positive_head_receive_three

/-- P1 receipts of the proposal in the source, indexed by receiver. -/
theorem positive_source_proposal_receipts (v : Validator) :
    source.events[36 + v.val]? = some (.deliver v firstProposal 4) := by
  fin_cases v
  · exact positive_source_get (by decide) positive_proposal_receive_zero
  · exact positive_source_get (by decide) positive_proposal_receive_one
  · exact positive_source_get (by decide) positive_proposal_receive_two
  · exact positive_source_get (by decide) positive_proposal_receive_three

/-- P1 receipts of the proposal in the continuation. -/
theorem positive_continuation_proposal_receipts (v : Validator) :
    continuation.events[36 + v.val]? = some (.deliver v firstProposal 4) := by
  fin_cases v
  · exact positive_continuation_get (by decide) positive_proposal_receive_zero
  · exact positive_continuation_get (by decide) positive_proposal_receive_one
  · exact positive_continuation_get (by decide) positive_proposal_receive_two
  · exact positive_continuation_get (by decide) positive_proposal_receive_three

/-- P3: the source receives the row at index 136, time 14. -/
theorem positive_source_row_receipt :
    source.events[136]? = some (.deliver 0 (ofRow params firstRow) 14) :=
  positive_source_get (by decide) positive_row_receive

/-- P3: the continuation receives the row at the same index and time. -/
theorem positive_continuation_row_receipt :
    continuation.events[136]? = some (.deliver 0 (ofRow params firstRow) 14) :=
  positive_continuation_get (by decide) positive_row_receive

end AvailableChain.FGSA.Run.Tests.WitnessPositive
