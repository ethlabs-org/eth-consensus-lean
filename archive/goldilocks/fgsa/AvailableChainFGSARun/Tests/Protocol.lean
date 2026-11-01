module
public import AvailableChainFGSARun.Proofs.Protocol -- shake: keep (examples)
public import AvailableChainFGSARun.Proofs.Acceptance -- shake: keep (examples)

@[expose] public section

/-! Smoke tests of the FG-SA protocol on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2): the duties at a
proposal, a vote and an action time; the FG payload and its record; the
application value of the proposal and `rowsOk`; the adapter round trips; the
full-wire admission and R6 exclusion; a malformed wire; a proposal whose body does
not pack its rows. -/

namespace AvailableChain.FGSA.Run.Tests

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3b. The test parameters: Δ = 1, n = 1, k = 2, R = 2, δ_t = 0. The
proposal times are `4s`, the vote times `4s + 1`, and the action time of round
`r` is `a_r = 8r + 6`. -/
abbrev p1 : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- ROOT-DIGEST W3b. The codec of a number input (plan §1a, the 2c I1 condition (iv)). -/
def natCodec : AppCodec Nat := ⟨id, some, fun _ => rfl⟩

abbrev P1 := fgsa p1 unitCodec
abbrev P1n := fgsa p1 natCodec

/-- ROOT-DIGEST W3b. The object of label `ℓ` with seat `0`, on a store label. -/
def baseObj (ℓ : Label) (m : Msg 1) : Obj p1 := ⟨.seat (.base ℓ) ⟨0, Nat.one_pos⟩, m⟩
/-- ROOT-DIGEST W3b. The object of the proposal duty of slot `s`. -/
def propObj (s : Slot) (m : Msg 1) : Obj p1 := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩

/-! ### Duties -/

/-- ROOT-DIGEST W3b. A proposal time, a vote time and two action times have their one label;
a time with no act time has none. -/
example : P1.duties 0 = [.propAction 0] ∧
    P1.duties 4 = [.propAction 1] ∧
    P1.duties 5 = [.headAction 1] ∧
    P1.duties 6 = [.fgAction 0] ∧
    P1.duties 14 = [.fgAction 1] ∧
    P1.duties 10 = [] ∧ P1.duties (-3) = [] := by
  decide +kernel

/-! ### The FG action and its record -/

/-- ROOT-DIGEST W3b. No source means no emitted row and no record write. -/
example : P1.act P1.init (.fgAction 0) () = none ∧
    (attest p1 (initial 1) RecordOnce.initial ⟨0, Nat.one_pos⟩).1 = none ∧
    (attest p1 (initial 1) RecordOnce.initial ⟨0, Nat.one_pos⟩).2.sent = [] := by
  decide +kernel

/-- ROOT-DIGEST W3b. A successful optional row is recorded before release. -/
example (nd : Node p1) (i : Fin 1) (body : RowPayload)
    (h : (attest p1 nd.st nd.record ⟨0, p1.nPos⟩).1 = some body) :
    (P1.recordOwn nd ⟨.seat (.base .fg) i, .row body⟩).record =
      (attest p1 nd.st nd.record ⟨0, p1.nPos⟩).2 :=
  recordOwn_attest (c := unitCodec) nd i body h

/-- ROOT-DIGEST W3b. A row with a vote at height `3` records the target at height `3`; a HEAD
object records nothing. -/
example : (recordRow? p1 RecordOnce.initial
      (baseObj .fg (.row (.vote ⟨.vote 3 genesisRoot false, none⟩)))).target 3 = some genesisRoot ∧
    (recordRow? p1 RecordOnce.initial (baseObj (.head 0) (.head genesisRoot))).target 3 = none := by
  decide +kernel

/-! ### The proposal -/

/-- ROOT-DIGEST W3b. The proposal of slot `1` at the initial node carries the input `5` in its
body; its block passes `rowsOk`, and the input decodes. With `unitCodec` the
application value is `0` (the I9 proposal). There is no proposal at slot `0`. -/
example : P1n.act P1n.init (.propAction 1) 5 =
      some (.proposal (.node .genesis 1 ⟨2⟩ (packBody 5 ([] : List (RowWire 1))) [] [] [])) ∧
    rowsOk (.node .genesis 1 ⟨2⟩ (packBody 5 ([] : List (RowWire 1)))) ([] : List (RowWire 1)) ∧
    natCodec.unapp (appOf (Block.node .genesis 1 ⟨2⟩ (packBody 5 ([] : List (RowWire 1)))).body) =
      some 5 ∧
    P1.act P1.init (.propAction 1) () =
      some (.proposal (.node .genesis 1 ⟨2⟩ (packBody 0 ([] : List (RowWire 1))) [] [] [])) ∧
    P1.act P1.init (.propAction 0) () = none := by
  decide +kernel

/-- ROOT-DIGEST W3b. One signed row under the fixed FG label. -/
def rws : List (RowWire 1) := [⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩]

/-- ROOT-DIGEST W3b. `withApp` on a block with one carried row: the rows stay, the application
value changes, and the block passes `rowsOk` with its rows. -/
example : withApp p1 7 (Msg.proposal (.node .genesis 1 ⟨2⟩ (packBody 0 rws) [] [] rws)) =
      .proposal (.node .genesis 1 ⟨2⟩ (packBody 7 rws) [] [] rws) ∧
    rowsOk (.node .genesis 1 ⟨2⟩ (packBody 7 rws)) rws = true ∧
    appOf (Block.node .genesis 1 ⟨2⟩ (packBody 7 rws)).body = 7 := by
  decide +kernel

/-! ### The adapter -/

/-- ROOT-DIGEST W3b. The adapter maps a store-label seat to its store seat, a proposal seat to
the proposer key, and an unsigned object to an unsigned wire; it round trips. -/
example : toWire p1 (baseObj (.head 2) (.head genesisRoot)) =
      ⟨.seat (.head 2) 0, .head genesisRoot⟩ ∧
    toWire p1 (propObj 3 (.head genesisRoot)) = ⟨.proposer 3, .head genesisRoot⟩ ∧
    toWire p1 ⟨.none, .row (.vote ⟨.empty, none⟩)⟩ = ⟨.none, .row (.vote ⟨.empty, none⟩)⟩ ∧
    ofWire p1 (toWire p1 (propObj 3 (.head genesisRoot))) = propObj 3 (.head genesisRoot) ∧
    ofWire p1 (toWire p1 (baseObj .fg (.row (.vote ⟨.empty, none⟩)))) =
      baseObj .fg (.row (.vote ⟨.empty, none⟩)) ∧
    toWire p1 (ofWire p1 ⟨.proposer 2, .row (.vote ⟨.empty, none⟩)⟩) =
      ⟨.proposer 2, .row (.vote ⟨.empty, none⟩)⟩ := by
  decide +kernel

/-! ### Row exclusion -/

/-- ROOT-DIGEST W3b. A store at time `40`: slot `10`, round `5`. -/
def st40 : State 1 := { initial 1 with base := { (initial 1).base with now := 40 } }

/-- ROOT-DIGEST W3b. A row with height `h`; the legacy round input has no effect. -/
def rowAt (_r h : Nat) : Obj p1 := baseObj .fg (.row (.vote ⟨.vote h genesisRoot false, none⟩))

/-- ROOT-DIGEST W3b. The old round argument changes neither the signed content nor admission.
Every decoded valid row enters the pool at the same store time. -/
example : excludesS p1 st40 (rowAt 1 1) = false ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 1 1))).rowPool.length = 1 ∧
    excludesS p1 st40 (rowAt 6 1) = false ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 6 1))).rowPool.length = 1 ∧
    excludesS p1 st40 (rowAt 5 1) = false ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 5 1))).rowPool.length = 1 := by
  decide +kernel

/-- ROOT-DIGEST W3b. The store after two distinct rows by fixed seat `0`. -/
def st40' : State 1 :=
  FGSA.process p1 (FGSA.process p1 st40 (toWire p1 (rowAt 5 1))) (toWire p1 (rowAt 5 2))

/-- ROOT-DIGEST W3b. A third distinct row from the same seat is admitted. Full-wire duplicates
are processed, and the row exclusion result remains false. -/
example : st40'.rowPool.length = 2 ∧ excludesS p1 st40' (rowAt 5 3) = false ∧
    (FGSA.process p1 st40' (toWire p1 (rowAt 5 3))).rowPool.length = 3 ∧
    processedS p1 st40' (rowAt 5 1) = true ∧ excludesS p1 st40' (rowAt 5 1) = false := by
  decide +kernel

/-! ### Malformed wires and the content check -/

/-- ROOT-DIGEST W3b. A row payload with a HEAD seat decodes to `none`: it is not well-formed,
not processed and not excluded, and it has no dependency. -/
example : (toWire p1 (baseObj (.head 0) (.row (.vote ⟨.empty, none⟩)))).decode = none ∧
    P1.wellFormed (baseObj (.head 0) (.row (.vote ⟨.empty, none⟩))) = false ∧
    P1.processed P1.init (baseObj (.head 0) (.row (.vote ⟨.empty, none⟩))) = false ∧
    P1.excludes P1.init (baseObj (.head 0) (.row (.vote ⟨.empty, none⟩))) = false ∧
    P1.depsPresent P1.init (baseObj (.head 0) (.row (.vote ⟨.empty, none⟩))) = true := by
  decide +kernel

/-- ROOT-DIGEST W3b. A proposal whose body is not the packing of its rows (`rowsOk = false`) is
not well-formed; with the packed body it is. -/
example : P1.wellFormed (propObj 1 (.proposal (.node .genesis 1 ⟨2⟩ 99 [] [] []))) = false ∧
    P1.wellFormed (propObj 1 (.proposal
      (.node .genesis 1 ⟨2⟩ (packBody 0 ([] : List (RowWire 1))) [] [] []))) = true := by
  decide +kernel

/-- ROOT-DIGEST W3b. A client with a live genesis source. This fixture tests the client action. -/
def sourceNode : Node p1 :=
  ⟨{ initial 1 with
      base := { (initial 1).base with
        now := 6
        obligations := [(.genesis, 2, 100)] }
      fastWrite := [(0, [.genesis])] }, RecordOnce.initial⟩

def sourcePayload : RowPayload := .vote ⟨.vote 1 genesisRoot false, none⟩

/-- ROOT-DIGEST W3b. A successful action releases a height vote. A later action with the durable
record suppresses the same content, including after restore. -/
example : P1.act sourceNode (.fgAction 0) () = some (.row sourcePayload) ∧
    let recorded := P1.recordOwn sourceNode (baseObj .fg (.row sourcePayload))
    P1.act recorded (.fgAction 1) () = none ∧
    (P1.restore (P1.durable recorded) 6).record.sent = recorded.record.sent ∧
    P1.act { P1.restore (P1.durable recorded) 6 with st := sourceNode.st }
      (.fgAction 2) () = none := by decide +kernel

/-- ROOT-DIGEST W3b. A well-formed row with the wrong parent height makes the entire proposal
invalid. Refusal preserves all store fields and skips its carried row. -/
example :
    let bad : RowWire 1 := ⟨.seat .fg 0, .vote ⟨.vote 2 genesisRoot false, none⟩⟩
    let obj := propObj 1 (.proposal (.node .genesis 1 ⟨2⟩ (packBody 0 [bad]) [] [] [bad]))
    let pre := P1.clock P1.init 4
    P1.wellFormed obj = true ∧ P1.excludes pre obj = true ∧
      (P1.process pre obj).st.rowPool = [] ∧ (P1.process pre obj).st.proposals = [] ∧
      (P1.process pre obj).st.fg.TF = pre.st.fg.TF := by decide +kernel

-- Acceptance controls (plan T7.7).

open AvailableChain.SimplexFG

private def t77Rows : List (RowWire 1) :=
  [⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩,
   ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot true, none⟩⟩,
   ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩⟩]

private def t77Envelope : Obj p1 :=
  propObj 1 (.proposal (.node .genesis 1 ⟨2⟩ (packBody 0 t77Rows) [] [] t77Rows))

private def t77Third : Obj p1 :=
  baseObj .fg (.row (.vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩))

private def t77Pre : Node p1 := P1.clock P1.init 4

/-- ROOT-DIGEST W3b. The old cap control now checks that all three distinct, parent-valid
contents from one fixed seat are admitted and none is excluded. -/
theorem fgsa_carried_row_cap_control :
    let t77Rows : List (RowWire 1) :=
      [⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩,
       ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot true, none⟩⟩,
       ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩⟩]
    let t77Envelope := propObj 1
      (.proposal (.node .genesis 1 ⟨2⟩ (packBody 0 t77Rows) [] [] t77Rows))
    let t77Third := baseObj .fg (.row (.vote ⟨.vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩))
    let t77Pre := P1.clock P1.init 4
    P1.wellFormed t77Envelope = true ∧
      P1.excludes t77Pre t77Third = false ∧
      P1.processed (P1.process t77Pre t77Envelope) t77Third = true ∧
      P1.excludes (P1.process t77Pre t77Envelope) t77Third = false ∧
      (P1.process t77Pre t77Envelope).st.rowPool.length = 3 := by
  decide +kernel

/-- ROOT-DIGEST W3b. The third row is a handled child. -/
example : P1.handles t77Pre t77Envelope t77Third := by
  change handlesS p1 t77Pre.st t77Envelope t77Third
  right
  change (namedParentHeld t77Pre.st _ = true ∧
    ∃ P, parentFG t77Pre.st _ = some P ∧
      blockAccepted p1 t77Pre.st 1 _ P = true) ∧
      (t77Third ∈ [].map (ofHead p1) ∨ t77Third ∈ t77Rows.map (ofRow p1))
  constructor
  · exact ⟨by decide +kernel, .genesis, by decide +kernel, by decide +kernel⟩
  · right
    decide +kernel

/-- ROOT-DIGEST W3b. A slot-zero HEAD can be admitted before the honest vote time of 1. Its
admission threshold is zero. -/
example :
    P1.processed (P1.process P1.init (baseObj (.head 0) (.head genesisRoot)))
      (baseObj (.head 0) (.head genesisRoot)) = true ∧
    fgsaTimely p1 P1.init (baseObj (.head 0) (.head genesisRoot)) := by
  unfold fgsaTimely
  decide +kernel

/-- ROOT-DIGEST W3b. A negative store clock shows why AdmitSound requires a nonnegative clock. -/
example :
    let nd : Node p1 := ⟨{ initial 1 with base.now := -1 }, RecordOnce.initial⟩
    P1.processed (P1.process nd (baseObj (.head 0) (.head genesisRoot)))
      (baseObj (.head 0) (.head genesisRoot)) = true ∧
    ¬ fgsaTimely p1 nd (baseObj (.head 0) (.head genesisRoot)) := by
  unfold fgsaTimely
  decide +kernel

end AvailableChain.FGSA.Run.Tests

end
