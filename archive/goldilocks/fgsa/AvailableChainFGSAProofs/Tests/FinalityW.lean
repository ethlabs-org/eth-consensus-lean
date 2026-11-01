module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels -- shake: keep (W consumer examples)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.FinalityW
open AvailableChain.SimplexFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 3, δt := 6, RLarge := by decide, digest :=
        fun d => ⟨d.slot + 1⟩ }

private def targets (h : Nat) (U : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h U.root false, none⟩, ⟨1, .vote h U.root false, none⟩,
    ⟨2, .vote h U.root false, none⟩]
private def first : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ 0 (targets 1 .genesis)
private def finWire (i : Fin 4) : RowWire 4 :=
  ⟨.seat .fg i, .vote ⟨.vote 2 first.root false, some ⟨1, genesisRoot⟩⟩⟩
private def actionState : State 4 :=
  { (FGSA.initial 4) with
    base := { (FGSA.initial 4).base with
      now := p.actionTime 1
      blocks := [.genesis, eraseFG first]
      obligations := [(eraseFG first, 1, 100)] }
    fg := { TF := {.genesis, first}, F := .genesis, J := .genesis, h_j := 1, h_max := 2 }
    fastWrite := [(3, [eraseFG first])] }

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- Complete exact-q model batch: all three quorum seats run the client at action 1.
This is a model fixture; it does not claim a BaseSet execution witness. -/
example : actionState.base.now = p.actionTime 1 ∧
    p.E.IsQuorum ({0, 1, 2} : Finset (Fin 4)) ∧
    ∀ i ∈ ({0, 1, 2} : Finset (Fin 4)),
      (attest p actionState RecordOnce.initial i).1 = some (finWire i).payload ∧
      (finWire i).valid = true ∧ (finWire i).auth = .seat .fg i ∧
      FinalityNames p (finWire i) 1 .genesis := by
  unfold FinalityNames Electorate.IsQuorum
  decide +kernel

/-- Permission does not repeat an emission at an already sent height. -/
example : ∀ i ∈ ({0, 1, 2} : Finset (Fin 4)),
    (attest p actionState (attest p actionState RecordOnce.initial i).2 i).1 = none := by
  decide +kernel

/-- κ = R, ΔF > 2Δ, and equality at the receipt-ready carrier boundary. -/
example : kappaF p 6 = p.R ∧ 2 * p.Δ < (6 : Time) ∧
    max (p.actionTime 1) 0 + 6 = SA.proposalTime p.toParams (1 * p.R + kappaF p 6) ∧
    kernelDeadlineW p 6 1 = 25 := by decide +kernel

private def finish : FGBlock (Fin 4) :=
  .node first 6 ⟨2⟩ 0 ([finWire 0, finWire 1, finWire 2].filterMap RowWire.toRow?)

/-- Item 1 is not vacuous: the parent entry is below quorum and the child completes it. -/
private theorem finishCover : FinalityCoveredByChild_W p finish .genesis 1 := by
  refine ⟨⟨1, .genesis, ∅⟩, by decide +kernel, rfl, rfl,
    {0, 1, 2}, ?_, ?_⟩
  · unfold Electorate.IsQuorum
    decide +kernel
  · unfold FinRowNames
    decide +kernel

example : (Window.derive p p.K_W first).W = [⟨1, .genesis, ∅⟩] ∧
    FinalityCoveredByChild_W p finish .genesis 1 := ⟨by decide +kernel, finishCover⟩

example : FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (Window.derive p p.K_W finish).F ∧
    1 ≤ (Window.derive p p.K_W finish).h_F :=
  pendingFold_consume_W p 1 .genesis finish ⟨by decide +kernel, finishCover⟩

/-- Separate height batch: seat 0 reuses its action-0 row at cutoff 1.
Seats 1 and 2 emit at action 1. The earlier row remains parent-valid. -/
private def earlierState : State 4 :=
  { actionState with
    base := { actionState.base with now := p.actionTime 0 }
    fastWrite := [(0, [eraseFG first])] }

example : (attest p earlierState RecordOnce.initial 0).1 = some (finWire 0).payload ∧
    (attest p actionState (attest p earlierState RecordOnce.initial 0).2 0).1 = none ∧
    (attest p actionState RecordOnce.initial 1).1 = some (finWire 1).payload ∧
    (attest p actionState RecordOnce.initial 2).1 = some (finWire 2).payload ∧
    p.E.IsQuorum ({0, 1, 2} : Finset (Fin 4)) ∧
    ∀ i ∈ ({0, 1, 2} : Finset (Fin 4)),
      NamesEntry p .target (finWire i) 2 first ∧
      Window.rowValidW (FGSA.parentFoldState p 6 first) (finWire i) = true := by
  unfold NamesEntry Electorate.IsQuorum
  decide +kernel

private def grow : FGBlock (Fin 4) :=
  .node first 2 ⟨3⟩ 0 ([finWire 0, finWire 1].filterMap RowWire.toRow?)
private def second : FGBlock (Fin 4) := .node grow 3 ⟨4⟩ 0 (targets 2 first)
private def higherWire (i : Fin 4) : RowWire 4 :=
  ⟨.seat .fg i, .vote ⟨.vote 3 second.root false, some ⟨2, first.root⟩⟩⟩
private def bothReady : FGBlock (Fin 4) := .node second 6 ⟨5⟩ 0
  ([finWire 2, higherWire 0, higherWire 1, higherWire 2].filterMap RowWire.toRow?)

private theorem bothLowerCover : FinalityCoveredByChild_W p bothReady .genesis 1 := by
  refine ⟨⟨1, .genesis, {1, 0}⟩, by decide +kernel, rfl, rfl,
    {0, 1, 2}, ?_, ?_⟩
  · unfold Electorate.IsQuorum
    decide +kernel
  · unfold FinRowNames
    decide +kernel

private theorem bothUpperCover : FinalityCoveredByChild_W p bothReady first 2 := by
  refine ⟨⟨2, first, ∅⟩, by decide +kernel, rfl, rfl,
    {0, 1, 2}, ?_, ?_⟩
  · unfold Electorate.IsQuorum
    decide +kernel
  · unfold FinRowNames
    decide +kernel

/-- Both ready entries: the greatest key supplies F. The lower key has prefix coverage. -/
example : FinalityCoveredByChild_W p bothReady .genesis 1 ∧
    FinalityCoveredByChild_W p bothReady first 2 ∧
    (Window.derive p p.K_W bothReady).h_F = 2 ∧
    (Window.derive p p.K_W bothReady).F = first ∧
    (Window.derive p p.K_W bothReady).F ≠ .genesis :=
  ⟨bothLowerCover, bothUpperCover, by decide +kernel, by decide +kernel, by decide +kernel⟩

example : FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (Window.derive p p.K_W bothReady).F ∧
    1 ≤ (Window.derive p p.K_W bothReady).h_F :=
  pendingFold_consume_W p 1 .genesis bothReady ⟨by decide +kernel, bothLowerCover⟩

private def higherOnly : FGBlock (Fin 4) := .node second 6 ⟨5⟩ 0
  ([higherWire 0, higherWire 1, higherWire 2].filterMap RowWire.toRow?)

-- The lower entry is pruned and covered without a finality quorum of its own.
example : ¬ p.E.IsQuorum ({1, 0} : Finset (Fin 4)) ∧
    (Window.derive p p.K_W second).W = [⟨1, .genesis, {1, 0}⟩, ⟨2, first, ∅⟩] ∧
    higherOnly.rows.all (fun row => row.finality_pair == some ⟨2, first.root⟩) = true ∧
    (Window.derive p p.K_W higherOnly).F = first ∧
    Window.CoveredW p higherOnly 1 .genesis := by
  unfold Electorate.IsQuorum Window.CoveredW
  decide +kernel

/-- Item 13: the same complete signed row uses HeightMatch or StaleUseful.
The newer target crossing changes the head, and preserves the exact older key. -/
example : Window.heightMatch (FGSA.parentFoldState p 6 first)
      ((finWire 2).payload.toRow 2) = true ∧
    Window.staleUseful (FGSA.parentFoldState p 6 second)
      ((finWire 2).payload.toRow 2) = true ∧
    Window.RetainedW p second 1 .genesis ∧
    (finWire 2).valid = true ∧
    rowHeight (finWire 2) = some 2 ∧ FinalityNames p (finWire 2) 1 .genesis := by
  unfold Window.RetainedW FinalityNames
  decide +kernel

/-- Fresh target birth exports the four W fields and the exact retained key. -/
example : (heightView p first).h = 2 ∧ (heightView p first).J = .genesis ∧
    (heightView p first).h_j = 1 ∧ (Window.derive p p.K_W first).h_F < 1 ∧
    Window.RetainedW p first 1 .genesis := by
  unfold Window.RetainedW
  decide +kernel

private def birthRows : List (Row (Fin 4)) :=
  [⟨0, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩,
    ⟨2, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩]

-- Raw fold only: these birth-height finality payloads fail R3 and are not admitted rows.
example : (Window.derive p p.K_W (.node .genesis 1 ⟨1⟩ 0 birthRows)).W =
    [⟨1, .genesis, ∅⟩] ∧
    (Window.derive p p.K_W (.node .genesis 1 ⟨1⟩ 0 birthRows)).h_F = 0 := by decide +kernel

/-- This literal family contains signed rows and empty HEAD lists at every ancestor. -/
private def namedFixture : FGBlock (Fin 4) → NamedProposal 4
  | .genesis => .genesis
  | B@(.node P slot root _ rows) =>
      .node (namedFixture P) slot root (eraseFG B).body [] []
        (rows.map (fun row => ⟨.seat .fg row.signer, .vote (RowBody.ofRow row)⟩))

/-- Acceptance guards can be discharged on the actual W cache and h_max. -/
private def beforeReceipt : State 4 :=
  { (FGSA.initial 4) with
    base := { (FGSA.initial 4).base with
      now := 24
      blocks := [.genesis, eraseFG first, eraseFG grow, eraseFG second] }
    proposals := [⟨.proposer first.slot, .proposal (namedFixture first)⟩,
      ⟨.proposer grow.slot, .proposal (namedFixture grow)⟩,
      ⟨.proposer second.slot, .proposal (namedFixture second)⟩]
    fg := [first, grow, second].foldl (Window.on_block p p.K_W) SimplexFG.Store.init }
private def receiptRows : List (RowWire 4) :=
  [finWire 2, higherWire 0, higherWire 1, higherWire 2]
private def receiptBlock : FGBlock (Fin 4) :=
  FGSA.fgBlock second (.node (eraseFG second) 6 ⟨7⟩ (packBody 0 receiptRows)) receiptRows

private def namedReceipt : NamedProposal 4 :=
  .node (namedFixture second) 6 ⟨7⟩ (packBody 0 receiptRows) [] [] receiptRows

example : blockAccepted p beforeReceipt 6 namedReceipt second = true ∧
    FGBlock.Preceq beforeReceipt.fg.J receiptBlock ∧
    max beforeReceipt.fg.h_max (heightView p receiptBlock).h ≤
      (heightView p receiptBlock).h + 1 ∧
    (admitBlock p beforeReceipt 6 namedReceipt).fg.F = first := by
  decide +kernel

-- The selected receipt index is shared by delivery and every guard.
example {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (W U : FGBlock (Fin p.n)) (a₀ d : Time)
    (h : AcceptPrem_W p c E rho W U a₀ d) (x : V) (hx : x ∈ rho.honest) :
    eventTime rho (h.deliver.selected x hx).index = some (h.deliver.selected x hx).time ∧
      (h.deliver.selected x hx).time < d := by
  exact ⟨(h.deliver.witness x hx).1, (h.deliver.witness x hx).2.1⟩

end AvailableChain.FGSA.Run.Tests.FinalityW
end
