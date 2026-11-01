module
public import AvailableChainFGSA.Proofs.Restart -- shake: keep (axioms)

@[expose] public section

namespace AvailableChain.FGSA.RestartTests

open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 1, n := 3, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun _ => ⟨99⟩ }

def h (s : Slot) (r : Nat) : HeadWire 3 := ⟨.seat (.head s) 0, ⟨r⟩⟩
def B : FGBlock (Fin 3) := .node .genesis 2 ⟨2⟩ 0 []
def C : FGBlock (Fin 3) := .node B 3 ⟨3⟩ 0 []
def off : FGBlock (Fin 3) := .node .genesis 2 ⟨4⟩ 0 []
def N : NamedProposal 3 := .node .genesis 2 B.root (eraseFG B).body [h 2 20] [] []
def M : NamedProposal 3 := .node N 3 C.root (eraseFG C).body [h 2 21] [] []
def O : NamedProposal 3 := .node .genesis 2 off.root (eraseFG off).body [h 2 22] [] []
def row : RowWire 3 := ⟨.seat .fg 0, .vote ⟨.vote 0 genesisRoot false, none⟩⟩
def st : State 3 :=
  { fg := { Store.init with TF := {.genesis, B, C, off}, F := B }
    proposals := [⟨.proposer 0, .proposal .genesis⟩, ⟨.proposer 2, .proposal N⟩,
      ⟨.proposer 2, .proposal O⟩, ⟨.proposer 3, .proposal M⟩]
    rowPool := [row]
    fastWrite := [(1, [eraseFG B])]
    base := { GridCO.initial 3 .root with
      blocks := [.genesis, eraseFG B, eraseFG C, eraseFG off]
      votes := [⟨.seat 2 1, .head ⟨40⟩⟩]
      voteStamp := [(⟨.seat 2 1, .head ⟨40⟩⟩, 8)]
      genuine := [(1, some (eraseFG B))]
      obligations := [(eraseFG B, 2, 20)]
      stableRecord := eraseFG B } }

/-- Durable fields and deadlines survive; pools and saved results are cleared. -/
theorem wipe_fields : (wipe p st 9).fg = st.fg ∧ (wipe p st 9).proposals = st.proposals ∧
    (wipe p st 9).rowPool = [row] ∧
    (wipe p st 9).base.obligations = [(eraseFG B, 2, 20)] ∧
    (wipe p st 9).base.stableRecord = eraseFG B ∧
    (wipe p st 9).base.votes = [] ∧ (wipe p st 9).base.voteStamp = [] ∧
    (wipe p st 9).base.genuine = [] ∧ (wipe p st 9).fastWrite = [] ∧
    (wipe p st 9).base.blockStamp =
      [(.genesis, 0), (eraseFG B, 9), (eraseFG C, 9), (eraseFG off, 9)] := by
  decide +kernel

/-- Non-genesis F is replayed; the off-frame and genesis proposals are excluded. -/
theorem replay_sources : restartSources p st = [N, M] ∧
    restartVotes p st = [⟨(h 2 20).auth, .head (h 2 20).payload⟩,
      ⟨(h 2 21).auth, .head (h 2 21).payload⟩] ∧
    (acRestart p st 9).base.votes =
      [⟨.seat 2 0, .head ⟨20⟩⟩, ⟨.seat 2 0, .head ⟨21⟩⟩] ∧
    (acRestart p st 9).base.voteStamp =
      [(⟨.seat 2 0, .head ⟨20⟩⟩, 9), (⟨.seat 2 0, .head ⟨21⟩⟩, 9)] ∧
    (acRestart p st 9).proposals = st.proposals ∧
    (acRestart p st 9).base.now = 9 ∧ (acRestart p st 9).restartTime = some 9 := by
  decide +kernel

/-- Duplicate, stale, future and third-seat HEADs are refused; replay order is observable. -/
theorem replay_cap_and_labels :
    let many : NamedProposal 3 := .node .genesis 2 B.root (eraseFG B).body
      [h 2 20, h 2 20, h 2 21, h 2 22, h 0 30, h 3 31] [] []
    let more : State 3 := { st with proposals := [⟨.proposer 2, .proposal many⟩] }
    (acRestart p more 9).base.votes =
      [⟨.seat 2 0, .head ⟨20⟩⟩, ⟨.seat 2 0, .head ⟨21⟩⟩] ∧
    (acRestart p { st with proposals := st.proposals.reverse } 9).base.votes =
      [⟨.seat 2 0, .head ⟨21⟩⟩, ⟨.seat 2 0, .head ⟨20⟩⟩] := by
  decide +kernel

end AvailableChain.FGSA.RestartTests
end

#print axioms AvailableChain.FGSA.RestartTests.wipe_fields
#print axioms AvailableChain.FGSA.RestartTests.replay_sources
#print axioms AvailableChain.FGSA.RestartTests.replay_cap_and_labels
