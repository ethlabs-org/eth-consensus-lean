module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationInputs
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRetainedTree
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRetainedBack
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrozenRaw
public import AvailableChainPCSAProofs.Proofs.Clean.FormationGateCounts
public import AvailableChainPCSAProofs.Proofs.Clean.FormationHeads
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCompose
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.FormationWalk
public import AvailableChainPCSAProofs.Proofs.Clean.FormationProposal
public import AvailableChainPCSAProofs.Proofs.Clean.FormationStore
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainPCSAProofs.Proofs.Clean.FormationGate
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCount
public import AvailableChainPCSAProofs.Proofs.Clean.FormationAck
public import AvailableChainPCSAProofs.Proofs.Clean.FormationPC
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSource
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTime
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRelay
public import AvailableChainPCSAProofs.Proofs.Clean.FormationOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFreeze
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSourceRetention
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollection
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTerminal

public section

/-! Formation boundaries (pcsa34-r4.3b §§5.3, 5.7).
Corrected F4 reanchors the proposer walk at the common base root and
bounds each actual voter root by the emitted proposal parent.
FormationWalk transfers the path under retained input hypotheses.
FormationStore proves the base/FG domain and stage-1 frame filter facts.
FormationTime proves the local clock bounds. FormationSource proves the
opening, frame activity of held targets, and the unique structural FG lift.
Tests.FormationAckCounterexample labels the old missing-PC run as a relay
regression. The old split fails current F1. The repaired run gives the old
PC to every honest node before the proposal and all seven nodes ack its child.
F3 constrains only nodes awake at v_s. C7 still needs the relay-derived
view bound at every honest early reader. Root-form carriage closes the PC
target alias gap: its installing call now handles the real PC for relay.
The alias regression checks installation, handling and all seven early acks.
FormationView proves signed proposal metadata uniqueness and conditional
receipt, early-view and A2 facts. FormationInputs derives frozen identity
receipt from target-body receipt.
It derives carried presence from exact metadata and PC validity.
Shared body relay closes the old frozen targets. Shared honest-proposal
receipt gives the metadata; stored metadata gives the vote-read body.
pcsa_formation_preFreeze_of_prem needs the premise and five retained
facts; FormationRetainedTree reduces them to two back receipts. Clean ack
admission closes the ack handler pool. FormationEarlyHeads
gives early HEAD receipt from Formation delivery once the retained facts
make the honest HEADs exact. The proposer lists and root-mode score
transport are proved.
The old release witness fails F4.
FormationCompose proves parts 1–4 with named run inputs.
FormationGateCounts proves the late gate counts from the exact honest
HEADs. Assembly.Formation proves FormationClaim and FormationSourceClaim
with no open input. FormationSourceRetention
derives snapshot and target retention. The stamped-PC part of C7 supplies the source when
connected to C1 PC target uniqueness. No source retention input remains.
FormationRetention closes hAckPoolMono from NoRestart and the Clean
AckStore facts.
FormationFreeze closes hFreezeKeep and supplies PC consumers.
FormationTerminal closes hStop from handler slot bounds and sorted run times.
FormationRetainedTree closes hKeep, hReflect and hUnique from equal
eligibility and voter-tree inclusion. FormationRetainedBack closes the two
back receipts from the frozen raw relay.
FormationOrigins closes hFrozenPCOrigin at the actual early read.
FormationCollection closes hPCCollect from the required early N counts.
Its PC consumers need only hAckAdmit from C3. FormationHeads closes honest pool non-equivocation.
Raw-HEAD carriage and the current child follow from body/metadata receipt.
Body relay and metadata close support retention and resolution.
FormationFrozenRaw proves the frozen raw relay from the Clean windowed HEAD
relay at T₀ = z_{s-1}. No Formation input remains open.
The main Clean.Export module is owned by the other Clean writer. -/

end
