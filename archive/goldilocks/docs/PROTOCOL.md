# Protocol and result

FG-SA combines the SA available-chain store with a finality gadget. Its model is under
[AvailableChainFGSA](../fgsa/AvailableChainFGSA/), with the execution binding in
[FGSARun.Model.Protocol](../fgsa/AvailableChainFGSARun/Model/Protocol.lean). The binding adapts
wire objects to the store and separates scheduled HEAD, proposal and FG actions. The FG action
can read the client record; `recordOwn` records its own FG action. These are explicit model
operations, not an implementation of networking or cryptography.

The public result is `AvailableChain.FGSA.Run.fgsaClaims : FGSAClaims p`, assembled in
[Assembly.Root](../fgsa/AvailableChainFGSAProofs/Proofs/Assembly/Root.lean). Read its fields in
[FGSAClaims](../fgsa/AvailableChainFGSAClaims/FGSAClaims.lean) before reading their producers.
The record includes inherited store/client safety, finality accountability and agreement,
finalized-output safety, inclusion, recovery and continuation results. Each field retains
its own regime, run, readiness, horizon and recovery assumptions. The aggregate theorem does
not remove those premises or close every item in the blueprint.

The duty execution model distinguishes event-prefix state and time-indexed reads. Event order,
strict delivery deadlines, ancestry, no-restart conditions and horizon bounds matter where a
claim requires them. Full sleep forbids tick, delivery and restart events while a node sleeps.
An awake quorum alone supplies no receipt guarantee for a sleeping receiver. Recovery and
receipt scopes must be read in the relevant statement, rather than inferred from a headline.

Shared FG contracts and proofs live in
[FGCompose](../generic/AvailableChainFGCompose/). Protocol proof lanes bind these contracts to
FG-SA reads, export their results, and assemble them. The exact registry and source-version
tables remain in [internal/FG-COMPOSITION.md](internal/FG-COMPOSITION.md); external research paths
there are provenance, not tracked specification files.

PC-SA uses preconfirmations and a PC-first root. Its four libraries remain in
[pcsa/](../pcsa/), but are not ported to the current full-sleep engine and are excluded from
compiled default checks. Their source records and retained snapshots do not establish a
current PC-SA result. [The disabled-scope record](internal/PCSA-DISABLED.md) lists the receiver
contracts and coordinated checks needed for a port. SAPC in `legacy/` is a distinct development.

For the blueprint comparison, consult [the claim map](internal/FGSA-BLUEPRINT-LEAN.json),
[open items](internal/FGSA-BLUEPRINT-OPEN.md), and [chapter snapshots](internal/blueprint/fgsa/).
The blueprint checker audits mapped names and fingerprints; that is not a proof of semantic
equivalence between prose and Lean statements.
