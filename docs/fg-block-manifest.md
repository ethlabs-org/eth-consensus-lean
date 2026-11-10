# FG logical ownership and boundary preparation

This is intended ownership, not a physical extraction or an achieved no-instance boundary.
The current FG modules remain under Instances/Goldilocks; no Blocks/FG module is introduced.
The exact file/import/declaration inventory and migration budget require a separate dry run.
Ordinary downward imports of generic foundational types remain allowed.

| Logical role | Current source groups | Classification to preserve |
| --- | --- | --- |
| FG protocol definitions | Spec/FG, Spec/Common prerequisites used by FG | protected/trusted-surface instance definitions |
| FG milestone vocabulary and statements | Milestones/Spec/FG, Milestones/Statements/FG | untrusted definitions/statements |
| Store vocabulary/statements | Milestones/Spec/FG/Store, Milestones/Statements/FGStore | untrusted definitions/statements |
| Chain/store results | Lemmas/FGChain, Lemmas/FGStore, Proofs/FGSafety, Proofs/FGStore | untrusted proofs |
| Growing FG results | Lemmas/Growing/FG, Proofs/Growing/FGStore and their milestone statements | untrusted proofs/statements, classified individually |
| Block finality rows | Milestones/Statements/Regimes/BlockFinality; Lemmas/Compose/Regimes/BlockFinality | untrusted statements/proofs; concrete specialisations remain instance-side |
| Node integration | ACInterface.toFG, Frame, NodeAC, Node handlers, Node.LocalRun, Requirements, run/AC/FG/Sync projections | mixed protected definitions, untrusted vocabulary/statements/proofs; classify per declaration |
| Planned persist interface | future block-level persist cut invariant/step/induction | provisional until its signature/proof freeze; no physical move authorised here |

All source groups above are relative to ConsensusLean/Instances/Goldilocks, except named declarations.
FG is not one uniformly trusted layer. Moving a declaration must preserve its classification;
new trusted destinations must extend trusted_paths without dropping legacy protected paths.
Shared prerequisites must be included in the dependency-closed move or stay genuinely generic.

## Enforceable preparation, not completed separation

check-boundaries.py rejects every actual ConsensusLean.Blocks module whose transitive
project-import closure reaches ConsensusLean.Instances, including through generic intermediaries.
The rule has no exception mechanism and does not stop at forwarding imports.
Existing layer/visibility rules still apply; this adds no allowed layer edge or exemption.
Positive graph fixtures cover foundational imports and component-prefix matching; negative
fixtures cover direct and transitive instance dependencies. Existing fixture verdicts must stay unchanged.

There are currently zero actual block modules. Passing today proves only preparation is installed,
not that these instance-owned groups are separated. A future migration must demonstrate a nonempty
dependency-closed block inventory, no backward Blocks → Instances forwarding, no cycles, exact
module ownership/import effects, preserved replay leaf coverage and per-declaration trust metadata.
Old forwarding paths may point toward Blocks; Blocks may not point back to them.

Service, Sleepy, Simulation, AsChainShape and Obligations remain instance-side.
The untrusted NodeEngine milestone definitions, contracts and supplier lemmas are also
instance-side, explicitly excluded from Blocks/FG; generic leaves do not import concrete suppliers.
Served, RecordWrites and SAFamily packages are outside this FG extraction.
No semantic/proof changes or silent ownership allowances belong in a physical move.
