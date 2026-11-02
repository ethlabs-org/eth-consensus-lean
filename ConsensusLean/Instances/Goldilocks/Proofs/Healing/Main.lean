module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, its corollary, H.2) from `Lemmas/Healing/`. `HealingRunStatements`
(HR.1–HR.4, H.2 (run), H.3, H.4) and `PhaseServiceStatements` (HS.1–HS.4) stay stated; their
whole-run proofs over the retired reset-existence route were removed (#136). -/

namespace Consensus.Goldilocks.Healing

/-- **Healing, the AC statements**: H.1, its corollary and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  corollary := SA.ac_healing_standalone_corollary
  inclusion := SA.ac_inclusion

end Consensus.Goldilocks.Healing

end
