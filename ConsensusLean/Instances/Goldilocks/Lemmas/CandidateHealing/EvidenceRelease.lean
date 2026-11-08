module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.EvidenceRelease
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone

public section

/-! # H.1 for evidence-release at a write mode

H.1 at `ḡ + (8k + 4)Δ` and its corollary hold at every write mode `m` of width `k` for every lock
rule whose locks after each unlock are related to the parent's by the unlock relation
(`ac_healing_standalone_of_parent_tightU`, `ac_healing_standalone_tight_corollaryU`, with
`m.width = sp.k`). A run of the evidence-release SA at mode `m`, forgotten (`projTraceM`), is a
run at mode `m` with the unlock given by `erOracleM` (`localRunU_projTraceM`), so H.1 holds for
evidence-release at every such mode, with no premise on its keep rule. At the parent's mode these
are the parent's results (`Lemmas/Healing/AC/Candidates/EvidenceRelease`), up to rewriting along
`evidenceReleaseSAM_parent`.

The premises other than the trace contract are H.1's own, read on the forgotten trace: its
times, calls, frames, awake sets, the parent's states (whose `holdsMsg`, the pool, is
evidence-release's) and the votes it emits. The honest proposals (`HonestProposalU` and `DrivenU`
at `erOracleM`) are evidence-release's own `ac_proposal` (`acProposalWith_erOracleM`). The
confirmed tip in the conclusion is evidence-release's (`acConfirmed` of the parent's state). -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {m : WriteMode}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (evidenceReleaseSAM sp m FGP ro)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- H.1's premises at mode `m` for a run of the evidence-release SA at mode `m`, on its forgotten
trace. -/
theorem standaloneRunU_of_er (hrun : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceM tr) H)
    (hdr : DrivenU (erOracleM tr) proposer (projTraceM tr) H)
    (htriv : TrivialFrames (projTraceM tr) H) (hheal : HealthyAC (projTraceM tr) H U g)
    (hcatch : CatchAC (projTraceM tr) H U g (2 * sp.Δ)) :
    StandaloneRunU m (erOracleM tr) (projTraceM tr) H U proposer g :=
  ⟨⟨⟨localRunU_projTraceM hrun, hobj⟩, hdr, hheal.core, hheal.two_faulty_lt, hcatch⟩, htriv⟩

/-- **H.1 at `ḡ + (8k + 4)Δ` for evidence-release at a write mode of width `k`** (trivial
frames): for an honest proposal `P` of slot `p` with `t_p ≥ ḡ + (8k + 4)Δ`, every honest vote of
slot `p` is `P`, and at every call of an honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself,
from its tick there on), `P ⪯ ac_confirmed` after the call.

The premises are read on the forgotten trace `projTraceM tr`, whose `holdsMsg` (the pool) is
evidence-release's own, so `HealthyAC` there asks for the deliveries evidence-release's own
forwarding makes. -/
theorem ac_healing_tight_er (hw : m.width = sp.k)
    (hrun : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceM tr) H)
    (hdr : DrivenU (erOracleM tr) proposer (projTraceM tr) H)
    (htriv : TrivialFrames (projTraceM tr) H) (hheal : HealthyAC (projTraceM tr) H U g)
    (hcatch : CatchAC (projTraceM tr) H U g (2 * sp.Δ)) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H)
    (hP : HonestProposalU (erOracleM tr) (projTraceM tr) (proposer p) p P)
    (hp : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt (projTraceM tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, (projTraceM tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', (projTraceM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j))) :=
  ac_healing_standalone_of_parent_tightU
    (standaloneRunU_of_er hrun hobj hdr htriv hheal hcatch) hw hpH hP hp

/-- **H.1 at `ḡ + (8k + 4)Δ` for evidence-release at a write mode of width `k`, corollary**
(proposal-block inclusion): under `Prop(G_p)`, for every `t ≥ ḡ + (8k + 4)Δ` an honest proposal
released in `[t, t + G_p]` is in every honest node's confirmed tip from `t + G_p + 6Δ` on.

The premises are read on the forgotten trace `projTraceM tr`, whose `holdsMsg` (the pool) is
evidence-release's own, so `HealthyAC` there asks for the deliveries evidence-release's own
forwarding makes. -/
theorem ac_healing_tight_corollary_er (hw : m.width = sp.k)
    (hrun : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceM tr) H)
    (hdr : DrivenU (erOracleM tr) proposer (projTraceM tr) H)
    (htriv : TrivialFrames (projTraceM tr) H) (hheal : HealthyAC (projTraceM tr) H U g)
    (hcatch : CatchAC (projTraceM tr) H U g (2 * sp.Δ)) {Gp : Time}
    (hprop : PropAC proposer H g Gp) (t : Time)
    (ht : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposalU (erOracleM tr) (projTraceM tr) (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, (projTraceM tr).CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j)) :=
  ac_healing_standalone_tight_corollaryU
    (standaloneRunU_of_er hrun hobj hdr htriv hheal hcatch) hw hprop t ht

end Consensus.Goldilocks.EvidenceRelease

end
