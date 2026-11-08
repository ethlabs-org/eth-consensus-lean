module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.RelTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # H.1 for the late-certificate rule

H.1 at `ḡ + (8k + 4)Δ` and its corollary hold for every lock rule whose locks after each unlock
are related to the parent's by the unlock relation (`ac_healing_standalone_of_parent_tightU`,
`ac_healing_standalone_tight_corollaryU`). A run of the late-certificate SA, with its archive and
weights forgotten (`projTraceC`), is such a run, with the unlock given by `certOracle`
(`localRunU_projTraceC`), so H.1 holds for the late-certificate rule with no premise on its keep
rule and without `HonestNotEarly`.

The premises other than the trace contract are H.1's own, read on the forgotten trace: its
times, calls, frames, awake sets, the parent's states and the votes it emits. **Caveat**: the
forgotten trace's `holdsMsg` is the pool's, so `HealthyAC` there constrains the delivery of the
messages the pool admits; the candidate's own `holdsMsg` also holds archive-only votes, whose
forwarding the forgotten trace does not read. The honest proposals (`HonestProposalU` and
`DrivenU` at `certOracle`) are the candidate's own `ac_proposal` (`acProposalWith_certOracle`).
The confirmed tip in the conclusion is the candidate's (`acConfirmed` of the parent's state). -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : ACTrace (certRecoverySA sp FGP ro)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- H.1's premises for a run of the late-certificate SA, on its forgotten trace. -/
theorem standaloneRunU_projTraceC (hrun : ACLocalRun (certRecoverySA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceC tr) H)
    (hdr : DrivenU (certOracle tr) proposer (projTraceC tr) H)
    (htriv : TrivialFrames (projTraceC tr) H) (hheal : HealthyAC (projTraceC tr) H U g)
    (hcatch : CatchAC (projTraceC tr) H U g (2 * sp.Δ)) :
    StandaloneRunU (WriteMode.parent sp) (certOracle tr) (projTraceC tr) H U proposer g :=
  ⟨⟨⟨localRunU_projTraceC hrun, hobj⟩, hdr, hheal.core, hheal.two_faulty_lt, hcatch⟩, htriv⟩

/-- **H.1 at `ḡ + (8k + 4)Δ` for the late-certificate rule** (trivial frames): for an honest
proposal `P` of slot `p` with `t_p ≥ ḡ + (8k + 4)Δ`, every honest vote of slot `p` is `P`, and at
every call of an honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself, from its tick there on),
`P ⪯ ac_confirmed` after the call.

**A pool-trace H.1.** The premises are read on the forgotten trace `projTraceC tr`, whose
`holdsMsg` is the pool's. So `HealthyAC` there constrains the delivery of the votes the pool
admits and excludes the forwarding of archive-only votes, which the candidate's own `holdsMsg`
holds. No bridge from an archive-aware network premise (on `certRecoverySA`'s trace) to this
pool-trace `HealthyAC` exists yet. -/
theorem cert_healing_standalone_tight (hrun : ACLocalRun (certRecoverySA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceC tr) H)
    (hdr : DrivenU (certOracle tr) proposer (projTraceC tr) H)
    (htriv : TrivialFrames (projTraceC tr) H) (hheal : HealthyAC (projTraceC tr) H U g)
    (hcatch : CatchAC (projTraceC tr) H U g (2 * sp.Δ)) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposalU (certOracle tr) (projTraceC tr) (proposer p) p P)
    (hp : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt (projTraceC tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, (projTraceC tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', (projTraceC tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j))) :=
  ac_healing_standalone_of_parent_tightU
    (standaloneRunU_projTraceC hrun hobj hdr htriv hheal hcatch) rfl hpH hP hp

/-- **H.1 at `ḡ + (8k + 4)Δ` for the late-certificate rule, corollary** (proposal-block
inclusion): under `Prop(G_p)`, for every `t ≥ ḡ + (8k + 4)Δ` an honest proposal released in
`[t, t + G_p]` is in every honest node's confirmed tip from `t + G_p + 6Δ` on.

**A pool-trace H.1.** The premises are read on the forgotten trace `projTraceC tr`, whose
`holdsMsg` is the pool's. So `HealthyAC` there constrains the delivery of the votes the pool
admits and excludes the forwarding of archive-only votes, which the candidate's own `holdsMsg`
holds. No bridge from an archive-aware network premise (on `certRecoverySA`'s trace) to this
pool-trace `HealthyAC` exists yet. -/
theorem cert_healing_standalone_tight_corollary
    (hrun : ACLocalRun (certRecoverySA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceC tr) H)
    (hdr : DrivenU (certOracle tr) proposer (projTraceC tr) H)
    (htriv : TrivialFrames (projTraceC tr) H) (hheal : HealthyAC (projTraceC tr) H U g)
    (hcatch : CatchAC (projTraceC tr) H U g (2 * sp.Δ)) {Gp : Time}
    (hprop : PropAC proposer H g Gp) (t : Time)
    (ht : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposalU (certOracle tr) (projTraceC tr) (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, (projTraceC tr).CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceC tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j)) :=
  ac_healing_standalone_tight_corollaryU
    (standaloneRunU_projTraceC hrun hobj hdr htriv hheal hcatch) rfl hprop t ht

end Consensus.Goldilocks.LateCertificate

end
