module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # H.1 for evidence-release

H.1 at `ḡ + (8k + 4)Δ` and its corollary hold for every lock rule whose locks after each unlock
are related to the parent's by the unlock relation (`ac_healing_standalone_of_parent_tightU`,
`ac_healing_standalone_tight_corollaryU`). A run of the evidence-release SA, forgotten
(`projTrace`), is such a run, with the unlock given by `erOracle` (`localRunU_projTrace`), so
H.1 holds for evidence-release with no premise on its keep rule.

The premises other than the trace contract are H.1's own, read on the forgotten trace: its
times, calls, frames, awake sets, the parent's states (whose `holdsMsg`, the pool, is
evidence-release's) and the votes it emits. The honest proposals (`HonestProposalU` and
`DrivenU` at `erOracle`) are evidence-release's own `ac_proposal` (`acProposalWith_erOracle`).
The confirmed tip in the conclusion is evidence-release's (`acConfirmed` of the parent's state). -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : ACTrace (evidenceReleaseSA sp FGP ro)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- H.1's premises for a run of the evidence-release SA, on its forgotten trace. -/
theorem standaloneRunU_projTrace (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTrace tr) H)
    (hdr : DrivenU (erOracle tr) proposer (projTrace tr) H)
    (htriv : TrivialFrames (projTrace tr) H) (hheal : HealthyAC (projTrace tr) H U g)
    (hcatch : CatchAC (projTrace tr) H U g (2 * sp.Δ)) :
    StandaloneRunU (erOracle tr) (projTrace tr) H U proposer g :=
  ⟨⟨⟨localRunU_projTrace hrun, hobj⟩, hdr, hheal, hcatch⟩, htriv⟩

/-- **H.1 at `ḡ + (8k + 4)Δ` for evidence-release** (trivial frames): for an honest proposal `P`
of slot `p` with `t_p ≥ ḡ + (8k + 4)Δ`, every honest vote of slot `p` is `P`, and at every
call of an honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself, from its tick there on),
`P ⪯ ac_confirmed` after the call.

The premises are read on the forgotten trace `projTrace tr`, whose `holdsMsg` (the pool) is
evidence-release's own, so `HealthyAC` there asks for the deliveries evidence-release's own
forwarding makes. -/
theorem er_healing_standalone_tight (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTrace tr) H)
    (hdr : DrivenU (erOracle tr) proposer (projTrace tr) H)
    (htriv : TrivialFrames (projTrace tr) H) (hheal : HealthyAC (projTrace tr) H U g)
    (hcatch : CatchAC (projTrace tr) H U g (2 * sp.Δ)) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposalU (erOracle tr) (projTrace tr) (proposer p) p P)
    (hp : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt (projTrace tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, (projTrace tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', (projTrace tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j))) :=
  ac_healing_standalone_of_parent_tightU
    (standaloneRunU_projTrace hrun hobj hdr htriv hheal hcatch) hpH hP hp

/-- **H.1 at `ḡ + (8k + 4)Δ` for evidence-release, corollary** (proposal-block inclusion): under
`Prop(G_p)`, for every `t ≥ ḡ + (8k + 4)Δ` an honest proposal released in `[t, t + G_p]` is in
every honest node's confirmed tip from `t + G_p + 6Δ` on.

The premises are read on the forgotten trace `projTrace tr`, whose `holdsMsg` (the pool) is
evidence-release's own, so `HealthyAC` there asks for the deliveries evidence-release's own
forwarding makes. -/
theorem er_healing_standalone_tight_corollary
    (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTrace tr) H)
    (hdr : DrivenU (erOracle tr) proposer (projTrace tr) H)
    (htriv : TrivialFrames (projTrace tr) H) (hheal : HealthyAC (projTrace tr) H U g)
    (hcatch : CatchAC (projTrace tr) H U g (2 * sp.Δ)) {Gp : Time}
    (hprop : PropAC proposer H g Gp) (t : Time)
    (ht : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposalU (erOracle tr) (projTrace tr) (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, (projTrace tr).CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTrace tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j)) :=
  ac_healing_standalone_tight_corollaryU
    (standaloneRunU_projTrace hrun hobj hdr htriv hheal hcatch) hprop t ht

end Consensus.Goldilocks.EvidenceRelease

end
