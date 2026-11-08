module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LateCertificate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone

public section

/-! # H.1 for the late-certificate rule at a write mode

H.1 at `ḡ + (8k + 4)Δ` and its corollary hold at every write mode `m` of width `k` for every lock
rule whose locks after each unlock are related to the parent's by the unlock relation
(`ac_healing_standalone_of_parent_tightU`, `ac_healing_standalone_tight_corollaryU`, with
`m.width = sp.k`). A run of the late-certificate SA at mode `m`, with its archive and weights
forgotten (`projTraceCM`), is a run at mode `m` with the unlock given by `certOracleM`
(`localRunU_projTraceCM`), so H.1 holds for the late-certificate rule at every such mode, with
no premise on its keep rule and without `HonestNotEarly`. At the parent's mode these are the
parent's results (`Lemmas/Healing/AC/Candidates/LateCertificate`), up to rewriting along
`certRecoverySAM_parent`.

The premises other than the trace contract are H.1's own, read on the forgotten trace: its
times, calls, frames, awake sets, the parent's states and the votes it emits. **Caveat**, as at
the parent's mode: the forgotten trace's `holdsMsg` is the pool's, so `HealthyAC` there
constrains the delivery of the messages the pool admits; the candidate's own `holdsMsg` also
holds archive-only votes, whose forwarding the forgotten trace does not read. The honest proposals
(`HonestProposalU` and `DrivenU` at `certOracleM`) are the candidate's own `ac_proposal`
(`acProposalWith_certOracleM`). The confirmed tip in the conclusion is the candidate's
(`acConfirmed` of the parent's state). -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {m : WriteMode}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (certRecoverySAM sp m FGP ro)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- H.1's premises at mode `m` for a run of the late-certificate SA at mode `m`, on its forgotten
trace. -/
theorem standaloneRunU_of_cert (hrun : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceCM tr) H)
    (hdr : DrivenU (certOracleM tr) proposer (projTraceCM tr) H)
    (htriv : TrivialFrames (projTraceCM tr) H) (hheal : HealthyAC (projTraceCM tr) H U g)
    (hcatch : CatchAC (projTraceCM tr) H U g (2 * sp.Δ)) :
    StandaloneRunU m (certOracleM tr) (projTraceCM tr) H U proposer g :=
  ⟨⟨⟨localRunU_projTraceCM hrun, hobj⟩, hdr, hheal.core, hheal.two_faulty_lt, hcatch⟩, htriv⟩

/-- **H.1 at `ḡ + (8k + 4)Δ` for the late-certificate rule at a write mode of width `k`**
(trivial frames): for an honest proposal `P` of slot `p` with `t_p ≥ ḡ + (8k + 4)Δ`, every honest
vote of slot `p` is `P`, and at every call of an honest node from `t_p + 6Δ` on (at `t_p + 6Δ`
itself, from its tick there on), `P ⪯ ac_confirmed` after the call.

**A pool-trace H.1.** The premises are read on the forgotten trace `projTraceCM tr`, whose
`holdsMsg` is the pool's. So `HealthyAC` there constrains the delivery of the votes the pool
admits and excludes the forwarding of archive-only votes, which the candidate's own `holdsMsg`
holds. No bridge from an archive-aware network premise (on `certRecoverySAM`'s trace) to this
pool-trace `HealthyAC` exists yet. -/
theorem ac_healing_tight_cert (hw : m.width = sp.k)
    (hrun : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceCM tr) H)
    (hdr : DrivenU (certOracleM tr) proposer (projTraceCM tr) H)
    (htriv : TrivialFrames (projTraceCM tr) H) (hheal : HealthyAC (projTraceCM tr) H U g)
    (hcatch : CatchAC (projTraceCM tr) H U g (2 * sp.Δ)) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H)
    (hP : HonestProposalU (certOracleM tr) (projTraceCM tr) (proposer p) p P)
    (hp : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt (projTraceCM tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, (projTraceCM tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', (projTraceCM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
          tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j))) :=
  ac_healing_standalone_of_parent_tightU
    (standaloneRunU_of_cert hrun hobj hdr htriv hheal hcatch) hw hpH hP hp

/-- **H.1 at `ḡ + (8k + 4)Δ` for the late-certificate rule at a write mode of width `k`,
corollary** (proposal-block inclusion): under `Prop(G_p)`, for every `t ≥ ḡ + (8k + 4)Δ` an honest
proposal released in `[t, t + G_p]` is in every honest node's confirmed tip from `t + G_p + 6Δ`
on.

**A pool-trace H.1**, as `ac_healing_tight_cert`: `HealthyAC` is read on the forgotten trace,
whose `holdsMsg` is the pool's. -/
theorem ac_healing_tight_corollary_cert (hw : m.width = sp.k)
    (hrun : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    (hobj : HonestObjects proposer (projTraceCM tr) H)
    (hdr : DrivenU (certOracleM tr) proposer (projTraceCM tr) H)
    (htriv : TrivialFrames (projTraceCM tr) H) (hheal : HealthyAC (projTraceCM tr) H U g)
    (hcatch : CatchAC (projTraceCM tr) H U g (2 * sp.Δ)) {Gp : Time}
    (hprop : PropAC proposer H g Gp) (t : Time)
    (ht : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposalU (certOracleM tr) (projTraceCM tr) (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, (projTraceCM tr).CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceCM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j)) :=
  ac_healing_standalone_tight_corollaryU
    (standaloneRunU_of_cert hrun hobj hdr htriv hheal hcatch) hw hprop t ht

end Consensus.Goldilocks.LateCertificate

end
