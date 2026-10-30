module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Goldilocks Healing: the setting of T1 §6 (unanimity)

`proposal_votes`'s premises with the honest proposal unfolded: a `StandaloneRun`, the honest
proposer `q` of slot `p` and its `ac_proposal` call at cut `k` at `t_p` (label `ℓp`, duty head
`d`, payload `pay`), the block `P` it makes on `d.head`, `t_p ≥ ḡ + 2Θ + 8Δ`, and the locks
settled from `t_{p−1}`. The canonical walk of T1 §6 is the proposer's walk (`ℓp.frame`'s scores
and eligibility at `t_p` against `View.ofLists pay`) on its tree with `P` added. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **The setting of T1 §6** for the honest proposal `P` of slot `p`, made from the
`ac_proposal` call at cut `k` with label `ℓp`, duty head `d` and payload `pay`. -/
structure UnanimitySetting (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g : Time) (p : Nat) (P : Blk sp.n FGP) (k : Nat) (ℓp : ACLabel (goldilocksSA sp FGP ro))
    (d : DutyHead sp.n FGP (Payload sp.n)) (pay : Payload sp.n) : Prop where
  standalone : StandaloneRun tr H U g
  proposer_mem : sp.toParams.proposer p ∈ H
  call : tr.CallAt (sp.toParams.proposer p) k ℓp
  call_proposal : ℓp.call = .proposal
  payload : (acProposal sp (tr.state (sp.toParams.proposer p) k) ℓp.frame (tr.time k)).2 =
    some (d, pay)
  time : tr.time k = sp.ts p
  parent : P.parent = some d.head.root
  slot : P.slot = p
  proposer : P.proposer = sp.toParams.proposer p
  acPayload : P.acPayload = pay
  accepted : ∃ j, k < j ∧ tr.AcceptAt (sp.toParams.proposer p) j P ∧ tr.time j = sp.ts p
  late : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p
  settled : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)

end Consensus.Goldilocks.SA

end
