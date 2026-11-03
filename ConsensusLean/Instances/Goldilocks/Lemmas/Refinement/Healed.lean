module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Healed

public section

/-! # Goldilocks Refinement: the Healed bundle (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` §4.6
(L4.6 `healed`) and `s5-justify.md` §1.2 (the components of Healed(S.heal) that s5 uses).
`Healed` extends the record half `Healing.HealedRecords` (C2*⁺ (i), (ii), R0, RH; L4.7, proved
under the bounded reset by `healed_records_of_reset_canonical_upTo`) with
the AC components C3 and C4 at the heal time `tH` as explicit fields. In the paper C3 and C4 are
CONDITIONAL on CH and FM (L4.5); they are not proved here. C1 and C5 are `HealthyRun`; HV, P4,
P5 and V0 are not fields (no Lean statement in the paper's form yet; see consensus-lean#137). -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- **The Healed bundle at the heal time `tH` from the height `h₀` on** (s4 L4.6; s5 §1.2).
The record half (`Healing.HealedRecords`) and:

* C3 (A-safe; L4.5, CONDITIONAL on CH, FM): if an honest node holds `X` in a live fast lock at
  a call at a time `x ≥ tH`, every honest proposal of a slot `s` with `x + Δ ≤ t_s` has a parent
  that extends `X`;
* C4 (no reorg of honest blocks; L4.5, CONDITIONAL on CH, FM): the honest proposal of a slot
  `s > slot(tH)` is an ancestor of the honest proposal of every slot `s' > s`. -/
structure Healed (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (proposer : Nat → Fin sp.n)
    (g tH : Time) (h₀ : Nat) (E : Nat → SA.Blk sp.n (List (FG.Att sp.n))) : Prop
    extends Healing.HealedRecords tr H g h₀ E where
  /-- C3 (A-safe), CONDITIONAL on CH and FM in the paper. -/
  c3 : ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
    ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
    ∀ X ∈ ℓ.frame.tree, X.root = l.block →
    ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
      ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr
  /-- C4 (no reorg of honest blocks), CONDITIONAL on CH and FM in the paper. -/
  c4 : ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
    Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
      Anc (tr.HonestBlocks H) P P'

end Consensus.Goldilocks.Refinement

end
