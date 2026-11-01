module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Healed

public section

/-! # Goldilocks Refinement: the Healed bundle (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` §4.6
(L4.6 `healed`) and `s5-justify.md` §1.2 (the components of Healed(S.heal) that s5 uses).
`Healed` extends the record half `Healing.HealedRecords` (C2*⁺ (i), (ii), R0, RH; L4.7, proved
under the reset by `Healing.healed_records_of_reset` and `Healing.healed_records_of_rows`) with
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

/-- **Healed from the reset and C3, C4.** The record half from `ResetPremises`, RH and the high
entries (`Healing.healed_records_of_reset`); C3 and C4 are the explicit premises `hc3`, `hc4`. -/
theorem healed_of_reset (hp : Healing.ResetPremises tr H proposer dg g ΔF a) {tH : Time}
    {h₀ : Nat} {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}
    (hrh : Healing.HZ tr H g + 1 ≤ h₀) (hE : ∀ h, h₀ ≤ h → Healing.HighEntry tr H g h (E h))
    (hc3 : ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
      ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr)
    (hc4 : ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
        Anc (tr.HonestBlocks H) P P') :
    Healed tr H proposer g tH h₀ E :=
  { Healing.healed_records_of_reset hp hrh hE with c3 := hc3, c4 := hc4 }

/-- **Healed from the reset and C3, C4, canonical form.** The record half from `ResetPremises`
and RH alone, for the canonical entries (`Healing.healed_records_of_reset_canonical`); C3 and
C4 are the explicit premises `hc3`, `hc4`. -/
theorem healed_of_reset_canonical (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {tH : Time} {h₀ : Nat} (hrh : Healing.HZ tr H g + 1 ≤ h₀)
    (Z₀ : SA.Blk sp.n (List (FG.Att sp.n)))
    (hc3 : ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
      ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr)
    (hc4 : ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
        Anc (tr.HonestBlocks H) P P') :
    Healed tr H proposer g tH h₀ (Healing.canonicalEntry tr H g Z₀) :=
  { Healing.healed_records_of_reset_canonical hp hrh Z₀ with c3 := hc3, c4 := hc4 }

end Consensus.Goldilocks.Refinement

end
