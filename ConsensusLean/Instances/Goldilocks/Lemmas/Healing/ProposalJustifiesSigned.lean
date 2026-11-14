module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifies
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature

public section

/-! # Goldilocks Healing: the parent of an honest proposal is held

`proposal_parent_held`: the parent of an honest proposal is held by the proposer at the proposal
cut (`onBlock` accepts only a block whose parent is stored), a run-level premise of the
justification from signed attestations. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The parent of an honest proposal is held at its cut**: the proposer's FG store before the
proposal cut `kX` holds a block `Pr` with `X.parent = some Pr.root` (`onBlock` accepts `X`). -/
theorem proposal_parent_held (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : SA.Blk sp.n (List (FG.Att sp.n)), X.parent = some Pr.root ∧
      Pr ∈ (tr.state p kX).fg.tree := by
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt hrun hnc hp hX
  obtain ⟨pr, _, _, hsome, hpar, _⟩ :=
    Goldilocks.Store.onBlock_fields (hrun.cutLaw p hp kX _ hacc).2.1
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hsome
  have hR := Compose.fg_reachable hrun.toLocalRun hp kX
  have hroot : Y.root = pr := hR.blocks_root hY
  refine ⟨Y, by rw [hpar, hroot], ?_⟩
  change (tr.state p kX).fg.blocks Y.root = some Y
  rw [hroot]
  exact hY

end Consensus.Goldilocks.Healing
