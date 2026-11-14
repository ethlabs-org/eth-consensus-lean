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

/-- **The parent of an honest proposal is held at its cut**, for any AC from the proposer's start
`ini p` at which it meets the requirements: the proposer's FG store before the proposal cut `kX`
holds a block `Pr` with `X.parent = some Pr.root` (`onBlock` accepts `X`). -/
theorem proposal_parent_held_from {P : Params} {A : NodeAC P}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} {proposer : Nat → Fin P.n} {ini : Fin P.n → A.State}
    (h : Node.LocalRun proposer dg H sg tr ini)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    {p : Fin P.n} (hp : p ∈ H) (hq : ({ A with initial := ini p } : NodeAC P).Requirements)
    {kX : Nat} {X : A.Blk} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : A.Blk, X.parent = some Pr.root ∧ Pr ∈ (tr.state p kX).fg.tree := by
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt_from h hroot hnc hp hq hX
  obtain ⟨pr, _, _, hsome, hpar, _⟩ :=
    Goldilocks.Store.onBlock_fields (h.cutLaw p hp kX _ hacc).2.1
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hsome
  have hR := Compose.fg_reachable h hp kX
  have hYr : Y.root = pr := hR.blocks_root hY
  refine ⟨Y, by rw [hpar, hYr], ?_⟩
  change (tr.state p kX).fg.blocks Y.root = some Y
  rw [hYr]
  exact hY

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The parent of an honest proposal is held at its cut** (`proposal_parent_held_from` at the
Goldilocks requirements from the run's starts). -/
theorem proposal_parent_held {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : SA.Blk sp.n (List (FG.Att sp.n)), X.parent = some Pr.root ∧
      Pr ∈ (tr.state p kX).fg.tree :=
  proposal_parent_held_from hrun.toLocalRun hrun.genesis_root_ok hnc hp
    (Compose.requirements_from sp ro (hrun.vstart p)) hX

end Consensus.Goldilocks.Healing
