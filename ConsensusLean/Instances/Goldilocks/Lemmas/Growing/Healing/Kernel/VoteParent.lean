module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteWalk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.OptimisticParent

public section

/-! # Noncurrent voter locks below the actual proposal parent

This assembly uses the clean-source parent's published contracts unchanged.
Their clean-domain and vote-retention dependencies remain explicit upstream.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- A finite noncurrent voter lock lies below the actual proposal parent. -/
theorem vote_old_live_lock_below_parent_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {u i : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ elly.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocksAt H) (elly.frame.viableAncestor L) d.head := by
  refine vote_old_live_lock_below_parent_of_sources_at hp hR ?_ ?_
    hy hcy hes hjb hl hne hlive hL hLr
  · intro x r s B hx hsource hs hsu hrb
    exact hp.clean_source_proposal_parent_before_at hx hpH hsource hs hsu hrb hR
      hci hcall hd hti hib
  · intro x r s B CV hx hop hs hrb he
    exact hp.clean_optimistic_proposal_parent_at hx hpH hop hs hrb (he ▸ hR)
      hci hcall hd (he ▸ hti) hib

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
