module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Shadow P-U run suppliers

The store facts are instances of the finality-parametric cache invariant. The run
wrappers do not identify shadow reachability with stock reachability.
-/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem own_block_payload (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {B : A.Blk} (hacc : tr.CallAt y i (.fg (.block B true))) : A.validPayload B := by
  rcases Coherence.blockCall_cases h hy hacc with hg |
      ⟨j, x, f, -, hg, hp, d, p, hdp, rfl, -⟩
  · exact (h.wire y hy i _ _ hg).2.2
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hy hg
  obtain ⟨hcoh, t₀, ht₀, hR⟩ := ac_states_reachable proposer dg y (hpay y hy) cfg hreach
  have hfg : cfg.st.fg.Reachable A.genesisPayload := by
    rw [hst]
    exact Node.fg_reachable_at h hy j
  have hs := (Node.step_iff _ _ _ _ _ _ _).mp hstep
  have hR' := ACInterface.ReachableAtFrom.step .tick hR (ht₀.trans hs.1)
    ⟨⟨by simpa only [Node.frame_eq] using (Store.frame_realization _ _ _ _ hfg).1,
      fun _ hX => by rw [Node.frame_eq, Store.toFrame_tree] at hX; exact hX.1⟩, rfl⟩
  rw [← hst] at hdp
  have hts : tr.time i = P.slotTime (P.slotOf (tr.time i)) := hp.2.1
  refine hpay y hy _ hcoh _ _ _ hR' (P.slotOf (tr.time i)) hts.le d p ?_ _ rfl rfl
  rw [← hts]
  simpa only [Node.acProposal_eq, Node.tickStep_eq, Node.acCall_eq,
    Node.frame_eq] using hdp

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Healing

open Node

section OwnBlock

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

end OwnBlock

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem hj_lt_hmax' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
  have hr := (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
  obtain ⟨_, _, _, ⟨Bj, hBj, _, hBjhj⟩, hge, _, _⟩ :=
    Goldilocks.Store.cache_invariants_with Goldilocks.Store.finalitySpec_updateFinality hr
  exact hBjhj ▸ (Goldilocks.Store.hj_lt_h_with
    Goldilocks.Store.finalitySpec_updateFinality hr hBj).trans_le (hge Bj hBj)

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {y : Fin sp.n} {i : Nat} {d : Time}

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.RunTrace

open AC (ACParams ReplayOrder Payload)

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

end Consensus.Goldilocks.Healing.Growing

end
