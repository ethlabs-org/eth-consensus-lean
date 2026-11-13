module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnProposalPool
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: a source processes its own vote

`sendOrAdmit_process_same_time_at`: a node honest at a cut at which it sends or freshly admits a
vote processes it at that same time. The node-local steps run on the prefix through the cut's
time, where the node is honest throughout (`Growing.GoldilocksRun.upTo`): the event of the cut
(`acBlock_cut_cases`) and the votes of an own proposal in a tick group
(`acBlock_vote_pooled_in_tick`, by `own_proposal_payload_pooled_run`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E)

/-- A node honest at a cut at which it sends or freshly admits a vote processes it at that same
time. Recursive delivery processing may occur later in the event, never at a later time. -/
theorem sendOrAdmit_process_same_time_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {i : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {m : SA.Vote (Fintype.card V)} (hsource : (simTraceAt S rho hn).SendOrAdmitAt y i m) :
    ∃ k, (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k = (simTraceAt S rho hn).time i := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  rw [simTraceAt_eq] at hrun hsim hy hsource ⊢
  have hmono := hrun.time_mono
  have hr := hrun.upTo (hrun.time_nonneg i)
  set d := (simTrace S rho hn).time i with hdd
  have hsource' : ((simTrace S rho hn).upTo d).SendOrAdmitAt y i m :=
    (RunTrace.upTo_sendOrAdmitAt hmono).mpr ⟨le_rfl, hsource⟩
  have hproj : ((simTrace S rho hn).upTo d).projAC.SendOrAdmit y i m := by
    obtain ⟨ℓ, hc, hs⟩ := hsource'
    refine ⟨ℓ, Compose.projAC_callAt.mpr hc, ?_⟩
    rw [Compose.projAC_state hr.toLocalRun hy]
    exact hs
  rcases Compose.sendOrAdmit_forward_source hr hy hproj with hem | ⟨hc, hf, _⟩
  · obtain ⟨ℓ, hc, he⟩ := hem
    have hc' := ((Trace.upTo_callAt _).mp hc).2
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc', Or.inr he⟩, rfl⟩
  rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, hm⟩
  · have hc' := ((Trace.upTo_callAt _).mp hc).2
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc', Or.inl hm⟩, rfl⟩
  rcases acBlock_cut_cases S rho hn ((Trace.upTo_callAt _).mp hc).2 hb hm with h |
      ⟨n, v, t, he, hpublic, hkey, hlo, hhi, ht⟩
  · exact h
  obtain ⟨hengine, hlen⟩ := hsim.tick_public v n t he hpublic
  rw [hkey] at hengine hlen
  have htd : t ≤ d := ht.symm.le
  have hcn : (simTrace S rho hn).time (cutMap S rho hn n) ≤ d :=
    (hengine.2.1 0 (List.length_pos_of_ne_nil hengine.1)).2.1 ▸ htd
  have hengine' := (RunTrace.upTo_groupAt hmono (d := d)).mpr ⟨htd, hengine⟩
  rw [← RunTrace.upTo_state_of_le hmono hcn] at hlen
  exact (hf (acBlock_vote_pooled_in_tick hr hy hengine' hlo (by omega) ht hc hb hm)).elim

end Consensus.Goldilocks.Obligations.Growing

end
