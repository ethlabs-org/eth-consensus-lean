module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule

public section

/-! # Releases of emitted votes

The engine releases a vote that the simulating trace emits at the emission's time: at a
tick, by its trailing polls; at a delivery, by its poll; at a restart, as a pending vote. Only
the tick's releases depend on the fault model, and they are a premise. Constant faults
(`RunSimulates`) and growing faults (`Growing/Simulation/PublishedVotes`) supply it. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A vote emitted at cut `k` by `y` is released by `y`'s engine node at the cut's time.
Premise `htick`: a public tick releases the votes its cuts emit (`tick_releases` for constant
faults, `tick_block_vote_releases_at` for growing faults). -/
theorem emit_released_of (hv : rho.ExecutionValid)
    (htick : ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t → ∀ r ∈ eventCuts S rho hn i,
      ∀ ℓ, r.label = .ac ℓ → ∀ m ∈ ℓ.emits, voteObj m.msg ∈ rho.releasesAt i)
    {y : Fin (Fintype.card V)} {k : Nat} {m : SA.Vote (Fintype.card V)}
    (hc : (simTrace S rho hn).EmitAt y k m) :
    ReleasedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, em, hem, rfl⟩ := hc
  erw [releasedFrom_iff]
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, htick he hp r hmem ℓ hrl em hem⟩
  | deliver v o t =>
    have hm := List.mem_of_getElem? he
    have ht0 := (hv.in_horizon _ hm).1
    have hnow : (stateAt S rho hn v i).now = t :=
      (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    have hmem' := hmem
    rw [← self_eq_ownKey S rho hn v i] at hmem'
    obtain ⟨hb, hval⟩ := (process_outbox (runProposer S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) t i _ (stateAt S rho hn v i) 0 hnow).2
      r hmem' ℓ hrl em hem
    have hpre : OneVote t (stateAt S rho hn v i) := by
      rcases (outbox_inv S rho hn hv v i).2 with h | h
      · exact absurd h (not_lastRestart_deliver S rho hv he)
      · rwa [hnow] at h
    have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht0
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) hnow hpre
    have hone : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox =
        [Body.vote (encodeVote em.msg)] := by
      have hlen := ((atMostOneVote_iff _).mp hproc.atMost).2
      match hq : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox with
      | [] => change _ ∈ (process _ _ _).outbox at hb; rw [hq] at hb; cases hb
      | [b] =>
        change _ ∈ (process _ _ _).outbox at hb
        rw [hq, List.mem_singleton] at hb
        rw [hb]
      | _ :: _ :: _ =>
        change (process _ _ _).outbox.length ≤ 1 at hlen
        rw [hq] at hlen
        simp at hlen
    have hobj := voteObj_eq_pollObj S rho (hval.trans (self_eq_ownKey S rho hn v i))
    rw [hobj]
    refine ⟨i, Or.inr ⟨o, he⟩, ?_⟩
    simp only [Model.Run.releasesAt, he]
    unfold Model.Run.deliver
    rw [deliverDuties_eq S t ht0]
    refine List.mem_append_left _ ?_
    erw [Model.Run.runDuties_cons]
    refine List.mem_append_left _ ?_
    apply dutyStep_poll_rel S rho hn v _ _ (poll_selected S rho hv v)
    · change (pollPre (process ((rho.stateBefore i v).st.1 hn) o
        (Model.digests rho.hash o))).outbox.head? = some _
      rw [← stateAt_eq S rho hn v i]
      rw [pollPre_eq]
      have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
        (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
      rw [hf]
      simp only [Bool.false_eq_true, ite_false, hone]
      rfl
    · rw [pollRole_vote]
      have hbody : Body.vote (encodeVote em.msg) ∈
          (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox := by
        rw [hone]
        exact List.mem_singleton_self _
      exact of_decide_eq_true
        (((VoteMember_iff _).1 (process_voteMember _ o _ (stateAt_voteMember S rho hn hv v i))).2
          em.msg hbody).2
    · exact protects_pollObj_vote S rho v _ _ _
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    have hb : Body.vote (encodeVote em.msg) ∈ (stateAt S rho hn v (i + 1)).outbox := by
      rw [stateAt_succ_restart S rho hn he]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hcut, by simpa using ⟨em, hem, rfl⟩⟩)
    exact (releasedFrom_iff S rho _ _ _).mp (releasedFrom_of_pending S rho hn hv he hb)

end Consensus.Goldilocks.Simulation
