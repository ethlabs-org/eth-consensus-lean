module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Own signing cuts behind processed attestations

An attestation processed while its signer is honest was signed by the signer at an earlier
cut. The argument reads only the engine run and its simulating trace; the fault model enters
through the signer's release analysis. Constant faults (`RunBlocks`) and growing faults
(`Growing/Simulation/Attestations`) supply it. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- An attestation that a node processes at cut `k`, while its signer is honest at the cut's
time, was signed by the signer at an earlier cut. Premise `hrel`: a release of the attestation
at an engine event of the signer comes from an own signing cut of that event
(`released_att_cut` for constant faults, `released_att_cut_at` for growing faults). -/
theorem attCall_sign_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {a : FG.Att (Fintype.card V)} (hc : (simTrace S rho hn).AttCallAt y k a)
    (hhon : rho.key a.val ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key a.val) j t → attObj a ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).SignAt a.val q a) :
    ∃ j < k, (simTrace S rho hn).SignAt a.val j a := by
  obtain ⟨hnode, hlab⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, hi, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.attestation a) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hidx
    have hm := (List.getElem?_eq_some_iff.mp hidx).1
    have hr := (List.getElem?_eq_some_iff.mp hidx).2
    have hc := (getElem_groupRecs _ _ _ _ _ _ _ _ hm).2.2.2.2
    rw [hr, hrl] at hc
    have hcs : (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2[k - cutMap S rho hn i]? =
          some (.fg (.attestation a)) := by
      rw [List.getElem?_eq_getElem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _)), ← hc]
    obtain ⟨q, hq, C, hC⟩ := Compose.tick_attestation_prev _ _ _ _ _ _ hcs
    have hval := attest_val_of_mem_exec (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t))) (List.mem_of_getElem? hC)
    have hq' : q < (eventCuts S rho hn i).length := by
      rw [eventCuts_tick_public S rho hn i v t he hp, length_groupRecs]
      exact (List.getElem?_eq_some_iff.mp hC).1
    have hrec := allCuts_getElem?_add S rho hn i q (List.getElem?_eq_some_iff.mp he).1 hq'
    rw [List.getElem?_eq_getElem hq'] at hrec
    refine ⟨cutMap S rho hn i + q, by omega, C, ?_, ?_⟩
    · rw [simTrace_node, hrec]
      simp only [Option.elim_some]
      simp only [eventCuts_tick_public S rho hn i v t he hp]
      exact (getElem_groupRecs _ _ _ _ _ _ _ _ _).1.trans hval.symm
    · rw [simTrace_label, hrec]
      simp only [Option.map_some]
      simp only [eventCuts_tick_public S rho hn i v t he hp]
      exact congrArg some ((getElem_groupRecs _ _ _ _ _ _ _ _ _).2.2.2.2.trans
        (List.getElem?_eq_some_iff.mp hC).2)
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hq
    rw [← hc, hrl] at hcut
    have heq : e = .attestation a := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | attestation a' =>
        simp only [exec, onAttestation, List.mem_singleton, Cut.fg.injEq,
          FGLabel.attestation.injEq] at hcut
        exact congrArg Event.attestation hcut.symm
      | block B =>
        simp only [exec, onBlock] at hcut
        split_ifs at hcut
        · simp at hcut
        · split at hcut <;> simp [acCall] at hcut
      | message => simp [exec, onMessage, acCall] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    have ho' : o' = attObj a := by
      rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨a', h, ho⟩
      · cases h
      · cases h
      · cases h; exact ho
    subst o'
    have hh' : rho.key a.val ∉ rho.faultyAt t := by
      rw [htime] at hhon
      exact hhon
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ (contains_of_mem_delivered ho)
      (rho.key a.val) rfl hh'
    obtain ⟨q, hq, hs⟩ := hrel hs hb
    have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
      cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
    exact ⟨q, by omega, hs⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

end Consensus.Goldilocks.Simulation
