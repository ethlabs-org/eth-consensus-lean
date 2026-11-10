module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule

public section

/-! # Sources of the payload objects of a called block

The payload provenance shared by the constant-fault `block_payload_source`
(`Simulation/RunBlocks`) and the growing-fault `block_payload_source_at`
(`Growing/Simulation/Payload`). A payload object of a block called at a public tick was in the
proposer's view before the tick; one of a delivered block was carried by the delivery. Only the
proposal closure at a tick (`hpre`) depends on the fault model; each supplies it. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **A payload object signed by a key honest at processing has an earlier genuine release.**
`hpre`: the objects a tick's proposal carries are in the proposer's view before the tick. -/
theorem block_payload_source_of (hv : rho.ExecutionValid)
    (hpre : ∀ {i : Nat} {v : V} {t : Time}, rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E)).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {k : Nat} {y} {B : Blk (S.params (pubOf E) hn)} (hc : (simTrace S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V)} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  obtain ⟨acc, hnode, hlab⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hbefore : ∀ j < i, cutMap S rho hn (j + 1) ≤ k := by
    intro j hj
    exact (cutMap_mono S rho hn (show j + 1 ≤ i by omega)).trans hstart
  cases ev with
  | tick v t =>
    have hv' : v ∉ rho.faultyAt 0 := by
      have hm := List.mem_of_getElem? he
      exact fun hf => hv.honest_only _ hm (rho.faultyAt_mono (hv.in_horizon _ hm).1 hf)
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    obtain ⟨N4, N5, Q, R4, F, G, _, _, _, _, _, _, _, hR4, hcar, _⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (hpre he)
    have hB : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
      rw [hR4]; exact mem_blockObjs.mpr ⟨B, acc, hcut, rfl⟩
    have ho' := hcar _ hB o ho
    have hnil := outbox_empty S rho hn hv v i
    have hrel : relHead S rho v (rho.stateBefore i v).seen
        (stateAt S rho hn v i).outbox.head? = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨b, hb, _⟩ := mem_relHead S rho hx
      simp [hnil] at hb
    rw [hrel, List.append_nil] at ho'
    have htime' : (simTrace S rho hn).time k = t := htime
    rw [htime'] at hu
    have hui : u ∉ rho.faultyAt (rho.cutTime i) := by
      have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
      have ht := hlaws.cutTime_mono i (i + 1) (by omega)
        (by
          change i + 1 ≤ rho.events.length
          exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1)
      change rho.cutTime i ≤ rho.cutTime (i + 1) at ht
      simp only [Model.Run.cutTime, he, Model.Event.time] at ht
      exact fun hf => hu (rho.faultyAt_mono ht hf)
    obtain ⟨j, hj, t', hs, hr⟩ := rho.signed_seen_released hv
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1) ho' hui hsign
    exact ⟨j, t', hbefore j hj, hs, hr⟩
  | deliver v x t =>
    rw [eventCuts_deliver S rho hn i v x t he] at hmem
    obtain ⟨x', e, st', hx, hce, m, hm, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hm
    rw [← hc, hrl] at hcut
    have heq : e = .block B := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        simp only [exec, onBlock] at hcut
        split_ifs at hcut
        · simp at hcut
        · split at hcut <;> simp [acCall] at hcut <;> simp_all
      | message => simp [exec, onMessage, acCall] at hcut
      | attestation => simp [exec, onAttestation] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    have hcontains := (contains_of_mem_delivered hx).trans (Model.Obj.Contains.step ho (.refl o))
    have htime' : (simTrace S rho hn).time k = t := htime
    rw [htime'] at hu
    obtain ⟨j, t', hj, hs, hr⟩ := hv.unforgeable i v x t he o hcontains u hsign hu
    exact ⟨j, t', hbefore j hj, hs, hr⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

end Consensus.Goldilocks.Simulation

end
