module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation

public section

/-! # Held blocks and their evidence belong to the engine reader's view

Track the accepting node cut back to its engine event, retaining the event index. A release
at the same time without that index would not suffice for an event-cut read. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every called block, accepted or refused, has its canonical object in the final view
of the honest engine node responsible for the call. -/
theorem occurring_in_view (hv : rho.ExecutionValid) {B : Blk (S.params (pubOf E) hn)}
    (hB : (simTrace S rho hn).Occurs B) :
    B.parent ≠ none ∧ ∃ v ∈ rho.honest, blockObj (S.params (pubOf E) hn) B ∈
      rho.ViewIdx v rho.events.length := by
  obtain ⟨y, k, acc, hnode, hlab⟩ := hB
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, _, _, hidx, hn', _, hpk, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hhon := hv.honest_only ev (List.mem_of_getElem? he)
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    have hr0 : r.pos ≠ 0 := by
      intro hr0
      obtain ⟨_, _, _, h⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inl ⟨hr0, _, hrl⟩)
      cases h
    have hnf := Regimes.non_framing _ _ _ _ _ _ (simTrace_goldilocksRun S rho hn hv)
      _ (honest_ownKey (S := S) hhon)
    have hrel := (tick_releases S rho hn hv hhon he hp hnf r hmem).1 B acc hrl hr0
    refine ⟨?_, v, hhon, rho.mem_viewIdx_iff.mpr
      ⟨i, _, hi, Or.inl ⟨t, Or.inl he, hrel⟩, .refl _⟩⟩
    have hy : y ∈ honestKeys S rho := by
      have : rho.ownKey v = y := hn'.symm.trans hnode
      rw [← this]
      exact honest_ownKey (S := S) hhon
    rcases Compose.blockCall_cases (simTrace_goldilocksRun S rho hn hv).toLocalRun hy
      ⟨hnode, hlab⟩ with hg | ⟨j, x, _, _, _, d, p, _, hB', _⟩
    · have hpos := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim (hr0 (hpk.symm.trans (by simpa using hpos)))
    · rw [hB']; simp [mkBlock]
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, kk, hk, hlk, _⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := hlk.symm.trans hrl
    have hzero := pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk hcut
    subst kk
    have heq : e = .block B := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        have hm := List.getElem_mem hk
        rw [hcut] at hm
        simp only [exec, onBlock] at hm
        split_ifs at hm
        · simp at hm
        · split at hm <;> simp [acCall] at hm <;> simp_all
      | message m => simp [exec, onMessage, acCall] at hcut
      | attestation a => simp [exec, onAttestation] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    have ho' := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    rw [ho'] at ho
    exact ⟨(decodeBlock_wire (decodeBlock_of_canonEvent hce)).2.1, v, hhon,
      rho.mem_viewIdx_iff.mpr ⟨i, o, hi, Or.inr ⟨t, he⟩, contains_of_mem_delivered ho⟩⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hlk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _))
    rw [← hlk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- An accepted block is in its reader's engine view at every subsequent mapped cut. -/
theorem accepted_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {k i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hacc : (simTrace S rho hn).AcceptAt (rho.ownKey v) k B)
    (hki : k < cutMap S rho hn i) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  obtain ⟨hnode, hlab⟩ := hacc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, j, ev, _, he, hjk, _, hidx, hn', _, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hji : j < i := by
    by_contra h
    have := cutMap_mono S rho hn (not_lt.1 h)
    omega
  have hrl : r.label = .fg (.block B true) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = v := rho.key.symm.injective (hn'.symm.trans hnode)
  have hrun := simTrace_goldilocksRun S rho hn hv
  cases ev with
  | tick w t =>
    change w = v at hkey
    subst w
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn j v t he hp] at hmem
      simp at hmem
    have hr0 : r.pos ≠ 0 := by
      intro hr0
      obtain ⟨_, _, _, h⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inl ⟨hr0, _, hrl⟩)
      cases h
    have hnf := Regimes.non_framing _ _ _ _ _ _ hrun _ (honest_ownKey (S := S) hv')
    have hrel := (tick_releases S rho hn hv hv' he hp hnf r hmem).1 B true hrl hr0
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji, Or.inl ⟨t, Or.inl he, hrel⟩, .refl _⟩
  | deliver w o t =>
    change w = v at hkey
    subst w
    rw [eventCuts_deliver S rho hn j v o t he] at hmem
    have hnow := (now_eq_lastClock S rho hn hv v j).trans (lastClock_deliver S rho hv he)
    have hq := ((process_relay (runProposer S rho hn)
      (digestOf S rho) (Model.digests rho.hash o) t j
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v j) 0 hnow).2.2.2 r
      (by rw [stateAt_self]; exact hmem)).1 B hrl
    obtain ⟨cs, hx, hrel⟩ := deliver_relays S rho hn he hq
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji, Or.inl ⟨t, Or.inr ⟨o, he⟩, hrel⟩,
      .step hx (.refl _)⟩
  | restart w t =>
    exfalso
    rw [eventCuts_restart S rho hn j w t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _))
    rw [← hlabk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- CLAIMS R.8/F.2 and Refinement G1.5: every held non-genesis block was accepted earlier;
`accepted_in_view` retains the engine event index needed to put it in this reader's view.

Paper argument (implementation bridge, not a quotation): apply `tree_cases` at node cut
`cutMap i`. Its genesis alternative contradicts `hg`; otherwise it gives acceptance at some
`k < cutMap i`. Apply `accepted_in_view` with that strict inequality. That theorem locates an
engine event `j` with `cutMap j ≤ k`; monotonicity forces `j < i`, so even simultaneous events
cannot move evidence past the read. No collision or awake-at-read assumption is needed.
Status: proved relative to the existing simulation/acceptance lemmas. -/
theorem held_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    (hg : B.root ≠ (S.params (pubOf E) hn).genesisRoot) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  rcases Compose.tree_cases (simTrace_goldilocksRun S rho hn hv).toLocalRun
      (honest_ownKey (S := S) hv') hB with hgen | ⟨k, hk, hacc⟩
  · exact (hg (congrArg Block.root hgen)).elim
  · exact accepted_in_view S rho hn hv hv' hacc hk

/-- CLAIMS G1.5 evidence binding: canonical block objects carry their payload attestations,
and views are closed under carried objects. Genesis has no attestations. This applies to ANY
held block, as required by R.7's two witness chains, not just finalized ancestors.

Paper argument: reachable-store coherence identifies any held block with genesis root as
genesis itself, whose FG payload is empty. Membership of `a` excludes that case. By
`held_in_view`, `blockObj B` is in the view. Its carried list is `payloadObjs B.fgPayload
B.acPayload`, which includes `attObj a` by list-map membership. Compose this direct containment
with the view's witnessing containment (`mem_viewIdx_iff`); views are transitively closed
under carried objects. This uses every held block, not the false restriction that R.7's
witness chains end at the finalized tips. The proof uses the acceptance alternative directly;
the genesis alternative has no attestations. Status: proved. -/
theorem held_att_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    {a : FG.Att (Fintype.card V)} (ha : a ∈ B.fgPayload) : attObj a ∈ rho.ViewIdx v i := by
  rcases Compose.tree_cases (simTrace_goldilocksRun S rho hn hv).toLocalRun
      (honest_ownKey (S := S) hv') hB with hgen | ⟨k, hk, hacc⟩
  · subst B
    simp [Params.genesisBlock] at ha
  · have hb := accepted_in_view S rho hn hv hv' hacc hk
    obtain ⟨j, o, hj, ho, hc⟩ := rho.mem_viewIdx_iff.mp hb
    refine rho.mem_viewIdx_iff.mpr ⟨j, o, hj, ho, hc.trans (.step ?_ (.refl _))⟩
    change attObj a ∈ payloadObjs B.fgPayload B.acPayload
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

variable (V) in
/-- CLAIMS Refinement G1.5 (b): `mem_chainTo` places each read header in the held tree;
encoding round-trip identifies its attestations, then `held_att_in_view` binds the evidence.

Paper argument: the quantified reader supplies `n ≥ 1`; use `simTrace_simulates` and
`read_finalized`. Its tip is held by the reachable-store cache invariant. `mem_chainTo` makes
the read header `headerOf B` for a held block B. `decodeInfo_encodeInfo` and injectivity of
`some` identify the decoded list `atts` with `B.fgPayload`; apply `held_att_in_view` to `a`.
If V is empty there is no reader, so no simulation with `n ≥ 1` is required. The bound
`i ≤ events.length` is exactly the domain of simulation's state agreement.
Status: proved relative to simulation. -/
theorem evidenceInView : EvidenceInView V S := by
  intro E rho hv v hv' i hi h hh atts p hd a ha
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hs := simTrace_simulates S rho hn hv
  have hr := Compose.fg_reachable hs.run.toLocalRun (honest_ownKey (S := S) hv')
    (cutMap S rho hn i)
  rw [read_finalized hs hv' hi] at hh
  obtain ⟨B, hB, _, _, rfl⟩ := mem_chainTo hr (Store.cache_invariants _ _ _ _ hr).1 hh
  have hd' : (B.fgPayload, B.acPayload) = (atts, p) := by
    simpa only [headerOf, decodeInfo_encodeInfo, Option.some.injEq] using hd
  have he : B.fgPayload = atts := congrArg Prod.fst hd'
  exact held_att_in_view S rho hn hv hv' hB (by rw [he]; exact ha)

end Consensus.Goldilocks.Refinement

end
