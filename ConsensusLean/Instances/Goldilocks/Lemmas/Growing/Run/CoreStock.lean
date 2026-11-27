module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # The stock run-facts bundles

The stock instances of the Option B bundles: `GoldilocksRun.toStaticCore` (the static core at
`Store.updateFinality` and `Node.frame`), with the bridges `Store.onBlock_eq_onBlockWith`,
`Store.Reachable.reachableWith` and `Node.CutStep.with`. -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

namespace Store

variable {P : Params} {ACP : Type}

/-- The stock acceptance is `onBlockWith` at the stock finality update. -/
theorem onBlock_eq_onBlockWith (st : Store P ACP) (B : NodeBlock P ACP) :
    st.onBlock B = st.onBlockWith updateFinality B := by
  rw [onBlockWith_eq]
  rfl

/-- A reachable store is reached with the stock finality update. -/
theorem Reachable.reachableWith {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    ReachableWith updateFinality acp₀ st := by
  rw [reachableWith_eq]
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    refine ih.tail ((stepWith_iff _ _ _).2 ?_)
    rcases hs with ⟨B, hB⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨B, (onBlock_eq_onBlockWith _ B) ▸ hB⟩
    · exact Or.inr ⟨a, ha⟩

end Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The stock cut law is the cut law at the stock finality update and frame. -/
theorem Node.CutStep.with {self : Fin sp.n} {t : Time} {st st' : NodeState (goldilocksNode sp ro)}
    {c : Cut (goldilocksNode sp ro)} (h : Node.CutStep self t st c st') :
    CutStepWith Store.updateFinality Node.frame self t st c st' := by
  rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
  · exact (cutStepWith_block_false B).2 ⟨by rw [← Store.onBlock_eq_onBlockWith]; exact h.1, h.2⟩
  · exact (cutStepWith_block_true B).2
      ⟨h.1, by rw [← Store.onBlock_eq_onBlockWith]; exact h.2.1, h.2.2⟩
  · exact (cutStepWith_attestation a).2 h
  · exact (cutStepWith_attest_none C).2 h
  · exact (cutStepWith_attest_some C a).2 h
  · exact (cutStepWith_ac ℓ).2 h

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **The static core of a stock Goldilocks run.** -/
theorem GoldilocksRun.toStaticCore (hrun : GoldilocksRun proposer dg H tr ini) :
    StaticRunCore Store.updateFinality Node.frame proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality
  frameOf_F _ := rfl
  frameOf_tree _ _ := Iff.rfl
  init := hrun.init
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  root_ok := hrun.genesis_root_ok
  cutLaw y hy i c hc := (hrun.cutLaw y hy i c hc).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  sleep_of_restart := hrun.sleep_of_restart
  sign_public y hy k a hs := by
    obtain ⟨C, hc⟩ := hs
    obtain ⟨j, -, ht⟩ := Compose.attestCall_tick hrun.toLocalRun hy hc
    exact hrun.tick_public y hy j _ ht
  reachable y hy i := (Compose.fg_reachable hrun.toLocalRun hy i).reachableWith
  frameOK y hy i := Compose.frameOK_state hrun.toLocalRun hy i
  projAC_state y hy i := Compose.projAC_state hrun.toLocalRun hy i
  acRun hnc := Compose.goldilocks_ac_projection_from hrun hnc
  coherent hnc := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  tree_mono y hy _ _ hki := Compose.tree_mono hrun.toLocalRun hy hki
  tree_accepted y hy _ _ hW := Healing.tree_accepted hrun.toLocalRun hy hW
  hj_mono y hy _ _ hij := Healing.hj_mono hrun.toLocalRun hy hij
  ac_block_after y hy _ _ ha := Healing.ac_block_after hrun.toLocalRun hy ha
  attest_source y hy _ _ _ hc := Compose.attest_source hrun.toLocalRun hy hc
  report_attest y hy _ _ _ hk hc hC := Healing.toFG_attest hrun.toLocalRun hy hk hc hC
  signed_tick y hy d C a hcd := by
    obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Compose.call_in_group hrun.toLocalRun hy hcd
    obtain ⟨x, rfl⟩ := @Compose.signed_only_in_ticks sp.toParams (goldilocksNode sp ro)
      proposer dg y _ _ _ C a (List.mem_of_getElem? hk)
    have hkk : kk < (Node.exec proposer dg y (tr.state y j) (tr.time d)
        (.tick x true)).2.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.mp h)] at hk
      cases hk
    refine ⟨j, by omega, fun i h1 h2 => ⟨?_, fun ℓ hc m hm => ?_⟩, fun i hi c hc ht => ?_⟩
    · have := (hg.2.1 (i - j) (by omega)).2.1
      rwa [Nat.add_sub_cancel' h1] at this
    · have hl := (hg.2.1 (i - j) (by omega)).2.2.2.2
      rw [Nat.add_sub_cancel' h1, hc.2] at hl
      have hmem := List.getElem_mem
        (l := (Node.exec proposer dg y (tr.state y j) (tr.time d) (.tick x true)).2)
        (n := i - j) (by omega)
      rw [← Option.some.inj hl] at hmem
      cases (Healing.exec_ac_call y _ _ _ hmem).2 m hm
    · obtain ⟨ℓ, he, hr⟩ := Compose.before_tick hrun.toLocalRun hy ⟨x, true, hg⟩ hc hi ht
      exact ⟨ℓ, he, hr⟩
  late_tick y hy t ht0 hpub hw := by
    obtain ⟨jt, x, fgDue, hgt⟩ := hrun.tick_of_awake y hy t ht0 hpub hw
    obtain ⟨hct, htt⟩ := Healing.tick_first_cut hgt
    refine ⟨jt, _, hct, rfl, htt, fun i W hA hit hnp => ?_⟩
    rcases Compose.blockCall_cases hrun.toLocalRun hy hA with hgW | ⟨j, x', f', -, -, hP, -⟩
    · rw [hit] at hgW
      rcases lt_trichotomy jt i with h | rfl | h
      · exact h
      · have := hct.2.symm.trans hA.2
        simp [Node.acCall] at this
      · have := hrun.phase_order y hy y hy i jt t (.block W) (.tick x fgDue) hgW hgt h (.inl rfl)
        simp [Node.Event.phase] at this
    · exact absurd (hit ▸ hP) hnp
  joined_at_call y hy i t hi hnr hit := (Compose.joined_projection_from hrun hy t).2.1 i hi hnr hit
  signed_before_attest y hy _ _ _ hc _ hY _ ha haH :=
    Healing.signed_before_attest hrun.toLocalRun hy hc hY ha haH
  accept_of_proposesAt hnc _ _ _ hp hW := Healing.accept_of_proposesAt hrun hnc hp hW
  proposal_payload hp hW := by
    obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
    rcases Compose.blockCall_cases hrun.toLocalRun hp hc with hg |
      ⟨j, x, fgDue, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
    · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    · exact ⟨d.head, by rw [hB]; rfl, by rw [hfgj, hB]; rfl⟩
  driven hnc := Healing.projection_driven_of_run hrun hnc hrun.genesis_root_ok
  lock_origin hnc y hy i := Compose.lock_origin hrun hnc hy i
  vote_of_awake_joined hnc y hy _ hmv hw hj := Compose.vote_of_awake_joined hrun hnc hy hmv hw hj
  awake_participant_early hnc _ _ hsync hb _ hX _ _ hu y hy hmv hw hj :=
    Compose.awake_participant_early hrun hnc hsync hb hX hu hy hmv hw hj

/-- **The core of a stock Goldilocks run under growing faults.** -/
theorem Growing.GoldilocksRun.toCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) :
    GoldilocksRunCore Store.updateFinality Node.frame proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality
  frameOf_F _ := rfl
  frameOf_tree _ _ := Iff.rfl
  antitone := hrun.antitone
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  upTo hd := (hrun.upTo hd).toStaticCore
  cutLaw y i c hc hy := (hrun.cutLaw y i c hc hy).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  acRun hnc := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  coherent hnc := Compose.Growing.honest_blocks_coherent hrun hnc
  held_anc_at hnc := fun hd hy hi h hW => Compose.Growing.held_anc_at hrun hnc hd hy hi h hW
  F_mono_at hd hy hi hki := Compose.Growing.F_mono_at hrun hd hy hi hki
  acRelayAt hx hacc hy hc hanc relay := hrun.toLocalRun.acRelayAt hx hacc hy hc hanc relay
  acCatchAt hcatch := fun hx ha hi hy hc hj hanc =>
    hrun.toLocalRun.acCatchAt hcatch hx ha hi hy hc hj hanc

end Consensus.Goldilocks

end
