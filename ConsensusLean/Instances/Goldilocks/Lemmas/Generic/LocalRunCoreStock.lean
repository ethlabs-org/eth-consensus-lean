module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.LocalRunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient

public section

/-! # The stock node-run bundle

`Growing.LocalRun.toLocalRunCore`: a stock node run under growing faults (any node AC) gives the
generic core at `Store.updateFinality`, each field the stock lemma on the honest prefix
(`hrun.upTo`), with the reachability bridge `Store.Reachable.reachableWith'`. -/

namespace Consensus.Goldilocks.Generic

namespace StockCore

variable {P : Params} {ACP : Type}

theorem onBlock_eq_onBlockWith (st : Store P ACP) (B : NodeBlock P ACP) :
    st.onBlock B = st.onBlockWith Store.updateFinality B := by
  rw [Store.onBlockWith_eq]
  rfl

theorem reachableWith {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    Store.ReachableWith Store.updateFinality acp₀ st := by
  rw [Store.reachableWith_eq]
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    refine ih.tail ((Store.stepWith_iff _ _ _).2 ?_)
    rcases hs with ⟨B, hB⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨B, (onBlock_eq_onBlockWith _ B) ▸ hB⟩
    · exact Or.inr ⟨a, ha⟩

end StockCore

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

private theorem held_att_signed (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (h.upTo ht) hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := h.att_unforgeable y k a
      (h.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (h.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **The core of a stock node run under growing faults.** -/
theorem _root_.Consensus.Goldilocks.Growing.LocalRun.toLocalRunCore
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) :
    LocalRunCore Store.updateFinality proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality
  antitone := hrun.antitone
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  reachable_at := fun {y k t} ht hle hy => by
    have h := Compose.fg_reachable (hrun.upTo ht) hy k
    rw [Trace.upTo_state tr y hle] at h
    exact StockCore.reachableWith h
  coherent hnc := Compose.Growing.honest_blocks_coherent_local hrun hnc
  held_anc_at hnc := fun {y k t B C} ht hle hy hBC hC => by
    have hs := Trace.upTo_state tr y hle
    have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
    have hanc := RunTrace.anc_upTo_of_right hrun hnc ht hc hBC
    rw [← hs]
    exact Healing.store_anc_of_honest_anc_from (hrun.upTo ht)
      (Compose.NoCollRun.upTo hnc t) hy hanc (by rwa [hs])
  tree_mono_at := fun {y k i t} ht hle hy hki => by
    have h := Compose.tree_mono (hrun.upTo ht) hy hki
    rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h
  tree_accepted_at := fun {y i t W} ht hle hy hW => by
    have hW' : W ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hW
    rcases Healing.tree_accepted (hrun.upTo ht) hy hW' with h | ⟨k, hk, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk, ((RunTrace.upTo_acceptAt _).mp ha).2⟩
  att_unforgeable := hrun.att_unforgeable
  attest_some := fun {y k C a} hc hy => hrun.cutLaw y k _ hc hy
  attest_none := fun {y k C} hc hy => hrun.cutLaw y k _ hc hy
  signAt_entry := fun {y k att} hy hs => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
    have h := Healing.signAt_entry_from (hrun.upTo (hrun.time_nonneg k)) hy
      ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    rwa [Trace.upTo_state tr y hle] at h
  signed_before_attest := fun {y k C s} hy hc {Y} hY {a} ha haH => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
    have hc' : (tr.upTo (tr.time k)).CallAt y k (.fg (.attest C s)) :=
      (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
    have hY' : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
      rw [Trace.upTo_state tr y hle]; exact hY
    obtain ⟨j, hj, hjt⟩ :=
      Healing.signed_before_attest (hrun.upTo (hrun.time_nonneg k)) hy hc' hY' ha haH
    exact ⟨j, ((RunTrace.upTo_signAt tr).mp hj).2, hjt⟩
  client_record_origin := fun {y i t} ht hle hy h r => by
    have hs := Trace.upTo_state tr y hle
    obtain ⟨h₁, h₂⟩ := Healing.client_record_origin_from (hrun.upTo ht) hy h r i
    rw [hs] at h₁ h₂
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨k, hk, att, hsa, he⟩ := h₁ hx
      exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
    · obtain ⟨k, hk, att, hsa, he⟩ := h₂ hx
      exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
  sent_origin := fun {y i t} ht hle hy {b} hb => by
    have hs := Trace.upTo_state tr y hle
    obtain ⟨k, hk, att, hsa, he⟩ :=
      Healing.sent_origin_from (hrun.upTo ht) hy i (by rw [hs]; exact hb)
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
  record_sentOK := fun {y i t} ht hle hy => by
    have h := (Healing.record_facts (hrun.upTo ht) hy i).1
    rw [Trace.upTo_state tr y hle] at h
    exact (Healing.Client.sentOK_iff _).1 h
  hj_mono_at := fun {y k i t} ht hle hy hki => by
    have h := Healing.hj_mono (hrun.upTo ht) hy hki
    rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h
  held_atts_safe_at := fun {y x m i u t d} hu hytime hy ht hxtime hx hud htd a b ha hb hav hab => by
    obtain ⟨k, hk, hka⟩ := held_att_signed hrun hu hytime hy ha (hrun.antitone hud hav)
    obtain ⟨l, hl, hlb⟩ := held_att_signed hrun ht hxtime hx hb
      (hab.1 ▸ hrun.antitone htd hav)
    rw [← hab.1] at hlb
    have hka' : (tr.upTo d).SignAt a.val k a :=
      (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
    have hlb' : (tr.upTo d).SignAt a.val l b :=
      (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
    obtain ⟨inputs, hin, hs⟩ :=
      Store.signed_run_of_exec (Compose.fg_exec (hrun.upTo (hu.trans hud))) hav (max k l + 1)
    exact FG.client_safety P.fg a.val inputs hin
      a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
      b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab
  signAt_wellFormed := fun {y k att} hy hs =>
    Healing.signAt_wellFormed_from (hrun.upTo (hrun.time_nonneg k)) hy
      ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  accept_of_proposesAt hnc hroot hq := fun {p k X} hp hX => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
    have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono (by omega)
    have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    obtain ⟨hacc, hm, hpost⟩ := Healing.accept_of_proposesAt_from (hrun.upTo (hrun.time_nonneg k))
      hroot (hnc.upTo _) hp (hq p) hX'
    rw [Trace.upTo_state tr p hle1] at hm hpost
    exact ⟨((RunTrace.upTo_acceptAt _).mp hacc).2, hm, hpost⟩
  proposal_parent_held hnc hroot hq := fun {p k X} hp hX => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
    have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    have h := Healing.proposal_parent_held_from (hrun.upTo (hrun.time_nonneg k)) hroot
      (hnc.upTo _) hp (hq p) hX'
    rwa [Trace.upTo_state tr p hle] at h
  proposal_rows_placed hnc hroot hq := fun {p kX X Pr} hp hX hpar hPr => by
    have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
    have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono (by omega)
    have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    have hst : (tr.upTo (tr.time kX)).projFG.store p (kX + 1) = (tr.state p (kX + 1)).fg := by
      change ((tr.upTo (tr.time kX)).projFG.state p (kX + 1)).1 = _
      rw [Compose.projFG_state (hrun.upTo (hrun.time_nonneg kX)) hp, Trace.upTo_state tr p hle1]
    obtain ⟨-, hXt, hPrt, hσX, hσPr, hplace⟩ :=
      Healing.proposal_rows_placed_from (hrun.upTo (hrun.time_nonneg kX)) (fun y _ => hq y) hroot
        (hnc.upTo _) hp hX' hpar (by rw [Trace.upTo_state tr p hle]; exact hPr)
    rw [hst] at hXt hPrt hσX hσPr
    rw [Trace.upTo_state tr p hle] at hσPr hplace
    refine ⟨hXt, hPrt, hσX, hσPr, fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
    have := hplace att ⟨k', hk', (RunTrace.upTo_processAttAt _).mpr
      ⟨hrun.time_mono hk'.le, hproc⟩⟩ hah haT
    rwa [hst] at this

end Consensus.Goldilocks.Generic

end
