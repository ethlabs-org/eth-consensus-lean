module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow P-U windows

The maximum height and top status are fixed at every honest cut. Justification is fixed
only in top windows. The sequential pigeonhole is the existing frame-independent theorem;
the key-to-frame-data step uses the shadow key instead of the merged stock key.
-/

namespace Consensus.Goldilocks.Healing

open Consensus.Goldilocks.Generic (riseRounds)

variable {P : Params} {A : NodeAC P}

/-- A P-U viable held block is above finality. In the predecessor-height top case use
`F ⪯ J ⪯ Q`; all other cases are strictly above `hj` and use the existing G1.2 proof. -/
theorem finalized_below_viable {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hR : st.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub : st.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ st.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ st.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    {Q : NodeBlock P ACP} (hQ : Q ∈ st.tree) (hv : st.IsViable Q) : st.Anc st.F Q := by
  have hj := Healing.Store.hj_lt_hmax_of_reachable hR
  rcases (Store.isViable_iff st Q).mp hv with hh | ⟨hh, hgap | hJ⟩
  · exact Healing.Store.F_anc_of_hj_lt_of_safe hR hR hU hsub hsub hV hsafe hQ (by omega)
  · exact Healing.Store.F_anc_of_hj_lt_of_safe hR hR hU hsub hsub hV hsafe hQ (by omega)
  · exact (Store.cache_invariants _ _ _ _ hR).2.2.1.trans hJ

/-- Viability transport within fixed numerical frame data. The caller separately supplies
finalized ancestry at the receiving cut, using `finalized_below_viable'`. -/
theorem isViable_of_window_data {ACP : Type} {a b : Store P ACP} {Q : NodeBlock P ACP}
    (hm : a.hmax = b.hmax) (ht : (a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1))
    (hJ : a.hmax = a.hj + 1 → a.J = b.J) (hb : b.hj < b.hmax)
    (hσ : a.σ Q.root = b.σ Q.root)
    (hanc : a.Anc a.J Q → b.Anc a.J Q) (hv : a.IsViable Q) : b.IsViable Q := by
  rw [Store.isViable_iff] at hv ⊢
  rcases hv with hh | ⟨hh, hgap | hAQ⟩
  · exact Or.inl (by rw [← hm, ← hσ]; exact hh)
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, Or.inl ?_⟩
    have hnot : ¬ b.hmax = b.hj + 1 := fun h => by
      have := ht.mpr h
      omega
    omega
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, ?_⟩
    by_cases htop : a.hmax = a.hj + 1
    · exact Or.inr (hJ htop ▸ hanc hAQ)
    · exact Or.inl (by have := ht.not.mp htop; omega)

open AC (ACParams Payload)

section Persistence

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The shadow fork-choice root is F at every cut, so its monotonicity needs no window
or top-status case split. -/
theorem fcRoot_mono (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i) :
    Anc (tr.HonestBlocks H) (Node.frame (tr.state y a)).fcRoot
      (Node.frame (tr.state y i)).fcRoot := by
  rw [Node.frame_eq, Node.frame_eq, Store.toFrame_fcRoot, Store.toFrame_fcRoot]
  exact run_F_mono hrun.toLocalRun hy hai

/-- V-B4: a write-frame viable head remains a viable head at later cuts in the P-U window.
The only new geometric step is `finalized_below_viable'`; the rest is the stock persistence
argument, with fixed maximum height and top status in place of the old merged floor. -/
theorem _root_.Consensus.Goldilocks.Generic.FrameWindow.viableHead_persists'
    {lo hi : Time} {M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) lo hi M isTop J)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y a ell)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    Q ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  have htime := hrun.time_mono hai
  rw [Compose.frame_of_projAC hrun hy hc, Node.frame_eq,
    Store.toFrame_viableHeads] at hv
  have hQa : Q ∈ (tr.state y a).fg.tree := hv.1
  have hQi := Compose.tree_mono hrun.toLocalRun hy hai hQa
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun B hB => ⟨y, hy, i, hB⟩
  have hvi : (tr.state y i).fg.IsViable Q := by
    apply isViable_of_window_data
      ((hframe.M_eq y a hy halo (htime.trans hihi)).trans
        (hframe.M_eq y i hy (halo.trans htime) hihi).symm)
      ((hframe.top_iff y a hy halo (htime.trans hihi)).trans
        (hframe.top_iff y i hy (halo.trans htime) hihi).symm)
      (fun ht => (hframe.root_eq y a hy halo (htime.trans hihi)
        ((hframe.top_iff y a hy halo (htime.trans hihi)).mp ht)).trans
        (hframe.root_eq y i hy (halo.trans htime) hihi
          ((hframe.top_iff y a hy halo (htime.trans hihi)).mp ht)).symm)
      (hj_lt_hmax hrun hy i)
      (Healing.Store.σ_eq_of_mem
        (Compose.fg_reachable hrun.toLocalRun hy a)
        (Compose.fg_reachable hrun.toLocalRun hy i)
        (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1
        (fun _ hB => ⟨y, hy, a, hB⟩) hsub hQa hQi)
      (fun h => h.mono (Compose.tree_mono hrun.toLocalRun hy hai)) hv.2.2
  have hFQ := finalized_below_viable (Compose.fg_reachable hrun.toLocalRun hy i)
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hsub hf
    (fun a b ha hb hv => held_atts_safe (Compose.projFG_localRun hrun hnc) hy hy i i a b
      (by simpa only [Compose.store_eq hrun hy] using ha)
      (by simpa only [Compose.store_eq hrun hy] using hb) hv) hQi hvi
  have hQt : Q ∈ (tr.state y i).fg.toFrame.tree := by
    rw [Store.toFrame_tree]
    exact ⟨hQi, hFQ⟩
  refine ⟨?_, ?_, ?_⟩
  · rwa [Node.frame_eq]
  · rw [Node.frame_eq, Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict .refl hFQ
  · rw [Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hQi, hFQ, hvi⟩

/-- An earlier action supplies a frozen viable descendant of the current F-root, in both
top and gap windows. No non-top premise or common-J fallback is needed. -/
theorem _root_.Consensus.Goldilocks.Generic.FrameWindow.root_witness_of_earlier_call'
    {lo hi g : Time} {M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) lo hi M isTop J)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode sp)}
    (ha : tr.projAC.CallAt y a ell₀) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < AC.freeze sp e.msg.slot)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot) :
    ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hR := Compose.fg_reachable hrun.toLocalRun hy a
  obtain ⟨-, -, -, -, -, ⟨Q, hQ, hQh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hv : (tr.state y a).fg.IsViable Q :=
    (Store.isViable_iff _ _).mpr (Or.inl hQh.ge)
  have hFQ := finalized_below_viable hR
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc)
    (fun B hB => ⟨y, hy, a, hB⟩) hf
    (fun b c h₁ h₂ hv => held_atts_safe (Compose.projFG_localRun hrun hnc) hy hy a a b c
      (by simpa only [Compose.store_eq hrun hy] using h₁)
      (by simpa only [Compose.store_eq hrun hy] using h₂) hv) hQ hv
  have hQt : Q ∈ ell₀.frame.tree := by
    rw [Compose.frame_of_projAC hrun hy ha, Node.frame_eq,
      Store.toFrame_tree]
    exact ⟨hQ, hFQ⟩
  have hv₀ : Q ∈ ell₀.frame.viableHeads := by
    rw [Compose.frame_of_projAC hrun hy ha, Node.frame_eq,
      Store.toFrame_viableHeads]
    exact ⟨hQ, hFQ, hv⟩
  obtain ⟨hQi, hrooti, hvi⟩ :=
    hframe.viableHead_persists' hrun hnc hf hy hai halo hihi ha hv₀
  rw [← Compose.frame_of_projAC hrun hy hc.1] at hQi hrooti hvi
  refine ⟨Q, ⟨hQi, Or.inl ?_⟩, hvi, hrooti⟩
  apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQt hQi hat
  intro r _ hrs
  exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf

end Persistence

namespace Growing

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State} {hold : Time}

/-- Pool membership and declared backing give committee membership for every counted vote
on the shadow AC projection. -/
theorem _root_.Consensus.Goldilocks.Compose.Growing.CommitteeFacts.committeeTAt'
    {K : AC.CommitteeDict sp.n} (hK : Compose.Growing.CommitteeFacts tr H K)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) : AC.CommitteeTAt K tr.projAC H := by
  intro y i ℓ e hy hcast m v hv
  have hri := Compose.goldilocks_ac_projection_from
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo (tr.time i))
  rw [RunTrace.upTo_projAC] at hri
  have hb : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hcastU := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hpool : ∀ k, ∀ w ∈ e.readPoint.pool k, w.slot = k := fun k w hw =>
    AC.state_pool_slotU _ hri.localRun.toU hri.vstart hy (i + 1) k w
      (AC.readPoint_poolU hri.localRun.toU hy hcastU hw).1
  have hmem : ∀ w ∈ e.readPoint.pool v.slot, w.val = v.val →
      v.val ∈ K.committee v.slot := by
    intro w hw hwv
    have hp := (AC.readPoint_poolU hri.localRun.toU hy hcastU hw).1
    rw [Trace.upTo_state tr.projAC y hb] at hp
    exact hwv ▸ hK.hP.1 (tr.time i) y hy (i + 1) hb _ w hp
  rcases AC.merged_declared_backing_at_vote_slot hpool hv with h | ⟨w, hw, -, -, -, hwv, -⟩
  · exact hmem v h rfl
  · exact hmem w hw hwv

/-- The stock-shaped healthy AC base supplier on shadow executions. The committee and
prefix bookkeeping is unchanged. Service synchrony and catch-up restrict to the prefix;
driven execution follows from the static shadow run on that prefix. -/
theorem CommitteeHalfUpTo.healthy_base_before_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b hold : Time} (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → AC.gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  have hpre := hrun.upTo hd0
  have hr := Compose.goldilocks_ac_projection_from hpre (hnc.upTo d)
  rw [RunTrace.upTo_projAC] at hr
  refine ⟨hr, ?_, ?_, ?_, ?_, hfaults d hd0 hdb, hK.facts.hsize,
    AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP d,
    AC.CommitteeTAt.upTo hrun.antitone (hK.facts.committeeTAt' hrun hnc) d,
    fun s hgs hsd => hK.cs2 s hgs (hsd.trans hdb) d hd0 hdb⟩
  · -- Shadow driven execution (proposal and acceptance run laws).
    have hdr := projection_driven_of_run hpre (hnc.upTo d) hpre.genesis_root_ok
    rwa [RunTrace.upTo_projAC] at hdr
  · -- Restrict actual service witnesses to the read prefix.
    have hm := hrun.time_mono
    have hsync := Healing.Growing.KernelProof.service_syncACAt hrun hs (lo := g) (hi := d) le_rfl
    constructor
    · intro x hx i m hsend hi y hy j ell hj ht hd
      obtain ⟨hid, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
      obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
      rw [ACTrace.upTo_deadline hm hjd] at ht hd
      obtain ⟨k, hkj, hik, hproc, hkt⟩ := hsync.1 x i m (hrun.antitone hid hx) hsend
        ((AC.le_gbar g).trans hi) hid y j ell (hrun.antitone hjd hy) hj hd
      have hkd : tr.time k ≤ d := (hm hkj).trans hjd
      exact ⟨k, hkj, hik, ACTrace.upTo_processAt.mpr ⟨hkd, hproc⟩,
        by rwa [ACTrace.upTo_deadline hm hkd]⟩
    · intro x hx i B hacc hi y hy j ell hj ht hd hF
      obtain ⟨hid, hacc⟩ := ACTrace.upTo_acceptAt.mp hacc
      obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
      rw [ACTrace.upTo_deadline hm hjd] at ht hd
      obtain ⟨k, hkj, hak, hkt⟩ := hsync.2 x i B (hrun.antitone hid hx) hacc
        ((AC.le_gbar g).trans hi) hid y j ell (hrun.antitone hjd hy) hj hd
        (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
      have hkd : tr.time k ≤ d := (hm hkj).trans hjd
      exact ⟨k, hkj, ACTrace.upTo_acceptAt.mpr ⟨hkd, hak⟩,
        by rwa [ACTrace.upTo_deadline hm hkd]⟩
  · -- Shadow AC catch-up on the prefix.
    rw [← RunTrace.upTo_projAC]
    constructor
    intro x hx i B ha hi y hy j ell hj ht hjd hF
    change AC.gbar g + 2 * sp.Δ ≤ tr.time j at ht
    change tr.time j ≤ d at hjd
    rw [RunTrace.upTo_projAC] at ha hj ⊢
    obtain ⟨hid, ha'⟩ := ACTrace.upTo_acceptAt.mp ha
    obtain ⟨_, hj'⟩ := (Trace.upTo_callAt _).mp hj
    obtain ⟨k, hkj, hak, hkt⟩ := hrun.toLocalRun.acCatchAt hc
      (hrun.antitone hid hx) ha' hi (hrun.antitone hjd hy) hj' ht
      (hF.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd0))
    exact ⟨k, hkj,
      ACTrace.upTo_acceptAt.mpr ⟨(hrun.time_mono hkj).trans hjd, hak⟩, hkt⟩
  · intro y hy t hgt htd
    exact (Trace.upTo_awake _ y t).mpr
      ⟨hawake y t (hrun.antitone htd hy) hgt (htd.trans hdb), htd⟩

end Growing

end Consensus.Goldilocks.Healing

end
