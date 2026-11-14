module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageReaderGate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Arming
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageMajority
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageService
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageGate
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks outage: the reader bridge

A reader ready at `t` from the
recovery point reads above the armed read tip of the ready source, given three inputs at the
origin: the head at the read label (`hhead`), the record of an early reader that ran the gate of
the first restored label (`hearly`), and the record of a late reader (`hlate`).

The proof takes the reader's latest gate (`outage_reader_gate`), the receiver service from the
stop (`outage_receiver_service`), and the lock module's reader facts at the read cut
(`outage_reader_frame`, `outage_reader_locks`, `outage_record_above_from`). With the read tip
below `Σ.F` the record and the head extend it at once; otherwise the record comes from the early
or the late gate (`gate_result_extends`) and the head from the extending majority of the read
label (`vote_held_before_early`, `read_majority_of_extending`). The read is the deepest common
ancestor of the two (`exposed_prefix_preserved_of_record_head`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

section Helpers

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A block between an honest node's `Σ.F` and a block of its store is in its frame. -/
private theorem mem_frame_between (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree)
    (hFX : Anc (tr.HonestBlocks H) (tr.state y i).fg.F X) (hXW : Anc (tr.HonestBlocks H) X W) :
    X ∈ (Node.frame (tr.state y i)).tree := by
  have hXt : X ∈ (tr.state y i).fg.tree := by
    by_cases hXW' : X = W
    · exact hXW' ▸ hW
    · exact (Anc.mem (Compose.honest_held_anc hrun hnc hy hXW hW) hXW').1
  exact ⟨hXt, Compose.honest_held_anc hrun hnc hy hFX hXt⟩

/-- Compatibility in the honest blocks is compatibility in a frame that holds both blocks. -/
private theorem compatible_tree {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    (hU : Coherent (tr.HonestBlocks H)) (hΦU : Φ.tree ⊆ tr.HonestBlocks H)
    {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ Φ.tree) (hY : Y ∈ Φ.tree)
    (h : Compatible (tr.HonestBlocks H) X Y) : Compatible Φ.tree X Y :=
  h.imp (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hX h hY)
    (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hY h hX)

end Helpers

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **The reader bridge.** A reader ready at `t` from the recovery point reads above the armed
read tip, given the head, early and late record inputs at the origin. -/
theorem outage_reader_bridge (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.params.Δ
        Q.start)
    {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon)
    (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArming S A V Q v)
    (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {t : Time} (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t)
    -- head at the read label (`outage_reader_head`)
    (hhead : ∀ G : OutageReaderGate S A V Q w t,
      Compose.ExtendingMajority Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) ar.origin (G.slot + 1) ∨
        Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.origin
          (SA.acHead Q.params
            (Q.trace.state (Q.run.2.ownKey w)
              (cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).ac
            (Node.frame (Q.trace.state (Q.run.2.ownKey w)
              (cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)))) t))
    -- early record (`outage_reader_early`)
    (hearly : ∀ c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c Q.restoredLabel ℓ →
      ∀ c', c < c' → Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.origin
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey w) c'))
          (Q.trace.state (Q.run.2.ownKey w) c').ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey w) c').fg.F))
    -- late record (`outage_reader_late`)
    (hlate : (¬ ∃ c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c Q.restoredLabel ℓ) →
      (∃ s' c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c s' ℓ ∧ Q.restoredLabel < s' ∧
          Q.trace.time c ≤ t ∧
          Compose.ExtendingMajority Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) ar.origin s') ∨
        Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.origin
          (Q.trace.state (Q.run.2.ownKey w)
            (cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).fg.F) :
    Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) ar.tip
      (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
        (cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t) := by
  classical
  obtain ⟨G⟩ := outage_reader_gate S A V Q ht hth hw
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision
  have hrun' := Compose.goldilocks_ac_projection _ _ _ _ _ _ hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hŵ := honest_ownKey (S := ⟨S, stock⟩)
    ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hw.1)
  have hS := outage_receiver_service S A V Q _ hŵ
  have hspec := restoredLabel_spec Q
  have hts1 : ∀ s : Nat, Q.params.ts (s + 1 : Nat) = Q.params.ts s + 4 * Q.params.Δ := by
    intro s; simp only [SA.SAParams.ts]; push_cast; ring
  set ŵ := Q.run.2.ownKey w
  set U := Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)
  set j := cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)
  set st := Q.trace.state ŵ j
  have hΦ : FrameOK (Node.frame st) := Compose.frameOK_state hrun.toLocalRun hŵ j
  have hΦU : (Node.frame st).tree ⊆ U := fun X hX => ⟨ŵ, hŵ, j, hX.1⟩
  have hTO : Anc U ar.tip ar.origin := by
    rcases ar.armed with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h]; exact .refl
    · exact h
  -- a cut at or before `t` is before the read cut
  have hbefore : ∀ c, Q.trace.time c ≤ t → c < j := by
    intro c hc
    by_contra h
    exact absurd (G.read.2.trans_le ((hrun.time_mono (not_lt.1 h)).trans hc)) (lt_irrefl t)
  have hGt : Q.trace.time G.cut = Q.params.ts G.slot + 6 * Q.params.Δ := G.update.2.2.1
  -- the lock module's reader facts at the read cut
  obtain ⟨hfc, hviab⟩ := outage_reader_frame Q service hv hTh hsh ar hS5 hŵ j t
  have hlocks := outage_reader_locks Q service hv hTh hsh ar hS5 ŵ hŵ j t
  -- the record and the head both extend the tip
  suffices hrh : Anc U ar.tip ((SA.lookup (Node.frame st) st.ac.latestConfirmed).getD
      (Node.frame st).F) ∧ Anc U ar.tip (SA.acHead Q.params st.ac (Node.frame st) t) from
    (exposed_prefix_preserved_of_record_head hU hΦ hΦU).2 hrh
  by_cases hA : Anc U ar.tip st.fg.F
  · -- Case A: the tip is below `Σ.F`
    refine ⟨?_, anc_acHead_of_current_certificate hΦ hΦU (Or.inl hA)⟩
    have hR : (SA.lookup (Node.frame st) st.ac.latestConfirmed).getD (Node.frame st).F ∈
        (Node.frame st).tree := by
      cases he : SA.lookup (Node.frame st) st.ac.latestConfirmed with
      | none => exact hΦ.rooted.1
      | some B => exact (SA.lookup_eq_some he).1
    exact hA.trans ((hΦ.rooted.2 _ hR).mono hΦU)
  -- Case B: `Σ.F` is below the tip
  have hFt : Anc U st.fg.F ar.tip := by
    have hFfc : Anc U st.fg.F (Node.frame st).fcRoot := hΦ.F_anc_fcRoot.mono hΦU
    rcases hfc with h | h
    · exact hFfc.trans h
    · rcases Anc.total hU hFfc h with h' | h'
      · exact h'
      · exact absurd h' hA
  -- `Σ.F` grows along the reader's cuts
  have hFc : ∀ c, c ≤ j → Anc U (Q.trace.state ŵ c).fg.F st.fg.F :=
    fun c hc => (Compose.fg_grows hrun hŵ hc).2
  refine ⟨?_, ?_⟩
  · -- the record
    by_cases hE : ∃ c ℓ, SA.UpdateAt Q.trace.projAC ŵ c Q.restoredLabel ℓ
    · obtain ⟨c, ℓ, hu⟩ := hE
      have hrs := hspec.2 G.slot G.restored
      have hcj : c < j := by
        apply hbefore
        have h1 : Q.trace.time c = Q.params.ts Q.restoredLabel + 6 * Q.params.Δ := hu.2.2.1
        have h2 := Compose.ts_le_ts (sp := Q.params) hrs
        linarith [G.gate_le]
      exact hTO.trans (hearly c ℓ hu j hcj)
    rcases hlate hE with ⟨s', c, ℓ, hu, hrs, hct, hmaj⟩ | hF
    · have hcj := hbefore c hct
      have hg : Q.stop ≤ Q.params.ts s' + Q.params.Δ := by
        linarith [hspec.1, Compose.ts_le_ts (sp := Q.params) hrs.le]
      have hFB : Anc U ℓ.frame.F ar.origin := by
        rw [Compose.frame_of_projAC hrun hŵ hu.1]
        exact ((hFc c hcj.le).trans hFt).trans hTO
      obtain ⟨⟨C, CV, hR⟩, hall⟩ := Compose.gate_result_extends hrun hnc hŵ hS hu hg hmaj hFB
      exact hTO.trans (outage_record_above_from Q service hv hTh hsh ar hS5 hŵ hu hg hR
        (hall C CV hR) j hcj)
    · exact absurd (hTO.trans hF) hA
  · -- the head
    rcases hhead G with hmaj | hh
    swap
    · exact hTO.trans hh
    set q := G.slot + 1
    have hmaj' := Compose.ExtendingMajority.anti hTO hmaj
    have hGj : G.cut ≤ j := G.cut_lt.le
    have hFG : G.label.frame = Node.frame (Q.trace.state ŵ G.cut) :=
      Compose.frame_of_projAC hrun hŵ G.update.1
    have hct : Q.params.ts q + 2 * Q.params.Δ ≤ Q.trace.time G.cut := by
      rw [hGt, hts1]; linarith
    have hgq : Q.stop ≤ Q.params.ts q + Q.params.Δ := by rw [hts1]; linarith [G.restored]
    have hres : ∀ k ≤ G.cut, Q.trace.projAC.RestartAt ŵ k → Q.trace.time k ≤ Q.params.ts q := by
      intro k hk hrk
      have := G.restarts k hrk ((hrun.time_mono hk).trans (hGt ▸ G.gate_le))
      rw [hts1]; linarith
    have hnr : ∀ k, G.cut ≤ k → k < j → ¬ Q.trace.projAC.RestartAt ŵ k := by
      intro k hk hkj hrk
      have h1 := G.restarts k hrk (G.read.1 k hkj)
      have h2 := hrun.time_mono hk
      linarith
    -- every vote extending the tip is delivered to the read cut
    have hdeliv : ∀ x ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ k e, SA.VoteAt Q.trace.projAC x k e →
        e.msg.slot = q → SA.VoteExtends U e.msg ar.tip →
        e.msg ∈ st.ac.pool q ∧ ∃ Hd ∈ (Node.frame st).tree, Hd.root = e.msg.head ∧
          st.ac.blockStamp Hd.root < ⊤ := by
      rintro x hx k e hv hes ⟨Hd, hHdU, hHdr, hBHd⟩
      have hF : Anc U G.label.frame.F Hd := by
        rw [hFG]; exact ((hFc G.cut hGj).trans hFt).trans hBHd
      obtain ⟨hpool, hHdt, hrt⟩ := Compose.vote_held_before_early hrun hnc hŵ hS G.update.1 hct
        hgq hres hx hv hes hHdU hHdr hF
      have hΦc : FrameOK G.label.frame := (SA.frameIn_of_callAt hr hŵ G.update.1).1
      have hbst : (Q.trace.projAC.state ŵ G.cut).blockStamp Hd.root < ⊤ := by
        unfold SA.resolutionTime at hrt
        rw [← hHdr, SA.lookup_of_mem hΦc hHdt] at hrt
        dsimp only at hrt
        split_ifs at hrt
        · exact absurd hrt (not_lt.2 le_top)
        · exact (max_lt_iff.1 hrt).2.trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))
      have hpool' : e.msg ∈ st.ac.pool q := by
        erw [← Compose.projAC_state hrun.toLocalRun hŵ j]
        exact SA.pool_mono hr hŵ hGj hnr q hpool
      have hfg : Hd ∈ (Q.trace.state ŵ G.cut).fg.tree := by
        rw [hFG] at hHdt; exact hHdt.1
      refine ⟨hpool', Hd, mem_frame_between hrun hnc hŵ ((Compose.fg_grows hrun hŵ hGj).1 hfg)
        (hFt.trans hBHd) .refl, hHdr, ?_⟩
      erw [← Compose.projAC_state hrun.toLocalRun hŵ j]
      exact Compose.blockStamp_finite hr hŵ hGj hnr hbst
    -- the tip is in the frame: an extending caster's head is, above the tip
    have hBt : ar.tip ∈ (Node.frame st).tree := by
      have hpos : 0 <
          (Compose.ExtendingCasters Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) ar.tip q).ncard :=
        lt_of_le_of_lt (Nat.zero_le _) (Compose.extendingMajority_iff.1 hmaj')
      obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
      obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ := Compose.extendingCasters_iff.1 hxE
      obtain ⟨-, Hd', hHd't, hHd'r, -⟩ := hdeliv x hx k e hv hes ⟨Hd, hHdU, hHdr, hBHd⟩
      obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
      exact mem_frame_between hrun hnc hŵ hHd't.1 hFt hBHd
    have hL3 := Compose.read_majority_of_extending hrun hnc hŵ G.view hmaj' hBt hdeliv
    have hanchor : Compatible (Node.frame st).tree
        (SA.getAnchor Q.params st.ac (Node.frame st) t) ar.tip :=
      Compose.anchor_compatible_of_live_candidates hΦ fun X hX => by
        rcases hX with hX | hX
        · exact compatible_tree hΦ hU hΦU hX.1 hBt (hlocks X hX)
        · rw [Set.mem_singleton_iff.1 hX]
          exact compatible_tree hΦ hU hΦU hΦ.fcRoot_mem hBt hfc
    exact anc_acHead_of_current_certificate hΦ hΦU
      (Or.inr ⟨hBt, hanchor, (hviab hBt).imp_right fun h => ⟨h, hL3⟩⟩)

end Consensus.Goldilocks.Obligations

end
