module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Gate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Step
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageGateSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage engine part under growing faults: the reader's gate, the read prefix and the bridge

A reader `w` ready at `t` from the recovery point is honest at
`t`; it is read at the trace cut `j` of the end of `t`, every cut before `j` at a time `≤ t`
(`ready_read_cut_at`), so every reader fact is read at the time `t` (the `_by` lemmas):

* `outage_reader_gate_at` (E0–E4): the reader's latest gate `s = slot(t − 6Δ)`: `b₁ ≤ t_s + Δ`,
  the update of slot `s` at `t_s + 6Δ ≤ t < t_s + 10Δ` before the read cut, no restart after `t_s`
  up to `t`, and the latest view at `t` of label `s + 1`;
* `outage_reader_prefix_at`: ancestry of two read tips is the prefix of the engine reads;
* `extending_majority_after_r_at`: the extending majority for the origin at every label past the
  first restored one, charged at every `d ∈ [t_q + Δ, t_q + 6Δ]` within the horizon (every vote
  of such a label by a node honest at its cast extends the origin, and the committee slot count at
  `d`);
* `outage_reader_bridge_at`: the reader's read extends the armed read tip of the ready source.
  The record comes from the early gate (`record_above_of_update_r_by`) or the latest gate
  (`gate_result_extends_at`, `record_above_from_at`), the head from the extending majority of the
  read label at `t` (`vote_held_before_early_at`, `read_majority_of_extending_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- The query's catch-up duration is not negative. -/
private theorem duration_nonneg (Q : OutageQueryAt S A V) : 0 ≤ Q.duration :=
  ((by unfold Regimes.catchUp; have := Q.params.toParams.hΔ; positivity :
    (0 : Time) ≤ Regimes.catchUp Q.params)).trans (outage_duration_supply_at Q)

/-- **E0–E4 under growing faults**: the latest gate of a reader ready at `t` from the recovery
point `b₁ + 9Δ`. Only readiness, joining, the gate tick and the read cut are used. -/
theorem outage_reader_gate_at (Q : OutageQueryAt S A V)
    {t : Time} (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    Nonempty (Compose.Growing.OutageReaderGate Q.trace Q.keys Q.stop (Q.run.2.ownKey w)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t) := by
  have hrec : Q.stop + 9 * Q.run.1.ΔAC ≤ t := by
    change Q.stop + ((9 : Nat) : Time) * Q.run.1.ΔAC ≤ t at ht
    push_cast at ht
    exact ht
  have hb₁ := outage_stop_nonneg Q.outage
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have ht0 : 0 ≤ t := by have := Q.run.1.ΔAC_pos; linarith
  have hR := ready_transport_at S Q.run.2 Q.hn Q.valid ht0 hth hw
  obtain ⟨hread, -, -⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid
    (duration_nonneg Q) ht0 hth hw
  exact Compose.Growing.outage_reader_gate_at hrun
    hb₁ (outage_duration_supply_at Q) hrec
    ⟨⟨hR.1, ⟨hread.1, hread.2.le⟩, ht0, hth⟩, hR.2⟩ hread.2

/-- The engine cut at the end of `t ≥ 0` is at a time `≤ t`. -/
private theorem cutTime_endCut_le (Q : OutageQueryAt S A V) {t : Time} (ht : 0 ≤ t) :
    Q.run.2.cutTime ((chainTrace Q.run.2).endCut t) ≤ t :=
  Nat.findGreatest_spec (P := fun i => Q.run.2.cutTime i ≤ t) (Nat.zero_le _)
    (by simpa [Model.Run.cutTime] using ht)

/-- The confirmed read of an engine node ready at `t ∈ [0, horizon]` is the chain of its read tip
at the trace cut of the end of `t`. -/
private theorem read_eq_chain (Q : OutageQueryAt S A V)
    {w : V} {t : Time} (ht0 : 0 ≤ t)
    (hth : t ≤ Q.run.2.horizon) (hw : Q.run.2.point.Ready Q.duration w t) :
    (chainTrace Q.run.2).readAt .confirmed w t =
      chainTo (Q.trace.state (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).fg.blocks
        ((Regimes.readAfter Q.trace (Q.run.2.ownKey w)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t).slot + 1)
        (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
          (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t) := by
  have hi : (chainTrace Q.run.2).endCut t ≤ Q.run.2.events.length := Nat.findGreatest_le _
  obtain ⟨-, -, hnow⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid (duration_nonneg Q) ht0 hth hw
  have hh : w ∉ Q.run.2.faultyAt (Q.run.2.cutTime ((chainTrace Q.run.2).endCut t)) := fun h =>
    hw.1 (Q.run.2.faultyAt_mono (cutTime_endCut_le Q ht0) h)
  change (chainTrace Q.run.2).read .confirmed w ((chainTrace Q.run.2).endCut t) = _
  rw [read_eq_out S Q.run.2 Q.hn, outOf, ← simTraceAt_state S Q.run.2 Q.hn Q.valid hh hi]
  dsimp only
  rw [hnow]
  rfl

/-- **The read prefix**: ancestry of the two read tips, inside the blocks held while honest, is
the prefix of the engine reads. -/
theorem outage_reader_prefix_at (Q : OutageQueryAt S A V)
    {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) {t : Time} (hTt : Q.T ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t)
    (h : Anc (Q.trace.HonestBlocksAt Q.keys)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t)) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  have hT0 : 0 ≤ Q.T := Q.outage.times.1
  have ht0 : 0 ≤ t := hT0.trans hTt
  have hTh := hTt.trans hth
  have hc := duration_nonneg Q
  obtain ⟨hcT, -, -⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid hc hT0 hTh hv
  obtain ⟨hct, -, -⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid hc ht0 hth hw
  change (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
    (chainTrace Q.run.2).readAt .confirmed w t
  rw [read_eq_chain Q hT0 hTh hv, read_eq_chain Q ht0 hth hw]
  exact read_prefix S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) hT0 hcT.1
    (honest_ownKey_at S Q.run.2 hv.1 hTh) ht0 hct.1 (honest_ownKey_at S Q.run.2 hw.1 hth) h

/-- Compatibility in the blocks held while honest is compatibility in a frame that holds both
blocks. -/
private theorem compatible_tree {sp : SA.SAParams} {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) (hU : Coherent U) (hΦU : Φ.tree ⊆ U)
    {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ Φ.tree) (hY : Y ∈ Φ.tree)
    (h : Compatible U X Y) : Compatible Φ.tree X Y :=
  h.imp (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hX h hY)
    (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hY h hX)

/-- **The extending majority past the first restored label**: at a label `q > r`, every vote of a
node honest at its cast extends the origin (`restored_votes_extend_at`), so the committee slot
count at `d ∈ [t_q + Δ, t_q + 6Δ]` within the horizon gives the extending majority charged at `d`
(the gate `voteK_gate` permits every member to vote). -/
theorem extending_majority_after_r_at (Q : OutageQueryAt S A V)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    {v : V} (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArmingAt Q v)
    (hinv : ∀ i, Compose.Growing.OutageLockInv (outageLockPremises_of_arming_at Q service hsh ar) i)
    {q : Nat} (hrq : Q.restoredLabel < q) {d : Time} (hd₁ : Q.params.ts q + Q.params.Δ ≤ d)
    (hd₂ : d ≤ Q.params.ts q + 6 * Q.params.Δ) (hdh : d ≤ Q.run.2.horizon) :
    Compose.Growing.ExtendingMajorityAt Q.trace Q.keys Q.K ar.origin q d := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hSD : ∀ y, Compose.Growing.ReceiverServiceAfterAt Q.keys (Q.trace.HonestBlocksAt Q.keys)
      (outageLockPremises_of_arming_at Q service hsh ar).b₁ y Q.trace.projAC := fun y => by
    rw [outageLockPremises_of_arming_at_b₁]
    exact outage_receiver_service_at Q y
  have hall := Compose.Growing.restored_votes_extend_at _ hSD hinv
  rw [outageLockPremises_of_arming_at_P, outageLockPremises_of_arming_at_r] at hall
  exact Compose.Growing.extendingMajority_of_all_at hrun hnc
    (fun t ht x hx i _ s => voteK_gate S Q.run.2 Q.hn Q.valid x (hrun.antitone ht hx) i s)
    (fun x k e hv hs => hall x k e hv (by rw [hs]; exact hrq)) hd₁
    ((Q.boundsK hrun hdh).slotK q d (Nat.zero_le _) hd₁ le_rfl hd₂)

/-- **The reader bridge under growing faults.** A reader ready at `t` from the recovery point
reads above the armed read tip of the ready source. -/
theorem outage_reader_bridge_at (Q : OutageQueryAt S A V)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    {v : V} (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArmingAt Q v)
    (hinv : ∀ i, Compose.Growing.OutageLockInv (outageLockPremises_of_arming_at Q service hsh ar) i)
    {t : Time} (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    Anc (Q.trace.HonestBlocksAt Q.keys) ar.tip
      (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t) := by
  classical
  obtain ⟨G⟩ := outage_reader_gate_at Q ht hth hw
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hrec : Q.stop + 9 * Q.run.1.ΔAC ≤ t := by
    change Q.stop + ((9 : Nat) : Time) * Q.run.1.ΔAC ≤ t at ht
    push_cast at ht
    exact ht
  clear ht
  have ht0 : 0 ≤ t := by linarith [outage_stop_nonneg Q.outage, Q.run.1.ΔAC_pos]
  have hŵ : Q.run.2.ownKey w ∈ Q.keys t := honest_ownKey_at S Q.run.2 hw.1 hth
  have hS := outage_receiver_service_at Q (Q.run.2.ownKey w)
  have hspec := restoredLabel_spec Q
  have hts1 : ∀ s : Nat, Q.params.ts (s + 1 : Nat) = Q.params.ts s + 4 * Q.params.Δ := by
    intro s; simp only [SA.SAParams.ts]; push_cast; ring
  have hP : (outageLockPremises_of_arming_at Q service hsh ar).P = ar.origin :=
    outageLockPremises_of_arming_at_P
  have hr : (outageLockPremises_of_arming_at Q service hsh ar).r = Q.restoredLabel :=
    outageLockPremises_of_arming_at_r
  have hSD : ∀ y, Compose.Growing.ReceiverServiceAfterAt Q.keys (Q.trace.HonestBlocksAt Q.keys)
      (outageLockPremises_of_arming_at Q service hsh ar).b₁ y Q.trace.projAC := fun y => by
    rw [outageLockPremises_of_arming_at_b₁]
    exact outage_receiver_service_at Q y
  set ŵ := Q.run.2.ownKey w
  set U := Q.trace.HonestBlocksAt Q.keys
  set j := cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)
  set st := Q.trace.state ŵ j
  have hjt : ∀ k < j, Q.trace.time k ≤ t := G.read.1.1
  have hΦ : FrameOK (Node.frame st) := Compose.Growing.frameOK_at hrun ht0 hŵ hjt
  have hΦU : (Node.frame st).tree ⊆ U := fun X hX => Compose.Growing.tree_held_at ht0 hŵ hjt hX.1
  have hTO : Anc U ar.tip ar.origin := ar.tip_anc
  -- a cut at or before `t` is before the read cut
  have hbefore : ∀ c, Q.trace.time c ≤ t → c < j := by
    intro c hc
    by_contra h
    exact absurd (G.read.2.trans_le ((hrun.time_mono (not_lt.1 h)).trans hc)) (lt_irrefl t)
  have hGt : Q.trace.time G.cut = Q.params.ts G.slot + 6 * Q.params.Δ := G.update.2.2.1
  have hGtt : Q.trace.time G.cut ≤ t := hGt ▸ G.gate_le
  have hŵG : ŵ ∈ Q.keys (Q.trace.time G.cut) := hrun.antitone hGtt hŵ
  -- the lock module's reader facts at the read time
  have hf : 2 * (Q.keys t)ᶜ.ncard < Q.params.n := (Q.bounds hth).two t ht0 le_rfl
  have hBP : Anc U ar.tip (outageLockPremises_of_arming_at Q service hsh ar).P := hP ▸ hTO
  obtain ⟨hfc, hviab⟩ := Compose.Growing.reader_frame_by hinv ht0 hjt hŵ hf t hBP
  have hlocks := Compose.Growing.liveLockBlocks_compatible_by hinv ht0 hjt hŵ t hBP
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
    fun c hc => Compose.Growing.F_mono_at hrun ht0 hŵ hjt hc
  refine ⟨?_, ?_⟩
  · -- the record
    by_cases hE : ∃ c ℓ, SA.UpdateAt Q.trace.projAC ŵ c Q.restoredLabel ℓ
    · obtain ⟨c, ℓ, hu⟩ := hE
      have hrs := hspec.2 G.slot G.restored
      have hct : Q.trace.time c ≤ t := by
        have h1 : Q.trace.time c = Q.params.ts Q.restoredLabel + 6 * Q.params.Δ := hu.2.2.1
        have h2 := Compose.ts_le_ts (sp := Q.params) hrs
        linarith [G.gate_le]
      have h := Compose.Growing.record_above_of_update_r_by _ hSD hinv (hrun.antitone hct hŵ)
        (by rw [hr]; exact hu) j t (hbefore c hct) ht0 hjt hŵ
      rw [hP] at h
      exact hTO.trans h
    -- otherwise the latest gate is past the first restored label
    have hrs : Q.restoredLabel < G.slot :=
      lt_of_le_of_ne (hspec.2 G.slot G.restored) fun h => hE ⟨G.cut, G.label, h ▸ G.update⟩
    have hcj := hbefore G.cut hGtt
    have hmaj := extending_majority_after_r_at Q service hsh ar hinv hrs
      (d := Q.trace.time G.cut) (by rw [hGt]; linarith) hGt.le (hGtt.trans hth)
    have hFB : Anc U G.label.frame.F ar.origin := by
      rw [Compose.Growing.frame_of_projAC_at hrun hŵG G.update.1]
      exact ((hFc G.cut hcj.le).trans hFt).trans hTO
    obtain ⟨⟨C, CV, hR⟩, hall⟩ :=
      Compose.Growing.gate_result_extends_at hrun hnc
        (voteK_committeeP S Q.run.2 Q.hn Q.valid hnc hrun) hŵG hS G.update
        G.restored hmaj hFB
    have h := Compose.Growing.record_above_from_at hinv G.update hR (by rw [hr]; exact hrs.le)
      (by rw [hP]; exact hall C CV hR) j t hcj ht0 hjt hŵ
    rw [hP] at h
    exact hTO.trans h
  · -- the head: the extending majority of the read label at `t`
    have hrq : Q.restoredLabel < G.slot + 1 := Nat.lt_succ_of_le (hspec.2 G.slot G.restored)
    have hmaj := extending_majority_after_r_at Q service hsh ar hinv hrq (d := t)
      (by rw [hts1]; linarith [G.gate_le]) (by rw [hts1]; linarith [G.lt_next]) hth
    have hmaj' := hmaj.anti hTO
    have hGj : G.cut ≤ j := G.cut_lt.le
    have hFG : G.label.frame = Node.frame (Q.trace.state ŵ G.cut) :=
      Compose.Growing.frame_of_projAC_at hrun hŵG G.update.1
    have hct : Q.params.ts (G.slot + 1 : Nat) + 2 * Q.params.Δ ≤ Q.trace.time G.cut := by
      rw [hGt, hts1]; linarith
    have hgq : Q.stop ≤ Q.params.ts (G.slot + 1 : Nat) + Q.params.Δ := by
      rw [hts1]; linarith [G.restored]
    have hres : ∀ k ≤ G.cut, Q.trace.projAC.RestartAt ŵ k →
        Q.trace.time k ≤ Q.params.ts (G.slot + 1 : Nat) := by
      intro k hk hrk
      have := G.restarts k hrk ((hrun.time_mono hk).trans hGtt)
      rw [hts1]; linarith
    have hnr : ∀ k, G.cut ≤ k → k < j → ¬ Q.trace.projAC.RestartAt ŵ k := by
      intro k hk hkj hrk
      have h1 := G.restarts k hrk (G.read.1.1 k hkj)
      have h2 := hrun.time_mono hk
      linarith
    -- the reader's AC states up to the read cut, in the prefix through `t`
    have hr' := (Compose.Growing.acRun_upTo hrun hnc ht0).localRun
    have hstp : ∀ m ≤ j, (Q.trace.projAC.upTo t).state ŵ m = Q.trace.projAC.state ŵ m :=
      fun m hm => Trace.upTo_state _ ŵ fun k hk => hjt k (by omega)
    have hstj : Q.trace.projAC.state ŵ j = st.ac := by
      have h := Compose.projAC_state (hrun.upTo ht0).toLocalRun hŵ j
      rwa [RunTrace.upTo_projAC, hstp j le_rfl, Trace.upTo_state Q.trace ŵ hjt] at h
    have hnr' : ∀ k, G.cut ≤ k → k < j → ¬ ACTrace.RestartAt (Q.trace.projAC.upTo t) ŵ k :=
      fun k h1 h2 hrk => hnr k h1 h2 ((Compose.Growing.ac_restartAt_upTo _).1 hrk).2
    -- every vote extending the tip, of a validator honest at `t`, is delivered to the read cut
    have hdeliv : ∀ x k e, Compose.Growing.HVoteAt Q.trace Q.keys x k e → x ∈ Q.keys t →
        e.msg.slot = G.slot + 1 → SA.VoteExtends U e.msg ar.tip →
        e.msg ∈ st.ac.pool (G.slot + 1) ∧ ∃ Hd ∈ (Node.frame st).tree, Hd.root = e.msg.head ∧
          st.ac.blockStamp Hd.root < ⊤ := by
      rintro x k e hv hxt hes ⟨Hd, hHdU, hHdr, hBHd⟩
      have hF : Anc U G.label.frame.F Hd := by
        rw [hFG]; exact ((hFc G.cut hGj).trans hFt).trans hBHd
      obtain ⟨hpool, hHdt, hrt⟩ := Compose.Growing.vote_held_before_early_at hrun hnc hŵG hS
        G.update.1 hct hgq hres hv (hrun.antitone hGtt hxt) hes hHdU hHdr hF
      have hΦc : FrameOK G.label.frame := (Compose.Growing.frameIn_at hrun hnc hŵG G.update.1).1
      have hbst : (Q.trace.projAC.state ŵ G.cut).blockStamp Hd.root < ⊤ := by
        unfold SA.resolutionTime at hrt
        rw [← hHdr, SA.lookup_of_mem hΦc hHdt] at hrt
        dsimp only at hrt
        split_ifs at hrt
        · exact absurd hrt (not_lt.2 le_top)
        · exact (max_lt_iff.1 hrt).2.trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))
      have hpool' : e.msg ∈ st.ac.pool (G.slot + 1) := by
        rw [← hstj, ← hstp j le_rfl]
        exact SA.pool_mono hr' hŵ hGj hnr' _ (by rw [hstp G.cut hGj]; exact hpool)
      have hfg : Hd ∈ (Q.trace.state ŵ G.cut).fg.tree := by
        rw [hFG] at hHdt; exact hHdt.1
      refine ⟨hpool', Hd, Compose.Growing.frame_mem_of_tree_at hrun hnc ht0 hŵ hjt
        (Compose.Growing.tree_mono_at hrun ht0 hŵ hjt hGj hfg) (hFt.trans hBHd), hHdr, ?_⟩
      rw [← hstj, ← hstp j le_rfl]
      exact Compose.blockStamp_finite hr' hŵ hGj hnr' (by rw [hstp G.cut hGj]; exact hbst)
    -- the tip is in the frame: an extending caster's head is, above the tip
    have hBt : ar.tip ∈ (Node.frame st).tree := by
      have hpos : 0 < (Compose.Growing.ExtendingCastersAt Q.trace Q.keys ar.tip
          (G.slot + 1) t).ncard :=
        lt_of_le_of_lt (Nat.zero_le _) (Compose.Growing.extendingMajorityAt_iff.1 hmaj')
      obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
      obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ :=
        Compose.Growing.extendingCastersAt_iff.1 hxE
      obtain ⟨-, Hd', hHd't, hHd'r, -⟩ := hdeliv x k e hv hx hes ⟨Hd, hHdU, hHdr, hBHd⟩
      obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
      have hfa := Compose.Growing.held_anc_at hrun hnc ht0 hŵ hjt hBHd hHd't.1
      have htt : ar.tip ∈ st.fg.tree := by
        by_cases he : ar.tip = Hd'
        · exact he ▸ hHd't.1
        · exact (Anc.mem hfa he).1
      exact Compose.Growing.frame_mem_of_tree_at hrun hnc ht0 hŵ hjt htt hFt
    have hL3 := Compose.Growing.read_majority_of_extending_at hrun hnc
      (voteK_committeeP S Q.run.2 Q.hn Q.valid hnc hrun) ht0 hŵ
      hjt G.view hmaj' hBt hdeliv
    have hanchor : Compatible (Node.frame st).tree
        (SA.getAnchor Q.params st.ac (Node.frame st) t) ar.tip :=
      Compose.anchor_compatible_of_live_candidates hΦ fun X hX => by
        rcases hX with hX | hX
        · exact compatible_tree hΦ hU hΦU hX.1 hBt (hlocks X hX)
        · rw [Set.mem_singleton_iff.1 hX]
          exact compatible_tree hΦ hU hΦU hΦ.fcRoot_mem hBt hfc
    exact anc_acHead_of_current_certificate hΦ hΦU
      (Or.inr ⟨hBt, hanchor, (hviab hBt).imp_right fun h => ⟨h, hL3⟩⟩)

end Consensus.Goldilocks.Obligations.Growing

end
