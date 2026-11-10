module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageGateSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks outage: the reader's latest gate (E0–E4) and the source prefix

A reader ready at `t` from the recovery point `b₁ + 9Δ` has its latest gate `s = slot(t − 6Δ)`:
`b₁ ≤ t_s + Δ`, the update of slot `s` at `d_s = t_s + 6Δ ≤ t < t_s + 10Δ` before the read cut, no
restart after `t_s` up to `t`, and the latest view at `t` of label `s + 1`. Only readiness,
joining, the gate tick and the read cut are used: no vote, frame walk or voter tree. The slot
arithmetic of the gate, its restarts and its view label is `OutageGateSlot`.
`outage_reader_prefix` turns ancestry of the two read tips into the prefix of the engine reads. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- E0–E4: the latest gate of a ready reader from the recovery point. -/
structure OutageReaderGate (Q : OutageQuery S A V) (w : V) (t : Time) where
  slot : Nat
  restored : Q.stop ≤ Q.params.ts slot + Q.params.Δ
  gate_le : Q.params.ts slot + 6 * Q.params.Δ ≤ t
  lt_next : t < Q.params.ts slot + 10 * Q.params.Δ
  cut : Nat
  label : ACLabel (SA.goldilocksSA Q.params (List (FG.Att Q.params.n)) (S.ro Q.params.n))
  update : SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) cut slot label
  cut_lt : cut < cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)
  restarts : ∀ k, Q.trace.projAC.RestartAt (Q.run.2.ownKey w) k → Q.trace.time k ≤ t →
    Q.trace.time k ≤ Q.params.ts slot
  read : Regimes.CutAfter Q.trace (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t
  view : (SA.latestView Q.params
      (Q.trace.state (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).ac
      (Node.frame (Q.trace.state (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)))) t).2 = ((slot + 1 : Nat) : Int)

/-- The query's catch-up duration covers the node catch-up `18Δ`, from
`contract_catchUp_ge_sleepy`. -/
private theorem duration_ge (Q : OutageQuery S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  simp only [OutageQuery.duration, System.cDur, Params.standard, contract_coefficients_catchUp]
  change 18 * Q.run.1.ΔAC ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
  linarith [mul_le_mul_of_nonneg_right hc (zero_le_one.trans hd)]

theorem outage_reader_gate (Q : OutageQuery S A V) {t : Time}
    (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t) (hth : t ≤ Q.run.2.horizon)
    {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    Nonempty (OutageReaderGate S A V Q w t) := by
  set sp := Q.params
  set tr := Q.trace
  set y := Q.run.2.ownKey w
  set j := cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hΔ : sp.Δ = Q.run.1.ΔAC := rfl
  have hrec : Q.stop + 9 * Q.run.1.ΔAC ≤ t := by
    change Q.stop + ((9 : Nat) : Time) * Q.run.1.ΔAC ≤ t at ht
    push_cast at ht
    exact ht
  have hb₁ := outage_stop_nonneg Q.outage
  have hdur := duration_ge S A V Q
  have hcu : Regimes.catchUp sp = 18 * sp.Δ := rfl
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  have ht0 : 0 ≤ t := by linarith
  -- E0: the reader is ready on the node trace
  have hR := ready_transport S Q.run.2 Q.hn Q.valid ht0 hth hw
  have hy : y ∈ honestKeys S Q.run.2 := hR.1
  -- E1: the latest gate `s = slot(t − 6Δ)`
  obtain ⟨s, hrestored, hgate, hnext⟩ := outage_latest_gate sp hb₁ hrec
  obtain ⟨hslu, hle⟩ := outage_gate_restarts sp hgate hnext
  -- E2: the gate tick at `u = t_s + 6Δ`, an update of slot `s`
  set u := sp.ts s + 6 * sp.Δ with hu_def
  have hu : u = 4 * sp.Δ * s + 6 * sp.Δ := rfl
  have hu0 : 0 ≤ u := by linarith
  have hpub : sp.toParams.IsPublic u := ⟨4 * s + 6, by rw [hu]; ring⟩
  have hwin : ∀ v, max 0 (u - (14 * sp.Δ - 1) - 1) ≤ v → v ≤ u → tr.awake y v := by
    intro v h₁ h₂
    exact hR.2 v (le_trans (max_le_max le_rfl (by rw [hcu] at hdur; linarith)) h₁)
      (by linarith)
  have hyu := hwin u (max_le hu0 (by linarith)) le_rfl
  obtain ⟨c₁, x, hg⟩ := hrun.tick_of_awake y hy u hu0 hpub hyu
  obtain ⟨hc₁, ht₁⟩ := Healing.tick_first_cut hg
  have hJu := (Compose.ready_implies_joined _ _ _ _ _ _ hrun y hy u (14 * sp.Δ - 1) hu0
    (by linarith) hwin).2
  have hj₁ : SA.joined sp (tr.state y c₁).ac u :=
    ((Compose.joined_projection _ _ _ _ _ _ hrun y hy u).2.1 c₁ ⟨_, hc₁⟩
      (fun ⟨ℓ, hc', hr⟩ => by
        have := Option.some.inj (hc₁.2.symm.trans hc'.2)
        simp only [Node.acCall, Cut.ac.injEq] at this
        rw [← this] at hr
        cases hr) ht₁).1 hJu
  obtain ⟨ℓ₁, hupd⟩ : ∃ ℓ₁, SA.UpdateAt tr.projAC y c₁ s ℓ₁ := by
    refine ⟨_, Compose.projAC_callAt.2 hc₁, rfl, ht₁.trans hu_def, ?_⟩
    change SA.joined sp (tr.projAC.state y c₁) (tr.time c₁)
    rw [Compose.projAC_state hrun.toLocalRun hy c₁, ht₁]
    exact hj₁
  -- E4: the read cut is after the gate
  obtain ⟨hread, -, -⟩ := ready_read_cut S Q.run.2 Q.hn Q.constant Q.valid
    (by rw [hcu] at hdur; linarith) ht0 hth hw
  have hc₁j : c₁ < j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ c₁ by omega)
    linarith [hread.2]
  -- E3: no restart after `t_s` up to `t`, by joining at `t` and at `u`
  have hJt := (Compose.ready_implies_joined _ _ _ _ _ _ hrun y hy t Q.duration ht0
    (by rw [hcu] at hdur; linarith) hR.2).2
  have hJt' := ((Compose.joined_projection _ _ _ _ _ _ hrun y hy t).1).mp hJt
  have hJu' := ((Compose.joined_projection _ _ _ _ _ _ hrun y hy u).1).mp hJu
  have hrestarts : ∀ k, tr.projAC.RestartAt y k → tr.time k ≤ t → tr.time k ≤ sp.ts s :=
    fun k hk hkt => (hJu' k hk ((hJt' k hk hkt).trans hle)).trans_eq hslu
  -- E4: the latest view at `t` has label `s + 1`
  have hview :=
    latestView_label_of_gate sp (tr.state y j).ac (Node.frame (tr.state y j)) hgate hnext
  exact ⟨⟨s, hrestored, hgate, hnext, c₁, ℓ₁, hupd, hc₁j, hrestarts, hread, hview⟩⟩

/-- Ancestry of the two tips is the engine read prefix. -/
theorem outage_reader_prefix (Q : OutageQuery S A V) {v : V}
    (hv : Q.run.2.point.Ready Q.duration v Q.T) {t : Time} (hTt : Q.T ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t)
    (h : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t)) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  have hT0 : 0 ≤ Q.T := Q.outage.1.1
  have hc : 0 ≤ Q.duration := le_trans (by
    change (0 : Time) ≤ 18 * Q.params.Δ
    have := Q.params.toParams.hΔ; positivity) (duration_ge S A V Q)
  obtain ⟨-, -, hvT⟩ := ready_read_cut S Q.run.2 Q.hn Q.constant Q.valid hc hT0 (hTt.trans hth) hv
  obtain ⟨-, -, hwt⟩ := ready_read_cut S Q.run.2 Q.hn Q.constant Q.valid hc (hT0.trans hTt) hth hw
  refine confirmed_prefix_of_anc (simTrace_simulates S Q.run.2 Q.hn Q.constant Q.valid)
    (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision)
    ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hv.1)
    ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hw.1)
    (Nat.findGreatest_le _) (Nat.findGreatest_le _) ?_
  rw [hvT, hwt]
  exact h

end Consensus.Goldilocks.Obligations

end
