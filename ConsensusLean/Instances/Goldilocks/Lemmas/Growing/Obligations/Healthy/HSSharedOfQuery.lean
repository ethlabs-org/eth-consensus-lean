module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap

public section

/-! # The shared HS premises of a healthy run under growing faults

The shared HS premises on the canonical growing trace with the time-indexed honest keys:

* `hsSharedUpTo_of_rows_at`: the shared HS premises through the horizon at a parametric `Δ_F`,
  from attestation service at `Δ_F`. The fault bound holds at every `t ∈ [0, horizon]` since
  compromise only grows (`faultyAt t ⊆ faultyAt horizon`); a node honest at a restart is asleep
  one tick before it, hence restarts by `ḡ`.
* `FinalQueryAt.hsSharedUpTo_at`, `FinalQueryAt.protoFGDelay_delivery_at`: the final query's
  instance at the release hold `R·Δ_AC` and the FG delay `Δ_F,p + R·Δ_AC`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Shape Blocks

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A restarting node of the canonical trace is asleep one tick before its restart, whatever its
honesty. -/
private theorem asleep_before_restart_at {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (y : Fin (Fintype.card V)) (i : Nat)
    (hr : (simTraceAt S rho hn).RestartAt y i) :
    ¬ (simTraceAt S rho hn).awake y
      ((simTraceAt S rho hn).time i - 1) := by
  rw [simTraceAt_eq S rho hn] at hr ⊢
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hr
  intro h
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨r, i₀, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ :=
    simTrace_cut_origin S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he
      (List.mem_of_getElem? hidx) hrl hcall
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  obtain ⟨-, -, hw2⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  have hw := ((awake_iff' S rho hn y _).mp h).1
  rw [ht, hw2] at hw
  exact Bool.false_ne_true hw

/-- **The shared HS premises of a healthy run through its horizon under growing faults, from
attestation service at `Δ_F` with release hold `hold ≤ Δ_F`**, at GST `g` and the digest of the
run. -/
private theorem hsSharedUpTo_of_rows_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (goldilocks S) V).Valid run)
    (noCollision : ¬ run.2.HashCollision)
    {g : Time} (K : Contract ProgressReq) (hβ : K.params.β ≤ 1 / 3)
    (healthy : (Sys (goldilocks S) V).Healthy
        (shapeProgress (goldilocks S) V).toExternal K g run)
    {ΔF hold : Time}
    (hrow : PSyncFGAttTransportAt S run.2
        (simTraceAt S run.2 hn)
        (honestKeysAt S run.2) ΔF hold)
    (hΔF : 0 < ΔF) (hhold : hold ≤ ΔF)
    (htd : 6 * (S.params
      (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ *
        (S.δt : Time)) :
    Healing.Growing.HSSharedUpTo (simTraceAt S run.2 hn)
      (honestKeysAt S run.2)
      (digestOf S run.2) g ΔF run.2.horizon hold := by
  have hnc := noCollRun_simTraceAt S run.2 hn valid noCollision
  have hnet : run.2.log.PSync run.2.point g := (Model.sysOf_delivers_iff _ _ _ _).mp healthy.1
  have hawake : ∀ y t, y ∈ honestKeysAt S run.2 t →
      AC.gbar g ≤ t → t ≤ run.2.horizon →
      (simTraceAt S run.2 hn).awake y t := by
    intro y t hy hg hb
    rw [simTraceAt_awake_iff S run.2 hn,
      awakeAt_iff S run.2 hn]
    rw [mem_honestKeysAt_iff S run.2, min_eq_left hb] at hy
    exact ⟨healthy.2.1.2 (run.2.key y) t hg hb hy, le_trans (le_max_right _ _) hg, hb⟩
  refine ⟨hnc, simTrace_genesis_root_ok S run.2 hn,
    resetService_of_psync_at S run.2 hn valid hnc hnet hrow
      (fun _ => healthy.2.1.2) hΔF hhold, hawake,
    ?_, ?_, htd⟩
  · exact healthy_preparation_faults_at run hn hβ le_rfl healthy.2.1
  · intro y k hy hk hkb
    by_contra hlt
    rw [not_le] at hlt
    have hy' : y ∈ honestKeysAt S run.2
        ((simTraceAt S run.2 hn).time k - 1) :=
      honestKeysAt_antitone S run.2 (by linarith) hy
    exact asleep_before_restart_at S V run.2 hn valid y k hk
      (hawake y _ hy' (Int.le_sub_one_of_lt hlt) (by linarith))

namespace FinalQueryAt

variable {S A V}

/-- **The shared HS premises of a final query through its horizon** under growing faults, at GST
`Q.gst`, the release hold `R·Δ_AC` of the contract's release gap `R = A.releaseGap` and the FG delay
`Δ_F,p + R·Δ_AC` (`Δ_F,p = protoFGDelay (pubOf E)`), with the network's attestation service there
(`signed_row_service_psync_at` at `A.release_liveness`), the rise timeout
`6Δ + Δ_F,p + R·Δ ≤ 4Δ·δ_t` (`protoFGDelay_delivery_of_fgDelay` and
`ContractAssumptions.fgSlots_releaseGap_signGap_le`), and the digest of the run. -/
theorem hsSharedUpTo_at
    (Q : FinalQueryAt S A V) :
    Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf S Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1) + (A.releaseGap : Time) * Q.run.1.ΔAC)
      Q.run.2.horizon ((A.releaseGap : Time) * Q.run.1.ΔAC) := by
  have hp := protoFGDelay_pos (Model.pubOf Q.run.1)
  have hΔ : 0 < Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hR : (0 : Time) ≤ (A.releaseGap : Time) * Q.run.1.ΔAC :=
    mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hd : 6 * Q.run.1.ΔAC + protoFGDelay (Model.pubOf Q.run.1) ≤
      4 * Q.run.1.ΔAC * (A.fgSlots : Time) :=
    protoFGDelay_delivery_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2.1
  have hc : 4 * (A.fgSlots : Time) + (A.releaseGap : Time) ≤ 4 * (S.δt : Time) := by
    have := A.fgSlots_releaseGap_signGap_le
    exact_mod_cast (show 4 * A.fgSlots + A.releaseGap ≤ 4 * S.δt by omega)
  have hcΔ := mul_le_mul_of_nonneg_left hc hΔ.le
  exact hsSharedUpTo_of_rows_at S V Q.run Q.hn Q.valid Q.noCollision (K S A)
    (by rw [goldilocksContract_params_eq]; norm_num [Params.standard]) Q.healthy
    (signed_row_service_psync_at S Q.run.2 Q.hn Q.valid
      (releaseGapAt_of_assumptions A (Model.pubOf Q.run.1) Q.hn))
    (by linarith) (by linarith)
    (by change 6 * Q.run.1.ΔAC + _ ≤ 4 * Q.run.1.ΔAC * (S.δt : Time); nlinarith)

/-- **The FG transport of a final query** at its FG gap: `6Δ + Δ_F,p ≤ 4Δ·fgSlots`. -/
theorem protoFGDelay_delivery_at
    (Q : FinalQueryAt S A V) :
    6 * Q.params.Δ + protoFGDelay (Model.pubOf Q.run.1) ≤ 4 * Q.params.Δ * (A.fgSlots : Time) :=
  protoFGDelay_delivery_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2.1

end FinalQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
