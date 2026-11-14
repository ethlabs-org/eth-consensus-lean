module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The shared HS premises of a healthy run under growing faults

The shared HS premises on the canonical growing trace with the time-indexed honest keys:

* `hsSharedUpTo_of_rows_at`: the shared HS premises through the horizon at a parametric `Δ_F`,
  from attestation service at `Δ_F`. The fault bound holds at every `t ∈ [0, horizon]` since
  compromise only grows (`faultyAt t ⊆ faultyAt horizon`); a node honest at a restart is asleep
  one tick before it, hence restarts by `ḡ`.
* `FinalQueryAt.hsSharedUpTo_at`, `FinalQueryAt.protoFGDelay_delivery_at`: the final query's
  instance at the protocol FG delay. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Shape Blocks

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A restarting node of the canonical trace is asleep one tick before its restart, whatever its
honesty. -/
private theorem asleep_before_restart_at {E : Env V} (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (y : Fin (Fintype.card V)) (i : Nat)
    (hr : (simTraceAt ⟨S, stock⟩ rho hn).RestartAt y i) :
    ¬ (simTraceAt ⟨S, stock⟩ rho hn).awake y ((simTraceAt ⟨S, stock⟩ rho hn).time i - 1) := by
  rw [simTraceAt_eq ⟨S, stock⟩ rho hn] at hr ⊢
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hr
  intro h
  have hl : (simTrace ⟨S, stock⟩ rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨r, i₀, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut ⟨S, stock⟩ rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts ⟨S, stock⟩ rho hn he (List.mem_of_getElem? hidx) hrl hcall
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey ⟨S, stock⟩ rho (hn'.symm.trans hnode)
  subst hkey
  obtain ⟨-, -, hw2⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  have hw := ((awake_iff' ⟨S, stock⟩ rho hn y _).mp h).1
  rw [ht, hw2] at hw
  exact Bool.false_ne_true hw

/-- **The shared HS premises of a healthy run through its horizon under growing faults, from
attestation service at `Δ_F`**, at GST `g` and the digest of the run. -/
theorem hsSharedUpTo_of_rows_at (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (goldilocks S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (goldilocks S) V).Healthy (K S A) g run) {ΔF : Time}
    (hrow : PSyncFGAttTransportAt ⟨S, stock⟩ run.2 (simTraceAt ⟨S, stock⟩ run.2 hn)
        (honestKeysAt ⟨S, stock⟩ run.2) ΔF)
    (hΔF : 0 < ΔF)
    (htd : 6 * (S.params (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time)) :
    Healing.Growing.HSSharedUpTo (simTraceAt ⟨S, stock⟩ run.2 hn) (honestKeysAt ⟨S, stock⟩ run.2)
      (digestOf ⟨S, stock⟩ run.2) g ΔF run.2.horizon := by
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ run.2 hn valid noCollision
  have hnet : run.2.log.PSync run.2.point g := (Model.sysOf_delivers_iff _ _ _ _).mp healthy.1
  have hawake : ∀ y t, y ∈ honestKeysAt ⟨S, stock⟩ run.2 t → SA.gbar g ≤ t → t ≤ run.2.horizon →
      (simTraceAt ⟨S, stock⟩ run.2 hn).awake y t := by
    intro y t hy hg hb
    rw [simTraceAt_awake_iff ⟨S, stock⟩ run.2 hn, awakeAt_iff ⟨S, stock⟩ run.2 hn]
    rw [mem_honestKeysAt_iff ⟨S, stock⟩ run.2, min_eq_left hb] at hy
    exact ⟨healthy.2.1.2 (run.2.key y) t hg hb hy, le_trans (le_max_right _ _) hg, hb⟩
  refine ⟨hnc, simTrace_genesis_root_ok ⟨S, stock⟩ run.2 hn,
    resetService_of_psync_at S run.2 hn valid hnc hnet hrow hΔF, hawake, ?_, ?_, htd⟩
  · intro t _ htb
    have hpop := healthy.2.1.1
    change ((run.2.faultyAt run.2.horizon).card : ℚ) <
      (K S A).params.β * Fintype.card V at hpop
    rw [goldilocksContract_params_eq] at hpop
    change ((run.2.faultyAt run.2.horizon).card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeysAt ⟨S, stock⟩ run.2 t)ᶜ.ncard = (run.2.faultyAt t).card := by
      have heq : (honestKeysAt ⟨S, stock⟩ run.2 t)ᶜ = run.2.key ⁻¹'
          (↑(run.2.faultyAt t) : Set V) := by
        ext k; simp [mem_honestKeysAt_iff ⟨S, stock⟩ run.2, min_eq_left htb]
      rw [heq, Set.ncard_preimage_of_injective_subset_range run.2.key.injective
        (by simp [run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    change 3 * (honestKeysAt ⟨S, stock⟩ run.2 t)ᶜ.ncard ≤ Fintype.card V - 1
    rw [hfault]
    have hle : (run.2.faultyAt t).card ≤ (run.2.faultyAt run.2.horizon).card :=
      Finset.card_le_card (run.2.faultyAt_mono htb)
    have hn3 : 3 * (run.2.faultyAt run.2.horizon).card < Fintype.card V := by
      exact_mod_cast
        (show (3 : ℚ) * (run.2.faultyAt run.2.horizon).card < Fintype.card V by linarith)
    omega
  · intro y k hy hk hkb
    by_contra hlt
    rw [not_le] at hlt
    have hy' : y ∈ honestKeysAt ⟨S, stock⟩ run.2 ((simTraceAt ⟨S, stock⟩ run.2 hn).time k - 1) :=
      honestKeysAt_antitone ⟨S, stock⟩ run.2 (by linarith) hy
    exact asleep_before_restart_at S V run.2 hn valid y k hk
      (hawake y _ hy' (Int.le_sub_one_of_lt hlt) (by linarith))

namespace FinalQueryAt

variable {S A V}

/-- **The shared HS premises of a final query through its horizon** under growing faults, at GST
`Q.gst`, the protocol FG delay `Δ_F,p = protoFGDelay (pubOf E)` with the network's attestation
service there (`signed_row_service_psync_at`), the rise timeout
`protoFGDelay_timeout_of_fgDelay`, and the digest of the run. -/
theorem hsSharedUpTo_at (Q : FinalQueryAt S A V) :
    Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf ⟨S, stock⟩ Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1)) Q.run.2.horizon :=
  hsSharedUpTo_of_rows_at S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy
    (signed_row_service_psync_at S Q.run.2 Q.hn Q.valid) (protoFGDelay_pos _)
    (protoFGDelay_timeout_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2)

/-- **The FG transport of a final query** at its FG gap: `6Δ + Δ_F,p ≤ 4Δ·fgSlots`. -/
theorem protoFGDelay_delivery_at (Q : FinalQueryAt S A V) :
    6 * Q.params.Δ + protoFGDelay (Model.pubOf Q.run.1) ≤ 4 * Q.params.Δ * (A.fgSlots : Time) :=
  protoFGDelay_delivery_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2

end FinalQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
