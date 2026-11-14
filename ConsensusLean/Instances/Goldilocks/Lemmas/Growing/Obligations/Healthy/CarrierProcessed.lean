module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The carrier of the last anchor is processed by the deadline, under growing faults

Under growing faults:

* `publication_held_ready_tail_at`: one protocol-delay tail after
  an actual publication of an origin honest at its event is held strictly before the read time of
  a node ready there;
* `held_forward_blockCall_lt_at`: a held forwarding wrapper of a
  signer honest at its stamp is processed before the holding bound;
* `carrier_processed_of_honest_at`, the premise `hcarrier` of
  `final_window_extract_of_gap_at`: every node ready at the deadline processes an honest proposal
  of a slot `s` by the deadline, when `query < t_s` and `t_s + Δ ≤ deadline`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- One protocol-delay publication tail is held strictly before a ready read, under growing
faults: the origin is honest at its event and the reader at its read time. -/
theorem publication_held_ready_tail_at (hn : 1 ≤ Fintype.card V) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution ⟨S, stock⟩ rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution ⟨S, stock⟩ rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {t c : Time}
    (hy : Regimes.Growing.ReadyAt (simTraceAt ⟨S, stock⟩ rho hn)
        (honestKeysAt ⟨S, stock⟩ rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((publisherExecution ⟨S, stock⟩ rho).eventTime r.event) g) 0 +
      (S.params (Model.pubOf E) hn).Δ ≤ t)
    (hc : (S.params (Model.pubOf E) hn).Δ ≤ c + 1) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧ d < t := by
  let a := max (max (max ((publisherExecution ⟨S, stock⟩ rho).eventTime r.event) g) 0) (t - c - 1)
  have hga : max a g = a := max_eq_left (by dsimp [a, Time]; omega)
  have hlt : a + E.ΔAC - 1 < t := by
    change max (max ((publisherExecution ⟨S, stock⟩ rho).eventTime r.event) g) 0 + E.ΔAC ≤ t
      at hbudget
    change E.ΔAC ≤ c + 1 at hc
    dsimp [a, Time] at *; omega
  have hw : rho.point.AwakeOnClosed (rho.key y) a (a + E.ΔAC - 1) := by
    intro u hau hud
    have h := hy.2 u (by dsimp [a, Time] at *; omega) (hud.trans hlt.le)
    exact ((awakeAt_iff ⟨S, stock⟩ rho hn y u).mp
        ((simTraceAt_awake_iff ⟨S, stock⟩ rho hn y u).mp h)).1
  have hh := (publication_held_psync_at ⟨S, stock⟩ rho hn hnet r hr hx hrow
    (by rw [hga]; exact not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ rho hy.1 hlt.le (hlt.le.trans ht))
    (show (publisherExecution ⟨S, stock⟩ rho).eventTime r.event ≤ a by dsimp [a, Time]; omega)
    (by rw [hga]; exact hlt.le.trans ht) (by rw [hga]; exact hw)).1
  rw [hga] at hh
  exact ⟨a + E.ΔAC - 1, hh, hlt⟩

/-- A held forwarding wrapper of a signer honest at its stamp is processed before the holding
bound (the cut-free form of `held_forward_blockCall_before_at`). -/
theorem held_forward_blockCall_lt_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) :
    ∃ k, (simTraceAt ⟨S, stock⟩ rho hn).BlockCallAt y k B ∧ (simTraceAt ⟨S, stock⟩ rho hn).time k <
        D := by
  rw [simTraceAt_eq ⟨S, stock⟩ rho hn]
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    have hxy := released_forward_signer ⟨S, stock⟩ rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp ⟨S, stock⟩ rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap ⟨S, stock⟩ rho hn (i + 1),
        (simTrace ⟨S, stock⟩ rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace ⟨S, stock⟩ rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance ⟨S, stock⟩ rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance ⟨S, stock⟩ rho hn hv he ho hdecode
    obtain ⟨k, _, ha, ht⟩ := hacc
    exact ⟨k, ⟨true, hkey ▸ ha⟩, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le_of_stamp_at ⟨S, stock⟩ rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall ⟨S, stock⟩ rho hn hi (.refl o) hdecode htu
    exact ⟨k, hkey ▸ hc, ht ▸ huD⟩

end Engine

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The carrier of an honest proposal is processed by the deadline**, under growing faults. -/
theorem carrier_processed_of_honest_at (Q : FinalQueryAt S A V) :
    ∀ s P, Healing.Growing.HonestProposalRun Q.trace Q.keys
      (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline := by
  intro s P hP hq hD y hy
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hrun hP
  have hmem := proposer_mem_of_proposesAt_at hrun hP hk
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt_at hrun hnc hmem hk
  have htk : Q.trace.time k = Q.params.ts s := by
    rw [hk.2.2, honestProposalRun_slot_at hP, Q.params.slotTime_eq]
    simp [SA.SAParams.ts]
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff ⟨S, stock⟩ Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance_at ⟨S, stock⟩ Q.run.2 Q.hn Q.valid) _ _ _ hmem hacc
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  have hΔ := Q.run.1.ΔAC_pos
  have hg : max Q.gst 0 ≤ Q.query :=
    (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hΔ.le)).trans Q.mature
  have hmax : max (max (Q.params.ts s) Q.gst) 0 = Q.params.ts s := by
    have h1 := le_max_left Q.gst 0
    have h2 := le_max_right Q.gst 0
    have h3 : Q.gst ≤ Q.params.ts s := by linarith
    have h4 : (0 : Time) ≤ Q.params.ts s := by linarith
    rw [max_eq_left h3, max_eq_left h4]
  have hc : Q.params.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := by
    have hc1 : (1 : Time) ≤ ((K S A).params.catchUp : Time) := by
      rw [goldilocksContract_params_eq]
      change (1 : Time) ≤ ((contract_coefficients S A).catchUp : Nat)
      exact_mod_cast (contract_coefficients S A).catchUp.pos
    change Q.run.1.ΔAC ≤ ((K S A).params.catchUp : Time) * Q.run.1.ΔAC + 1
    linarith [mul_le_mul_of_nonneg_right hc1 (zero_le_one.trans Q.run.1.ΔAC_pos)]
  have hkh : Q.trace.time k ≤ Q.run.2.horizon := by
    have hΔp := Q.params.toParams.hΔ
    rw [htk]
    linarith [Q.bounded]
  have hx : Q.run.2.key (runProposer ⟨S, stock⟩ Q.run.2 Q.hn s) ∉
      Q.run.2.faultyAt (Q.trace.time k) :=
    not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ Q.run.2 hmem le_rfl hkh
  obtain ⟨d, hheld, hdt⟩ := publication_held_ready_tail_at S Q.run.2 Q.hn hnet r hr
    (by rw [horg, htime]; exact hx) (not_isFGAtt_of_decodeForward hdecode) hy Q.bounded
    (by rw [htime, htk, hmax]; exact hD) hc
  obtain ⟨j, hj, hjt⟩ := held_forward_blockCall_lt_at S Q.run.2 Q.hn Q.valid hx hheld hdecode hdt
  exact ⟨j, hj, hjt.le⟩

end Consensus.Goldilocks.Obligations.Growing

end
