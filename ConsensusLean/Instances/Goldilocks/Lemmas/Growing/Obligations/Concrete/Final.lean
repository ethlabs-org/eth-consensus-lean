module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.FinalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowFieldsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing obligations: the final branch of healthy liveness

The growing-fault form of the static final route (`Obligations/CarrierProcessed` and
`Obligations/Concrete`), without a constant-fault premise. Honesty is read at each event's own
time: a proposer at its acceptance, a reader at its read time.

* `held_forward_blockCall_lt_at`: holdings of a wrapper of a signer honest at its stamp give a
  block call strictly before the deadline;
* `publication_held_ready_tail_at`: one protocol-delay publication tail gives holdings strictly
  before a ready read;
* `carrier_processed_of_honest_at`: (H4) of the final-window extraction, the carrier is processed
  by the deadline at every node ready at the deadline;
* `final_payload_projection_at`: window extraction with cache coverage gives the final
  `healthyLive` field. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- Holdings of a decoded wrapper of a signer honest at its stamp, strictly before `D`, give a
block call strictly before `D`. The form of `held_forward_blockCall_before_at` without an
observation cut. -/
theorem held_forward_blockCall_lt_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) :
    ∃ k, (simTraceAt S rho hn).BlockCallAt y k B ∧ (simTraceAt S rho hn).time k < D := by
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rw [simTraceAt_eq]
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    have hxy := released_forward_signer S rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp S rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap S rho hn (i + 1),
        (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace S rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
    obtain ⟨k, _, ha, ht⟩ := hacc
    exact ⟨k, ⟨true, hkey ▸ ha⟩, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le_of_stamp_at S rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    exact ⟨k, hkey ▸ hc, ht ▸ huD⟩

/-- **One protocol-delay publication tail gives holdings strictly before a ready read.** The
origin is honest at its publication event, the reader is ready at the read time `t`; the holding
time is strictly before `t`, so the reader is honest then. -/
theorem publication_held_ready_tail_at (hn : 1 ≤ Fintype.card V) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {t c : Time}
    (hy : Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((publisherExecution S rho).eventTime r.event) g) 0 +
      (S.params (Model.pubOf E) hn).Δ ≤ t)
    (hc : (S.params (Model.pubOf E) hn).Δ ≤ c + 1) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧ d < t := by
  let a := max (max (max ((publisherExecution S rho).eventTime r.event) g) 0) (t - c - 1)
  have hga : max a g = a := max_eq_left (by dsimp [a, Time]; omega)
  have hlt : a + E.ΔAC - 1 < t := by
    change max (max ((publisherExecution S rho).eventTime r.event) g) 0 + E.ΔAC ≤ t
      at hbudget
    change E.ΔAC ≤ c + 1 at hc
    dsimp [a, Time] at *; omega
  have hw : rho.point.AwakeOnClosed (rho.key y) a (a + E.ΔAC - 1) := by
    intro u hau hud
    have h := hy.2 u (by dsimp [a, Time] at *; omega) (hud.trans hlt.le)
    exact ((awakeAt_iff S rho hn y u).mp ((simTraceAt_awake_iff S rho hn y u).mp h)).1
  have hyd : rho.key y ∉ rho.faultyAt (max a g + E.ΔAC - 1) := by
    rw [hga]
    exact not_faulty_of_mem_honestKeysAt S rho hy.1 hlt.le (hlt.le.trans ht)
  have hh := (publication_held_psync_at S rho hn hnet r hr hx hrow hyd
    (show (publisherExecution S rho).eventTime r.event ≤ a by dsimp [a, Time]; omega)
    (by rw [hga]; exact hlt.le.trans ht) (by rw [hga]; exact hw)).1
  rw [hga] at hh
  exact ⟨a + E.ΔAC - 1, hh, hlt⟩

end Engine

section Query

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **(H4) of the final-window extraction under growing faults.** Every node ready at the
deadline processes an honest proposal of a slot `s` by the deadline, when `query < t_s` and
`t_s + Δ ≤ deadline`. The proposer is read at its acceptance (honest through `t_s + hold`), the
reader at the deadline. -/
theorem carrier_processed_of_honest_at (Q : FinalQueryAt S A V) :
    ∀ s P, Healing.Growing.HonestProposalRun Q.trace Q.keys
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline := by
  intro s P hP hq hD y hy
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hrun hP
  have htk : Q.trace.time k = Q.params.ts s := by
    rw [hk.2.2, honestProposalRun_slot_at hP, Q.params.slotTime_eq]
    simp [SA.SAParams.ts]
  have hΔ := Q.run.1.ΔAC_pos
  have hhold : Q.params.ts s ≤ Q.params.ts s + Regimes.Growing.hold Q.params := by
    have : (0 : Time) ≤ Regimes.Growing.hold Q.params := Q.params.toParams.hΔ.le
    linarith
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.keys (Q.trace.time k) :=
    htk ▸ honestKeysAt_antitone S Q.run.2 hhold hP.1
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt_at hrun hnc hmem hk
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance_at S Q.run.2 Q.hn Q.valid) _ _ _ hmem hacc
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
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
  have hth : Q.params.ts s ≤ Q.run.2.horizon := by
    have := Q.bounded
    have : (0 : Time) ≤ Q.params.Δ := Q.params.toParams.hΔ.le
    change Q.params.ts s ≤ Q.run.2.horizon
    linarith
  have hxk : Q.run.2.key (runProposer S Q.run.2 Q.hn s) ∉
      Q.run.2.faultyAt (Q.trace.time k) :=
    not_faulty_of_mem_honestKeysAt S Q.run.2 hmem le_rfl (htk ▸ hth)
  obtain ⟨d, hheld, hdt⟩ := publication_held_ready_tail_at S Q.run.2 Q.hn hnet r hr
    (by rw [horg, htime]; exact hxk)
    (not_isFGAtt_of_decodeForward hdecode) hy Q.bounded
    (by rw [htime, htk, hmax]; exact hD) hc
  obtain ⟨j, hj, hjt⟩ := held_forward_blockCall_lt_at S Q.run.2 Q.hn Q.valid hxk hheld
    hdecode hdt
  exact ⟨j, hj, hjt.le⟩

/-- **Payload/read projection of the final route under growing faults.** Window extraction with
cache coverage of the extracted window, for every final query, gives the `healthyLive` field at
the final capability: the first anchor is an engine proposal released after the query by a key
ready then, and its header is in the finalized read of every engine node ready at the deadline. -/
theorem final_payload_projection_at
    (windows : ∀ Q : FinalQueryAt S A V,
      ∃ W : FinalWindowDataAt S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
        W.CacheCoverage) :
    ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r)
        g ((Sys (goldilocks S) V).heal (K S A) .final i gst r)
        ((K S A).params.latency .final i) := by
  intro g hg i gst r hv ⟨hhealthy, hprog⟩
  have hg' : g = Out.finalized := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro t hm hb hr
  obtain ⟨v, hvr⟩ := hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : FinalQueryAt S A V := ⟨r, hn, i, gst, t, hv, hcollision, hhealthy, hprog, hm, hb, v, hvr⟩
  obtain ⟨W, -, hcover⟩ := windows Q
  have ht : 0 ≤ t := by
    have hd := r.1.ΔAC_pos
    have hg0 : (0 : Time) ≤ max gst 0 := le_max_right _ _
    have hp : 0 ≤ ((K S A).params.heal .final i : Time) * r.1.ΔAC :=
      mul_nonneg (Int.natCast_nonneg _) hd.le
    exact (add_nonneg hg0 hp).trans hm
  have hτ : 0 ≤ Q.trace.time (W.cut 0) := ht.trans W.fresh.le
  have hτh : Q.trace.time (W.cut 0) ≤ r.2.horizon := (W.bounded 0).trans hb
  have hproposal : Regimes.Growing.ReadyProposalAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) r) (Q.trace.time (W.cut 0)) 0 (W.block 0) :=
    ⟨_, W.cut 0, W.ready 0, by rw [add_zero]; exact (W.ready 0).1, W.proposals 0, rfl⟩
  obtain ⟨k, hk, hrel⟩ := ready_proposal_at S r.2 hn hv hτh hproposal
  refine ⟨Q.trace.time (W.cut 0), k, headerOf Q.params (W.block 0), W.fresh, hk, hrel, ?_⟩
  have hc : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) r := by
    exact mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le
  have hdeadline : 0 ≤ Q.deadline := ht.trans (by
    change t ≤ t + _
    exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le))
  have hroot : (W.block 0).root ≠ Q.params.genesisRoot := by
    have run := (simTraceAt_goldilocksRun S r.2 hn hv).upTo hτ
    rcases Compose.blockCall_cases run.toLocalRun (W.ready 0).1
        ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, W.accepted 0⟩) with hg | hg
    · have hz := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      simp only [Nat.add_zero] at hz
      exact False.elim ((W.proposals 0).1.2 hz)
    · obtain ⟨j, x, _, _, _, d, p, _, hB, _⟩ := hg
      rw [hB, digestOf_eq]
      simp only [Node.mkBlock]
      erw [dgOf_eq]
      exact taggedRoot_ne _ _
  exact finalized_inBy_at S r.2 hn hv (noCollRun_simTraceAt S r.2 hn hv hcollision) hc hdeadline
    hb hroot (fun y j hy hj => W.cacheCoverage_iff.mp hcover y Q.deadline j le_rfl hb hy hj)

end Query

end Consensus.Goldilocks.Obligations.Growing

end
