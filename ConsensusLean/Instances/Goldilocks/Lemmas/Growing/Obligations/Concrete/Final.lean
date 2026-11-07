module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalDutyProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorRoute
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.FinalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
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
* `final_duty_proposal_at`, `final_window_extract_at`: the route-A window extraction of a final
  query, with the carrier premise discharged;
* `final_anchor_coverage_at`: the anchor route's coverage at the last anchor's store;
* `final_cache_acceptance_of_publication_tail_at`, `final_cache_acceptance_at`: the last anchor's
  publication transfers the anchor coverage to every ready reader's final cache;
* `final_payload_projection_at`: window extraction with cache coverage gives the final
  `healthyLive` field;
* `meetsObligations_healthyLive_final_growing`: that field. -/

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

section Node

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The FG projection's store of a node honest at `d ≥ 0`, before a cut whose predecessors are at
times `≤ d`, is its state's FG part. -/
private theorem projFG_store_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {z : Fin sp.n} {k : Nat} {d : Time} (hd : 0 ≤ d) (hb : ∀ m < k, tr.time m ≤ d)
    (hz : z ∈ H d) : tr.projFG.store z k = (tr.state z k).fg := by
  have hp := Compose.projFG_state (hrun.upTo hd).toLocalRun hz k
  rw [RunTrace.upTo_projFG, Trace.upTo_state _ _ hb,
    Trace.upTo_state _ _ (show ∀ m < k, tr.projFG.time m ≤ d from hb)] at hp
  change (tr.projFG.state z k).1 = _
  rw [hp]

end Node

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

/-- (H2) of the final-window extraction under growing faults: the duty → proposal adapter. -/
theorem final_duty_proposal_at (Q : FinalQueryAt S A V) :
    ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGridAt S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.Growing.HonestProposalRun Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn) s P := by
  intro s hs hth hduty
  obtain ⟨_, P, hP, -⟩ := final_duty_proposal_run_at S A V Q hs hth hduty
  exact ⟨P, hP⟩

/-- **Extraction and endpoint budget under growing faults** (route A): a window of four honest
anchors at `start + [0, c, 2c, 3c]` after the query (`c = fgSlots`), with the publication slack,
its anchor run and its three anchor steps. -/
theorem final_window_extract_at (Q : FinalQueryAt S A V) :
    ∃ W : FinalWindowDataAt S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises_of_query_at S A V Q
  obtain ⟨W, -, hslack, hrun, hsteps⟩ :=
    final_window_extract_of_gap_at S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
      Q.hsSharedUpTo_at Q.protoFGDelay_delivery_at (final_latency_gap_at S A V Q) hreset
      (final_duty_proposal_at S A V Q) hplace (carrier_processed_of_honest_at S A V Q)
  exact ⟨W, hslack, hrun, hsteps⟩

/-- **Window coverage by the anchor route under growing faults.** The run premises and the three
anchor steps give, at the last anchor's store, the block `F` of root `σ[P₃].F` and `P₀ ⪯ F` inside
the blocks held while honest. The last anchor's proposer is read at its acceptance. -/
theorem final_anchor_coverage_at (Q : FinalQueryAt S A V) (W : FinalWindowDataAt S A V Q)
    (run : W.AnchorRun) (steps : W.AnchorSteps) :
    ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧ W.Extends (W.block 0) F := by
  obtain ⟨proposer, dg, g, ΔF, a, b, hp, hc, hP, hR, hb⟩ := W.anchorRun_iff.mp run
  have hg2 := W.gap_two
  have hg3 := W.gap_span
  have hs0 : (W.block 0).slot = W.start := W.slots 0
  have hs3 : (W.block 3).slot = W.start + 3 * W.gap := W.slots 3
  have hmono : StrictMono fun i : Fin 4 => W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> dsimp <;> omega
  have hsl : (W.block 3).slot ≤ (W.block 0).slot + Q.params.toParams.fg.δt := by
    change (W.block 3).slot ≤ (W.block 0).slot + S.δt
    omega
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hle : ∀ q < W.cut 3 + 1, Q.trace.time q ≤ Q.trace.time (W.cut 3) :=
    fun _ hq => hrun.time_mono (by omega)
  have hB3 := (accept_of_proposesAt_at hrun hnc (W.ready 3).1 (W.proposals 3)).2.1
  obtain ⟨F, hF, hAF⟩ := cacheCoverage_of_anchor_window_upTo_at hp hc hP hmono
    hR hb (by intro h; simp at h; omega) (W.anchorSteps_iff.mp steps) hsl
    (hrun.time_nonneg _) hle (W.ready 3).1 hB3
  refine ⟨F, ?_, hAF⟩
  change (Q.trace.post (W.cut 3)).fg.blocks ((Q.trace.post (W.cut 3)).fg.σ (W.block 3).root).F =
    some F
  rw [← Q.trace.state_succ_of_call (W.accepted 3)]
  exact hF

/-- The last anchor's actual forwarding publication has one protocol-delay tail before the
original deadline, and that tail fits every reader's catch-up interval. -/
def FinalPublicationTailAt (Q : FinalQueryAt S A V) (W : FinalWindowDataAt S A V Q) : Prop :=
  max (max (Q.trace.time (W.cut 3)) Q.gst) 0 + Q.params.Δ ≤ Q.deadline ∧
    Q.params.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run + 1

/-- Under the healthy population bound, fewer than `2q − n` keys are compromised at every time. -/
private theorem final_fault_count_at (Q : FinalQueryAt S A V) (d : Time) :
    (Q.keys d)ᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n := by
  have hpop := Q.healthy.2.1.1
  change ((Q.run.2.point.faultyAt Q.run.2.horizon).card : ℚ) <
    (K S A).params.β * Fintype.card V at hpop
  rw [goldilocksContract_params_eq] at hpop
  change ((Q.run.2.point.faultyAt Q.run.2.horizon).card : ℚ) < 1 / 3 * Fintype.card V at hpop
  have hle : (Q.keys d)ᶜ.ncard ≤ (Q.run.2.point.faultyAt Q.run.2.horizon).card := by
    have hsub : (Q.keys d)ᶜ ⊆
        Q.run.2.key ⁻¹' (↑(Q.run.2.point.faultyAt Q.run.2.horizon) : Set V) := by
      intro k hk
      have hk' : Q.run.2.key k ∈ Q.run.2.faultyAt (min d Q.run.2.horizon) := by
        by_contra h
        exact hk ((mem_honestKeysAt_iff S Q.run.2 d k).mpr h)
      exact Q.run.2.faultyAt_mono (min_le_right _ _) hk'
    calc (Q.keys d)ᶜ.ncard ≤ (Q.run.2.key ⁻¹'
          (↑(Q.run.2.point.faultyAt Q.run.2.horizon) : Set V)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (Q.run.2.point.faultyAt Q.run.2.horizon).card := by
          rw [Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
            (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
  have hn : 3 * (Q.run.2.point.faultyAt Q.run.2.horizon).card < Fintype.card V := by
    exact_mod_cast (show (3 : ℚ) * (Q.run.2.point.faultyAt Q.run.2.horizon).card <
      Fintype.card V by linarith only [hpop])
  change (Q.keys d)ᶜ.ncard < 2 * ((2 * Fintype.card V + 2) / 3) - Fintype.card V
  omega

/-- **Cache acceptance from the publication tail under growing faults.** With the last anchor's
publication tail, the anchor route's coverage at the last anchor's store transfers to the final
cache of every node ready at a read time from the deadline on. The proposer of the last anchor is
read at its acceptance, each reader at its read time, and the counts at the later observation. -/
theorem final_cache_acceptance_of_publication_tail_at (Q : FinalQueryAt S A V)
    (W : FinalWindowDataAt S A V Q) (tail : FinalPublicationTailAt S A V Q W)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hq := SA.interface_requirements Q.params (List (FG.Att Q.params.n)) (S.ro _)
  have fg := Compose.Growing.fg_projection _ _ _ _ _ _ _
    ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, SA.proposal_payload_valid _ _ _⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hx3 : (W.block 3).proposer ∈ Q.keys (Q.trace.time (W.cut 3)) := (W.ready 3).1
  have hd3 := hrun.time_nonneg (W.cut 3)
  have hle3 : ∀ q < W.cut 3 + 1, Q.trace.time q ≤ Q.trace.time (W.cut 3) :=
    fun _ hq => hrun.time_mono (by omega)
  have hpost : Q.trace.post (W.cut 3) = Q.trace.state (W.block 3).proposer (W.cut 3 + 1) :=
    (Q.trace.state_succ_of_call (W.accepted 3)).symm
  have hB3 := (accept_of_proposesAt_at hrun hnc hx3 (W.proposals 3)).2.1
  have hreach : W.store.Reachable (goldilocksNode Q.params (S.ro _)).genesisPayload := by
    change (Q.trace.post (W.cut 3)).fg.Reachable _
    rw [hpost]
    exact Healing.Growing.fg_reachable_at hrun hd3 hle3 hx3
  have hB : W.block 3 ∈ W.store.tree := by
    change W.block 3 ∈ (Q.trace.post (W.cut 3)).fg.tree
    rw [hpost]
    exact hB3
  have hsub : W.store.tree ⊆ Q.trace.HonestBlocksAt Q.keys := fun Z hZ =>
    ⟨_, W.cut 3 + 1, _, hd3, hle3, hx3, by rw [← hpost]; exact hZ⟩
  have hsource : W.store = Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) := by
    rw [projFG_store_at hrun hd3 hle3 hx3, ← hpost]
  have hk31 : Q.trace.time (W.cut 3 + 1) = Q.trace.time (W.cut 3) :=
    (Healing.ac_block_after (hrun.upTo hd3).toLocalRun hx3
      ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, W.accepted 3⟩)).2.1
  obtain ⟨X, hX, hAX⟩ := coverage
  have hXR := hreach.blocks_root hX
  have hXt : X ∈ W.store.tree := by change W.store.blocks X.root = some X; rwa [hXR]
  have hXB : W.Extends X (W.block 3) := by
    obtain ⟨_, ⟨X', hX', hX'r, hanc⟩, _⟩ :=
      Store.entry_state_of_source _ _ _ _ hreach _ hB
    have he : X' = X := (Store.accepted_tree _ _ _ _ hreach).2.1.1 hX' hXt (hX'r.trans hXR.symm)
    subst X'
    exact hanc.mono hsub
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff S Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance_at S Q.run.2 Q.hn Q.valid) _ _ _ hx3 (W.accepted 3)
  have hτh : Q.trace.time (W.cut 3) ≤ Q.run.2.horizon := (W.bounded 3).trans Q.bounded
  have hxk : Q.run.2.key (W.block 3).proposer ∉ Q.run.2.faultyAt (Q.trace.time (W.cut 3)) :=
    not_faulty_of_mem_honestKeysAt S Q.run.2 hx3 le_rfl hτh
  refine W.cacheCoverage_iff.mpr ?_
  intro y t j hdt hth hy hj
  have ht0 : 0 ≤ t := hd3.trans ((W.bounded 3).trans hdt)
  have hsafe := Consensus.Goldilocks.Growing.FGLocalRun.replay_finalized_safety_upTo fg
    (x := (W.block 3).proposer) (i := W.cut 3 + 1)
    (by change _ ∈ Q.keys (Q.trace.time (W.cut 3 + 1)); rw [hk31]; exact hx3) ht0 hj.1 hy.1
    (final_fault_count_at S A V Q _) (hsource ▸ hB) (hsource ▸ hXt)
    (show X.root = _ by rw [← hsource]; exact hXR)
  rw [projFG_store_at hrun ht0 hj.1 hy.1] at hsafe
  rcases hsafe with hXF | hFX
  · exact hAX.trans hXF
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  obtain ⟨d, hheld, hdt'⟩ := publication_held_ready_tail_at S Q.run.2 Q.hn hnet r hr
    (by rw [horg, htime]; exact hxk) (not_isFGAtt_of_decodeForward hdecode) hy hth
    (by rw [htime]; exact tail.1.trans hdt) tail.2
  have hrel : Q.run.2.releases (Q.run.2.key (W.block 3).proposer) r.object
      (Q.trace.time (W.cut 3)) :=
    ⟨r.event, by rw [← horg, ← htime]; exact (publisherExecution S Q.run.2).actual_event r hr,
      (publisherExecution S Q.run.2).actual_release r hr⟩
  have hyt : Q.run.2.key y ∉ Q.run.2.faultyAt t := not_faulty_of_mem_honestKeysAt S Q.run.2 hy.1
    le_rfl hth
  obtain ⟨k, hkj, hacc, hkt⟩ := held_forward_accepted_before_at S Q.run.2 Q.hn Q.valid hnc
    hj.1 hyt hxk hrel hheld hdecode hdt' hj.2.le (hFX.trans hXB)
  have hkj' : k + 1 ≤ j := by
    have : k ≠ j := by intro he; subst k; exact (not_lt_of_ge hj.2.le) hkt
    exact Nat.lt_of_le_of_ne hkj this
  have hlek : ∀ q < k + 1, Q.trace.time q ≤ t := fun q hq => hj.1 q (by omega)
  have hlek' : ∀ q < k, Q.trace.time q ≤ t := fun q hq => hj.1 q (by omega)
  have hyk : y ∈ Q.keys (Q.trace.time k) := honestKeysAt_antitone S Q.run.2 hkt.le hy.1
  have hpostB := (Healing.Growing.fg_reachable_at hrun ht0 hlek' hy.1)
  have hpostB : W.block 3 ∈ (Q.trace.state y (k + 1)).fg.tree := by
    rw [Q.trace.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ hpostB).1 _ _ (hrun.cutLaw y k _ hacc hyk).2.1]
    exact Set.mem_insert _ _
  have hpostX : X ∈ (Q.trace.state y (k + 1)).fg.tree :=
    Healing.Growing.mem_of_honest_anc_at hrun hnc ht0 hlek hy.1 hXB hpostB
  have hσ := Healing.Growing.σ_eq_honest_at hrun hnc hd3 hle3 hx3 ht0 hlek hy.1 hB3 hpostB
  have hFmono : ∀ {m m'}, m ≤ m' → m' ≤ j →
      Anc (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state y m).fg.F (Q.trace.state y m').fg.F := by
    intro m m' hmm hmj
    have h := Healing.run_F_mono (hrun.upTo ht0).toLocalRun hy.1 hmm
    rw [Trace.upTo_state _ _ fun q hq => hj.1 q (by omega),
      Trace.upTo_state _ _ fun q hq => hj.1 q (by omega)] at h
    exact h.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht0)
  have hkFX : Anc (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state y k).fg.F X :=
    (hFmono (Nat.le_succ k |>.trans hkj') le_rfl).trans hFX
  have hdk : 0 ≤ Q.trace.time k := hrun.time_nonneg k
  have hlek0 : ∀ q < k, Q.trace.time q ≤ Q.trace.time k := fun _ hq => hrun.time_mono hq.le
  have hlek1 : ∀ q < k + 1, Q.trace.time q ≤ t := hlek
  have hcache := Healing.Growing.accepted_replay_finalized_cached fg (y := y) (k := k) hyk
    (final_fault_count_at S A V Q _) (Compose.projFG_callAt.mpr hacc)
    (by rw [projFG_store_at hrun ht0 hlek1 hy.1]; exact hpostX)
    (by
      rw [projFG_store_at hrun ht0 hlek1 hy.1, ← hσ]
      change X.root = ((Q.trace.post (W.cut 3)).fg.σ (W.block 3).root).F at hXR
      rw [hpost] at hXR
      exact hXR)
    (by rw [projFG_store_at hrun hdk hlek0 hyk]; exact hkFX)
  rw [projFG_store_at hrun ht0 hlek1 hy.1] at hcache
  exact hAX.trans (hcache.trans (hFmono hkj' le_rfl))

/-- **Cache acceptance from the window's publication slack under growing faults.** -/
theorem final_cache_acceptance_at (Q : FinalQueryAt S A V) (W : FinalWindowDataAt S A V Q)
    (hslack : Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  apply final_cache_acceptance_of_publication_tail_at S A V Q W ?_ coverage
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hd := Q.run.1.ΔAC_pos
  have hq : max Q.gst 0 ≤ Q.query :=
    (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hd.le)).trans Q.mature
  have hs : max Q.gst 0 ≤ Q.trace.time (W.cut 3) :=
    (hq.trans W.fresh.le).trans (hrun.time_mono (W.ordered.monotone (by decide)))
  constructor
  · simpa only [max_eq_left ((le_max_left _ _).trans hs),
      max_eq_left ((le_max_right _ _).trans hs)] using hslack
  · have hc : (1 : Time) ≤ ((K S A).params.catchUp : Time) := by
      rw [goldilocksContract_params_eq]
      change (1 : Time) ≤ ((contract_coefficients S A).catchUp : Nat)
      exact_mod_cast (contract_coefficients S A).catchUp.pos
    change Q.run.1.ΔAC ≤ ((K S A).params.catchUp : Time) * Q.run.1.ΔAC + 1
    linarith only [mul_le_mul_of_nonneg_right hc hd.le]

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

/-- **Final healthy liveness under growing faults**: the `healthyLive` field of the shape claims
at the final capability. The route-A window extraction gives four honest anchors after the query,
the anchor route covers the last anchor's store, and the last anchor's publication transfers that
coverage to the final cache of every reader ready from the deadline on. -/
theorem meetsObligations_healthyLive_final_growing : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r)
        g ((Sys (goldilocks S) V).heal (K S A) .final i gst r)
        ((K S A).params.latency .final i) := by
  apply final_payload_projection_at S A V
  intro Q
  obtain ⟨W, hslack, run, steps⟩ := final_window_extract_at S A V Q
  exact ⟨W, hslack,
    final_cache_acceptance_at S A V Q W hslack (final_anchor_coverage_at S A V Q W run steps)⟩

end Query

end Consensus.Goldilocks.Obligations.Growing

end
