module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalResetPremises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CarrierProcessed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorRoute
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalReplay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Final healthy liveness under growing faults (route A)

The growing form of the final branch of `Obligations/Concrete`
(`meetsObligations_healthyLive_final`): a final query has a window of four honest anchors with its
run premises and anchor steps (`final_window_extract_at`), whose first anchor is covered by the
finalized cache of every node ready from the deadline (`final_cache_coverage_at`); the payload
projection (`final_payload_projection_at`) turns that into the shape's proposal liveness.

Each store is read at an observation of a node honest there: the last anchor's proposer at its
acceptance, a ready reader at its read time. Finalized safety between them is charged at the later
observation (`FGLocalRun.replay_finalized_safety_upTo_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Obligations
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

private theorem final_node_requirements_at (Q : FinalQueryAt S A V) :
    (goldilocksNode Q.params (S.ro _)).Requirements := by
  have h := SA.interface_requirements Q.params (List (FG.Att Q.params.n)) (S.ro _)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid _ _ _⟩

private theorem final_fg_run_at (Q : FinalQueryAt S A V) :
    Consensus.Goldilocks.Growing.FGLocalRun (goldilocksNode Q.params (S.ro _)).genesisPayload
      Q.keys (Q.trace.HonestBlocksAt Q.keys) Q.trace.projFG := by
  have hr := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  exact Compose.Growing.fg_projection _ _ _ _ _ _ _ (final_node_requirements_at S A V Q)
    hr.genesis_root_ok hr.toLocalRun
        (noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision)

/-- The FG store of a node honest at an observation after its earlier cuts is its node state's. -/
private theorem final_store_eq_at (Q : FinalQueryAt S A V) {y : Fin Q.params.n} {i : Nat}
    {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, Q.trace.time k ≤ t) (hy : y ∈ Q.keys t) :
    Q.trace.projFG.store y i = (Q.trace.state y i).fg := by
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have h := Compose.projFG_state (hrun.toLocalRun.upTo ht) hy i
  rw [RunTrace.upTo_projFG, Trace.upTo_state Q.trace.projFG y hle,
    Trace.upTo_state Q.trace y hle] at h
  exact congrArg Prod.fst h

/-- The validators compromised at any time number fewer than `2q − n`. -/
private theorem final_faults_at (Q : FinalQueryAt S A V) {t : Time} (ht : 0 ≤ t)
    (hth : t ≤ Q.run.2.horizon) :
    (Q.keys t)ᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n := by
  have h := (FinalQueryAt.hsSharedUpTo_at Q).faults t ht hth
  change (Q.keys t)ᶜ.ncard < 2 * ((2 * Fintype.card V + 2) / 3) - Fintype.card V
  change 3 * (Q.keys t)ᶜ.ncard ≤ Fintype.card V - 1 at h
  have := Q.hn
  omega

/-- (H2) of the final window, route A: the duty → proposal adapter under growing faults. -/
theorem final_duty_proposal_at (Q : FinalQueryAt S A V) :
    ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGridAt S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.Growing.HonestProposalRun Q.trace Q.keys (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) s
          P := by
  intro s hs hth hduty
  obtain ⟨_, P, hP, -⟩ := final_duty_proposal_run_at S A V Q hs hth hduty
  exact ⟨P, hP⟩

/-- **Final-window extraction** (route A) under growing faults: a window of four honest anchors
at the FG gap `c = fgSlots`, with its slack, its anchor run and its three anchor steps. -/
theorem final_window_extract_at (Q : FinalQueryAt S A V) :
    ∃ W : FinalWindowDataAt S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises_at S A V Q
  obtain ⟨W, -, hslack, hrun, hsteps⟩ :=
    final_window_extract_of_gap_at S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
      (FinalQueryAt.hsSharedUpTo_at Q) (FinalQueryAt.protoFGDelay_delivery_at Q)
      (final_latency_gap_at S A V Q) hreset (final_duty_proposal_at S A V Q) hplace
      (carrier_processed_of_honest_at S A V Q)
  exact ⟨W, hslack, hrun, hsteps⟩

/-- **Window coverage at a holder of the last anchor.** The run premises and the three anchor
steps give, at a holder of `P₃` honest at an observation after its cuts, the block `F` of root
`σ[P₃].F` with `P₀ ⪯ F`. -/
theorem final_anchor_coverage_at (Q : FinalQueryAt S A V) (W : FinalWindowDataAt S A V Q)
    (run : W.AnchorRun) (steps : W.AnchorSteps) {z : Fin Q.params.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, Q.trace.time q ≤ t) (hz : z ∈ Q.keys t)
    (hB : W.block 3 ∈ (Q.trace.state z k).fg.tree) :
    ∃ F, (Q.trace.state z k).fg.blocks ((Q.trace.state z k).fg.σ (W.block 3).root).F = some F ∧
      W.Extends (W.block 0) F := by
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
  exact cacheCoverage_of_anchor_window_upTo_at hp hc hP hmono hR hb
    (by intro h; simp at h; omega) (W.anchorSteps_iff.mp steps) hsl ht hle hz hB

/-- **Finalized-cache coverage of the first anchor** at every ready read after the deadline. The
last anchor's proposer holds the covering block `X` at its acceptance; finalized safety against
the reader's cache, charged at the read time, puts `X` below the reader's cache or the cache below
`X`. In the second case the reader accepts the last anchor before its read and caches `X` there.
-/
theorem final_cache_coverage_at (Q : FinalQueryAt S A V) (W : FinalWindowDataAt S A V Q)
    (hslack : Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline)
    (run : W.AnchorRun) (steps : W.AnchorSteps) : W.CacheCoverage := by
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have fg := final_fg_run_at S A V Q
  have hmono := hrun.time_mono
  -- the last anchor's proposer, at its acceptance
  set x := (W.block 3).proposer with hxdef
  set c := W.cut 3 with hcdef
  have hx : x ∈ Q.keys (Q.trace.time c) := (W.ready 3).1
  have hc0 := hrun.time_nonneg c
  have hlc : ∀ q < c + 1, Q.trace.time q ≤ Q.trace.time c := fun q hq => hmono (by omega)
  obtain ⟨hacc, hBx, -⟩ := accept_of_proposesAt_at hrun hnc hx (W.proposals 3)
  obtain ⟨X, hX, hAX⟩ := final_anchor_coverage_at S A V Q W run steps hc0 hlc hx hBx
  have hRx := Healing.Growing.fg_reachable_at hrun hc0 hlc hx
  have hXR := hRx.blocks_root hX
  have hXt : X ∈ (Q.trace.state x (c + 1)).fg.tree := by
    change (Q.trace.state x (c + 1)).fg.blocks X.root = some X
    rwa [hXR]
  have hancx : (Q.trace.state x (c + 1)).fg.Anc X (W.block 3) := by
    obtain ⟨_, ⟨X', hX', hX'r, hanc⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hRx _ hBx
    have he : X' = X := (Store.accepted_tree _ _ _ _ hRx).2.1.1 hX' hXt (hX'r.trans hXR.symm)
    subst X'
    exact hanc
  have hXB : W.Extends X (W.block 3) := Healing.Growing.honest_anc_of_store_anc_at hc0 hlc hx hancx
  have hsx := final_store_eq_at S A V Q hc0 hlc hx
  -- its forwarding publication
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptanceAt_iff ⟨S, stock⟩ Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance_at ⟨S, stock⟩ Q.run.2 Q.hn Q.valid) _ _ _ hx hacc
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  have hd := Q.run.1.ΔAC_pos
  have hq : max Q.gst 0 ≤ Q.query :=
    (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hd.le)).trans Q.mature
  have hcq : max Q.gst 0 ≤ Q.trace.time c :=
    (hq.trans W.fresh.le).trans (hmono (W.ordered.monotone (by decide)))
  have hch : Q.trace.time c ≤ Q.run.2.horizon := (W.bounded 3).trans
    (by linarith [Q.bounded, show Q.deadline = Q.query + _ from rfl])
  have hxr : Q.run.2.key x ∉ Q.run.2.faultyAt (Q.trace.time c) :=
    not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ Q.run.2 hx le_rfl hch
  have hrel : Q.run.2.releases (Q.run.2.key x) r.object (Q.trace.time c) := by
    rw [← horg, ← htime]
    exact ⟨r.event, (publisherExecution ⟨S, stock⟩ Q.run.2).actual_event r hr,
      (publisherExecution ⟨S, stock⟩ Q.run.2).actual_release r hr⟩
  have hcd : Q.params.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := by
    have hc1 : (1 : Time) ≤ ((K S A).params.catchUp : Time) := by
      rw [goldilocksContract_params_eq]
      change (1 : Time) ≤ ((contract_coefficients S A).catchUp : Nat)
      exact_mod_cast (contract_coefficients S A).catchUp.pos
    change Q.run.1.ΔAC ≤ ((K S A).params.catchUp : Time) * Q.run.1.ΔAC + 1
    linarith only [mul_le_mul_of_nonneg_right hc1 hd.le]
  refine W.cacheCoverage_iff.mpr ?_
  intro y t j hdt hth hy hj
  have ht0 : 0 ≤ t := (hc0.trans ((W.bounded 3).trans hdt))
  have hle := hj.1
  have hct : Q.trace.time c ≤ t := (W.bounded 3).trans hdt
  have hsy := final_store_eq_at S A V Q ht0 hle hy.1
  have hft := final_faults_at S A V Q ht0 hth
  have hf : (Q.keys (max (Q.trace.time c) t))ᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n :=
    by rw [max_eq_right hct]; exact hft
  have hsafe := fg.replay_finalized_safety_upTo_at hc0 hlc hx ht0 hle hy.1 hf
    (B := W.block 3) (X := X) (by rw [hsx]; exact hBx) (by rw [hsx]; exact hXt)
    (by rw [hsx]; exact hXR)
  rw [hsy] at hsafe
  rcases hsafe with hXF | hFX
  · exact hAX.trans hXF
  -- the reader's cache is below `X`: it accepts the last anchor before its read
  obtain ⟨d, hheld, hdt'⟩ := publication_held_ready_tail_at S Q.run.2 Q.hn hnet r hr
    (by rw [horg, htime]; exact hxr) (not_isFGAtt_of_decodeForward hdecode) hy hth
    (by
      rw [htime, max_eq_left (show Q.gst ≤ Q.trace.time c from (le_max_left _ _).trans hcq),
        max_eq_left hc0]
      exact hslack.trans hdt) hcd
  obtain ⟨k, hkj, hacc', hkt⟩ := held_forward_accepted_before_at ⟨S, stock⟩ Q.run.2 Q.hn Q.valid hnc
    hle (not_faulty_of_mem_honestKeysAt ⟨S, stock⟩ Q.run.2 hy.1 le_rfl hth) hxr hrel hheld
    hdecode hdt' hj.2.le (hFX.trans hXB)
  have hkj' : k + 1 ≤ j := by
    have : k ≠ j := by intro he; subst k; exact (not_lt_of_ge hj.2.le) hkt
    omega
  have hlk : ∀ q < k + 1, Q.trace.time q ≤ t := fun q hq => hle q (by omega)
  have hlk' : ∀ q < k, Q.trace.time q ≤ t := fun q hq => hle q (by omega)
  have hsk1 := final_store_eq_at S A V Q ht0 hlk hy.1
  have hsk := final_store_eq_at S A V Q ht0 hlk' hy.1
  -- the reader's acceptance, on the prefix through its read
  have fgt := fg.upTo ht0
  have hpre1 := Trace.upTo_state Q.trace.projFG y hlk
  have hpre := Trace.upTo_state Q.trace.projFG y hlk'
  have hac : FGTrace.AcceptAt (Q.trace.projFG.upTo t) y k (W.block 3) :=
    (Trace.upTo_callAt Q.trace.projFG).mpr ⟨hle k (by omega), Compose.projFG_callAt.mpr hacc'⟩
  have hpostB : W.block 3 ∈ (FGTrace.store (Q.trace.projFG.upTo t) y (k + 1)).tree := by
    have h := Store.accept_onBlock fgt hy.1 hac
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fgt hy.1 k)).1 _ _ h]
    exact Set.mem_insert _ _
  have hpostB' : W.block 3 ∈ (Q.trace.projFG.store y (k + 1)).tree := by
    simpa only [FGTrace.store, hpre1] using hpostB
  have hBx' : W.block 3 ∈ (Q.trace.projFG.store x (c + 1)).tree := by rw [hsx]; exact hBx
  have hσ := Store.Growing.σ_eq_of_held fg hc0 ht0 hx hy.1 hlc hlk hBx' hpostB'
  have hancy := Store.Growing.anc_transfer fg hc0 ht0 hx hy.1 hlc hlk
    (show (Q.trace.projFG.store x (c + 1)).Anc X (W.block 3) by rw [hsx]; exact hancx) hpostB'
  have hpostX : X ∈ (Q.trace.projFG.store y (k + 1)).tree := by
    by_cases he : X = W.block 3
    · exact he ▸ hpostB'
    · exact (Anc.mem hancy he).1
  have hXr' : X.root = ((Q.trace.projFG.store y (k + 1)).σ (W.block 3).root).F := by
    rw [← hσ, hsx]; exact hXR
  -- the reader's cache before the acceptance is below `X`
  have hrt := hrun.upTo ht0
  have hgrow : ∀ {k₁ k₂}, k₁ ≤ k₂ → k₂ ≤ j →
      Anc (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state y k₁).fg.F (Q.trace.state y k₂).fg.F := by
    intro k₁ k₂ h12 h2
    have h := (Compose.fg_grows hrt hy.1 h12).2
    have hl₂ : ∀ q < k₂, Q.trace.time q ≤ t := fun q hq => hle q (by omega)
    have hl₁ : ∀ q < k₁, Q.trace.time q ≤ t := fun q hq => hle q (by omega)
    rw [Trace.upTo_state Q.trace y hl₁, Trace.upTo_state Q.trace y hl₂] at h
    exact h.mono (RunTrace.honestBlocks_upTo_subset hmono ht0)
  have hFX' : Anc (Q.trace.HonestBlocksAt Q.keys)
      (FGTrace.store (Q.trace.projFG.upTo t) y k).F X := by
    rw [show FGTrace.store (Q.trace.projFG.upTo t) y k = Q.trace.projFG.store y k by
      simp only [FGTrace.store, hpre], hsk]
    exact (hgrow (Nat.le_of_lt (by omega)) (by omega)).trans hFX
  have hcache := Healing.accepted_replay_finalized_cached fgt (by exact hft) hy.1 hac
    (by simpa only [FGTrace.store, hpre1] using hpostX)
    (by simpa only [FGTrace.store, hpre1] using hXr') hFX'
  rw [show FGTrace.store (Q.trace.projFG.upTo t) y (k + 1) = Q.trace.projFG.store y (k + 1) by
    simp only [FGTrace.store, hpre1], hsk1] at hcache
  exact hAX.trans (hcache.trans (hgrow hkj' le_rfl))

/-- **The payload projection** under growing faults: final windows whose first anchor is covered
by the finalized cache of every node ready from the deadline give the shape's final proposal
liveness. -/
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
  let Q : FinalQueryAt S A V := ⟨r, hn, i, gst, t, hv, hcollision, hhealthy,
    hprog, hm, hb, v, hvr⟩
  obtain ⟨W, hslack, hcover⟩ := windows Q
  have ht : 0 ≤ t := by
    have hd := r.1.ΔAC_pos
    have hg0 : (0 : Time) ≤ max gst 0 := le_max_right _ _
    have hp : 0 ≤ ((K S A).params.heal .final i : Time) * r.1.ΔAC :=
      mul_nonneg (Int.natCast_nonneg _) hd.le
    exact (add_nonneg hg0 hp).trans hm
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
    have run := simTraceAt_goldilocksRun ⟨S, stock⟩ r.2 hn hv
    have h0 := run.time_nonneg (W.cut 0)
    have hc0 : (Q.trace.upTo (Q.trace.time (W.cut 0))).CallAt (W.block 0).proposer (W.cut 0)
        (.fg (.block (W.block 0) true)) :=
      (Trace.upTo_callAt_of_le _ le_rfl).mpr (W.accepted 0)
    rcases Compose.blockCall_cases (run.upTo h0).toLocalRun (W.ready 0).1 hc0 with hg | hg
    · have hz : Q.trace.pos (W.cut 0) = 0 := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim ((W.proposals 0).1.2 (by simpa using hz))
    · obtain ⟨j, x, _, _, _, d, p, _, hB, _⟩ := hg
      rw [hB, digestOf_eq ⟨S, stock⟩ r.2]
      simp only [Node.mkBlock]
      erw [dgOf_eq]
      exact taggedRoot_ne _ _
  exact finalized_inBy_at S r.2 hn hv
    (noCollRun_simTraceAt ⟨S, stock⟩ r.2 hn hv hcollision) hc hdeadline hb hroot
    (fun y j hy hj => W.cacheCoverage_iff.mp hcover y Q.deadline j le_rfl hb hy hj)

/-- **Final healthy liveness under growing faults**: the `healthyLive` field of the shape claims
at the final capability. -/
theorem meetsObligations_healthyLive_final_growing : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r)
        g ((Sys (goldilocks S) V).heal (K S A) .final i gst r)
        ((K S A).params.latency .final i) :=
  final_payload_projection_at S A V fun Q => by
    obtain ⟨W, hslack, run, steps⟩ := final_window_extract_at S A V Q
    exact ⟨W, hslack, final_cache_coverage_at S A V Q W hslack run steps⟩

end Consensus.Goldilocks.Obligations.Growing

end
