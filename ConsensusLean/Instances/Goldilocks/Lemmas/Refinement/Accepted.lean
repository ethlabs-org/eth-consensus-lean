module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalEndpoints
import ConsensusLean.Lemmas.Model.Laws
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ForwardingDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAnchorRoute
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.CarrierProcessed
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalDutyProposal

public section

/-! # Acceptance assembly with finite guarantee witnesses

The assumptions are fixed before choosing guarantees. The three named coefficient
holes and named supplier leaves are joint obligations, not independent arbitrary
choices. Every endpoint adapter is assembled; this does not prove acceptance.
Do not import into Main/Solution.
The local pattern is a fixed function of Setup's timeout; no legacy consecutive-run
formula or dependence of timeout on the outer gap is imposed here.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- R8, claims C0.1/C0.2/F.2, node outputs_valid. NO PAPER PROOF for
engine/read transport; replacement endpoint: engine_outputValid. -/
theorem accepted_outputValid : (Sys (family S) V).HoldsAlways fun r =>
    ∀ c g, schema.output c = some g → OutputValid r.2 g := by
  exact shape_outputValid V S

/-- R8, claims C0.1/C0.2/F.2, node outputs_nested. NO PAPER PROOF for
engine chain transport; replacement endpoint: engine_nested. -/
theorem accepted_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂ := by
  exact shape_nested V S

/-- R8, claims F.2, node finalized_monotone. NO PAPER PROOF for engine
read transport; replacement endpoint: engine_finalMonotone. -/
theorem accepted_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0 := by
  exact shape_finalMonotone V S

/-- R7, claims G0.5 and G1.1–G1.5, node final_accountable.
NO PAPER PROOF for held-tree evidence/view and collision transport. Raw
GenesisFresh is not a premise here: the encoding must discharge root separation. -/
theorem accepted_finalAccountable : ∀ g, schema.output .final = some g →
    (Sys (family S) V).Holds (fun _ => True) fun r =>
      (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable
        (K S A).params.α g 0 := by
  exact shape_finalAccountable V S (K S A) (by norm_num [Params.standard])

private theorem final_node_requirements (Q : FinalQuery S A V) :
    (goldilocksNode Q.params (S.ro _)).Requirements := by
  have h := SA.interface_requirements Q.params (List (FG.Att Q.params.n)) (S.ro _)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid _ _ _⟩

private theorem final_fg_run (Q : FinalQuery S A V) :
    FGLocalRun (goldilocksNode Q.params (S.ro _)).genesisPayload (honestKeys S Q.run.2)
      (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Q.trace.projFG := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  exact Compose.fg_projection _ _ _ _ _ _ _ (final_node_requirements S A V Q)
    hr.genesis_root_ok hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)

private theorem final_anchor_post (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (a : Fin 4) :
    Q.trace.post (W.cut a) = Q.trace.state (W.block a).proposer (W.cut a + 1) := by
  exact (Q.trace.state_succ_of_call (W.accepted a)).symm

private theorem final_store_reachable (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.store.Reachable (goldilocksNode Q.params (S.ro _)).genesisPayload := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  change (Q.trace.post (W.cut 3)).fg.Reachable _
  rw [final_anchor_post S A V Q W 3]
  exact Compose.fg_reachable hr.toLocalRun (W.ready 3).1 _

private theorem final_anchor_held (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.block 3 ∈ W.store.tree := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hon := (hr.cutLaw _ (W.ready 3).1 _ _ (W.accepted 3)).2.1
  change W.block 3 ∈ (Q.trace.post (W.cut 3)).fg.tree
  rw [(Store.tree_grows _ _ _ _ (Compose.fg_reachable hr.toLocalRun (W.ready 3).1 _)).1 _ _ hon]
  exact Set.mem_insert _ _

/-- Assemble independently produced finite anchors and carrier processing.
Every budget and actual event remains explicit; eligible duties alone do not suffice. -/
theorem final_window_of_production (Q : FinalQuery S A V) (start : Nat)
    (block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))) (cut : Fin 4 → Nat)
    (slots : ∀ a, (block a).slot = start + (![0, 2, 4, 6] a))
    (proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a))
    (accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a))
    (ready : ∀ a, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a)))
    (fresh : Q.query < Q.trace.time (cut 0)) (ordered : StrictMono cut)
    (bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline)
    (chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (block a) (block b))
    (carrier : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline) :
    Nonempty (FinalWindowData S A V Q) :=
  ⟨⟨start, block, cut, slots, proposals, accepted, ready, fresh, ordered, bounded, chain, carrier⟩⟩


/-- OPEN (H1)+(H3) of `final_window_extract_of'` (CarrierProcessed.lean), route A (#136). One
reset `a` with a bound `ΔR` such that (H1) the reset premises `ResetPremisesUpTo` hold through the
horizon at GST `Q.gst`, with the run proposer and digest (Sol's M1′ reset), and (H3) the
placement `(P)` holds with `u_min = finalSeedMin Q a = slot a + 2k + 5` (the heal coefficient must
be large enough; #145 removed a time summand that made (H3) false for large GST). (H1) and (H3)
are one leaf because (H3) depends on the reset `a` of (H1): two separate existentials would not
give the same `a`. No producer is assumed. -/
theorem final_reset_premises (Q : FinalQuery S A V) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen := by
  sorry

/-- (H2) of `final_window_extract_of'` (CarrierProcessed.lean), route A (#136): the duty →
proposal adapter. An honest proposer that is ready in a slot `s > 0` with `t_s ≤ horizon`
(`HonestReadyIn`) makes an honest proposal run at `s` (`HonestProposalRun`). Proved by
`final_duty_proposal_run` (FinalDutyProposal.lean). -/
theorem final_duty_proposal (Q : FinalQuery S A V) :
    ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P := by
  intro s hs hth hduty
  obtain ⟨_, P, hP, -⟩ := final_duty_proposal_run S A V Q hs hth hduty
  exact ⟨P, hP⟩

/-- Extraction and endpoint budget (route A). A window of four honest anchors at the slots
`start + [0, 2, 4, 6]` after the query, its route-A run premises, and its three anchor steps.
Proved by `final_window_extract_of'` from the open leaf `final_reset_premises` ((H1), (H3)) and
the proved `final_duty_proposal` ((H2)); (H4) is proved there. Paper: workbench route_a_gap2.md,
window_start_h0.md, anchor_row_supplier.md, anchor_tick_ac_producer.md (read-back #136). -/
theorem final_window_extract (Q : FinalQuery S A V) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises S A V Q
  obtain ⟨W, hslack, hrun, hsteps⟩ :=
    final_window_extract_of' S A V Q hreset (final_duty_proposal S A V Q) hplace
  exact ⟨W, hslack, W.anchorRun_iff.mpr hrun, W.anchorSteps_iff.mpr hsteps⟩

/-- **Window coverage by the anchor route.** The run premises and the three anchor steps give,
at the last anchor's store, the block `F` of root `σ[P₃].F` and `P₀ ⪯ F`. The window slots and
`6 ≤ δt` give `P₃.slot ≤ P₀.slot + δt`; the adjacent-anchor guard is vacuous (gap 2). -/
theorem final_anchor_coverage (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (run : W.AnchorRun) (steps : W.AnchorSteps) :
    ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧ W.Extends (W.block 0) F := by
  obtain ⟨proposer, dg, g, ΔF, a, b, hp, hc, hP, hR, hb⟩ := W.anchorRun_iff.mp run
  have hd := A.timeout
  have hs0 : (W.block 0).slot = W.start := by simpa using W.slots 0
  have hs3 : (W.block 3).slot = W.start + 6 := by simpa using W.slots 3
  have hmono : StrictMono fun i : Fin 4 => W.start + ![0, 2, 4, 6] i := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simp
  have hsl : (W.block 3).slot ≤ (W.block 0).slot + Q.params.toParams.fg.δt := by
    change (W.block 3).slot ≤ (W.block 0).slot + S.δt
    omega
  have hB3 : W.block 3 ∈ (Q.trace.state (W.block 3).proposer (W.cut 3 + 1)).fg.tree := by
    rw [← final_anchor_post S A V Q W 3]
    exact final_anchor_held S A V Q W
  obtain ⟨F, hF, hAF⟩ := cacheCoverage_of_anchor_window_upTo hp hc hP hmono
    (by simpa using hR) (by simpa using hb) (by intro h; simp at h) (W.anchorSteps_iff.mp steps) hsl
    (W.ready 3).1 hB3
  refine ⟨F, ?_, hAF⟩
  change (Q.trace.post (W.cut 3)).fg.blocks ((Q.trace.post (W.cut 3)).fg.σ (W.block 3).root).F =
    some F
  rw [final_anchor_post S A V Q W 3]
  exact hF

/-- Transport an acceptance-or-coverage certificate from its actual historical
cut to the reader endpoint. The acceptance branch must already transfer immutable
carrier finality to the recipient cache; a BlockCallAt or compatibility is insufficient. -/
theorem final_cache_coverage_of_prior_cache (Q : FinalQuery S A V)
    (W : FinalWindowData S A V Q)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F)
    (producer : ∀ F, W.store.blocks (W.state (W.block 3)).F = some F →
      ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
      ∃ k ≤ j, W.Extends F (Q.trace.state y k).fg.F ∨
        W.Extends (W.block 0) (Q.trace.state y k).fg.F) : W.CacheCoverage := by
  obtain ⟨F, hF, hAF⟩ := coverage
  refine W.cacheCoverage_iff.mpr ?_
  intro y t j hdt hth hy hj
  obtain ⟨k, hkj, hk⟩ := producer F hF y t j hdt hth hy hj
  have hmono := (Compose.fg_grows
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid) hy.1 hkj).2
  rcases hk with h | h
  · exact (hAF.trans h).trans hmono
  · exact h.trans hmono

/-- The last anchor's actual forwarding publication has one protocol-delay tail before
the original deadline, and that tail fits every reader's catch-up interval. -/
def FinalPublicationTail (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) : Prop :=
  max (max (Q.trace.time (W.cut 3)) Q.gst) 0 + Q.params.Δ ≤ Q.deadline ∧
    Q.params.Δ ≤ (Sys (family S) V).cDur (K S A) Q.run + 1

/-- Conditional endpoint assembly. The only additional timing premise is the named
publication tail; receipt, historical acceptance and cache transfer are proved. -/
theorem final_cache_acceptance_of_publication_tail (Q : FinalQuery S A V)
    (W : FinalWindowData S A V Q) (tail : FinalPublicationTail S A V Q W)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have fg := final_fg_run S A V Q
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  have hst : ∀ z, z ∈ honestKeys S Q.run.2 → ∀ k,
      Q.trace.projFG.store z k = (Q.trace.state z k).fg := by
    intro z hz k
    simp only [FGTrace.store, Compose.projFG_state run.toLocalRun hz k]
  have hsource : W.store = Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) := by
    rw [hst _ (W.ready 3).1]
    exact congrArg NodeState.fg (final_anchor_post S A V Q W 3)
  have hf : (honestKeys S Q.run.2)ᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n := by
    have hpop := Q.healthy.2.1
    change (Q.run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [acceptanceContract_params_eq] at hpop
    change (Q.run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S Q.run.2)ᶜ.ncard = Q.run.2.point.faulty.card := by
      have heq : (honestKeys S Q.run.2)ᶜ = Q.run.2.key ⁻¹' (↑Q.run.2.point.faulty : Set V) := by
        ext k; simp [honestKeys, EnvPoint.faulty, Model.Run.point]
      rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
        (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    rw [hfault]
    have hn : 3 * Q.run.2.point.faulty.card < Fintype.card V := by
      exact_mod_cast (show (3 : ℚ) * Q.run.2.point.faulty.card < Fintype.card V by linarith)
    change Q.run.2.point.faulty.card < 2 * ((2 * Fintype.card V + 2) / 3) - Fintype.card V
    omega
  obtain ⟨X, hX, hAX⟩ := coverage
  have hXR := (final_store_reachable S A V Q W).blocks_root hX
  have hXt : X ∈ W.store.tree := by change W.store.blocks X.root = some X; rwa [hXR]
  have hB := final_anchor_held S A V Q W
  have hXB : W.Extends X (W.block 3) := by
    obtain ⟨_, ⟨X', hX', hX'r, hanc⟩, _⟩ :=
      Store.entry_state_of_source _ _ _ _ (final_store_reachable S A V Q W) _ hB
    have he : X' = X := (Store.accepted_tree _ _ _ _
      (final_store_reachable S A V Q W)).2.1.1 hX' hXt (hX'r.trans hXR.symm)
    subst X'
    exact hanc.mono (by rw [hsource]; exact fg.tree_subset _ (W.ready 3).1 _)
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance S Q.run.2 Q.hn Q.valid) _ (W.ready 3).1 _ _ (W.accepted 3)
  refine W.cacheCoverage_iff.mpr ?_
  intro y t j hdt hth hy hj
  have hsafe := Store.replay_finalized_safety fg hf (W.ready 3).1 hy.1
    (hsource ▸ hB) (hsource ▸ hXt) (show X.root = _ by rw [← hsource]; exact hXR)
    (j := j)
  rw [hst _ hy.1] at hsafe
  rcases hsafe with hXF | hFX
  · exact hAX.trans hXF
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst := by
    constructor
    · intro v hv o s hs w hw a hsa hc hh haw
      have h := Q.healthy.1.msgs v hv ⟨Q.run.1, o⟩ s ⟨o, rfl, hs⟩ w hw a hsa hc hh haw
      rcases h with ⟨u, hu, hsent | hrecv, hnowake⟩
      · obtain ⟨o', he, hs'⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl hs', hnowake⟩
      · obtain ⟨o', he, hr'⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr hr', hnowake⟩
    · exact Q.healthy.1.txs
  obtain ⟨d, hheld, hdt'⟩ := publication_held_ready_tail S Q.run.2 Q.hn hnet r hr
    (horg ▸ (W.ready 3).1) hy hth (by rw [htime]; exact tail.1.trans hdt) tail.2
  obtain ⟨k, hkj, hacc, hkt⟩ := held_forward_accepted_before S Q.run.2 Q.hn Q.valid hnc
    hy.1 (W.ready 3).1 hheld hdecode hdt' hj.2.le (hFX.trans hXB)
  have hkj' : k + 1 ≤ j := by
    have : k ≠ j := by intro he; subst k; exact (not_lt_of_ge hj.2.le) hkt
    omega
  have hac : Q.trace.projFG.AcceptAt y k (W.block 3) := Compose.projFG_callAt.mpr hacc
  have hpostB : W.block 3 ∈ (Q.trace.projFG.store y (k + 1)).tree := by
    have h := Store.accept_onBlock fg hy.1 hac
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fg hy.1 k)).1 _ _ h]
    exact Set.mem_insert _ _
  have hpostXB := Store.anc_of_U fg hy.1 hXB hpostB
  have hpostX : X ∈ (Q.trace.projFG.store y (k + 1)).tree := by
    by_cases he : X = W.block 3
    · exact he ▸ hpostB
    · exact (Anc.mem hpostXB he).1
  have hσ := Store.σ_eq_of_held fg (W.ready 3).1 hy.1 (hsource ▸ hB) hpostB
  have hkFX : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Q.trace.projFG.store y k).F X := by
    rw [hst _ hy.1]
    exact ((Compose.fg_grows run hy.1 hkj).2).trans hFX
  have hcache := Healing.accepted_replay_finalized_cached fg hf hy.1 hac hpostX
    (by rw [← hσ, ← hsource]; exact hXR) hkFX
  rw [hst _ hy.1] at hcache
  exact hAX.trans (hcache.trans (Compose.fg_grows run hy.1 hkj').2)

/-- Acceptance from the selected window's publication slack. Catch-up duration and
the source's position after GST follow from the existing query and window premises. -/
theorem final_cache_acceptance (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (hslack : Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  apply final_cache_acceptance_of_publication_tail S A V Q W ?_ coverage
  have hd := Q.run.1.Δ_pos
  have hq : max Q.gst 0 ≤ Q.query := by
    exact (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hd.le)).trans Q.mature
  have hs : max Q.gst 0 ≤ Q.trace.time (W.cut 3) :=
    (hq.trans W.fresh.le).trans
      (simTrace_time_mono S Q.run.2 Q.hn Q.valid (W.ordered.monotone (by decide)))
  constructor
  · simpa only [max_eq_left ((le_max_left _ _).trans hs),
      max_eq_left ((le_max_right _ _).trans hs)] using hslack
  · have hc : (1 : Time) ≤ ((K S A).params.catchUp : Time) := by
      rw [acceptanceContract_params_eq]
      change (1 : Time) ≤ ((accepted_coefficients S A).catchUp : Nat)
      exact_mod_cast (accepted_coefficients S A).catchUp.pos
    change Q.run.1.Δ + 1 ≤ ((K S A).params.catchUp : Time) * Q.run.1.Δ + 1
    nlinarith

/-- Conditional payload/read projection of the finite supplier package. Uses the engine's
existing catch-up duration, raw own-block release, and final cache membership at endCut.
Window extraction with CacheCoverage of the extracted window remains an explicit input;
no coefficient is synthesized. -/
theorem final_payload_projection
    (windows : ∀ Q : FinalQuery S A V,
      ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
        W.CacheCoverage) :
    ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  intro g hg i gst r hv ⟨hhealthy, hprog⟩
  have hg' : g = Out.finalized := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro t hm hb hr
  obtain ⟨v, hvr⟩ := hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : FinalQuery S A V := ⟨r, hn, i, gst, t, hv, hcollision, hhealthy,
    hprog, hm, hb, v, hvr⟩
  obtain ⟨W, hslack, hcover⟩ := windows Q
  have ht : 0 ≤ t := by
    have hd := r.1.Δ_pos
    have hg0 : (0 : Time) ≤ max gst 0 := le_max_right _ _
    have hp : 0 ≤ ((K S A).params.heal .final i : Time) * r.1.Δ :=
      mul_nonneg (Int.natCast_nonneg _) hd.le
    exact (add_nonneg hg0 hp).trans hm
  have hτ : 0 ≤ Q.trace.time (W.cut 0) := ht.trans W.fresh.le
  have hτh : Q.trace.time (W.cut 0) ≤ r.2.horizon := (W.bounded 0).trans hb
  have hproposal : Regimes.ReadyProposalAt Q.trace (honestKeys S r.2)
      ((Sys (family S) V).cDur (K S A) r) (Q.trace.time (W.cut 0)) (W.block 0) :=
    ⟨_, W.cut 0, W.ready 0, W.proposals 0, rfl⟩
  obtain ⟨k, hk, hrel⟩ := ready_proposal S r.2 hn hv hτ hτh hproposal
  refine ⟨Q.trace.time (W.cut 0), k, headerOf Q.params (W.block 0), W.fresh, hk, hrel, ?_⟩
  have hc : 0 ≤ (Sys (family S) V).cDur (K S A) r := by
    exact mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le
  have hdeadline : 0 ≤ Q.deadline := ht.trans (by
    change t ≤ t + _
    exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le))
  have hroot : (W.block 0).root ≠ Q.params.genesisRoot := by
    have run := simTrace_goldilocksRun S r.2 hn hv
    rcases Compose.blockCall_cases run.toLocalRun (W.ready 0).1 (W.accepted 0) with hg | hg
    · have hz := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim ((W.proposals 0).1.2 (by simpa using hz))
    · obtain ⟨j, x, _, _, _, d, p, _, hB, _⟩ := hg
      rw [hB]
      exact taggedRoot_ne _ _
  exact finalized_inBy S r.2 hn hv
    (noCollTransport V S r.1 r.2 hn hv hcollision) hc hdeadline hb hroot
    (fun y j hy hj => W.cacheCoverage_iff.mp hcover y Q.deadline j le_rfl hb hy hj)

/-- Statement-only assembly of the OPEN route-A suppliers; not a completed liveness proof.
Coverage is the anchor route (`final_anchor_coverage`); the open leaf is
`final_reset_premises` (via `final_window_extract`; `final_duty_proposal` is proved).
Paper: workbench route_a_gap2.md (read-back #136). -/
theorem accepted_healthyLive_final : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  apply final_payload_projection S A V
  intro Q
  obtain ⟨W, hslack, run, steps⟩ := final_window_extract S A V Q
  exact ⟨W, hslack,
    final_cache_acceptance S A V Q W hslack (final_anchor_coverage S A V Q W run steps)⟩

/-- R3 available/stable inclusion; R4 FinalInclude for final.
NO PAPER PROOF for exact contract gHeal, bounded recurrence→node progress,
or repaired engine timing transport. See generic-r3-bridge-audit.md.
This field must not acquire whole-run progress before ready as a premise. -/
theorem accepted_healthyLive : ∀ cap g, schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
          ((Sys (family S) V).ready (K S A) gst r)
          ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  intro cap g hg idx gst r hv ⟨hh, hp⟩
  by_cases hf : cap = .final
  · subst cap
    exact accepted_healthyLive_final S A V g hg idx gst r hv ⟨hh, hp⟩
  have hcap : cap = .available ∨ cap = .stable := by cases cap <;> simp_all
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQuery S A V := ⟨r, hn, cap, hcap, idx, gst, t, hv, hc,
    Or.inr ⟨hh, hp, ht⟩, hb, hr⟩
  obtain ⟨P, cover⟩ := healthy_confirmed_supply S A V Q hh hp ht
  have h0 : 0 ≤ t :=
    (add_nonneg (le_max_right gst 0)
      (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le)).trans ht
  exact confirmed_payload_projection S A V Q h0 P cover

/-- R1, sleepy-record-invariant.md §§2–5.1 and sleepy-proposal-adoption.md
§§2–4 (conditional S1–S4 package). NO PAPER PROOF for engine network,
readiness and read-cut transport. Node route: sleepy_invariant and ready reads. -/
theorem accepted_sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → (Sys (family S) V).Holds
      ((Sys (family S) V).Sleepy (K S A)) fun r =>
        (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r) g 0 := by
  intro cap g hcap hg r hv hs
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  by_cases hn : 1 ≤ Fintype.card V
  · let Q : SleepySafetyQuery S A V := ⟨r, hn, hv, hc, hs⟩
    obtain ⟨hd, hsync, hf⟩ := sleepy_safety_inputs S A V Q
    have safe := sleepy_safe_engine S r.2 hn hv
      (noCollTransport V S r.1 r.2 hn hv hc) hsync hf
    have ready : ∀ v t, r.2.point.Ready ((Sys (family S) V).cDur (K S A) r) v t →
        r.2.point.Ready (Regimes.catchUp (S.params (Model.pubOf r.1) hn) + 1) v t := by
      intro v t h
      refine ⟨h.1, fun τ hlo hhi => h.2 τ ?_ hhi⟩
      exact (max_le_max_left 0 (sub_le_sub_right (sub_le_sub_left hd t) 1)).trans hlo
    exact ⟨fun u v i j hi hj hu hv => safe.1 u v i j hi hj (ready _ _ hu) (ready _ _ hv),
      fun v i j hi hij hj hvi hvj => safe.2 v i j hi hij hj (ready _ _ hvi) (ready _ _ hvj)⟩
  · have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩

/-- R2 inclusion/growth, node sleepy_statements. NO PAPER PROOF yet pinned
for the exact recurrence/readiness/deadline transport; keep this gap explicit. -/
theorem accepted_sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ i : (K S A).Idx,
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Sleepy (K S A) r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            0 ((Sys (family S) V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
          g 0 ((K S A).params.latency cap i) := by
  intro cap g hcap hg idx r hv ⟨hs, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQuery S A V := ⟨r, hn, cap, hcap, idx, 0, t, hv, hc,
    Or.inl ⟨hs, hp, ht⟩, hb, hr⟩
  obtain ⟨P, service⟩ := sleepy_serviced_proposal_supply S A V Q hs hp ht
  exact confirmed_payload_projection S A V Q ht P
    (sleepy_serviced_proposal_coverage S A V Q P service)

/-- R3 healed safety. NO PAPER PROOF for bounded [ready,heal] recurrence
to current whole-run HealedPremises or the target gHeal bound. RecRet also
has no completed proof (rc-recret-induction.md §6). -/
theorem accepted_healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ (i : (K S A).Idx) (gst : Time),
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            ((Sys (family S) V).ready (K S A) gst r)
            ((Sys (family S) V).heal (K S A) cap i gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r)
          g ((Sys (family S) V).heal (K S A) cap i gst r) := by
  intro cap g hcap hg idx gst r hv ⟨hh, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  have htime : ∀ k, k ≤ (chainTrace r.2).cuts →
      (chainTrace r.2).cutTime k ≤ r.2.horizon :=
    (Model.sysOf_laws schema (compiled (family S)) V).trace r hv |>.cutTime_le_horizon
  let heal := (Sys (family S) V).heal (K S A) cap idx gst r
  by_cases hb : heal ≤ r.2.horizon
  · by_cases hn : 1 ≤ Fintype.card V
    · let Q : HealthyPreparationQuery S A V := ⟨r, hn, cap, hcap, idx, gst, hv,
        hcollision, hh⟩
      have h0 : 0 ≤ Q.heal :=
        add_nonneg (le_max_right gst 0)
          (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le)
      exact healthy_ready_safety S A V Q h0 hb hp
    · have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
      exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩
  · have hnone : ∀ k, ¬ (chainTrace r.2).InCuts heal k :=
      fun k hk => hb (hk.2.trans (htime k hk.1))
    exact ⟨fun _ _ i _ hi => (hnone i hi).elim,
      fun _ i _ hi => (hnone i hi).elim⟩

/-- R5 OC1–OC4: NO PAPER PROOF for composed-node outage continuation.
Blocked by lifetime (4k−1 versus 4k−2) and finite pre-outage network scope:
SyncUntil b₀ does not give unrestricted late-wake SyncRun calls. Do not
insert that false implication as an intermediate lemma. -/
theorem accepted_persists : ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys (family S) V).Holds ((Sys (family S) V).Outage (K S A) T b₀ b₁)
      fun r => (chainTrace r.2).ProtectedThrough
        ((Sys (family S) V).cDur (K S A) r) g (resilienceTarget schema g) T b₀ b₁ := by
  intro g hg T b₀ b₁ r hv ho
  have hg' : g = Out.confirmed := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro v hvr t ht hth w hw hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : OutageQuery S A V := ⟨r, hn, T, b₀, b₁, hv, hcollision, ho⟩
  exact outage_protected S A V Q v hvr t ht hth w hw hr

/-- Exact nine-field assembly; the named gaps above are not a blanket claims assumption. -/
theorem accepted_claims : ShapeClaims (family S) (K S A) := by
  intro V _ _
  exact {
    outputValid := accepted_outputValid S V
    nested := accepted_nested S V
    finalMonotone := accepted_finalMonotone S V
    finalAccountable := accepted_finalAccountable S A V
    healthyLive := accepted_healthyLive S A V
    sleepySafe := accepted_sleepySafe S A V
    sleepyLive := accepted_sleepyLive S A V
    healedSafe := accepted_healedSafe S A V
    persists := accepted_persists S A V }

/-- Selection-aware singleton duties make every recurrence fit. -/
theorem accepted_progressFits : ProgressFits (K S A) (family S) := by
  intro cap i pub s
  rfl

/-- At an outer gap beyond the local span there is room for a bad slot. -/
theorem accepted_progressTolerant : ProgressTolerant schema (K S A) := by
  intro cap _ N
  let P := if cap = .final then finalWindow S else Pattern.single
  exact ⟨⟨P.span + 2, by omega⟩, Nat.le_refl _⟩

/-- Fixed thresholds and positive finite catch-up/budget are admissible. -/
theorem accepted_admissible : (K S A).params.Admissible := by
  rw [acceptanceContract_params_eq]
  exact {
    catchUp_pos := (accepted_coefficients S A).catchUp.pos
    θ_range := by norm_num [Params.standard]
    β_range := by norm_num [Params.standard]
    cover_range := by norm_num [Params.standard]
    α_range := by norm_num [Params.standard]
    budget_pos := by have := A.lookback.pos; have := S.two_le_k; dsimp [Params.standard]; omega }

/-- Concrete existential endpoint. Every gap is a named numeric or adapter
leaf; no simulation, GenesisFresh, or desired safety premise is added. -/
theorem accepted : ∃ C : AcceptanceCoefficients,
    Accepted (family S) (acceptanceContract A C) := by
  refine ⟨accepted_coefficients S A, ?_⟩
  exact {
    claims := accepted_claims S A
    admissible := accepted_admissible S A
    serves := by simp [OutputSchema.Serves, schema]
    progressFits := accepted_progressFits S A
    progressTolerant := accepted_progressTolerant S A }

end Consensus.Goldilocks.Refinement
