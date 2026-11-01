module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation

public section

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- A different honest recipient processes a first-release vote envelope before its
processing-cut deadline. Network holdings alone do not cover source self-service. -/
theorem vote_message_service_other {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : SA.Vote (Fintype.card V)}
    (hx : x ∈ honestKeys S rho) (hy : y ∈ honestKeys S rho) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hj : (simTrace S rho hn).IsCall y j)
    (hb : (simTrace S rho hn).projAC.deadline y j τ ≤ b)
    (hd : (simTrace S rho hn).projAC.deadline y j τ ≤ (simTrace S rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).projAC.ProcessAt y k m ∧
      (simTrace S rho hn).time k < (simTrace S rho hn).projAC.deadline y k τ := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hv hy hj hτ
    have heq' : (simTrace S rho hn).projAC.deadline y j τ =
        a + (S.params (Model.pubOf E) hn).Δ := by
      rw [Compose.projAC_deadline]
      exact heq
    have hslack : a + E.Δ < a + (S.params (Model.pubOf E) hn).Δ := by
      change a + E.Δ < a + (E.Δ + 1)
      linarith
    have hbound : a + E.Δ ≤ b := hslack.le.trans (heq' ▸ hb)
    have hheld := hnet.msgs (rho.key x) hx _ τ ⟨source, hs, hrel⟩ (rho.key y) hy
      a ha hbound (hbound.trans hbh)
      (fun u hau hud => hw u hau (hud.trans (hslack.le.trans (heq' ▸ hd))))
    rcases held_voteForward_source_or_process S rho hn hv hx hs hfirst hheld with
      h | ⟨k, hp, hlo, hhi⟩
    · exact False.elim (hne h)
    have htime : (simTrace S rho hn).time k < (simTrace S rho hn).projAC.deadline y j τ := by
      rw [heq']
      exact hhi.trans_lt hslack
    have hkj : k < j := by
      by_contra h
      have := simTrace_time_mono S rho hn hv (Nat.le_of_not_gt h)
      linarith
    by_cases hk : (simTrace S rho hn).time k < (simTrace S rho hn).projAC.deadline y k τ
    · exact ⟨k, hkj.le, hlo, hp, hk⟩
    · have hm : (simTrace S rho hn).projAC.deadline y k τ ≤
          (simTrace S rho hn).projAC.deadline y j τ := by
        rw [Compose.projAC_deadline, Compose.projAC_deadline]
        exact deadline_mono_cut S rho hn hv y τ (S.params (Model.pubOf E) hn).Δ hkj.le
      obtain ⟨l, hl, hlo', hp', hlt⟩ := ih k hkj ⟨_, Compose.projAC_callAt.mp hp.choose_spec.1⟩
        (hm.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj.le, hlo', hp', hlt⟩

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Sleepy network service survives removal of the system's environment tags.
Validity supplies nonnegative send times before converting PSync at zero. -/
theorem sleepy_raw_syncUntil (r : (Sys (family S) V).Run)
    (hv : (Sys (family S) V).Valid r)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) r) (b : Time) :
    r.2.log.SyncUntil r.2.point b := by
  have hp : r.2.log.PSync r.2.point 0 := by
    constructor
    · intro x hx m t hs y hy a hta hcut hhor haw
      have hh := hsleepy.1.msgs x hx ⟨r.1, m⟩ t ⟨m, rfl, hs⟩
        y hy a hta hcut hhor haw
      obtain ⟨u, hu, hsent | hrecv, hnw⟩ := hh
      · obtain ⟨o, he, ho⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl ho, hnw⟩
      · obtain ⟨o, he, ho⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr ho, hnw⟩
    · exact hsleepy.1.txs
  apply hp.syncUntil_zero ?_ b
  rw [CommLog.sendsFromZero_iff]
  intro x hx m t hs
  obtain ⟨i, he | ⟨o, he⟩, -⟩ := hs
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1

/-- Draft: the two non-final liveness routes keep their distinct capability budgets.
The endpoint readiness duration is unchanged; this is not protocol catchUp. -/
structure ConfirmedQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  regime :
    ((Sys (family S) V).Sleepy (K S A) run ∧
      (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap index
        0 run.2.horizon run ∧ 0 ≤ query) ∨
    ((Sys (family S) V).Healthy (K S A) gst run ∧
      (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap index
        ((Sys (family S) V).ready (K S A) gst run) run.2.horizon run ∧
      (Sys (family S) V).heal (K S A) cap index gst run ≤ query)
  bounded : query + ((K S A).params.latency cap index : Time) * run.1.Δ ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (family S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency cap index : Time) * run.1.Δ)

namespace ConfirmedQuery
variable {S A V}
abbrev params (Q : ConfirmedQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : ConfirmedQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev duration (Q : ConfirmedQuery S A V) :=
  (Sys (family S) V).cDur (K S A) Q.run
noncomputable abbrev deadline (Q : ConfirmedQuery S A V) : Time :=
  Q.query + ((K S A).params.latency Q.cap Q.index : Time) * Q.run.1.Δ
end ConfirmedQuery

/-- Actual production at a finite cut, not an eligible schedule slot alone.
Acceptance is explicit: release alone does not imply local acceptance. -/
structure ConfirmedProposal (Q : ConfirmedQuery S A V) where
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Nat
  proposal : Q.trace.ProposesAt block.proposer cut block
  accepted : Q.trace.AcceptAt block.proposer cut block
  ready : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration
    block.proposer (Q.trace.time cut)
  fresh : Q.query < Q.trace.time cut
  bounded : Q.trace.time cut ≤ Q.deadline

/-- Concrete finite service inputs for the Sleepy inclusion consumer. These are
supplier conclusions, never additional assumptions of the Accepted endpoint.
The duration inequality is directional and preserves the endpoint's exact cDur. -/
structure SleepyProposalService (Q : ConfirmedQuery S A V)
    (P : ConfirmedProposal S A V Q) : Prop where
  nonnegative : 0 ≤ Q.trace.time P.cut
  margin : Q.trace.time P.cut + 6 * Q.params.Δ ≤ Q.deadline
  duration : Regimes.catchUp Q.params ≤ Q.duration
  sync : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.deadline
  population : ∀ s : Nat, ∀ d ∈ ({0, Q.params.Δ, 2 * Q.params.Δ} : Set Time),
    Q.params.ts s + d ≤ Q.deadline →
      Q.trace.FaultBound (honestKeys S Q.run.2) (Q.params.ts s + d)

/-- Directional node-readiness bridge. Larger catch-up duration requires an awake
interval containing the smaller one; no equality of engine and protocol scales. -/
theorem confirmed_ready_mono (Q : ConfirmedQuery S A V) {c d : Time}
    (hcd : c ≤ d) {y t}
    (h : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) d y t) :
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t := by
  change _ ∧ (∀ τ, max 0 (t - d - 1) ≤ τ → τ ≤ t → _) at h
  change _ ∧ (∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → _)
  refine ⟨h.1, fun τ hlo hhi => h.2 τ ?_ hhi⟩
  exact (max_le_max_left 0 (sub_le_sub_right (sub_le_sub_left hcd t) 1)).trans hlo

/-- The named joint coefficient bound covers the node duration; no equality of scales. -/
theorem confirmed_duration_supply (Q : ConfirmedQuery S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  have hc : (37 : Time) ≤ (accepted_catchUp S A : Nat) := by
    exact_mod_cast accepted_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  simp only [ConfirmedQuery.duration, System.cDur,
    Params.standard, accepted_coefficients_catchUp]
  change 18 * (Q.run.1.Δ + 1) ≤ (accepted_catchUp S A : Nat) * Q.run.1.Δ
  nlinarith

/-- Restrict the missing full-horizon service producer to the original query
deadline. Both SA service and block relay are restricted; no regime disjunct,
recurrence, or extra processing event is inferred. -/
theorem sleepy_query_sync_of_horizon (Q : ConfirmedQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2)
      Q.params.Δ Q.run.2.horizon) :
    Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.deadline := by
  refine ⟨service.deltaF, ⟨?_, ?_⟩, ?_⟩
  · intro x hx i v hi h0 y hy j ℓ hj hdb hdj
    exact service.ac.message x hx i v hi h0 y hy j ℓ hj (hdb.trans Q.bounded) hdj
  · intro x hx i B hi h0 y hy j ℓ hj hdb hdj hFB
    exact service.ac.relay x hx i B hi h0 y hy j ℓ hj (hdb.trans Q.bounded) hdj hFB
  · intro x hx i B hi h0 y hy j hj hdb hdj hFB
    exact service.relay x hx i B hi h0 y hy j hj (hdb.trans Q.bounded) hdj hFB

/-- OPEN canonical recipient service through the actual query deadline. -/
theorem sleepy_query_sync (Q : ConfirmedQuery S A V)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) Q.run) :
    Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.deadline := by
  sorry

/-- Shortening the readiness duration preserves a strict half-ready population. -/
theorem half_ready_of_duration (p : EnvPoint V) {c d t : Time} (hd : c ≤ d)
    (hh : p.ReadyAbove (1 / 2) d t) : p.ReadyAbove (1 / 2) c t := by
  classical
  have hsub : p.readyAt d t ⊆ p.readyAt c t := by
    intro v hv
    obtain ⟨hhon, hr⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨hhon, hr.1, ?_⟩
    intro u hu hut
    exact hr.2 u ((max_le_max_left 0 (by linarith)).trans hu) hut
  have hc := Finset.card_le_card hsub
  unfold EnvPoint.ReadyAbove at hh ⊢
  have hc' : ((p.readyAt d t).card : ℚ) ≤ (p.readyAt c t).card := by exact_mod_cast hc
  linarith

/-- Population transport at finite slot points, conditional on the joint duration supplier. -/
theorem sleepy_query_population (Q : ConfirmedQuery S A V)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) Q.run) :
    ∀ s : Nat, ∀ d ∈ ({0, Q.params.Δ, 2 * Q.params.Δ} : Set Time),
      Q.params.ts s + d ≤ Q.deadline →
        Q.trace.FaultBound (honestKeys S Q.run.2) (Q.params.ts s + d) := by
  apply sleepy_faultBound S Q.run.2 Q.hn Q.valid Q.bounded
  intro t ht htb
  exact half_ready_of_duration V Q.run.2.point (confirmed_duration_supply S A V Q)
    (hsleepy.2 t ht (htb.trans Q.bounded))

/-- The recurrence/grid supplier selects readiness at exact endpoint cDur directly.
Readiness merely at 18Δp cannot be upgraded to this field by monotonicity. -/
structure ConfirmedProducerSlot (Q : ConfirmedQuery S A V) where
  slot : Nat
  positive : 1 ≤ slot
  fresh : Q.query < Q.params.ts slot
  margin : Q.params.ts slot + 6 * Q.params.Δ ≤ Q.deadline
  ready : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration
    (runProposer S Q.run.2 Q.hn slot) (Q.params.ts slot)

/-- Recurrence/grid selection after an explicit readiness start, at exact cDur.
No healthy or sleepy run premise is needed; the joint latency lower bound remains a dependency. -/
theorem healthy_query_slot (Q : ConfirmedQuery S A V) {ready : Time}
    (hprogress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index ready Q.run.2.horizon Q.run)
    (hquery : max ready 0 ≤ Q.query) : Nonempty (ConfirmedProducerSlot S A V Q) := by
  classical
  have hquery0 : 0 ≤ Q.query := (le_max_right ready 0).trans hquery
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (family S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index⟩ Q.duration ready Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ite_eq_right hcap,
      Model.sysExternal, ConfirmedQuery.duration, System.cDur, System.pt, Sys,
      Model.sysOf, Model.Run.point]
      using hprogress
  have hlat : (8 * (Q.index : Time) + 12) ≤ accepted_latency S A Q.cap Q.index := by
    exact_mod_cast accepted_latency_ge_sleepy S A Q.cap Q.index Q.nonfinal
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hi : (0 : Time) ≤ Q.index := by positivity
  have hbudget : (4 * (Q.index : Time) + 6) * Q.params.Δ ≤
      ((K S A).params.latency Q.cap Q.index : Time) * Q.run.1.Δ := by
    rw [show (K S A).params.latency Q.cap Q.index = accepted_latency S A Q.cap Q.index from
      congrFun (congrFun (accepted_coefficients_latency S A) Q.cap) Q.index]
    change (4 * (Q.index : Time) + 6) * (Q.run.1.Δ + 1) ≤ _
    nlinarith
  have hwin : Q.query + (Q.index : Time) * (4 * Q.params.Δ) ≤ Q.run.2.horizon := by
    have hb := Q.bounded
    have hp := Q.params.toParams.hΔ
    change Q.query + _ ≤ _ at hb
    linarith
  obtain ⟨s, hlo, hhi, hr⟩ := hrec Q.query (by simpa using hquery)
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, family, skeleton] using hwin)
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, family, skeleton,
      Model.Run.point] using hwin)
  have htime : (family S (Model.pubOf Q.run.1)).skel.grid.slotTime s = Q.params.ts s := by
    change (s : Time) * (4 * (Q.run.1.Δ + 1)) = 4 * (Q.run.1.Δ + 1) * s
    ring
  rw [htime] at hlo hhi
  have hmargin : Q.params.ts s + 6 * Q.params.Δ ≤ Q.deadline := by
    change Q.params.ts s ≤ Q.query + (Q.index : Time) * (4 * Q.params.Δ) at hhi
    change _ ≤ Q.query + _
    linarith
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    simp only [runProposer, dite_eq_left hready.1]
    exact Finset.min'_mem _ _
  have hR := hready.2 _ hmem
  rw [htime] at hR
  have hnode := ready_transport S Q.run.2 Q.hn Q.valid (hquery0.trans hlo.le)
    ((le_add_of_nonneg_right (by positivity : 0 ≤ 6 * Q.params.Δ)).trans
      (hmargin.trans Q.bounded)) hR
  rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
    runProposer S Q.run.2 Q.hn s from Q.run.2.key.symm_apply_apply _] at hnode
  refine ⟨⟨s, ?_, hlo, hmargin, hnode⟩⟩
  change 1 ≤ s
  cases s with
  | zero => simp [SA.SAParams.ts] at hlo; linarith
  | succ s => exact Nat.succ_pos s

set_option linter.unusedVariables false in
/-- Recurrence/grid selection at exact cDur, using the joint latency lower bound. -/
theorem sleepy_query_slot (Q : ConfirmedQuery S A V)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) Q.run)
    (hprogress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index 0 Q.run.2.horizon Q.run)
    (hquery : 0 ≤ Q.query) : Nonempty (ConfirmedProducerSlot S A V Q) :=
  healthy_query_slot S A V Q hprogress (by simpa using hquery)

/-- Selected eligible slot to actual canonical proposal event. Acceptance is
not assumed here: the existing own-proposal acceptance theorem supplies it.
The proof must establish joined/eligible state and an actual scheduled engine
event. Slot eligibility is not event existence. W.margin and Q.bounded bound
the slot by the horizon; any ready-to-joined use of confirmed_duration_supply
retains that unresolved joint coefficient dependency. -/
theorem confirmed_slot_event (Q : ConfirmedQuery S A V)
    (W : ConfirmedProducerSlot S A V Q) :
    ∃ (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (k : Nat),
      B.proposer = runProposer S Q.run.2 Q.hn W.slot ∧
      Q.trace.ProposesAt B.proposer k B ∧ Q.trace.time k = Q.params.ts W.slot := by
  obtain ⟨k, B, hp, ht⟩ := Regimes.ready_proposer_proposes
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    W.positive (confirmed_ready_mono S A V Q (confirmed_duration_supply S A V Q) W.ready)
  exact ⟨B, k, hp.2.1, hp.2.1 ▸ hp, ht⟩

/-- Actual production assembled from selected slot, canonical event and proved
own acceptance, preserving the exact-cDur readiness selected by recurrence. -/
theorem sleepy_query_producer (Q : ConfirmedQuery S A V)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) Q.run)
    (hprogress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index 0 Q.run.2.horizon Q.run)
    (hquery : 0 ≤ Q.query) :
    ∃ P : ConfirmedProposal S A V Q,
      Q.trace.time P.cut + 6 * Q.params.Δ ≤ Q.deadline := by
  obtain ⟨W⟩ := sleepy_query_slot S A V Q hsleepy hprogress hquery
  obtain ⟨B, k, hp, he, ht⟩ := confirmed_slot_event S A V Q W
  have hr : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration
      B.proposer (Q.trace.time k) := by rw [hp, ht]; exact W.ready
  have hacc := Compose.proposal_accepted (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) hr.1 he
  have hmargin : Q.trace.time k + 6 * Q.params.Δ ≤ Q.deadline := by
    rw [ht]; exact W.margin
  have hbound : Q.trace.time k ≤ Q.deadline :=
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) Q.params.toParams.hΔ.le)).trans hmargin
  exact ⟨⟨B, k, he, hacc, hr, ht ▸ W.fresh, hbound⟩, hmargin⟩

/-- Assembly of the named production, coefficient and finite-service obligations.
The approved joint signature is unchanged; its body no longer hides those leaves. -/
theorem sleepy_serviced_proposal_supply (Q : ConfirmedQuery S A V)
    (hsleepy : (Sys (family S) V).Sleepy (K S A) Q.run)
    (hprogress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index 0 Q.run.2.horizon Q.run)
    (hquery : 0 ≤ Q.query) :
    ∃ P : ConfirmedProposal S A V Q, SleepyProposalService S A V Q P := by
  obtain ⟨P, hm⟩ := sleepy_query_producer S A V Q hsleepy hprogress hquery
  exact ⟨P, ⟨hquery.trans P.fresh.le, hm, confirmed_duration_supply S A V Q,
    sleepy_query_sync S A V Q hsleepy, sleepy_query_population S A V Q hsleepy⟩⟩

/-- Coverage consumes the selected proposal's service evidence, not boundedness
alone. Its remaining proof dependency is the existing finite inclusion theorem. -/
theorem sleepy_serviced_proposal_coverage (Q : ConfirmedQuery S A V)
    (P : ConfirmedProposal S A V Q) (W : SleepyProposalService S A V Q P) :
    ∀ y j, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
        (Regimes.readAfter Q.trace y j Q.deadline) := by
  intro y j hy hj
  exact sleepy_include_finite S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    (W.nonnegative.trans P.bounded) Q.bounded W.sync W.population
    W.nonnegative P.bounded
    ⟨P.block.proposer, P.cut, confirmed_ready_mono S A V Q W.duration P.ready,
      P.proposal, rfl⟩ W.margin le_rfl
    (confirmed_ready_mono S A V Q W.duration hy) hj

end Consensus.Goldilocks.Refinement
end
