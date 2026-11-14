module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.QuerySlot
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Finite sleepy service and confirmed proposals

`vote_message_service_other` handles another recipient's first-release vote envelope;
`sleepyServiceBefore_of_syncUntil` packages service at bounded labelled cuts. `ConfirmedQuery`
retains the query budget. Source self-service is separate from network holdings. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

/-- A different honest recipient processes a first-release vote envelope before its
processing-cut deadline. Network holdings alone do not cover source self-service. -/
theorem vote_message_service_other {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid) {b : Time} (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ : Time} {m : SA.Vote (Fintype.card V)}
    (hx : x ∈ honestKeys ⟨S, stock⟩ rho) (hy : y ∈ honestKeys ⟨S, stock⟩ rho) (hne : y ≠ x)
    (hτ : 0 ≤ τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hrel : Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∈
      rho.releasesAt source)
    (hfirst : ∀ i < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt i)
    {j : Nat} (hj : (simTrace ⟨S, stock⟩ rho hn).IsCall y j)
    (hb : (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y j τ ≤ b)
    (hd : (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y j τ ≤
        (simTrace ⟨S, stock⟩ rho hn).time j) :
    ∃ k ≤ j, τ ≤ (simTrace ⟨S, stock⟩ rho hn).time k ∧
      (simTrace ⟨S, stock⟩ rho hn).projAC.ProcessAt y k m ∧
      (simTrace ⟨S, stock⟩ rho hn).time k < (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y k τ := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    obtain ⟨a, ha, heq, hw⟩ := deadline_awake_interval S rho hn hconst hv hy hj hτ
    have heq' : (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y j τ =
        a + (S.params (Model.pubOf E) hn).Δ := by
      rw [Compose.projAC_deadline]
      exact heq
    have hslack : a + E.ΔAC - 1 < a + (S.params (Model.pubOf E) hn).Δ := by
      change a + E.ΔAC - 1 < a + E.ΔAC
      linarith
    have hbound : a + E.ΔAC - 1 ≤ b := hslack.le.trans (heq' ▸ hb)
    have hheld := hnet.msgs (rho.key x) _ τ ⟨source, hs, hrel⟩
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff ⟨S, stock⟩ rho x).mp hx))
      (by erw [log_fgAtt_iff]; simp [isFGAtt, IsAttObj]) (rho.key y)
      a ha hbound (hbound.trans hbh)
      ((rho.point.honestAt_iff_zero hconst _ _).mpr ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy))
      (fun u hau hud => hw u hau (hud.trans (hslack.le.trans (heq' ▸ hd))))
    rcases held_voteForward_source_or_process ⟨S, stock⟩ rho hn hconst hv
      ((mem_honestKeys_iff ⟨S, stock⟩ rho x).mp hx) hs hfirst hheld with
      h | ⟨k, hp, hlo, hhi⟩
    · exact False.elim (hne h)
    have htime : (simTrace ⟨S, stock⟩ rho hn).time k < (simTrace ⟨S, stock⟩ rho hn).projAC.deadline
        y j τ := by
      rw [heq']
      exact hhi.trans_lt hslack
    have hkj : k < j := by
      by_contra h
      have := simTrace_time_mono ⟨S, stock⟩ rho hn hv (Nat.le_of_not_gt h)
      linarith
    by_cases hk : (simTrace ⟨S, stock⟩ rho hn).time k <
        (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y k τ
    · exact ⟨k, hkj.le, hlo, hp, hk⟩
    · have hm : (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y k τ ≤
          (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y j τ := by
        rw [Compose.projAC_deadline, Compose.projAC_deadline]
        exact deadline_mono_cut S rho hn hconst hv y τ (S.params (Model.pubOf E) hn).Δ hkj.le
      obtain ⟨l, hl, hlo', hp', hlt⟩ := ih k hkj ⟨_, Compose.projAC_callAt.mp hp.choose_spec.1⟩
        (hm.trans hb) (le_of_not_gt hk)
      exact ⟨l, hl.trans hkj.le, hlo', hp', hlt⟩

/-- Finite canonical service needs only raw synchrony through its deadline bound.
Self-service uses fresh processing at the source time, never retention across a restart. -/
theorem sleepyServiceBefore_of_syncUntil {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.SleepyServiceBefore (simTrace ⟨S, stock⟩ rho hn) (honestKeys ⟨S, stock⟩ rho)
      (S.params (Model.pubOf E) hn).Δ b := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  apply Compose.sleepyServiceBefore_of_message_relay hr.toLocalRun
  · intro x hx i m hsrc h0 y hy j ℓ hj hb hd
    rw [SA.messageServedBefore_iff]
    apply Or.inl
    by_cases hxy : y = x
    · subst y
      have hsource : (simTrace ⟨S, stock⟩ rho hn).SendOrAdmitAt x i m := by
        obtain ⟨l, hl, hm⟩ := hsrc
        refine ⟨l, Compose.projAC_callAt.mp hl, ?_⟩
        rw [Compose.projAC_state hr.toLocalRun hx] at hm
        exact hm
      obtain ⟨k, hp, ht⟩ := sendOrAdmit_process_same_time S rho hn hconst hv hx hsource
      have hlt : ∀ q, (simTrace ⟨S, stock⟩ rho hn).time i <
          (simTrace ⟨S, stock⟩ rho hn).projAC.deadline x q
              ((simTrace ⟨S, stock⟩ rho hn).time i) := by
        intro q
        unfold ACTrace.deadline
        cases (simTrace ⟨S, stock⟩ rho hn).projAC.lastWake x q with
        | bot => exact lt_add_of_pos_right _ (S.params (Model.pubOf E) hn).toParams.hΔ
        | coe w =>
          exact lt_of_le_of_lt (le_max_left _ _)
            (lt_add_of_pos_right _ (S.params (Model.pubOf E) hn).toParams.hΔ)
      refine ⟨k, ?_, ht.ge, hp, ?_⟩
      · by_contra h
        have hm := simTrace_time_mono ⟨S, stock⟩ rho hn hv (Nat.le_of_lt (Nat.lt_of_not_ge h))
        have := hlt j
        linarith
      · change (simTrace ⟨S, stock⟩ rho hn).time k < _
        rw [ht]
        exact hlt k
    · obtain ⟨r, -, -, hs, hrel, hf⟩ := simTrace_vote_forwarded S rho hn hconst hv x hx i m
        (Compose.sendOrAdmit_forward_source hr hx hsrc)
      exact vote_message_service_other S rho hn hconst hv hbh hnet hx hy hxy h0 hs hrel hf
        ⟨_, Compose.projAC_callAt.mp hj⟩ hb hd
  · intro x hx i B hi h0 y hy j hj hb hd hF
    exact acceptance_relay_syncUntil S rho hn hconst hv hnc hbh hnet hx hi h0 hy hj hb hd hF

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Sleepy network service survives removal of the system's environment tags.
Validity supplies nonnegative send times before converting PSync at zero. -/
theorem sleepy_raw_syncUntil (r : (Sys (goldilocks S) V).Run)
    (hv : (Sys (goldilocks S) V).Valid r)
    (hsleepy : (Sys (goldilocks S) V).Sleepy (K S A) r) (b : Time) :
    r.2.log.SyncUntil r.2.point b := by
  have hp : r.2.log.PSync r.2.point 0 := (Model.sysOf_delivers_iff _ _ _ _).mp hsleepy.1
  apply hp.syncUntil_zero ?_ b
  rw [CommLog.sendsFromZero_iff]
  intro x m t hs hx
  obtain ⟨i, he | ⟨o, he⟩, -⟩ := hs
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1
  · exact (hv.in_horizon _ (List.mem_of_getElem? he)).1

/-- Draft: the two non-final liveness routes keep their distinct capability budgets.
The endpoint readiness duration is unchanged; this is not protocol catchUp. -/
structure ConfirmedQuery where
  run : (Sys (goldilocks S) V).Run
  constant : run.2.point.ConstantFaults
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  regime :
    ((Sys (goldilocks S) V).Sleepy (K S A) run ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        0 run.2.horizon run ∧ 0 ≤ query) ∨
    ((Sys (goldilocks S) V).Healthy (K S A) gst run ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ query)
  bounded : query + ((K S A).params.latency cap index : Time) * run.1.ΔAC ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency cap index : Time) * run.1.ΔAC)

namespace ConfirmedQuery
variable {S A V}
abbrev params (Q : ConfirmedQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : ConfirmedQuery S A V) := simTrace ⟨S, stock⟩ Q.run.2 Q.hn
noncomputable abbrev duration (Q : ConfirmedQuery S A V) :=
  (Sys (goldilocks S) V).cDur (K S A) Q.run
noncomputable abbrev deadline (Q : ConfirmedQuery S A V) : Time :=
  Q.query + ((K S A).params.latency Q.cap Q.index : Time) * Q.run.1.ΔAC
end ConfirmedQuery

omit [DecidableEq V] in
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

/-- The recurrence/grid supplier selects readiness at exact endpoint cDur directly.
Readiness merely at 18Δp cannot be upgraded to this field by monotonicity. -/
structure ConfirmedProducerSlot (Q : ConfirmedQuery S A V) where
  slot : Nat
  positive : 1 ≤ slot
  fresh : Q.query < Q.params.ts slot
  margin : Q.params.ts slot + 6 * Q.params.Δ ≤ Q.deadline
  ready : Regimes.ReadyAt Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.duration
    (runProposer ⟨S, stock⟩ Q.run.2 Q.hn slot) (Q.params.ts slot)

/-- Recurrence/grid selection after an explicit readiness start, at exact cDur.
No healthy or sleepy run premise is needed; the joint latency lower bound remains a dependency. -/
theorem healthy_query_slot (Q : ConfirmedQuery S A V) {ready : Time}
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ready Q.run.2.horizon Q.run)
    (hquery : max ready 0 ≤ Q.query) : Nonempty (ConfirmedProducerSlot S A V Q) := by
  obtain ⟨s, hs1, hlo, hmargin, hts0, htsh, hR, -⟩ := nonfinal_query_slot S A V Q.run Q.hn
    Q.nonfinal Q.index Q.bounded hprogress hquery
  have hnode := ready_transport S Q.run.2 Q.hn Q.valid hts0 htsh hR
  rw [show Q.run.2.ownKey (Q.run.2.key (runProposer ⟨S, stock⟩ Q.run.2 Q.hn s)) =
    runProposer ⟨S, stock⟩ Q.run.2 Q.hn s from Q.run.2.key.symm_apply_apply _] at hnode
  exact ⟨⟨s, hs1, hlo, hmargin, hnode⟩⟩

end Consensus.Goldilocks.Obligations
end
