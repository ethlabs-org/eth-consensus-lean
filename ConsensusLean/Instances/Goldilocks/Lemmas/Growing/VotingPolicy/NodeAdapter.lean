module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.VotingPolicy.StockTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components

public section

/-! # Voting-policy spike: the node adapter

A node run of the calendar AC (`calendarAC`, the Goldilocks AC whose `ac_to_fg` runs only at the
signing appointments) under growing faults has, as its AC projection with the stutters
unlabelled (`stockTrace`), a run of the Goldilocks AC under the same contract
(`calendar_acProjection`). So every lemma over `Growing.ACLocalRun (goldilocksAC …)` applies to a
calendar node run.

* `reachable_stock`: a state the calendar AC reaches, the Goldilocks AC reaches up to the report
  marker, by the same calls without the `ac_to_fg` calls, by a last call no later;
  so requirement 5 (`ReqPayloadFrom`) carries over (`reqPayloadFrom_calendar`).
* `stutter_after_tick`: in a node run, an `ac_to_fg` call is a cut of a tick group, after the
  tick's own `ac_on_tick` call at the same time; this is the premise of `acLocalRun_stockTrace`. -/

namespace Consensus.Goldilocks.VotingPolicy

open AC

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP} {sign : Time → Bool}

private theorem eq_rep {A B : ACState sp.n}
    (h : { A with fgReported := 0 } = { B with fgReported := 0 }) :
    B = { A with fgReported := B.fgReported } := by
  cases A; cases B; cases h; rfl

/-- **Calendar reachability is Goldilocks reachability up to the report marker**, by a last call
no later. -/
theorem reachable_stock {s₀ : (calendarAC ro sign).State} {self : Fin sp.n}
    {U : Set (calendarAC ro sign).Blk} {s : (calendarAC ro sign).State}
    {Φ : (calendarAC ro sign).Frm} {t : Time}
    (h : (calendarAC ro sign).ReachableAtFrom s₀ self U s Φ t) :
    ∃ s' t', (goldilocksAC sp FGP ro).ReachableAtFrom s₀ self U s' Φ t' ∧ t' ≤ t ∧
      { s with fgReported := 0 } = { s' with fgReported := 0 } := by
  induction h with
  | init Φ hi hin =>
    exact ⟨s₀, 0, ACInterface.ReachableAtFrom.init (A := goldilocksAC sp FGP ro) Φ hi hin, le_rfl,
      rfl⟩
  | @step s Φ Φ' t t' c _ htt hok ih =>
    obtain ⟨s', t'', hr, ht, he⟩ := ih
    have hok' := (calendarAC_callOK_iff ro sign c).1 hok
    by_cases hc : c = .toFG
    · subst hc
      have hΦ : Φ' = Φ := hok.2
      subst hΦ
      refine ⟨s', t'', hr, ht.trans htt, ?_⟩
      have hstep : ((calendarAC ro sign).step self s Φ' t' .toFG).1 =
          { s with fgReported := ((calendarAC ro sign).step self s Φ' t' .toFG).1.fgReported } := by
        cases hsg : sign t'
        · rw [calendarAC_step_toFG_of_not_sign ro hsg]
        · rw [calendarAC_step_toFG_of_sign ro hsg]
          exact acToFG_rep s Φ' t'
      rw [hstep]
      exact he
    · have hstep := calendarAC_step ro sign self s Φ' t' c hc
      obtain ⟨r, hr'⟩ : ∃ r, s' = { s with fgReported := r } := ⟨_, eq_rep he⟩
      subst hr'
      have hgr := ACInterface.ReachableAtFrom.step (stockCall c) hr (ht.trans htt) hok'
      refine ⟨_, t', hgr, le_rfl, ?_⟩
      rw [hstep]
      by_cases hrs : c = .restart
      · subst hrs
        rw [stockCall_restart]
        exact congrArg (fun A : ACState sp.n => { A with fgReported := 0 })
          (congrArg Prod.fst (acRestart_rep ro self s r Φ' t')).symm
      · rw [step_rep ro self s r Φ' t' (stockCall c)
          (by rwa [ne_eq, stockCall_eq_toFG_iff]) (by rwa [ne_eq, stockCall_eq_restart_iff])]

/-- **Requirement 5 carries over to the calendar AC**: a proposal of a calendar-reachable state is
the proposal of a Goldilocks-reachable state. -/
theorem reqPayloadFrom_calendar {s₀ : ACState sp.n} {self : Fin sp.n}
    (h : (goldilocksAC sp FGP ro).ReqPayloadFrom s₀ self) :
    (calendarAC ro sign).ReqPayloadFrom s₀ self := by
  intro U hU s Φ t₀ hr σ hσ d p hp B hB hBp
  obtain ⟨s', t', hr', ht, he⟩ := reachable_stock hr
  obtain ⟨r, rfl⟩ : ∃ r, s' = { s with fgReported := r } := ⟨_, eq_rep he⟩
  refine h U hU _ Φ t' hr' σ (ht.trans hσ) d p ?_ B hB hBp
  change (acProposal sp { s with fgReported := r } Φ _).2 = _
  rw [acProposal_rep]
  exact hp

section Groups

variable {P : Params} {A : NodeAC P}

/-- An `ac_to_fg` cut of an event's handler belongs to a tick: it is the FG update's. -/
theorem exec_toFG_tick (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (self : Fin P.n) (st : NodeState A) (t : Time) (e : Node.Event A) {ℓ : ACLabel A}
    (hℓ : Cut.ac ℓ ∈ (Node.exec proposer dg self st t e).2) (hc : ℓ.call = .toFG) :
    ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | block B =>
    simp only [Node.exec, Node.onBlock] at hℓ
    split_ifs at hℓ
    · simp at hℓ
    · split at hℓ
      · simp at hℓ
      · simp only [Node.acCall, List.mem_cons, List.not_mem_nil, or_false] at hℓ
        rcases hℓ with h | h <;> cases h
        cases hc
  | message m =>
    simp only [Node.exec, Node.onMessage, Node.acCall, List.mem_singleton] at hℓ
    cases hℓ; cases hc
  | attestation a => simp [Node.exec, Node.onAttestation] at hℓ
  | restart =>
    simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton] at hℓ
    cases hℓ; cases hc

/-- The first cut of a tick is its `ac_on_tick` call. -/
theorem exec_tick_head (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (self : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    ∃ ℓ : ACLabel A, (Node.exec proposer dg self st t (.tick x)).2[0]? = some (.ac ℓ) ∧
      ℓ.call = .tick := by
  refine ⟨⟨.tick, Node.frame st, (A.step self st.ac (Node.frame st) t .tick).2⟩, ?_, rfl⟩
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep, Node.acCall]

end Groups

section Run

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {sg : Vote sp.n → Fin sp.n}
  {ro' : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : RunTrace (calendarAC ro' sign)} {ini : Fin sp.n → ACState sp.n}

/-- **In a calendar node run, each stutter follows its tick's `ac_on_tick` call**, at the same
time. -/
theorem stutter_after_tick (h : Growing.LocalRun proposer dg H sg tr ini) :
    ∀ y k ℓ, y ∈ H (tr.projAC.time k) → tr.projAC.CallAt y k ℓ →
      isStutter sign (tr.projAC.time k) ℓ.call = true →
      ∃ j < k, ∃ ℓ', tr.projAC.CallAt y j ℓ' ∧ isStutter sign (tr.projAC.time j) ℓ'.call = false ∧
        tr.projAC.time j = tr.projAC.time k := by
  intro y k ℓ hy hc hs
  have hcall : ℓ.call = .toFG := ((isStutter_eq_true_iff _ _).1 hs).1
  have hc' := Compose.projAC_callAt.1 hc
  obtain ⟨j, e, hg, hjk, hkj⟩ := h.grouped y k _ hc' hy
  have hk := (hg.2.1 (k - j) (by omega))
  rw [Nat.add_sub_cancel' hjk, hc'.2] at hk
  have hmem : Cut.ac ℓ ∈ (Node.exec proposer dg y (tr.state y j) (tr.time k) e).2 := by
    rw [Option.some.inj hk.2.2.2.2]; exact List.getElem_mem _
  obtain ⟨x, hx⟩ := exec_toFG_tick (A := calendarAC ro' sign) proposer dg y _ _ e hmem hcall
  rw [hx] at hg
  obtain ⟨ℓ₀, h₀, h₀c⟩ := exec_tick_head proposer dg y (tr.state y j) (tr.time k) x
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j) (tr.time k) (.tick x)).2.length := by
    rcases List.getElem?_eq_some_iff.1 h₀ with ⟨hl, -⟩; exact hl
  have hj := hg.2.1 0 hlen
  simp only [Nat.add_zero] at hj
  have hl0 : tr.label j = some (.ac ℓ₀) := by
    rw [hj.2.2.2.2, ← List.getElem?_eq_getElem hlen, h₀]
  have hjk' : j ≠ k := by
    rintro rfl
    rw [hc'.2] at hl0
    cases Option.some.inj hl0
    rw [hcall] at h₀c; cases h₀c
  refine ⟨j, by omega, ℓ₀, Compose.projAC_callAt.2 ⟨hj.1, hl0⟩, ?_, hj.2.1⟩
  rw [h₀c]; exact isStutter_tick _

/-- **The node adapter.** The AC projection of a calendar node run under growing faults, with
the stutters unlabelled, is a run of the Goldilocks AC under the same contract, over the same
honest blocks and from the same starts; requirement 5 at the starts is the Goldilocks AC's. -/
theorem calendar_acProjection
    (hpay : ∀ y ∈ H 0, (goldilocksAC sp (List (FG.Att sp.n)) ro').ReqPayloadFrom (ini y) y)
    (h : Growing.LocalRun proposer dg H sg tr ini) (hnc : Compose.NoCollRun dg tr) :
    Growing.ACLocalRun (goldilocksAC sp (List (FG.Att sp.n)) ro') H (tr.HonestBlocksAt H)
      (stockTrace tr.projAC) ini :=
  acLocalRun_stockTrace
    (Compose.Growing.ac_projection _ _ dg H sg tr proposer
      (fun y hy => reqPayloadFrom_calendar (hpay y hy)) h hnc)
    (stutter_after_tick h)

end Run

end Consensus.Goldilocks.VotingPolicy
