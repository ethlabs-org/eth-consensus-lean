module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks runs: one AC tick per honest node and time

In a run, an AC tick call is the first cut of a tick event's handler: no other handler and no
other step of a tick calls `ac_on_tick`. The run has one tick per honest node and time
(`Node.LocalRun.tick_unique`), so two AC tick calls of an honest node at one time are one cut
(`acTick_unique`): the AC trace of the run (`RunTrace.projAC`) has one tick per honest node and
time. An argument about AC traces that needs a lock rule's tick-time writes (the update at
`t_s + 2Δ`) to run once per slot can take this as its premise on runs. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}
variable (proposer : Nat → Fin P.n)

/-- The cut is an AC tick call. -/
private def IsTickCut (c : Cut A) : Prop := ∃ ℓ : ACLabel A, c = .ac ℓ ∧ ℓ.call = .tick

private theorem not_tick_onBlock (y : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    ∀ c ∈ (onBlock y st t B).2, ¬ IsTickCut c := by
  rintro c hc ⟨ℓ, rfl, hℓ⟩
  unfold onBlock at hc
  split_ifs at hc
  · simp at hc
  · split at hc
    · simp at hc
    · simp only [acCall, List.mem_cons, reduceCtorEq, Cut.ac.injEq,
        false_or, List.not_mem_nil, or_false] at hc
      subst hc
      simp at hℓ

private theorem not_tick_attest (y : Fin P.n) (st : NodeState A) (C : A.Blk) :
    ∀ c ∈ (attest y st C).2, ¬ IsTickCut c := by
  rintro c hc ⟨ℓ, rfl, -⟩
  unfold attest at hc
  split at hc <;> simp [onAttestation] at hc

/-- The proposal and FG-update steps of a tick call no `ac_on_tick`. -/
private theorem not_tick_step (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (step : TickStep) (hs : step ≠ .acTick) :
    ∀ c ∈ (tickStep proposer dg y st t x step).2, ¬ IsTickCut c := by
  intro c hc
  cases step with
  | acTick => exact absurd rfl hs
  | proposal =>
    simp only [tickStep] at hc
    split_ifs at hc
    · rcases hp : (acProposal st t).2.2 with _ | ⟨d, p⟩ <;> simp only [hp] at hc
      · rintro ⟨ℓ, rfl, hℓ⟩
        simp only [acProposal, List.mem_singleton, Cut.ac.injEq] at hc
        subst hc
        simp at hℓ
      · rcases List.mem_cons.1 hc with rfl | hc
        · rintro ⟨ℓ, he, hℓ⟩
          simp only [acProposal, Cut.ac.injEq] at he
          subst he
          simp at hℓ
        · exact not_tick_onBlock y _ t _ c hc
    · simp at hc
  | fgUpdate =>
    simp only [tickStep] at hc
    rcases hp : (acToFG st t).2.2 with _ | C <;> simp only [hp] at hc
    · rintro ⟨ℓ, rfl, hℓ⟩
      simp only [acToFG, List.mem_singleton, Cut.ac.injEq] at hc
      subst hc
      simp at hℓ
    · rcases List.mem_cons.1 hc with rfl | hc
      · rintro ⟨ℓ, he, hℓ⟩
        simp only [acToFG, Cut.ac.injEq] at he
        subst he
        simp at hℓ
      · exact not_tick_attest y _ _ c hc

/-- **An AC tick call is the first cut of a tick event.** -/
private theorem exec_tick (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {ℓ : ACLabel A}
    (hk : (exec proposer dg y st t e).2[k]? = some (.ac ℓ)) (hℓ : ℓ.call = .tick) :
    (∃ x, e = .tick x) ∧ k = 0 := by
  have hmem := List.mem_of_getElem? hk
  cases e with
  | tick x =>
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hcuts : (exec proposer dg y st t (.tick x)).2 =
        (tickStep proposer dg y st t x .acTick).2 ++
        ((tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
        (tickStep proposer dg y
          (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
          t x .fgUpdate).2) := by
      simp [exec, onTick, runSteps, tickSteps]
    rw [hcuts] at hk
    rcases k with _ | k
    · rfl
    · exfalso
      have hlen : (tickStep proposer dg y st t x .acTick).2.length = 1 := rfl
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
        show k + 1 - 1 = k by omega] at hk
      have hm := List.mem_of_getElem? hk
      rcases List.mem_append.1 hm with hm | hm
      · exact not_tick_step proposer dg y _ t x .proposal (by simp) _ hm ⟨ℓ, rfl, hℓ⟩
      · exact not_tick_step proposer dg y _ t x .fgUpdate (by simp) _ hm ⟨ℓ, rfl, hℓ⟩
  | block B =>
    exact absurd ⟨ℓ, rfl, hℓ⟩ (not_tick_onBlock y st t B _ (by simpa [exec] using hmem))
  | message m =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hmem
    subst hmem
    simp at hℓ
  | attestation a => simp [exec, onAttestation] at hmem
  | restart =>
    simp only [exec, restart, acCall, List.mem_singleton, Cut.ac.injEq] at hmem
    subst hmem
    simp at hℓ

variable {proposer} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- **One AC tick per honest node and time.** In the AC trace of a run, two AC tick calls of an
honest node at one time are one cut. -/
theorem acTick_unique (h : Node.LocalRun proposer dg H sg tr) :
    ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel A), tr.projAC.CallAt y i ℓ → tr.projAC.CallAt y j ℓ' →
      ℓ.call = .tick → ℓ'.call = .tick → tr.projAC.time i = tr.projAC.time j → i = j := by
  intro y hy i j ℓ ℓ' hc hc' hℓ hℓ' ht
  obtain ⟨g, e, k, hg, rfl, hk⟩ := call_in_group h hy (projAC_callAt.1 hc)
  obtain ⟨g', e', k', hg', rfl, hk'⟩ := call_in_group h hy (projAC_callAt.1 hc')
  obtain ⟨⟨x, rfl⟩, rfl⟩ := exec_tick proposer dg y _ _ e hk hℓ
  obtain ⟨⟨x', rfl⟩, rfl⟩ := exec_tick proposer dg y _ _ e' hk' hℓ'
  change tr.time (g + 0) = tr.time (g' + 0) at ht
  rw [ht] at hg
  rw [h.tick_unique y hy g g' _ ⟨x, hg⟩ ⟨x', hg'⟩]

end Consensus.Goldilocks.Compose

end
