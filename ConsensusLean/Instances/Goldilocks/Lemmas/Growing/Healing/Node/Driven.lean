module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

public section

/-! # Handler suppliers for the shadow driven AC projection -/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem onTick_cuts (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) (fgDue : Bool) :
    (onTick proposer dg y st t x fgDue).2 =
      (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (if fgDue then (tickStep proposer dg y
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1
          t x .proposal).1 t x .fgUpdate).2 else []) := by
  cases fgDue <;> simp [onTick_eq]

private theorem onBlock_call (y : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk)
    {ℓ : ACLabel A} (hm : Cut.ac ℓ ∈ (onBlock y st t B).2) : ℓ.call = .block B := by
  rw [onBlock_eq] at hm
  split_ifs at hm
  · simp at hm
  · split at hm
    · simp at hm
    · simp only [acCall_eq, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
        List.not_mem_nil, or_false] at hm
      subst hm; rfl

private theorem tickStep_call (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat)
    (s : TickStep) {ℓ : ACLabel A}
    (hm : Cut.ac ℓ ∈ (tickStep proposer dg y st t x s).2) :
    ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG ∨ ∃ B, ℓ.call = .block B := by
  cases s <;> simp only [tickStep_eq] at hm
  · simp only [acCall_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm; exact Or.inl rfl
  · split_ifs at hm
    · split at hm
      · simp only [acProposal_eq, List.mem_singleton, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.1 hm with hm | hm
        · simp only [acProposal_eq, Cut.ac.injEq] at hm
          subst hm; exact Or.inr (Or.inl rfl)
        · rw [proposeBlock_eq] at hm
          exact Or.inr (Or.inr (Or.inr ⟨_, onBlock_call _ _ _ _ hm⟩))
    · simp at hm
  · split at hm
    · simp only [acToFG_eq, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm; exact Or.inr (Or.inr (Or.inl rfl))
    · rcases List.mem_cons.1 hm with hm | hm
      · simp only [acToFG_eq, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inr (Or.inl rfl))
      · simp only [attest] at hm
        split at hm <;> simp at hm

/-- Shadow AC tick and proposal calls occur only in ticks; messages only in delivery groups. -/
theorem exec_call_kind (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {ℓ : ACLabel A} (hm : Cut.ac ℓ ∈ (exec proposer dg y st t e).2) :
    (ℓ.call = .tick ∨ ℓ.call = .proposal → ∃ x fgDue, e = .tick x fgDue) ∧
      (∀ m, ℓ.call = .message m → e = .message m) := by
  cases e with
  | tick x fgDue =>
    refine ⟨fun _ => ⟨x, fgDue, rfl⟩, fun m hc => ?_⟩
    exfalso
    rw [exec_eq, onTick_cuts] at hm
    simp only [List.mem_append] at hm
    have noMsg {st : NodeState A} {s : TickStep}
        (hm : Cut.ac ℓ ∈ (tickStep proposer dg y st t x s).2) : False := by
      rcases tickStep_call y st t x s hm with h | h | h | ⟨B, h⟩ <;> rw [h] at hc <;>
        cases hc
    rcases hm with (hm | hm) | hm
    · exact noMsg hm
    · exact noMsg hm
    · split at hm
      · exact noMsg hm
      · simp at hm
  | block B =>
    have hb := onBlock_call y st t B (by simpa only [exec_eq] using hm)
    rw [hb]
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun m h => (by cases h)⟩
  | message m =>
    simp only [exec_eq, onMessage_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h; rfl)⟩
  | attestation a => simp [exec_eq, onAttestation] at hm
  | restart =>
    simp only [exec_eq, restart_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h)⟩

private theorem frame_root_or_accepted {sp : AC.ACParams} {FGP : Type}
    {H : Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
    {tr : AC.GTrace sp FGP} {ini}
    (hr : ACLocalRun (AC.goldilocksAC sp FGP) H U tr ini) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ Φ : AC.Frm sp.n FGP,
        (AC.goldilocksAC sp FGP).CallOK U Φ (tr.time i) ℓ.call ℓ.frame →
        (∀ B ∈ Φ.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B) →
        ∀ B ∈ ℓ.frame.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
      intro Φ hok hv X hX
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm
      cases c with
      | block B =>
        rw [hm.1.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact Or.inr ⟨i, le_rfl, ℓ, hc, hcall⟩
        · exact hv X hX
      | message m => exact hv X (hm.1 ▸ hX)
      | tick => exact hv X (hm ▸ hX)
      | proposal => exact hv X (hm ▸ hX)
      | toFG => exact hv X (hm ▸ hX)
      | restart => exact hv X (hm ▸ hX)
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      exact Or.inl hroot
    · exact step _ hok fun B hB =>
        (ih j hj hc' B hB).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩

section Goldilocks

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

private theorem honest_proposal_of_tick (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg)
    {p : Fin sp.n} (hp : p ∈ H) {j : Nat} {t : Time} {x : Nat} {fgDue : Bool}
    (hg : tr.GroupAt proposer dg p j t (.tick x fgDue))
    (hP : Proposes proposer p t) {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n}
    (hr : (acProposal (tickStep proposer dg p (tr.state p j) t x .acTick).1 t).2.2 =
      some (d, pay)) :
    AC.HonestProposal tr.projAC p (sp.slot t)
      (mkBlock dg p (tr.state p j).fg t x d.head pay) := by
  have h := hrun.toLocalRun
  obtain ⟨hc1, ht1, hst1⟩ := Coherence.tick_proposal_call h hp hg hP
  obtain ⟨hacc, ht2⟩ := own_block_accepted h
    (Compose.requirements_from sp (hrun.vstart p)) hroot hnc hp hg hP hr
  obtain ⟨hacc3, ht3, -⟩ := ac_block_after h hp hacc
  simp only [acProposal_eq] at hc1
  simp only [acProposal_eq, tickStep_eq, acCall_eq] at hacc3
  have hts : t = sp.ts (sp.slot t) := hP.2.1.trans (sp.slotTime_eq _)
  refine ⟨j + 1,
    ⟨.proposal, frame (tickStep proposer dg p (tr.state p j) t x .acTick).1, []⟩,
    d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, rfl, rfl, rfl,
    j + 3, by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = t := ht1
  rw [Compose.projAC_state h hp, hst1, ht1']
  simpa only [acProposal_eq] using hr

end Goldilocks

end Consensus.Goldilocks.Healing
