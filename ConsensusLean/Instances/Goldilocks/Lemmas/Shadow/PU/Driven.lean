module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

public section

/-! # Handler suppliers for the shadow driven AC projection -/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- An AC block call on the shadow projection has an immediately preceding FG acceptance. -/
theorem fg_accept_before' (h : LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {B : A.Blk}
    (ha : tr.projAC.AcceptAt y i B) :
    ∃ k, i = k + 1 ∧ tr.AcceptAt y k B ∧ tr.time k = tr.time i := by
  obtain ⟨ℓ, hc, hb⟩ := ha
  obtain ⟨j, e, k, hg, rfl, hk⟩ :=
    Coherence.call_in_group' h hy (Compose.projAC_callAt.1 hc)
  obtain ⟨k', rfl, hk'⟩ := Coherence.exec_acBlock_prev' proposer dg y _ _ e hk hb
  obtain ⟨hc', ht⟩ := Compose.group_cut' hg hk'
  exact ⟨j + k', by omega, hc', ht⟩

/-- A shadow tick has the same three cut segments as a stock tick. -/
theorem onTick_cuts' (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) (fgDue : Bool) :
    (onTick' proposer dg y st t x fgDue).2 =
      (tickStep' proposer dg y st t x .acTick).2 ++
      (tickStep' proposer dg y (tickStep' proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (if fgDue then (tickStep' proposer dg y
        (tickStep' proposer dg y (tickStep' proposer dg y st t x .acTick).1
          t x .proposal).1 t x .fgUpdate).2 else []) := by
  cases fgDue <;> simp [onTick'_eq, runSteps'_eq, tickSteps]

/-- Every public shadow tick starts with its AC tick cut. -/
theorem tick_first_cut' {y : Fin P.n} {j : Nat} {t : Time} {x : Nat} {fgDue : Bool}
    (hg : tr.GroupAt' proposer dg y j t (.tick x fgDue)) :
    tr.CallAt y j (acCall' y (tr.state y j) t .tick).2 ∧ tr.time j = t := by
  have hk : (exec' proposer dg y (tr.state y j) t (.tick x fgDue)).2[0]? =
      some (acCall' y (tr.state y j) t .tick).2 := by
    rw [exec'_eq, onTick_cuts']
    simp [tickStep'_eq, acCall'_eq]
  simpa only [Nat.add_zero] using Compose.group_cut' hg hk

private theorem onBlock_call' (y : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk)
    {ℓ : ACLabel A} (hm : Cut.ac ℓ ∈ (onBlock' y st t B).2) : ℓ.call = .block B := by
  rw [onBlock'_eq] at hm
  split_ifs at hm
  · simp at hm
  · split at hm
    · simp at hm
    · simp only [acCall'_eq, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
        List.not_mem_nil, or_false] at hm
      subst hm; rfl

private theorem tickStep_call' (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat)
    (s : TickStep) {ℓ : ACLabel A}
    (hm : Cut.ac ℓ ∈ (tickStep' proposer dg y st t x s).2) :
    ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG ∨ ∃ B, ℓ.call = .block B := by
  cases s <;> simp only [tickStep'_eq] at hm
  · simp only [acCall'_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm; exact Or.inl rfl
  · split_ifs at hm
    · split at hm
      · simp only [acProposal'_eq, List.mem_singleton, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.1 hm with hm | hm
        · simp only [acProposal'_eq, Cut.ac.injEq] at hm
          subst hm; exact Or.inr (Or.inl rfl)
        · rw [proposeBlock'_eq] at hm
          exact Or.inr (Or.inr (Or.inr ⟨_, onBlock_call' _ _ _ _ hm⟩))
    · simp at hm
  · split at hm
    · simp only [acToFG'_eq, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm; exact Or.inr (Or.inr (Or.inl rfl))
    · rcases List.mem_cons.1 hm with hm | hm
      · simp only [acToFG'_eq, Cut.ac.injEq] at hm
        subst hm; exact Or.inr (Or.inr (Or.inl rfl))
      · simp only [attest] at hm
        split at hm <;> simp at hm

/-- Shadow AC tick and proposal calls occur only in ticks; messages only in delivery groups. -/
theorem exec_call_kind' (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {ℓ : ACLabel A} (hm : Cut.ac ℓ ∈ (exec' proposer dg y st t e).2) :
    (ℓ.call = .tick ∨ ℓ.call = .proposal → ∃ x fgDue, e = .tick x fgDue) ∧
      (∀ m, ℓ.call = .message m → e = .message m) := by
  cases e with
  | tick x fgDue =>
    refine ⟨fun _ => ⟨x, fgDue, rfl⟩, fun m hc => ?_⟩
    exfalso
    rw [exec'_eq, onTick_cuts'] at hm
    simp only [List.mem_append] at hm
    have noMsg {st : NodeState A} {s : TickStep}
        (hm : Cut.ac ℓ ∈ (tickStep' proposer dg y st t x s).2) : False := by
      rcases tickStep_call' y st t x s hm with h | h | h | ⟨B, h⟩ <;> rw [h] at hc <;>
        cases hc
    rcases hm with (hm | hm) | hm
    · exact noMsg hm
    · exact noMsg hm
    · split at hm
      · exact noMsg hm
      · simp at hm
  | block B =>
    have hb := onBlock_call' y st t B (by simpa only [exec'_eq] using hm)
    rw [hb]
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun m h => (by cases h)⟩
  | message m =>
    simp only [exec'_eq, onMessage'_eq, acCall'_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h; rfl)⟩
  | attestation a => simp [exec'_eq, onAttestation] at hm
  | restart =>
    simp only [exec'_eq, restart'_eq, acCall'_eq, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h)⟩

/-- A shadow tick's proposal is at position one; blocks occur strictly later. -/
theorem onTick_ac_index' (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat)
    (fgDue : Bool) {k : Nat} {ℓ : ACLabel A}
    (hk : (onTick' proposer dg y st t x fgDue).2[k]? = some (Cut.ac ℓ)) :
    (ℓ.call = .proposal → k = 1) ∧ (k ≤ 1 → ∀ B, ℓ.call ≠ .block B) := by
  have h2 : ∀ st' : NodeState A, (tickStep' proposer dg y st' t x .proposal).2 = [] ∨
      ∃ ℓp Lb, ℓp.call = .proposal ∧
        (tickStep' proposer dg y st' t x .proposal).2 = Cut.ac ℓp :: Lb ∧
        ∀ ℓ', Cut.ac ℓ' ∈ Lb → ∃ B, ℓ'.call = .block B := by
    intro st'
    simp only [tickStep'_eq]
    split_ifs
    · split
      · refine Or.inr ⟨⟨.proposal, frame' st', []⟩, [], rfl, ?_, by simp⟩
        rw [acProposal'_eq]
      · rename_i d pay hret
        refine Or.inr ⟨⟨.proposal, frame' st', []⟩,
          (proposeBlock' dg y (acProposal' st' t).1 t x d.head pay).2,
          rfl, ?_, fun ℓ' hm => ?_⟩
        · rw [acProposal'_eq]
        · rw [proposeBlock'_eq] at hm
          exact ⟨_, onBlock_call' _ _ _ _ hm⟩
    · exact Or.inl rfl
  have h3 : ∀ st' : NodeState A, ∃ ℓt La, ℓt.call = .toFG ∧
      (tickStep' proposer dg y st' t x .fgUpdate).2 = Cut.ac ℓt :: La ∧
        ∀ ℓ', Cut.ac ℓ' ∉ La := by
    intro st'
    simp only [tickStep'_eq]
    split
    · refine ⟨⟨.toFG, frame' st', []⟩, [], rfl, ?_, by simp⟩
      rw [acToFG'_eq]
    · rename_i C hret
      refine ⟨⟨.toFG, frame' st', []⟩, (attest y (acToFG' st' t).1 C).2,
        rfl, ?_, fun ℓ' hm => ?_⟩
      · rw [acToFG'_eq]
      · simp only [attest] at hm
        split at hm <;> simp at hm
  have h0 : (tickStep' proposer dg y st t x .acTick).2 = [(acCall' y st t .tick).2] := by
    simp only [tickStep'_eq]
  cases fgDue
  case false =>
    rw [onTick_cuts', h0] at hk
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hk
    rcases h2 (tickStep' proposer dg y st t x .acTick).1 with h2e | ⟨ℓp, Lb, hℓp, h2e, hLb⟩
    · rw [h2e] at hk
      cases k with
      | zero =>
        simp only [List.append_nil, List.getElem?_cons_zero, Option.some.injEq,
          acCall'_eq, Cut.ac.injEq] at hk
        subst hk
        exact ⟨fun h => (by cases h), fun _ B h => (by cases h)⟩
      | succ k => simp at hk
    · rw [h2e] at hk
      rcases k with _ | _ | k
      · simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
          Option.some.injEq, acCall'_eq, Cut.ac.injEq] at hk
        subst hk
        exact ⟨fun h => (by cases h), fun _ B h => (by cases h)⟩
      · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
        subst hk
        exact ⟨fun _ => rfl, fun _ B h => by rw [hℓp] at h; cases h⟩
      · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hk
        obtain ⟨B, hB⟩ := hLb ℓ (List.mem_of_getElem? hk)
        exact ⟨fun h => (by rw [hB] at h; cases h), fun h => (by omega)⟩
  rw [onTick_cuts', h0] at hk
  simp only [↓reduceIte] at hk
  obtain ⟨ℓt, La, hℓt, h3e, hLa⟩ :=
    h3 (tickStep' proposer dg y (tickStep' proposer dg y st t x .acTick).1 t x .proposal).1
  rw [h3e] at hk
  rcases h2 (tickStep' proposer dg y st t x .acTick).1 with h2e | ⟨ℓp, Lb, hℓp, h2e, hLb⟩
  · rw [h2e] at hk
    rcases k with _ | _ | k
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq, acCall'_eq, Cut.ac.injEq] at hk
      subst hk
      exact ⟨fun h => (by cases h), fun _ B h => (by cases h)⟩
    · simp only [List.cons_append, List.nil_append, List.append_nil, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
      subst hk
      exact ⟨by simp [hℓt], by simp [hℓt]⟩
    · simp only [List.cons_append, List.nil_append, List.append_nil,
        List.getElem?_cons_succ] at hk
      exact absurd (List.mem_of_getElem? hk) (hLa ℓ)
  · rw [h2e] at hk
    rcases k with _ | _ | k
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq, acCall'_eq, Cut.ac.injEq] at hk
      subst hk
      exact ⟨fun h => (by cases h), fun _ B h => (by cases h)⟩
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
      subst hk
      exact ⟨fun _ => rfl, fun _ B h => by rw [hℓp] at h; cases h⟩
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hk
      have hm := List.mem_of_getElem? hk
      simp only [List.mem_append, List.mem_cons] at hm
      refine ⟨fun hc => ?_, fun h => by omega⟩
      rcases hm with hm | hm | hm
      · obtain ⟨B, hB⟩ := hLb ℓ hm
        rw [hB] at hc; cases hc
      · simp only [Cut.ac.injEq] at hm
        subst hm; rw [hℓt] at hc; cases hc
      · exact absurd hm (hLa ℓ)

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
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

private theorem honest_proposal_of_tick' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg)
    {p : Fin sp.n} (hp : p ∈ H) {j : Nat} {t : Time} {x : Nat} {fgDue : Bool}
    (hg : tr.GroupAt' proposer dg p j t (.tick x fgDue))
    (hP : Proposes proposer p t) {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n}
    (hr : (acProposal' (tickStep' proposer dg p (tr.state p j) t x .acTick).1 t).2.2 =
      some (d, pay)) :
    AC.HonestProposal tr.projAC p (sp.slot t)
      (mkBlock dg p (tr.state p j).fg t x d.head pay) := by
  have h := hrun.toLocalRun'
  obtain ⟨hc1, ht1, hst1⟩ := Coherence.tick_proposal_call' h hp hg hP
  obtain ⟨hacc, ht2⟩ := own_block_accepted' h
    (Compose.requirements_from sp (hrun.vstart p)) hroot hnc hp hg hP hr
  obtain ⟨hacc3, ht3, -⟩ := ac_block_after' h hp hacc
  simp only [acProposal'_eq] at hc1
  simp only [acProposal'_eq, tickStep'_eq, acCall'_eq] at hacc3
  have hts : t = sp.ts (sp.slot t) := hP.2.1.trans (sp.slotTime_eq _)
  refine ⟨j + 1,
    ⟨.proposal, frame' (tickStep' proposer dg p (tr.state p j) t x .acTick).1, []⟩,
    d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, rfl, rfl, rfl,
    j + 3, by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = t := ht1
  rw [Compose.projAC_state' h hp, hst1, ht1']
  simpa only [acProposal'_eq] using hr

/-- The shadow run supplies the stock driven-execution contract on its AC projection. -/
theorem projection_driven_of_run' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg) :
    AC.Driven proposer tr.projAC H := by
  have h := hrun.toLocalRun'
  have hac := Compose.goldilocks_ac_projection_from' hrun hnc
  have hr := hac.localRun
  have blocks : ∀ y ∈ H, ∀ i B, tr.projAC.AcceptAt y i B → B.root ≠ sp.genesisRoot →
      B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.projAC.time i) ∧
        ∃ Pb : AC.Blk sp.n (List (FG.Att sp.n)), B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
          (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.projAC.AcceptAt y k Pb) := by
    intro y hy i B ha hB
    obtain ⟨ℓ, hc, hcall⟩ := ha
    obtain ⟨Φ, hok, hΦU, hprev⟩ : ∃ Φ, (goldilocksNode sp).CallOK (tr.HonestBlocks H) Φ
        (tr.projAC.time i) ℓ.call ℓ.frame ∧ Φ.tree ⊆ tr.HonestBlocks H ∧
        ∀ X ∈ Φ.tree, X.root = sp.genesisRoot ∨ ∃ k < i, tr.projAC.AcceptAt y k X := by
      rcases hr.frameLaw y hy i ℓ hc with
        ⟨-, Φ₀, ⟨htree, hroot₀, -⟩, hin, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
      · refine ⟨Φ₀, hok, hin.2, fun X hX => ?_⟩
        rw [htree, Set.mem_singleton_iff] at hX
        subst hX
        exact Or.inl hroot₀
      · have hin : (goldilocksNode sp).FrameIn (tr.HonestBlocks H) ℓ'.frame := by
          rcases hr.frameLaw y hy j ℓ' hc' with ⟨_, _, _, _, hok'⟩ | ⟨_, _, _, _, _, hok'⟩ <;>
            exact hok'.1
        exact ⟨ℓ'.frame, hok, hin.2, fun X hX => (frame_root_or_accepted hr hy hc' X hX).imp_right
          fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩⟩
    obtain ⟨⟨-, hΦ'U⟩, hm⟩ := hok
    rw [hcall] at hm
    obtain ⟨hs, -, hslot⟩ := hm
    have hBt : B ∈ ℓ.frame.tree := by rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
    obtain ⟨Pb, hPb, hpar⟩ := hs.parent_mem
    exact ⟨hac.honest.proposer B ⟨y, hy, i, ℓ, hc, hBt⟩ hB, hslot, Pb, hpar,
      hr.coherent.2 Pb (hΦU hPb) B (hΦ'U hBt) hpar, hprev Pb hPb⟩
  refine ⟨blocks, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy i B ha hB hpH
    have hprop := (blocks y hy i B ha hB).1
    obtain ⟨k, rfl, hk, -⟩ := fg_accept_before' h hy ha
    obtain ⟨j', -, ⟨acc, ho⟩, hpos⟩ := h.block_unforgeable y hy k B ⟨true, hk⟩ (hprop ▸ hpH)
    generalize hpB : B.proposer = p at ho hpos
    have hp : p ∈ H := hpB ▸ hprop ▸ hpH
    rcases Coherence.blockCall_cases' h hp ho with hd |
      ⟨j, x, fgDue, rfl, hg, hP, d, pay, hr', rfl, -⟩
    · rw [RunTrace.groupAt'_iff] at hd
      exact absurd (by simpa using (hd.2.1 0 (List.length_pos_iff.2 hd.1)).2.2.2.1) hpos
    have hps : proposer (sp.slot (tr.time (j + 2))) = p := hP.2.2
    change AC.HonestProposal tr.projAC (proposer (sp.slot (tr.time (j + 2))))
      (sp.slot (tr.time (j + 2))) _
    rw [hps]
    exact honest_proposal_of_tick' hrun hnc hroot hp hg hP hr'
  · intro y hy t ht hpub haw
    obtain ⟨j, hj⟩ := h.tick_of_awake y hy t ht hpub haw
    obtain ⟨x, fgDue, hg⟩ := (RunTrace.tickAt'_iff _ _ _ _ _ _).mp hj
    obtain ⟨hc, htj⟩ := tick_first_cut' hg
    simp only [acCall'_eq] at hc
    exact ⟨j, ⟨.tick, frame' (tr.state y j), _⟩, Compose.projAC_callAt.2 hc, rfl, htj⟩
  · intro s hs p hp hps haw _
    have hΔ := sp.toParams.hΔ
    have hts0 : 0 ≤ sp.ts s := by unfold ACParams.ts; positivity
    have hpub : sp.toParams.IsPublic (sp.ts s) := ⟨4 * (s : Int), by unfold ACParams.ts; ring⟩
    obtain ⟨j, hj⟩ := h.tick_of_awake p hp _ hts0 hpub haw
    obtain ⟨x, fgDue, hg⟩ := (RunTrace.tickAt'_iff _ _ _ _ _ _).mp hj
    have hslot : sp.toParams.slotOf (sp.ts s) = s :=
      AC.slot_of_mem sp s le_rfl ((AC.ts_lt_iff sp).2 (by omega))
    have hP : Proposes proposer p (sp.ts s) :=
      ⟨by rw [hslot]; exact hs, by rw [hslot, sp.slotTime_eq]; rfl, by rw [hslot, hps]⟩
    obtain ⟨hc1, ht1, hst1⟩ := Coherence.tick_proposal_call' h hp hg hP
    simp only [acProposal'_eq] at hc1
    refine ⟨j + 1, ⟨.proposal, frame' (tickStep' proposer dg p (tr.state p j) (sp.ts s)
      x .acTick).1, []⟩, Compose.projAC_callAt.2 hc1, rfl, ht1, ?_⟩
    rintro ⟨pay, -, -, d, hd⟩
    have ht1' : tr.projAC.time (j + 1) = sp.ts s := ht1
    rw [Compose.projAC_state' h hp, hst1, ht1'] at hd
    have hd' : (acProposal' (tickStep' proposer dg p (tr.state p j) (sp.ts s)
        x .acTick).1 (sp.ts s)).2.2 = some (d, pay) := by
      simpa only [acProposal'_eq] using hd
    have hp' := honest_proposal_of_tick' hrun hnc hroot hp hg hP hd'
    rw [show sp.slot (sp.ts s) = s from hslot] at hp'
    exact ⟨_, hp'⟩
  · rintro y hy i j ℓ ℓ' hci hcj htick htime ⟨m, hm⟩
    obtain ⟨ji, ei, qi, hgi, rfl, hqi⟩ :=
      Coherence.call_in_group' h hy (Compose.projAC_callAt.1 hci)
    obtain ⟨jj, ej, qj, hgj, rfl, hqj⟩ :=
      Coherence.call_in_group' h hy (Compose.projAC_callAt.1 hcj)
    have hei := (exec_call_kind' _ _ _ _ (List.mem_of_getElem? hqi)).2 m hm
    obtain ⟨x, fgDue, hej⟩ :=
      (exec_call_kind' _ _ _ _ (List.mem_of_getElem? hqj)).1 (Or.inl htick)
    subst hei hej
    have htime' : tr.time (ji + qi) = tr.time (jj + qj) := htime
    rw [htime'] at hgi
    have hlt : jj < ji := by
      rcases lt_trichotomy jj ji with h1 | rfl | h1
      · exact h1
      · exfalso
        rw [RunTrace.groupAt'_iff] at hgi hgj
        have h1 := (hgj.2.1 0 (List.length_pos_iff.2 hgj.1)).2.2.2.2
        have h2 := (hgi.2.1 0 (List.length_pos_iff.2 hgi.1)).2.2.2.2
        rw [h1] at h2
        simp [exec'_eq, onMessage'_eq, acCall'_eq, onTick_cuts', tickStep'_eq] at h2
      · exact absurd (h.phase_order y hy y hy ji jj _ _ _ hgi hgj h1 (.inl rfl))
          (by simp [Event.phase])
    by_contra hle
    have hqjlen := (List.getElem?_eq_some_iff.1 hqj).1
    rw [RunTrace.groupAt'_iff] at hgi hgj
    have hev := (hgj.2.1 (ji - jj) (by omega)).2.2.1
    rw [Nat.add_sub_cancel' hlt.le] at hev
    have := (hgi.2.2 jj hev.symm).1
    omega
  · rintro y hy i j ℓ ℓ' hci hcj hprop htime hobj
    obtain ⟨ji, ei, qi, hgi, rfl, hqi⟩ :=
      Coherence.call_in_group' h hy (Compose.projAC_callAt.1 hci)
    obtain ⟨jj, ej, qj, hgj, rfl, hqj⟩ :=
      Coherence.call_in_group' h hy (Compose.projAC_callAt.1 hcj)
    obtain ⟨x, fgDue, rfl⟩ :=
      (exec_call_kind' _ _ _ _ (List.mem_of_getElem? hqj)).1 (Or.inr hprop)
    have hqj1 : qj = 1 := (onTick_ac_index' _ _ _ _ _
      (by simpa only [exec'_eq] using hqj)).1 hprop
    have htime' : tr.time (ji + qi) = tr.time (jj + qj) := htime
    rw [htime'] at hgi hqi
    have later : ei.phase = 2 → jj + qj < ji + qi := by
      intro hph
      have hlt : jj < ji := by
        rcases lt_trichotomy jj ji with h1 | rfl | h1
        · exact h1
        · exfalso
          obtain ⟨hc, -⟩ := tick_first_cut' hgj
          simp only [acCall'_eq] at hc
          rw [RunTrace.groupAt'_iff] at hgi
          have hl := (hgi.2.1 0 (List.length_pos_iff.2 hgi.1)).2.2.2.2
          simp only [Nat.add_zero] at hl
          have he := Option.some.inj (hl.symm.trans hc.2)
          have hmem := List.mem_of_getElem? (List.getElem?_eq_some_iff.mpr
            ⟨List.length_pos_iff.2 hgi.1, he⟩)
          cases ei with
          | block B =>
            have hb := onBlock_call' y (tr.state y jj) _ B
              (by simpa only [exec'_eq] using hmem)
            cases hb
          | message m => simp [exec'_eq, onMessage'_eq, acCall'_eq] at hmem
          | tick x f => simp [Event.phase] at hph
          | restart => simp [Event.phase] at hph
          | attestation a => simp [exec'_eq, onAttestation] at hmem
        · have := h.phase_order y hy y hy ji jj _ _ _ hgi hgj h1 (.inl rfl)
          rw [hph] at this
          simp [Event.phase] at this
      by_contra hle
      have hqjlen := (List.getElem?_eq_some_iff.1 hqj).1
      rw [RunTrace.groupAt'_iff] at hgi hgj
      have hev := (hgj.2.1 (ji - jj) (by omega)).2.2.1
      rw [Nat.add_sub_cancel' hlt.le] at hev
      have := (hgi.2.2 jj hev.symm).1
      omega
    cases ei with
    | tick x' fgDue' =>
      have hji : ji = jj := h.tick_unique y hy ji jj _
        ((RunTrace.tickAt'_iff _ _ _ _ _ _).mpr ⟨x', fgDue', hgi⟩)
        ((RunTrace.tickAt'_iff _ _ _ _ _ _).mpr ⟨x, fgDue, hgj⟩)
      subst hji
      have hidx := (onTick_ac_index' _ _ _ _ _
        (by simpa only [exec'_eq] using hqi)).2
      rcases hobj with ⟨m, hm⟩ | ⟨B, hB⟩
      · exact absurd ((exec_call_kind' _ _ _ _ (List.mem_of_getElem? hqi)).2 m hm) (by simp)
      · have : ¬ qi ≤ 1 := fun hle => hidx hle B hB
        omega
    | block B => exact later rfl
    | message m => exact later rfl
    | attestation a =>
      have := List.mem_of_getElem? hqi
      simp [exec'_eq, onAttestation] at this
    | restart =>
      exfalso
      have hm := List.mem_of_getElem? hqi
      simp only [exec'_eq, restart'_eq, acCall'_eq, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm
      rcases hobj with ⟨m, hm⟩ | ⟨B, hB⟩
      · cases hm
      · cases hB

end Goldilocks

end Consensus.Goldilocks.Healing
