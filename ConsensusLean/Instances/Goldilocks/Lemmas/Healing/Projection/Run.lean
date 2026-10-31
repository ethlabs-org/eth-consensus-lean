module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Goldilocks Healing: run facts for the AC projection (H.2 (run))

The facts of a run (`Node.LocalRun`) that H.2 (run) reads on the AC projection `projAC`, beyond
those of `Compose/Run/{Groups,Handlers,Trees,Projection}`:

* `Σ.F` of an honest node moves only to descendants (`run_F_mono`);
* an FG acceptance is followed at the next cut by the `ac_on_block` of the block, which is not a
  restart, and every `ac_on_block` follows its FG acceptance, read on `projAC`
  (`ac_block_after`, `fg_accept_before`; C0.5 (b), `Compose.accept_next`,
  `Compose.acBlock_prev`);
* an `ac_on_tick` cut is a tick's and an `ac_on_message` cut a delivery's (`exec_ac_call`), an
  `ac_proposal` cut is a tick's, its second cut, and the tick's first two cuts are not
  `ac_on_block` cuts (`exec_ac_proposal`, `onTick_ac_index`);
* a tick's first cut is its `ac_on_tick`, and for a proposer its second is `ac_proposal`, from
  the AC state the tick left (`tick_first_cut`, `tick_proposal_call`);
* C0.3 in a run: the own block of a proposal is accepted at once (`own_block_accepted`, from
  `Compose.group_step` and `Compose.honest_block_accepted`). -/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- The cut at index `k` of a group's handler cuts is the run's cut `j + k`. -/
private theorem group_get? {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt dg y j t e) {k : Nat} {c : Cut A}
    (hk : (exec dg y (tr.state y j) t e).2[k]? = some c) :
    tr.CallAt y (j + k) c ∧ tr.time (j + k) = t ∧ tr.pos (j + k) = k := by
  obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨hn, ht, -, hp, hl⟩ := hg.2.1 k hk'
  exact ⟨⟨hn, hl.trans (congrArg some hc)⟩, ht, hp⟩

/-- The latest wake does not change at a cut that is not a restart. -/
theorem lastWake_succ {y : Fin P.n} {k : Nat} (hn : ¬ tr.RestartAt y (k + 1)) :
    tr.lastWake y (k + 1) = tr.lastWake y k := by
  simp [RunTrace.lastWake, hn]

/-- `Σ.F` of an honest node moves only to descendants, inside the honest blocks. -/
theorem run_F_mono (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i i' : Nat}
    (hii : i ≤ i') : Anc (tr.HonestBlocks H) (tr.state y i).fg.F (tr.state y i').fg.F := by
  induction i', hii using Nat.le_induction with
  | base => exact .refl
  | succ i' _ ih =>
    refine ih.trans ?_
    by_cases hc : ∃ c, tr.CallAt y i' c
    · obtain ⟨c, hc⟩ := hc
      have hF := (Compose.chain_fg y (.cons (h.cutLaw y hy i' c hc) (.nil _))
        (Compose.fg_reachable h hy i')).2.2
      rw [← tr.state_succ_of_call hc] at hF
      exact Anc.mono (fun X hX => ⟨y, hy, i' + 1, hX⟩) hF
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- **An FG acceptance is followed by its `ac_on_block`** at the next cut, at the same time;
that cut is not a restart. -/
theorem ac_block_after (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {k : Nat}
    {B : A.Blk} (ha : tr.AcceptAt y k B) :
    tr.projAC.AcceptAt y (k + 1) B ∧ tr.time (k + 1) = tr.time k ∧
      ¬ tr.RestartAt y (k + 1) := by
  obtain ⟨ℓ, hcall, hc, ht⟩ := Compose.accept_next h hy ha
  refine ⟨⟨ℓ, Compose.projAC_callAt.2 hcall, hc⟩, ht, ?_⟩
  rintro ⟨ℓ', hc', hr⟩
  have := hc'.2.symm.trans hcall.2
  simp only [Option.some.injEq, Cut.ac.injEq] at this
  rw [this, hc] at hr
  cases hr

/-- **An `ac_on_block` follows its FG acceptance** at the previous cut, at the same time. -/
theorem fg_accept_before (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : A.Blk} (ha : tr.projAC.AcceptAt y i B) :
    ∃ k, i = k + 1 ∧ tr.AcceptAt y k B ∧ tr.time k = tr.time i := by
  obtain ⟨ℓ, hc, hcall⟩ := ha
  exact Compose.acBlock_prev h hy (Compose.projAC_callAt.1 hc) hcall

/-! ### The cuts of ticks and deliveries -/

/-- The cuts of a tick: the AC's tick, the proposal step's cuts, the FG update's cuts. -/
theorem onTick_eq (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    (onTick dg y st t x).2 = (tickStep dg y st t x .acTick).2 ++
      (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).2 ++
      (tickStep dg y (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).1 t x
        .fgUpdate).2 := by
  simp [onTick, runSteps, tickSteps]

/-- In the cuts of an event, an `ac_on_tick` cut is a tick's and an `ac_on_message(m)` cut is the
delivery of `m`'s. -/
theorem exec_ac_call (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) {ℓ : ACLabel A}
    (hm : Cut.ac ℓ ∈ (exec dg y st t e).2) :
    (ℓ.call = .tick → ∃ x, e = .tick x) ∧ ∀ m, ℓ.call = .message m → e = .message m := by
  cases e with
  | tick x =>
    refine ⟨fun _ => ⟨x, rfl⟩, fun m hc => ?_⟩
    exfalso
    change Cut.ac ℓ ∈ (onTick dg y st t x).2 at hm
    rw [onTick_eq] at hm
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · simp only [Node.tickStep, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm; cases hc
    · simp only [Node.tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp only [Node.acProposal, List.mem_singleton, Cut.ac.injEq] at hm; subst hm; cases hc
        · rcases List.mem_cons.1 hm with hm | hm
          · simp only [Node.acProposal, Cut.ac.injEq] at hm; subst hm; cases hc
          · simp only [Node.proposeBlock, Node.onBlock] at hm
            split_ifs at hm
            · simp at hm
            · split at hm
              · simp at hm
              · simp only [Node.acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
                  List.not_mem_nil, or_false] at hm
                subst hm; cases hc
      · simp at hm
    · simp only [Node.tickStep] at hm
      split at hm
      · simp only [Node.acToFG, List.mem_singleton, Cut.ac.injEq] at hm; subst hm; cases hc
      · rcases List.mem_cons.1 hm with hm | hm
        · simp only [Node.acToFG, Cut.ac.injEq] at hm; subst hm; cases hc
        · simp only [Node.attest] at hm
          split at hm <;> simp [Node.onAttestation] at hm
  | block B =>
    have : ℓ.call = .block B := by
      simp only [exec, Node.onBlock] at hm
      split_ifs at hm
      · simp at hm
      · split at hm
        · simp at hm
        · simp only [Node.acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
            List.not_mem_nil, or_false] at hm
          subst hm; rfl
    rw [this]; exact ⟨fun h => (by cases h), fun m h => (by cases h)⟩
  | message m' =>
    simp only [exec, Node.onMessage, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by cases h), fun m h => (by cases h; rfl)⟩
  | attestation a => simp [exec, Node.onAttestation] at hm
  | restart =>
    simp only [exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    exact ⟨fun h => (by cases h), fun m h => (by cases h)⟩

/-- In the cuts of an event, an `ac_proposal` cut is a tick's. -/
theorem exec_ac_proposal (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {ℓ : ACLabel A} (hm : Cut.ac ℓ ∈ (exec dg y st t e).2) (hc : ℓ.call = .proposal) :
    ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | block B =>
    exfalso
    simp only [exec, Node.onBlock] at hm
    split_ifs at hm
    · simp at hm
    · split at hm
      · simp at hm
      · simp only [Node.acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
          List.not_mem_nil, or_false] at hm
        subst hm; cases hc
  | message m =>
    exfalso
    simp only [exec, Node.onMessage, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm; cases hc
  | attestation a => simp [exec, Node.onAttestation] at hm
  | restart =>
    exfalso
    simp only [exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm; cases hc

/-- The AC cuts of a tick by position: its `ac_proposal` cut is its second cut, and its first
two cuts are not `ac_on_block` cuts. -/
theorem onTick_ac_index (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) {k : Nat}
    {ℓ : ACLabel A} (hk : (onTick dg y st t x).2[k]? = some (Cut.ac ℓ)) :
    (ℓ.call = .proposal → k = 1) ∧ (k ≤ 1 → ∀ B, ℓ.call ≠ .block B) := by
  -- the proposal step: no cuts, or the `ac_proposal` cut and then `ac_on_block` or FG cuts
  have h2 : ∀ st' : NodeState A, (tickStep dg y st' t x .proposal).2 = [] ∨
      ∃ ℓp Lb, ℓp.call = .proposal ∧ (tickStep dg y st' t x .proposal).2 = Cut.ac ℓp :: Lb ∧
        ∀ ℓ', Cut.ac ℓ' ∈ Lb → ∃ B, ℓ'.call = .block B := by
    intro st'
    simp only [Node.tickStep]
    split_ifs
    · split
      · exact Or.inr ⟨_, [], rfl, rfl, by simp⟩
      · refine Or.inr ⟨_, _, rfl, rfl, fun ℓ' hm => ?_⟩
        simp only [Node.proposeBlock, Node.onBlock] at hm
        split_ifs at hm
        · simp at hm
        · split at hm
          · simp at hm
          · simp only [Node.acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
              List.not_mem_nil, or_false] at hm
            subst hm; exact ⟨_, rfl⟩
    · exact Or.inl rfl
  -- the FG update: the `ac_to_fg` cut, then FG cuts only
  have h3 : ∀ st' : NodeState A, ∃ ℓt La, ℓt.call = .toFG ∧
      (tickStep dg y st' t x .fgUpdate).2 = Cut.ac ℓt :: La ∧ ∀ ℓ', Cut.ac ℓ' ∉ La := by
    intro st'
    simp only [Node.tickStep]
    split
    · exact ⟨_, [], rfl, rfl, by simp⟩
    · refine ⟨_, _, rfl, rfl, fun ℓ' hm => ?_⟩
      simp only [Node.attest] at hm
      split at hm <;> simp [Node.onAttestation] at hm
  have h0 : (tickStep dg y st t x .acTick).2 = [(acCall y st t .tick).2] := rfl
  rw [onTick_eq, h0] at hk
  obtain ⟨ℓt, La, hℓt, h3e, hLa⟩ := h3 (tickStep dg y (tickStep dg y st t x .acTick).1 t x
    .proposal).1
  rw [h3e] at hk
  rcases h2 (tickStep dg y st t x .acTick).1 with h2e | ⟨ℓp, Lb, hℓp, h2e, hLb⟩
  · rw [h2e] at hk
    rcases k with _ | _ | k
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq, Node.acCall, Cut.ac.injEq] at hk
      subst hk
      exact ⟨fun h => (by cases h), fun _ B h => (by cases h)⟩
    · simp only [List.cons_append, List.nil_append, List.append_nil, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
      subst hk
      exact ⟨fun _ => rfl, fun _ B h => by rw [hℓt] at h; cases h⟩
    · simp only [List.cons_append, List.nil_append, List.append_nil,
        List.getElem?_cons_succ] at hk
      exact absurd (List.mem_of_getElem? hk) (hLa ℓ)
  · rw [h2e] at hk
    rcases k with _ | _ | k
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq, Node.acCall, Cut.ac.injEq] at hk
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

/-- The first cut of a tick is its `ac_on_tick`. -/
theorem tick_first_cut {y : Fin P.n} {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt dg y j t (.tick x)) :
    tr.CallAt y j (acCall y (tr.state y j) t .tick).2 ∧ tr.time j = t := by
  have : (exec dg y (tr.state y j) t (.tick x)).2[0]? =
      some (acCall y (tr.state y j) t .tick).2 := by
    change (onTick dg y (tr.state y j) t x).2[0]? = _
    rw [onTick_eq]; simp [Node.tickStep]
  obtain ⟨hc, ht, -⟩ := group_get? hg this
  exact ⟨hc, ht⟩

/-- The proposal step's cuts, when `ac_proposal` returns a proposal: its cut, then the own
block's `on_block`. -/
theorem proposal_cuts_some {y : Fin P.n} {st : NodeState A} {t : Time} {x : Nat}
    (hP : Proposes y t)
    {d : DutyHead P.n (List (FG.Att P.n)) A.Payload} {pay : A.Payload}
    (hr : (Node.acProposal st t).2.2 = some (d, pay)) :
    (tickStep dg y st t x .proposal).2 = (Node.acProposal st t).2.1 ::
      (onBlock y (Node.acProposal st t).1 t
        (mkBlock dg y (Node.acProposal st t).1.fg t x d.head pay)).2 := by
  simp only [Node.tickStep, hP, ↓reduceIte, hr, Node.proposeBlock]

/-- The cut after a tick's `ac_on_tick`, for a proposer: `ac_proposal`, from the AC state the
tick left. -/
theorem tick_proposal_call (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {t : Time} {x : Nat} (hg : tr.GroupAt dg y j t (.tick x)) (hP : Proposes y t) :
    tr.CallAt y (j + 1)
        (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).2.1 ∧
      tr.time (j + 1) = t ∧
      (tr.state y (j + 1)).ac = (tickStep dg y (tr.state y j) t x .acTick).1.ac := by
  have h1 : (exec dg y (tr.state y j) t (.tick x)).2[1]? =
      some (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).2.1 := by
    change (onTick dg y (tr.state y j) t x).2[1]? = _
    rw [onTick_eq]
    simp only [Node.tickStep, hP, ↓reduceIte]
    split <;> simp [Node.acProposal]
  obtain ⟨hc, ht, -⟩ := group_get? hg h1
  obtain ⟨hc0, ht0⟩ := tick_first_cut hg
  refine ⟨hc, ht, ?_⟩
  rw [tr.state_succ_of_call hc0]
  have hl := h.cutLaw y hy j _ hc0
  rw [ht0] at hl
  obtain ⟨-, hstep, -, -⟩ := hl
  exact (congrArg Prod.fst hstep).symm

/-- **C0.3 in a run: the own block of a proposal is accepted** at once, at the cut after the
`ac_proposal` cut. -/
theorem own_block_accepted (h : Node.LocalRun dg H sg tr) (hq : A.Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt dg y j t (.tick x)) (hP : Proposes y t)
    {d : DutyHead P.n (List (FG.Att P.n)) A.Payload} {pay : A.Payload}
    (hr : (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).2.2 =
      some (d, pay)) :
    tr.AcceptAt y (j + 2) (mkBlock dg y
      (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x d.head pay) ∧
      tr.time (j + 2) = t := by
  have hcs : ∀ l, (onBlock y
      (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1 t
      (mkBlock dg y (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x
        d.head pay)).2[0]? = some l →
      (exec dg y (tr.state y j) t (.tick x)).2[2]? = some l := by
    intro l hl
    change (onTick dg y (tr.state y j) t x).2[2]? = _
    have h0 : (tickStep dg y (tr.state y j) t x .acTick).2 =
        [(acCall y (tr.state y j) t .tick).2] := rfl
    rw [onTick_eq, proposal_cuts_some hP hr, h0]
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hl).1]
    exact hl
  have hs : ¬ P.slotOf t < (mkBlock dg y
      (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x d.head
        pay).slot :=
    lt_irrefl _
  have hoc : tr.Occurs (mkBlock dg y
      (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x d.head pay) := by
    cases hb : (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg.onBlock
      (mkBlock dg y (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x
        d.head pay) with
    | none =>
      exact ⟨y, j + 2, false, (group_get? hg (hcs _ (by simp [Node.onBlock, hs, hb]))).1⟩
    | some fg' =>
      exact ⟨y, j + 2, true, (group_get? hg (hcs _ (by simp [Node.onBlock, hs, hb]))).1⟩
  obtain ⟨⟨st, τ, ph⟩, hR, hst, hS⟩ := Compose.group_step h hy hg
  simp only at hst
  subst hst
  obtain ⟨-, -, -, -, -, -, hacc⟩ :=
    Compose.honest_block_accepted dg y hq hroot _ _ t x hR hS hP d pay hr
  have hsub : insert (mkBlock dg y
      (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x d.head pay)
      (tr.state y j).fg.tree ⊆ insert (P.genesisBlock A.genesisPayload) {B | tr.Occurs B} :=
    Set.insert_subset (Set.mem_insert_of_mem _ hoc) (Compose.tree_subset_run h hy j)
  obtain ⟨-, fg', hb⟩ := hacc (Compose.NoCollOn.mono hnc hsub)
  have h2 := hcs (.fg (.block (mkBlock dg y
    (Node.acProposal (tickStep dg y (tr.state y j) t x .acTick).1 t).1.fg t x d.head pay) true))
    (by simp [Node.onBlock, hs, hb])
  obtain ⟨hc, ht, -⟩ := group_get? hg h2
  exact ⟨hc, ht⟩

end Consensus.Goldilocks.Healing

end
