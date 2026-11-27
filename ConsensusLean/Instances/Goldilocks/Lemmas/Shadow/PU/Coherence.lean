module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Shadow P-U: honest trees and node suppliers

Stock tree and cut proofs, using the cache transport for the shadow finality update.
No interface stub in Node is used by these proofs.
-/

namespace Consensus.Goldilocks.Coherence

open Node

section Handlers

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)

private def Paired (cs : List (Cut A)) : Prop :=
  (∀ k B, cs[k]? = some (.fg (.block B true)) →
      ∃ ℓ : ACLabel A, cs[k + 1]? = some (.ac ℓ) ∧ ℓ.call = .block B) ∧
    ∀ k (ℓ : ACLabel A) B, cs[k]? = some (.ac ℓ) → ℓ.call = .block B →
      ∃ k', k = k' + 1 ∧ cs[k']? = some (.fg (.block B true))

private theorem Paired.append {l₁ l₂ : List (Cut A)} (h₁ : Paired l₁) (h₂ : Paired l₂) :
    Paired (l₁ ++ l₂) := by
  refine ⟨fun k B hk => ?_, fun k ℓ B hk hb => ?_⟩
  · by_cases hlt : k < l₁.length
    · rw [List.getElem?_append_left hlt] at hk
      obtain ⟨ℓ, h, hb⟩ := h₁.1 k B hk
      have : k + 1 < l₁.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at h
        cases h
      exact ⟨ℓ, by rwa [List.getElem?_append_left this], hb⟩
    · rw [List.getElem?_append_right (by omega)] at hk
      obtain ⟨ℓ, h, hb⟩ := h₂.1 _ B hk
      refine ⟨ℓ, ?_, hb⟩
      rwa [List.getElem?_append_right (by omega),
        show k + 1 - l₁.length = k - l₁.length + 1 by omega]
  · by_cases hlt : k < l₁.length
    · rw [List.getElem?_append_left hlt] at hk
      obtain ⟨k', rfl, h⟩ := h₁.2 k ℓ B hk hb
      exact ⟨k', rfl, by rwa [List.getElem?_append_left (by omega)]⟩
    · rw [List.getElem?_append_right (by omega)] at hk
      obtain ⟨k', hk', h⟩ := h₂.2 _ ℓ B hk hb
      refine ⟨l₁.length + k', by omega, ?_⟩
      rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem paired_nil : Paired ([] : List (Cut A)) := ⟨by simp, by simp⟩

private theorem paired_single {c : Cut A} (h₁ : ∀ B, c ≠ .fg (.block B true))
    (h₂ : ∀ (ℓ : ACLabel A) B, c = .ac ℓ → ℓ.call ≠ .block B) : Paired [c] := by
  refine ⟨fun k B hk => ?_, fun k ℓ B hk hb => ?_⟩
  · rcases k with _ | k
    · exact absurd (Option.some.inj hk) (h₁ B)
    · simp at hk
  · rcases k with _ | k
    · exact absurd hb (h₂ ℓ B (Option.some.inj hk))
    · simp at hk

private theorem paired_ac {c : A.Call} {Φ : A.Frm} {es : List A.Em} (hc : ∀ B, c ≠ .block B) :
    Paired [Cut.ac ⟨c, Φ, es⟩] :=
  paired_single (fun _ h => by cases h) fun _ B h => by cases h; exact hc B

private theorem paired_fg {ℓ : FGLabel P A.Payload} (hℓ : ∀ B, ℓ ≠ .block B true) :
    Paired [Cut.fg (A := A) ℓ] :=
  paired_single (fun B h => hℓ B (Cut.fg.inj h)) fun _ _ h => by cases h

private theorem paired_onBlock (y : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    Paired (onBlock y st t B).2 := by
  rw [Node.onBlock_eq]
  split_ifs
  · exact paired_nil
  split
  · exact paired_fg fun _ h => by cases h
  · refine ⟨fun k B' hk => ?_, fun k ℓ B' hk hb => ?_⟩
    · rcases k with _ | _ | k <;>
        simp only [acCall_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil, Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq,
          and_true, reduceCtorEq] at hk
      subst hk
      exact ⟨⟨.block B, frame _, (A.step y _ (frame _) t (.block B)).2⟩,
        by rw [acCall_eq]; rfl, rfl⟩
    · rcases k with _ | _ | k <;>
        simp only [acCall_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil, Option.some.injEq, Cut.ac.injEq, reduceCtorEq] at hk
      subst hk
      cases hb
      exact ⟨0, rfl, rfl⟩

private theorem tick_cuts (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) :
    (exec proposer dg y st t (.tick x true)).2 = (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (tickStep proposer dg y
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 := by
  simp [exec_eq, onTick_eq, runSteps_eq, tickSteps]

private theorem tick_cuts_false (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) :
    (exec proposer dg y st t (.tick x false)).2 = (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 := by
  simp [exec_eq, onTick_eq, runSteps_eq, tickSteps]

private theorem paired_tickStep (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (s : TickStep) :
    Paired (tickStep proposer dg y st t x s).2 := by
  cases s with
  | acTick =>
    rw [tickStep_eq, acCall_eq]
    exact paired_ac fun _ h => by cases h
  | proposal =>
    simp only [tickStep_eq]
    split_ifs
    · split
      · simpa only [acProposal_eq] using
          (paired_ac (c := .proposal) fun _ h => by cases h)
      · rw [proposeBlock_eq]
        simpa only [acProposal_eq, List.singleton_append] using
          (paired_ac (c := .proposal) fun _ h => by cases h).append (paired_onBlock y _ t _)
    · exact paired_nil
  | fgUpdate =>
    simp only [tickStep_eq]
    split
    · simpa only [acToFG_eq] using (paired_ac (c := .toFG) fun _ h => by cases h)
    · simp only [acToFG_eq]
      refine (paired_ac (c := .toFG) fun _ h => by cases h).append ?_
      simp only [attest]
      split
      · exact paired_fg fun _ h => by cases h
      · exact paired_fg fun _ h => by cases h

private theorem paired_exec (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) : Paired (exec proposer dg y st t e).2 := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · rw [tick_cuts_false]
      exact (paired_tickStep proposer dg y st t x _).append (paired_tickStep proposer dg y _ t x _)
    · rw [tick_cuts]
      exact ((paired_tickStep proposer dg y st t x _).append
        (paired_tickStep proposer dg y _ t x _)).append (paired_tickStep proposer dg y _ t x _)
  | block B => simpa only [exec_eq] using paired_onBlock y st t B
  | message m =>
    simpa only [exec_eq, onMessage_eq, acCall_eq] using
      (paired_ac (c := .message m) fun _ h => by cases h)
  | attestation a =>
    simpa only [exec_eq, onAttestation] using
      (paired_fg (ℓ := .attestation a) fun _ h => by cases h)
  | restart =>
    simpa only [exec_eq, restart_eq, acCall_eq] using
      (paired_ac (c := .restart) fun _ h => by cases h)

/-- Every AC block call is preceded by the matching successful FG block cut. -/
theorem exec_acBlock_prev (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {ℓ : ACLabel A} {B : A.Blk}
    (hk : (exec proposer dg y st t e).2[k]? = some (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ k', k = k' + 1 ∧ (exec proposer dg y st t e).2[k']? = some (.fg (.block B true)) :=
  (paired_exec proposer dg y st t e).2 k ℓ B hk hb

/-- Every successful FG block cut is followed by its matching AC block call. -/
theorem exec_accept_next (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {B : A.Blk}
    (hk : (exec proposer dg y st t e).2[k]? = some (.fg (.block B true))) :
    ∃ ℓ : ACLabel A, (exec proposer dg y st t e).2[k + 1]? = some (.ac ℓ) ∧
      ℓ.call = .block B :=
  (paired_exec proposer dg y st t e).1 k B hk

private theorem onBlock_block {y : Fin P.n} {st : NodeState A} {t : Time} {B' B : A.Blk}
    {acc : Bool} {k : Nat} (hk : (onBlock y st t B').2[k]? = some (.fg (.block B acc))) :
    k = 0 ∧ B' = B := by
  rw [Node.onBlock_eq] at hk
  split_ifs at hk
  · simp at hk
  split at hk <;> rcases k with _ | _ | k <;>
    simp only [acCall_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq,
      reduceCtorEq] at hk
  all_goals exact ⟨rfl, hk.1⟩

private theorem update_no_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (B : A.Blk) (acc : Bool) :
    Cut.fg (.block B acc) ∉ (tickStep proposer dg y st t x .fgUpdate).2 := by
  simp only [tickStep_eq]
  split
  · simp [acToFG_eq]
  · simp only [attest, List.mem_cons, acToFG_eq, reduceCtorEq, false_or]
    split <;> simp

private theorem proposal_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {B : A.Blk} {acc : Bool} {m : Nat}
    (hm : (tickStep proposer dg y st t x .proposal).2[m]? = some (.fg (.block B acc))) :
    m = 1 ∧ Proposes proposer y t ∧ ∃ d p, (acProposal st t).2.2 = some (d, p) ∧
      B = mkBlock dg y st.fg t x d.head p ∧
      (acc = true ↔ ∃ fg', st.fg.onBlock B = some fg') := by
  simp only [tickStep_eq] at hm
  split_ifs at hm with hp
  · split at hm
    · rcases m with _ | m <;>
        simp only [acProposal_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil, Option.some.injEq, reduceCtorEq] at hm
    rename_i d p hdp
    rcases m with _ | m
    · simp only [acProposal_eq, List.getElem?_cons_zero, Option.some.injEq, reduceCtorEq] at hm
    simp only [List.getElem?_cons_succ] at hm
    rw [proposeBlock_eq] at hm
    obtain ⟨rfl, rfl⟩ := onBlock_block (B' := mkBlock dg y _ t x d.head p) hm
    refine ⟨rfl, hp, d, p, hdp, by rw [acProposal_eq], ?_⟩
    simp only [Node.onBlock_eq] at hm
    split_ifs at hm
    · simp at hm
    split at hm <;> simp at hm <;> rename_i h <;> subst hm
    · simp [acProposal_eq] at h ⊢
      rw [h]
      simp
    · simp only [acProposal_eq] at h ⊢
      simp [h]
  · simp at hm

private theorem exec_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {B : A.Blk} {acc : Bool} {k : Nat}
    (hk : (exec proposer dg y st t e).2[k]? = some (.fg (.block B acc))) :
    (e = .block B ∧ k = 0) ∨
      (∃ x fgDue, e = .tick x fgDue ∧ k = 2 ∧ Proposes proposer y t ∧ ∃ d p,
      (acProposal (tickStep proposer dg y st t x .acTick).1 t).2.2 = some (d, p) ∧
      B = mkBlock dg y st.fg t x d.head p ∧
      (acc = true ↔ ∃ fg', st.fg.onBlock B = some fg') ∧
      (∃ ℓ : ACLabel A, (exec proposer dg y st t e).2[0]? = some (.ac ℓ)) ∧
      ∃ ℓ : ACLabel A, (exec proposer dg y st t e).2[1]? = some (.ac ℓ)) := by
  cases e with
  | block B' =>
    rw [exec_eq] at hk
    obtain ⟨rfl, rfl⟩ := onBlock_block hk
    exact Or.inl ⟨rfl, rfl⟩
  | message m => rcases k with _ | k <;> simp [exec_eq, onMessage_eq, acCall_eq] at hk
  | attestation a => rcases k with _ | k <;> simp [exec_eq, onAttestation] at hk
  | restart => rcases k with _ | k <;> simp [exec_eq, restart_eq, acCall_eq] at hk
  | tick x fgDue =>
    refine Or.inr ⟨x, fgDue, rfl, ?_⟩
    obtain ⟨rest, hcut, hrest⟩ : ∃ rest, (exec proposer dg y st t (.tick x fgDue)).2 =
        (tickStep proposer dg y st t x .acTick).2 ++
          (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
          rest ∧ Cut.fg (.block B acc) ∉ rest := by
      cases fgDue
      · exact ⟨[], by rw [tick_cuts_false, List.append_nil], by simp⟩
      · exact ⟨_, tick_cuts proposer dg y st t x, update_no_block proposer dg y _ t x B acc⟩
    rw [hcut] at hk ⊢
    have hl₁ : (tickStep proposer dg y st t x .acTick).2.length = 1 := by
      rw [tickStep_eq]
      rfl
    have hn : (tickStep proposer dg y st t x .acTick).2.length +
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1
          t x .proposal).2.length > k := by
      by_contra hle
      rw [List.getElem?_append_right (by simp only [List.length_append]; omega)] at hk
      exact hrest (List.mem_of_getElem? hk)
    rw [List.getElem?_append_left (by simp only [List.length_append]; omega)] at hk
    rcases k with _ | k
    · simp [tickStep_eq, acCall_eq] at hk
    rw [List.getElem?_append_right (by omega), hl₁, Nat.add_sub_cancel] at hk
    obtain ⟨rfl, hp, d, p, hdp, rfl, hacc⟩ := proposal_block proposer dg y _ t x hk
    refine ⟨rfl, hp, d, p, hdp, ?_, ?_, ⟨⟨.tick, frame st,
      (A.step y st.ac (frame st) t .tick).2⟩, ?_⟩, ?_⟩
    · simp only [tickStep_eq, acCall_eq]
    · simpa only [tickStep_eq, acCall_eq] using hacc
    · simp only [tickStep_eq, acCall_eq, List.getElem?_cons_zero, List.cons_append]
    rw [List.getElem?_append_left, List.getElem?_append_right (by rw [hl₁]), hl₁]
    · simp only [tickStep_eq, hp, ↓reduceIte, Nat.sub_self]
      split <;> simp [acProposal_eq]
    · have := (List.getElem?_eq_some_iff.1 hk).1
      simp only [List.length_append]
      omega

end Handlers

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- A proposer's tick calls AC proposal immediately after AC tick. -/
theorem tick_proposal_call (h : LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat} {fgDue : Bool}
    (hg : tr.GroupAt proposer dg y j t (.tick x fgDue))
    (hP : Proposes proposer y t) :
    tr.CallAt y (j + 1)
        (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 ∧
      tr.time (j + 1) = t ∧
      (tr.state y (j + 1)).ac = (tickStep proposer dg y (tr.state y j) t x .acTick).1.ac := by
  have h1 : (exec proposer dg y (tr.state y j) t (.tick x fgDue)).2[1]? =
      some (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 := by
    simp only [exec_eq, onTick_eq, runSteps_eq, tickSteps]
    cases fgDue <;> simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_cons,
      List.foldl_nil, List.nil_append, tickStep_eq, hP]
    all_goals split <;> simp [acProposal_eq, acCall_eq]
  rw [RunTrace.groupAt_iff] at hg
  have get {k : Nat} {c : Cut A}
      (hk : (exec proposer dg y (tr.state y j) t (.tick x fgDue)).2[k]? = some c) :
      tr.CallAt y (j + k) c ∧ tr.time (j + k) = t := by
    obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hk
    obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 k hk'
    exact ⟨⟨hn, hl.trans (congrArg some hc)⟩, ht⟩
  obtain ⟨hc, ht⟩ := get h1
  have h0 : (exec proposer dg y (tr.state y j) t (.tick x fgDue)).2[0]? =
      some (.ac ⟨.tick, frame (tr.state y j),
        (A.step y (tr.state y j).ac (frame (tr.state y j)) t .tick).2⟩) := by
    cases fgDue <;>
      simp [exec_eq, onTick_eq, runSteps_eq, tickSteps, tickStep_eq, acCall_eq]
  obtain ⟨hc0, ht0⟩ := get h0
  simp only [Nat.add_zero] at hc0 ht0
  refine ⟨hc, ht, ?_⟩
  rw [tr.state_succ_of_call hc0, tickStep_eq, acCall_eq]
  have hl := h.cutLaw y hy j _ hc0
  rw [cutStep_ac, ht0] at hl
  exact (congrArg Prod.fst hl.2.1).symm

theorem call_in_group (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {c : Cut A} (hc : tr.CallAt y i c) :
    ∃ j e k, tr.GroupAt proposer dg y j (tr.time i) e ∧ i = j + k ∧
      (exec proposer dg y (tr.state y j) (tr.time i) e).2[k]? = some c := by
  obtain ⟨j, e, hg⟩ := h.grouped y hy i c hc
  rw [RunTrace.inGroup_iff] at hg
  obtain ⟨hg, hji, hij⟩ := hg
  refine ⟨j, e, i - j, hg, by omega, ?_⟩
  rw [RunTrace.groupAt_iff] at hg
  have := (hg.2.1 (i - j) (by omega)).2.2.2.2
  rw [Nat.add_sub_cancel' hji, hc.2] at this
  rw [List.getElem?_eq_getElem (by omega), Option.some.inj this]

private theorem group_cut {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt proposer dg y j t e) {k : Nat} {c : Cut A}
    (hk : (exec proposer dg y (tr.state y j) t e).2[k]? = some c) :
    tr.CallAt y (j + k) c ∧ tr.time (j + k) = t := by
  rw [RunTrace.groupAt_iff] at hg
  obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 k hk'
  exact ⟨⟨hn, hl.trans (congrArg some hc)⟩, ht⟩

theorem accept_next (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {B : A.Blk} (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ℓ : ACLabel A, tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨ℓ, hk', hb⟩ := (paired_exec proposer dg y _ _ e).1 k B hk
  obtain ⟨hc', ht⟩ := group_cut hg hk'
  exact ⟨ℓ, hc', hb, ht⟩

theorem blockCall_cases (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {B : A.Blk} {acc : Bool} (hc : tr.CallAt y i (.fg (.block B acc))) :
    tr.GroupAt proposer dg y i (tr.time i) (.block B) ∨
    ∃ j x fgDue, i = j + 2 ∧ tr.GroupAt proposer dg y j (tr.time i) (.tick x fgDue) ∧
      Proposes proposer y (tr.time i) ∧ ∃ d p,
      (acProposal (tickStep proposer dg y (tr.state y j) (tr.time i) x .acTick).1
        (tr.time i)).2.2 = some (d, p) ∧
      B = mkBlock dg y (tr.state y j).fg (tr.time i) x d.head p ∧
      (acc = true ↔ ∃ fg', (tr.state y j).fg.onBlock B = some fg') ∧
      (∃ ℓ : ACLabel A, tr.CallAt y j (.ac ℓ)) ∧
      (∃ ℓ : ACLabel A, tr.CallAt y (j + 1) (.ac ℓ)) ∧
      (tr.state y i).fg = (tr.state y j).fg := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  rcases exec_block proposer dg y _ _ e hk with ⟨rfl, rfl⟩ |
    ⟨x, fgDue, rfl, rfl, hp, d, p, hdp, hB, hacc, ⟨ℓ₀, h₀⟩, ℓ₁, h₁⟩
  · exact Or.inl hg
  have c₀ := (group_cut hg h₀).1
  have c₁ := (group_cut hg h₁).1
  rw [Nat.add_zero] at c₀
  refine Or.inr ⟨j, x, fgDue, rfl, hg, hp, d, p, hdp, hB, hacc, ⟨_, c₀⟩, ⟨_, c₁⟩, ?_⟩
  rw [show j + 2 = j + 1 + 1 by omega, tr.state_succ_of_call c₁,
    ((cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy _ _ c₁)).2.2.1,
    tr.state_succ_of_call c₀, ((cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy _ _ c₀)).2.2.1]

theorem fg_step (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) (m : Nat) :
    (tr.state y (m + 1)).fg = (tr.state y m).fg ∨
      (∃ B, tr.AcceptAt y m B ∧ (tr.state y m).fg.onBlock B =
        some (tr.state y (m + 1)).fg) ∨
      ∃ a, tr.AttCallAt y m a ∧
        (tr.state y (m + 1)).fg = (tr.state y m).fg.onAttestation a := by
  by_cases hc : tr.IsCall y m
  · obtain ⟨c, hc⟩ := hc
    rw [Trace.state_succ_of_call _ hc]
    have hs := h.cutLaw y hy m c hc
    rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
    · rw [cutStep_block_false] at hs; exact Or.inl (by rw [hs.2])
    · rw [cutStep_block_true] at hs; exact Or.inr (Or.inl ⟨B, hc, hs.2.1⟩)
    · rw [cutStep_attestation] at hs; exact Or.inr (Or.inr ⟨a, hc, hs.1⟩)
    · rw [cutStep_attest_none] at hs; exact Or.inl (by rw [hs.2])
    · rw [cutStep_attest_some] at hs; exact Or.inl hs.2.1
    · rw [cutStep_ac] at hs; exact Or.inl hs.2.2.1
  · rw [Trace.state_succ_of_not _ fun c hc' => hc ⟨c, hc'⟩]
    exact Or.inl rfl

theorem tree_mono' (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k i : Nat} (hki : k ≤ i) : (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  induction i, hki using Nat.le_induction with
  | base => exact subset_rfl
  | succ i _ ih =>
    refine ih.trans ?_
    rcases fg_step h hy i with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
    · rw [he]
    · rw [Store.onBlock_eq_onBlockWith] at hB
      rw [(Store.tree_grows_with Store.finalitySpec_updateFinality).1 B _ hB]
      exact Set.subset_insert _ _
    · rw [he, (Store.tree_grows_with Store.finalitySpec_updateFinality).2 a]

theorem tree_accepted (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {m : Nat} {B : A.Blk} (hB : B ∈ (tr.state y m).fg.tree) :
    B = P.genesisBlock A.genesisPayload ∨ ∃ k < m, tr.AcceptAt y k B := by
  induction m with
  | zero =>
    left
    change (tr.init y).fg.blocks B.root = some B at hB
    rw [h.init y hy] at hB
    change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
      some B at hB
    split_ifs at hB
    exact (Option.some.inj hB).symm
  | succ m ih =>
    have lift : B ∈ (tr.state y m).fg.tree →
        B = P.genesisBlock A.genesisPayload ∨ ∃ k < m + 1, tr.AcceptAt y k B := fun hB =>
      (ih hB).imp_right fun ⟨k, hk, hA⟩ => ⟨k, by omega, hA⟩
    rcases fg_step h hy m with he | ⟨B', hA, hB'⟩ | ⟨a, -, he⟩
    · exact lift (he ▸ hB)
    · rw [Store.onBlock_eq_onBlockWith] at hB'
      rw [(Store.tree_grows_with Store.finalitySpec_updateFinality).1 B' _ hB'] at hB
      rcases hB with rfl | hB
      · exact Or.inr ⟨m, by omega, hA⟩
      · exact lift hB
    · rw [he, (Store.tree_grows_with Store.finalitySpec_updateFinality).2 a] at hB
      exact lift hB

/-- Stock tree-cases interface: every non-genesis held block was accepted earlier. -/
theorem tree_cases (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {m : Nat} {B : A.Blk} (hB : B ∈ (tr.state y m).fg.tree) :
    B = P.genesisBlock A.genesisPayload ∨ ∃ k < m, tr.AcceptAt y k B :=
  tree_accepted h hy hB

theorem accept_mem_from (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {k : Nat} {B : A.Blk} (hA : tr.AcceptAt y k B) :
    B ∈ (tr.state y (k + 1)).fg.tree := by
  have hb := ((cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy k _ hA)).2.1
  rw [Store.onBlock_eq_onBlockWith] at hb
  rw [tr.state_succ_of_call hA,
    (Store.tree_grows_with Store.finalitySpec_updateFinality).1 B _ hb]
  exact Set.mem_insert _ _

theorem hmax_mono (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H) :
    Monotone fun m => (tr.state y m).fg.hmax := by
  refine monotone_nat_of_le_succ fun m => ?_
  rcases fg_step h hy m with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
  · rw [he]
  · rw [Store.onBlock_eq_onBlockWith] at hB
    obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some hB
    obtain ⟨atts, ha⟩ := Store.addAtts_eq (Store.updateFinality { (tr.state y m).fg with
      blocks := Function.update (tr.state y m).fg.blocks B.root (some B),
      σ := Function.update (tr.state y m).fg.σ B.root σ' } σ') B.fgPayload
    rw [he, ha, Store.finalitySpec_updateFinality.hmax]
    exact le_max_left _ _
  · obtain ⟨atts, ha⟩ := (tr.state y m).fg.onAttestation_eq a
    rw [he, ha]

theorem tree_subset_run (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.tree ⊆ insert (P.genesisBlock A.genesisPayload) {B | tr.Occurs B} :=
  fun _ hX => (tree_accepted h hy hX).imp_right fun ⟨k, _, hk⟩ => ⟨y, k, true, hk⟩

theorem accept_facts (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {X : A.Blk} (hk : tr.AcceptAt y k X) :
    X.RootOk dg ∧ X.proposer = proposer X.slot ∧ (tr.state y k).fg.blocks X.root = none ∧
      X.root ≠ P.genesisRoot := by
  have hb := ((cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy k _ hk)).2.1
  rw [Store.onBlock_eq_onBlockWith] at hb
  obtain ⟨pr, σ', -, hnew, -, -, hσ, -⟩ := Store.onBlockWith_eq_some hb
  refine ⟨?_, ?_, hnew, fun hg => ?_⟩
  · rcases blockCall_cases h hy hk with hg | ⟨j, x, -, -, -, -, d, p, -, rfl, -⟩
    · exact (h.wire y hy k _ _ hg).1
    · rfl
  · rcases blockCall_cases h hy hk with hg | ⟨j, x, -, -, -, hp, d, p, -, rfl, -⟩
    · exact h.proposerCredential y hy k _ _ hg
    · exact hp.2.2.symm
  · have hG := (Store.accepted_tree_with Store.finalitySpec_updateFinality
      (Node.fg_reachable_at h hy k).reachableWith).2.2.1
    change (tr.state y k).fg.blocks P.genesisRoot = some _ at hG
    rw [← hg, hnew] at hG
    cases hG

private theorem tree_root_inj (h : LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y y' : Fin P.n}
    (hy : y ∈ H) (hy' : y' ∈ H) {i i' : Nat} {X X' : A.Blk}
    (hX : X ∈ (tr.state y i).fg.tree) (hX' : X' ∈ (tr.state y' i').fg.tree)
    (hr : X.root = X'.root) : X = X' := by
  rcases tree_accepted h hy hX with rfl | ⟨k, -, hk⟩ <;>
    rcases tree_accepted h hy' hX' with rfl | ⟨k', -, hk'⟩
  · rfl
  · exact absurd hr.symm (accept_facts h hy' hk').2.2.2
  · exact absurd hr (accept_facts h hy hk).2.2.2
  obtain ⟨hro, hpr, -⟩ := accept_facts h hy hk
  obtain ⟨hro', hpr', -⟩ := accept_facts h hy' hk'
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hnc X (Or.inr ⟨y, k, true, hk⟩)
    X' (Or.inr ⟨y', k', true, hk'⟩) (by rw [← hro, ← hro', hr])
  obtain ⟨r, pa, sl, pp, inp, fp, ap⟩ := X
  obtain ⟨r', pa', sl', pp', inp', fp', ap'⟩ := X'
  simp only at hr h₁ h₂ h₃ h₄ h₅ hpr hpr'
  subst hr h₁ h₂ h₃ h₄ h₅
  rw [hpr, hpr']

theorem honest_blocks_coherent (h : LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) : Coherent (tr.HonestBlocks H) := by
  refine ⟨fun X ⟨y, hy, i, hX⟩ X' ⟨y', hy', i', hX'⟩ hr =>
    tree_root_inj h hnc hy hy' hX hX' hr,
    fun Y ⟨y', hy', i', hY⟩ X ⟨y, hy, i, hX⟩ hp => ?_⟩
  rcases tree_accepted h hy hX with rfl | ⟨k, hki, hk⟩
  · cases hp
  have hb := ((cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy k _ hk)).2.1
  rw [Store.onBlock_eq_onBlockWith] at hb
  obtain ⟨pr, -, hpar, -, hheld, -⟩ := Store.onBlockWith_eq_some hb
  rw [hp] at hpar
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hheld
  have hrk := (Node.fg_reachable_at h hy k).reachableWith
  have hZr := Store.blocks_root_with Store.finalitySpec_updateFinality hrk hZ
  have hZt : Z ∈ (tr.state y k).fg.tree := by
    change _ = _
    rw [hZr, hZ]
  cases Option.some.inj hpar
  obtain rfl : Z = Y := tree_root_inj h hnc hy hy' hZt hY hZr
  exact (Store.accepted_tree_with Store.finalitySpec_updateFinality
    (Node.fg_reachable_at h hy i).reachableWith).2.1.2 Z (tree_mono' h hy hki.le hZt) X hX hp

theorem store_anc_of_honest_anc (h : LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} (hy : y ∈ H) {k : Nat} {B C : A.Blk}
    (hBC : Anc (tr.HonestBlocks H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc B C := by
  have hr := (Node.fg_reachable_at h hy k).reachableWith
  have hU := honest_blocks_coherent h hnc
  induction hBC with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((Store.accepted_tree_with Store.finalitySpec_updateFinality hr).2.2.2 _ hC).cases_tail
      with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := hU.1 ⟨y, hy, k, hZ.1⟩ hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

theorem honest_held_anc' {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {A W : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A W) (hW : W ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.Anc A W :=
  store_anc_of_honest_anc hrun.toLocalRun hnc hy h hW

theorem honest_held_height' {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
    (hrun : GoldilocksRun proposer dg H tr ini) (_hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {A W : AC.Blk sp.n (List (FG.Att sp.n))} (h : (tr.state y i).fg.Anc A W) :
    ((tr.state y i).fg.σ A.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ A.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ A.root).Th) := by
  have hr := (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
  exact ⟨Store.h_le_of_store_anc_with Store.finalitySpec_updateFinality hr h,
    Store.Th_eq_of_anc_with Store.finalitySpec_updateFinality hr h⟩

theorem honest_eq_genesis {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
    (hrun : GoldilocksRun proposer dg H tr ini) (hU : Coherent (tr.HonestBlocks H))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  have hg := (Store.accepted_tree_with Store.finalitySpec_updateFinality
    (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith).2.2.1
  exact hU.1 ⟨y, hy, i, hBt⟩ ⟨y, hy, i, hg⟩ hr

section Growing

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}

private theorem held_block_cases
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ tr.HonestBlocksAt H) :
    X = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      tr.Occurs X ∧ X.RootOk dg ∧ X.proposer = proposer X.slot ∧ X.root ≠ sp.genesisRoot := by
  obtain ⟨y, i, t, ht, hb, hy, hX⟩ := hX
  have hs := Trace.upTo_state tr y hb
  have hp := (h.upTo ht).toLocalRun
  rw [← hs] at hX
  rcases tree_accepted hp hy hX with hg | ⟨k, _, hk⟩
  · exact Or.inl hg
  · obtain ⟨hr, hpr, _, hng⟩ := accept_facts hp hy hk
    exact Or.inr ⟨RunTrace.upTo_occurs ⟨y, k, true, hk⟩, hr, hpr, hng⟩

private theorem held_root_inj
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {X Y : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ tr.HonestBlocksAt H) (hY : Y ∈ tr.HonestBlocksAt H)
    (hr : X.root = Y.root) : X = Y := by
  rcases held_block_cases h hX with rfl | ⟨hx, hro, hpr, hng⟩ <;>
    rcases held_block_cases h hY with rfl | ⟨hy, hro', hpr', hng'⟩
  · rfl
  · exact absurd hr.symm hng'
  · exact absurd hr hng
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hnc X (Or.inr hx) Y (Or.inr hy)
    (by rw [← hro, ← hro', hr])
  obtain ⟨r, pa, sl, pp, inp, fp, ap⟩ := X
  obtain ⟨r', pa', sl', pp', inp', fp', ap'⟩ := Y
  simp only at hr h₁ h₂ h₃ h₄ h₅ hpr hpr'
  subst hr h₁ h₂ h₃ h₄ h₅
  rw [hpr, hpr']

theorem honest_blocks_coherent_at
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) := by
  refine ⟨fun _ hx _ hy hr => held_root_inj h hnc hx hy hr, fun Y hY X hX hp => ?_⟩
  obtain ⟨y, i, t, ht, hb, hy, hXi⟩ := hX
  have hs := Trace.upTo_state tr y hb
  have hr := (h.upTo ht).toLocalRun
  rw [← hs] at hXi
  rcases tree_accepted hr hy hXi with rfl | ⟨k, hki, hk⟩
  · cases hp
  have hblock := ((cutStep_block_true _ _ _ _ _).1 (hr.cutLaw y hy k _ hk)).2.1
  rw [Store.onBlock_eq_onBlockWith] at hblock
  obtain ⟨pr, _, hpar, _, hheld, _⟩ := Store.onBlockWith_eq_some hblock
  rw [hp] at hpar
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hheld
  have hrk := (Node.fg_reachable_at hr hy k).reachableWith
  have hZr := Store.blocks_root_with Store.finalitySpec_updateFinality hrk hZ
  have hZt : Z ∈ ((tr.upTo t).state y k).fg.tree := by
    change _ = _
    rw [hZr, hZ]
  cases Option.some.inj hpar
  have hZH : Z ∈ tr.HonestBlocksAt H :=
    RunTrace.honestBlocks_upTo_subset h.time_mono ht ⟨y, hy, k, hZt⟩
  obtain rfl : Z = Y := held_root_inj h hnc hZH hY hZr
  exact (Store.accepted_tree_with Store.finalitySpec_updateFinality
    (Node.fg_reachable_at hr hy i).reachableWith).2.1.2 Z
    (tree_mono' hr hy hki.le hZt) X hXi hp

theorem honestBlocksAt_coherent
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) :=
  honest_blocks_coherent_at h hnc

theorem held_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} {y : Fin sp.n} {i : Nat}
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d)
    {A W : AC.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocksAt H) A W)
    (hW : W ∈ (tr.state y i).fg.tree) : (tr.state y i).fg.Anc A W := by
  have hr := (Node.fg_reachable_at (hrun.upTo hd).toLocalRun hy i).reachableWith
  rw [Trace.upTo_state tr y hi] at hr
  have hU := honestBlocksAt_coherent hrun hnc
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((Store.accepted_tree_with Store.finalitySpec_updateFinality hr).2.2.2 _ hW).cases_tail
      with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := hU.1 ⟨y, i, d, hd, hi, hy, hZ.1⟩ hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

end Growing

end Consensus.Goldilocks.Coherence

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open AC (ACParams ReplayOrder Payload)

theorem honest_row_signed_before' {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {ini} (hrun : GoldilocksRun proposer dg H tr ini) (_hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y i).fg.tree) {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a := by
  rcases Coherence.tree_accepted hrun.toLocalRun hy hX with rfl | ⟨m, hm, hA⟩
  · simp [Params.genesisBlock] at ha
  · exact ⟨m, hm, hA,
      hrun.att_unforgeable y hy m a (Or.inr ⟨X, ⟨true, hA⟩, ha⟩) hav⟩

end Consensus.Goldilocks.Compose

end
