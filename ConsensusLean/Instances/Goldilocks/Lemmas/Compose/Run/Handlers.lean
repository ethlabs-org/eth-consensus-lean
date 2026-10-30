module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # Goldilocks runs: the cuts of the handlers, read in the run

The run records each handler's cuts at consecutive cuts of its node, so the shape of the
handlers is a fact of the run: an accepted block's FG cut is followed by the AC cut of that
block and every AC block call follows its accepting FG cut; an AC message call is a message
delivery; a signing `fg_attest` follows the FG update's `ac_to_fg`, which returned its source.
The component states before each cut are the run's (the projections commute with
`Trace.state`), and every honest FG state is reachable. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}

/-! ### Handler cuts -/

/-- Every accepted-block FG cut is followed by the AC cut of that block, and every AC cut of a
block follows the FG cut that accepts it. -/
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
  unfold onBlock
  split_ifs
  · exact paired_nil
  split
  · exact paired_fg fun _ h => by cases h
  · refine ⟨fun k B' hk => ?_, fun k ℓ B' hk hb => ?_⟩
    · rcases k with _ | _ | k <;> simp [acCall] at hk
      subst hk
      exact ⟨_, rfl, rfl⟩
    · rcases k with _ | _ | k <;> simp [acCall] at hk
      subst hk
      cases hb
      exact ⟨0, rfl, rfl⟩

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) :
    (exec dg y st t (.tick x)).2 = (tickStep dg y st t x .acTick).2 ++
      (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).2 ++
      (tickStep dg y (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 :=
  by simp [exec, onTick, runSteps, tickSteps]

private theorem paired_tickStep (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (s : TickStep) :
    Paired (tickStep dg y st t x s).2 := by
  cases s with
  | acTick => exact paired_ac fun _ h => by cases h
  | proposal =>
    simp only [tickStep]
    split_ifs
    · split
      · exact paired_ac fun _ h => by cases h
      · exact (paired_ac fun _ h => by cases h).append (paired_onBlock y _ t _)
    · exact paired_nil
  | fgUpdate =>
    simp only [tickStep]
    split
    · exact paired_ac fun _ h => by cases h
    · refine (paired_ac (c := .toFG) fun _ h => by cases h).append ?_
      simp only [attest]
      split
      · exact paired_fg fun _ h => by cases h
      · exact (paired_fg fun _ h => by cases h).append (paired_fg fun _ h => by cases h)

private theorem paired_exec (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) : Paired (exec dg y st t e).2 := by
  cases e with
  | tick x =>
    rw [tick_cuts]
    exact ((paired_tickStep dg y st t x _).append (paired_tickStep dg y _ t x _)).append
      (paired_tickStep dg y _ t x _)
  | block B => exact paired_onBlock y st t B
  | message m => exact paired_ac fun _ h => by cases h
  | attestation a => exact paired_fg fun _ h => by cases h
  | restart => exact paired_ac fun _ h => by cases h

/-- The FG update signs at its second cut, after its `ac_to_fg`, which returned the source. -/
private theorem update_attest (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {m : Nat} {C : A.Blk} {a : FG.Att P.n}
    (hm : (tickStep dg y st t x .fgUpdate).2[m]? = some (.fg (.attest C (some a)))) :
    m = 1 ∧ (tickStep dg y st t x .fgUpdate).2[0]? = some (.ac ⟨.toFG, frame st, []⟩) ∧
      (A.toFG st.ac (frame st) t).2.1 = some C := by
  simp only [tickStep, acToFG] at hm ⊢
  split at hm
  · rcases m with _ | m <;> simp at hm
  rename_i C' hC'
  simp only [attest] at hm
  split at hm
  · rcases m with _ | _ | m <;> simp at hm
  rcases m with _ | _ | _ | m <;> simp [onAttestation] at hm
  obtain ⟨rfl, -⟩ := hm
  exact ⟨rfl, rfl, hC'⟩

/-- The proposal step signs nothing. -/
private theorem proposal_no_attest (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (C : A.Blk) (s : Option (FG.Att P.n)) :
    Cut.fg (.attest C s) ∉ (tickStep dg y st t x .proposal).2 := by
  simp only [tickStep]
  split_ifs
  · split
    · simp [acProposal]
    · rename_i d p _
      simp only [proposeBlock, onBlock, List.mem_cons, acProposal, reduceCtorEq, false_or]
      by_cases hf : P.slotOf t < (mkBlock dg y st.fg t x d.head p).slot
      · simp [hf]
      · simp only [hf, ↓reduceIte]
        split <;> simp [acCall]
  · simp

/-- A signing `fg_attest` cut follows the FG update's `ac_to_fg`, which returned its source. -/
private theorem attest_prev (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {C : A.Blk} {a : FG.Att P.n}
    (hk : (exec dg y st t e).2[k]? = some (.fg (.attest C (some a)))) :
    ∃ k', k = k' + 1 ∧ ∃ st₁, CutChain y t st ((exec dg y st t e).2.take k') st₁ ∧
      (exec dg y st t e).2[k']? = some (.ac ⟨.toFG, frame st₁, []⟩) ∧
      (A.toFG st₁.ac (frame st₁) t).2.1 = some C := by
  obtain ⟨x, rfl⟩ : ∃ x, e = .tick x :=
    signed_only_in_ticks dg y st t e C a (List.mem_of_getElem? hk)
  rw [tick_cuts] at hk ⊢
  set l₁ := (tickStep dg y st t x .acTick).2 with hl₁
  set r₂ := tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal
  have hch : CutChain y t st (l₁ ++ r₂.2) r₂.1 :=
    chain_append y (tickStep_chain dg y st t x _) (tickStep_chain dg y _ t x _)
  have hn : (l₁ ++ r₂.2).length ≤ k := by
    by_contra hlt
    rw [List.getElem?_append_left (by omega)] at hk
    rcases List.mem_append.1 (List.mem_of_getElem? hk) with hm | hm
    · simp [hl₁, tickStep, acCall] at hm
    · exact proposal_no_attest dg y _ t x C _ hm
  rw [List.getElem?_append_right hn] at hk
  obtain ⟨hm, h0, hC⟩ := update_attest dg y r₂.1 t x hk
  refine ⟨(l₁ ++ r₂.2).length, by omega, r₂.1, by rw [List.take_left' rfl]; exact hch, ?_, hC⟩
  rw [List.getElem?_append_right le_rfl, Nat.sub_self]
  exact h0

/-- The FG cut of `on_block` is its first cut, of its block. -/
private theorem onBlock_block {y : Fin P.n} {st : NodeState A} {t : Time} {B' B : A.Blk}
    {acc : Bool} {k : Nat} (hk : (onBlock y st t B').2[k]? = some (.fg (.block B acc))) :
    k = 0 ∧ B' = B := by
  unfold onBlock at hk
  split_ifs at hk
  · simp at hk
  split at hk <;> rcases k with _ | _ | k <;> simp [acCall] at hk
  all_goals exact ⟨rfl, hk.1⟩

/-- The FG update makes no block cut. -/
private theorem update_no_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (B : A.Blk) (acc : Bool) :
    Cut.fg (.block B acc) ∉ (tickStep dg y st t x .fgUpdate).2 := by
  simp only [tickStep]
  split
  · simp [acToFG]
  · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or]
    split <;> simp [onAttestation]

/-- The block cut of the proposal step is its second, of the own proposal. -/
private theorem proposal_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {B : A.Blk} {acc : Bool} {m : Nat}
    (hm : (tickStep dg y st t x .proposal).2[m]? = some (.fg (.block B acc))) :
    m = 1 ∧ Proposes y t ∧ ∃ d p, (acProposal st t).2.2 = some (d, p) ∧
      B = mkBlock dg y st.fg t x d.head p ∧
      (acc = true ↔ ∃ fg', st.fg.onBlock B = some fg') := by
  simp only [tickStep] at hm
  split_ifs at hm with hp
  · split at hm
    · rcases m with _ | m <;> simp [acProposal] at hm
    rename_i d p hdp
    rcases m with _ | m
    · simp [acProposal] at hm
    simp only [List.getElem?_cons_succ] at hm
    obtain ⟨rfl, rfl⟩ := onBlock_block (B' := mkBlock dg y _ t x d.head p) hm
    refine ⟨rfl, hp, d, p, hdp, rfl, ?_⟩
    simp only [proposeBlock, onBlock] at hm
    split_ifs at hm
    · simp at hm
    split at hm <;> simp at hm <;> rename_i h <;> subst hm
    · simp [acProposal] at h ⊢
      rw [h]
      simp
    · simp only [acProposal] at h ⊢
      simp [h]
  · simp at hm

/-- **The block cuts of a handler**: a delivery's first cut, or the own proposal's in a tick, at
its third cut. -/
private theorem exec_block (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {B : A.Blk} {acc : Bool} {k : Nat}
    (hk : (exec dg y st t e).2[k]? = some (.fg (.block B acc))) :
    (e = .block B ∧ k = 0) ∨ (∃ x, e = .tick x ∧ k = 2 ∧ Proposes y t ∧ ∃ d p,
      (acProposal (tickStep dg y st t x .acTick).1 t).2.2 = some (d, p) ∧
      B = mkBlock dg y st.fg t x d.head p ∧ (acc = true ↔ ∃ fg', st.fg.onBlock B = some fg') ∧
      (∃ ℓ : ACLabel A, (exec dg y st t e).2[0]? = some (.ac ℓ)) ∧
      ∃ ℓ : ACLabel A, (exec dg y st t e).2[1]? = some (.ac ℓ)) := by
  cases e with
  | block B' =>
    obtain ⟨rfl, rfl⟩ := onBlock_block hk
    exact Or.inl ⟨rfl, rfl⟩
  | message m => rcases k with _ | k <;> simp [exec, onMessage, acCall] at hk
  | attestation a => rcases k with _ | k <;> simp [exec, onAttestation] at hk
  | restart => rcases k with _ | k <;> simp [exec, restart, acCall] at hk
  | tick x =>
    refine Or.inr ⟨x, rfl, ?_⟩
    rw [tick_cuts] at hk ⊢
    have hl₁ : (tickStep dg y st t x .acTick).2.length = 1 := rfl
    have hn : (tickStep dg y st t x .acTick).2.length +
        (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).2.length > k := by
      by_contra hle
      rw [List.getElem?_append_right (by simp only [List.length_append]; omega)] at hk
      exact update_no_block dg y _ t x B acc (List.mem_of_getElem? hk)
    rw [List.getElem?_append_left (by simp only [List.length_append]; omega)] at hk
    rcases k with _ | k
    · simp [tickStep, acCall] at hk
    rw [List.getElem?_append_right (by omega), hl₁, Nat.add_sub_cancel] at hk
    obtain ⟨rfl, hp, d, p, hdp, rfl, hacc⟩ := proposal_block dg y _ t x hk
    refine ⟨rfl, hp, d, p, hdp, rfl, hacc, ⟨_, rfl⟩, ?_⟩
    rw [List.getElem?_append_left, List.getElem?_append_right (by rw [hl₁]), hl₁]
    · simp only [tickStep, hp, ↓reduceIte, Nat.sub_self]
      split <;> simp [acProposal]
    · have := (List.getElem?_eq_some_iff.1 hk).1
      simp only [List.length_append]
      omega

/-- An AC message call is a message delivery. -/
private theorem exec_message (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {ℓ : ACLabel A} {m : A.Msg}
    (h : Cut.ac ℓ ∈ (exec dg y st t e).2) (hm : ℓ.call = .message m) : e = .message m := by
  cases e with
  | message m' =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
    rfl
  | attestation a => simp [exec, onAttestation] at h
  | restart =>
    simp only [exec, restart, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  | block B =>
    simp only [exec, onBlock] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp [acCall] at h
      subst h
      cases hm
  | tick =>
    rw [tick_cuts] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [tickStep, acCall, List.mem_singleton, Cut.ac.injEq] at h
      subst h
      cases hm
    · simp only [tickStep] at h
      split_ifs at h
      · split at h
        · simp only [acProposal, List.mem_singleton, Cut.ac.injEq] at h
          subst h
          cases hm
        · rcases List.mem_cons.1 h with h | h
          · simp only [acProposal, Cut.ac.injEq] at h
            subst h
            cases hm
          · simp only [proposeBlock, onBlock] at h
            split_ifs at h
            · simp at h
            · split at h <;> simp [acCall] at h
              subst h
              cases hm
      · simp at h
    · simp only [tickStep] at h
      split at h
      · simp only [acToFG, List.mem_singleton, Cut.ac.injEq] at h
        subst h
        cases hm
      · rcases List.mem_cons.1 h with h | h
        · simp only [acToFG, Cut.ac.injEq] at h
          subst h
          cases hm
        · simp only [attest] at h
          split at h <;> simp [onAttestation] at h

/-- An `fg_attest` cut is in a tick. -/
private theorem exec_attest (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {C : A.Blk} {s : Option (FG.Att P.n)}
    (h : Cut.fg (.attest C s) ∈ (exec dg y st t e).2) : ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | block B =>
    simp only [exec, onBlock, acCall] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [exec, onMessage, acCall] at h
  | attestation a' => simp [exec, onAttestation] at h
  | restart => simp [exec, restart, acCall] at h

/-- The FG update's `fg_attest` cut is its second. -/
private theorem update_attest_pos (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {m : Nat} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hm : (tickStep dg y st t x .fgUpdate).2[m]? = some (.fg (.attest C s))) : m = 1 := by
  simp only [tickStep, acToFG] at hm
  split at hm
  · rcases m with _ | m <;> simp at hm
  simp only [attest] at hm
  split at hm
  · rcases m with _ | _ | m <;> simp at hm ⊢
  · rcases m with _ | _ | _ | m <;> simp [onAttestation] at hm ⊢

/-- In a tick, the FG cuts before an `fg_attest` cut are the own proposal's. -/
private theorem tick_before_attest (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {m m₂ : Nat} {ℓ : FGLabel P A.Payload} {C : A.Blk}
    {s : Option (FG.Att P.n)} (hm : (exec dg y st t (.tick x)).2[m]? = some (.fg ℓ))
    (hm₂ : (exec dg y st t (.tick x)).2[m₂]? = some (.fg (.attest C s))) (hlt : m < m₂) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = t := by
  rw [tick_cuts] at hm hm₂
  set l := (tickStep dg y st t x .acTick).2 ++
    (tickStep dg y (tickStep dg y st t x .acTick).1 t x .proposal).2
  have hl : l.length ≤ m₂ := by
    by_contra hlt'
    rw [List.getElem?_append_left (by omega)] at hm₂
    rcases List.mem_append.1 (List.mem_of_getElem? hm₂) with h | h
    · simp [tickStep, acCall] at h
    · exact proposal_no_attest dg y _ t x C s h
  rw [List.getElem?_append_right hl] at hm₂
  -- the FG update signs at its second cut
  have h₂ := update_attest_pos dg y _ t x hm₂
  rcases lt_trichotomy m l.length with hml | hml | hml
  · rw [List.getElem?_append_left hml] at hm
    rcases m with _ | m
    · simp [l, tickStep, acCall] at hm
    rw [List.getElem?_append_right (by simp [tickStep]), show (m + 1 -
      (tickStep dg y st t x .acTick).2.length) = m by simp [tickStep]] at hm
    simp only [tickStep] at hm
    split_ifs at hm with hp
    · split at hm
      · rcases m with _ | m <;> simp [acProposal] at hm
      rename_i d p _
      rcases m with _ | m
      · simp [acProposal] at hm
      simp only [List.getElem?_cons_succ, proposeBlock, onBlock] at hm
      split_ifs at hm
      · simp at hm
      split at hm <;> rcases m with _ | _ | m <;> simp [acCall] at hm
      all_goals
        subst hm
        exact ⟨_, _, rfl, rfl, hp.2.1.symm⟩
    · simp at hm
  · subst hml
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hm
    simp only [tickStep] at hm
    split at hm <;> simp [acToFG] at hm
  · omega

variable {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-! ### In the run -/

/-- A cut of an honest node is the cut of its group's handler at its offset. -/
theorem call_in_group (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {c : Cut A} (hc : tr.CallAt y i c) :
    ∃ j e k, tr.GroupAt dg y j (tr.time i) e ∧ i = j + k ∧
      (exec dg y (tr.state y j) (tr.time i) e).2[k]? = some c := by
  obtain ⟨j, e, hg, hji, hij⟩ := h.grouped y hy i c hc
  refine ⟨j, e, i - j, hg, by omega, ?_⟩
  have := (hg.2.1 (i - j) (by omega)).2.2.2.2
  rw [Nat.add_sub_cancel' hji, hc.2] at this
  rw [List.getElem?_eq_getElem (by omega), Option.some.inj this]

/-- The cut at offset `k` of a group. -/
private theorem group_cut {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt dg y j t e) {k : Nat} {c : Cut A}
    (hk : (exec dg y (tr.state y j) t e).2[k]? = some c) :
    tr.CallAt y (j + k) c ∧ tr.time (j + k) = t := by
  obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 k hk'
  exact ⟨⟨hn, hl.trans (congrArg some hc)⟩, ht⟩

/-- **An accepted block's FG cut is followed by the AC cut of that block.** -/
theorem accept_next (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : A.Blk} (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ℓ : ACLabel A, tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨ℓ, hk', hb⟩ := (paired_exec dg y _ _ e).1 k B hk
  obtain ⟨hc', ht⟩ := group_cut hg hk'
  exact ⟨ℓ, hc', hb, ht⟩

/-- **An AC block call follows the FG cut that accepts the block.** -/
theorem acBlock_prev (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel A} {B : A.Blk} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨k', rfl, hk'⟩ := (paired_exec dg y _ _ e).2 k ℓ B hk hb
  obtain ⟨hc', ht⟩ := group_cut hg hk'
  exact ⟨j + k', rfl, hc', ht⟩

/-! ### The component states -/

/-- A call of the AC projection is an AC cut of the run. -/
theorem projAC_callAt {y : Fin P.n} {i : Nat} {ℓ : ACLabel A} :
    tr.projAC.CallAt y i ℓ ↔ tr.CallAt y i (.ac ℓ) := by
  unfold Trace.CallAt
  change tr.node i = y ∧ (tr.label i).bind RunTrace.acLabel = some ℓ ↔ _
  cases tr.label i with
  | none => simp
  | some c => cases c <;> simp [RunTrace.acLabel]

/-- A call of the FG projection is an FG cut of the run. -/
theorem projFG_callAt {y : Fin P.n} {i : Nat} {ℓ : FGLabel P A.Payload} :
    tr.projFG.CallAt y i ℓ ↔ tr.CallAt y i (.fg ℓ) := by
  unfold Trace.CallAt
  change tr.node i = y ∧ (tr.label i).bind RunTrace.fgLabel = some ℓ ↔ _
  cases tr.label i with
  | none => simp
  | some c => cases c <;> simp [RunTrace.fgLabel]


/-- **The AC projection's state is the AC part of the run's state** (honest node). -/
theorem projAC_state (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    tr.projAC.state y i = (tr.state y i).ac := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projAC, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl]
        rw [← ih]
        simp [Trace.state, RunTrace.projAC, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | ac ℓ => simp [Trace.state, RunTrace.projAC, hn, hl, RunTrace.acLabel]
        | fg ℓ =>
          rw [show (tr.post i).ac = (tr.state y i).ac by
            cases ℓ with
            | block B acc =>
              cases acc
              · rw [hlaw.2]
              · exact hlaw.2.2.1
            | attestation a => exact hlaw.2.1
            | attest C s =>
              cases s
              · rw [hlaw.2]
              · exact hlaw.2.2, ← ih]
          simp [Trace.state, RunTrace.projAC, hl, RunTrace.acLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projAC, hn]

/-- **The FG projection's state is the FG part and the record of the run's state** (honest
node). -/
theorem projFG_state (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.state y i = ((tr.state y i).fg, (tr.state y i).record) := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projFG, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl, ← ih]
        simp [Trace.state, RunTrace.projFG, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | fg ℓ => simp [Trace.state, RunTrace.projFG, hn, hl, RunTrace.fgLabel]
        | ac ℓ =>
          rw [hlaw.2.2.1, hlaw.2.2.2, ← ih]
          simp [Trace.state, RunTrace.projFG, hl, RunTrace.fgLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projFG, hn]

/-- **Every honest FG state of a run is reachable.** -/
theorem fg_reachable (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.Reachable A.genesisPayload := by
  induction i with
  | zero => rw [Trace.state, h.init y hy]; exact .refl
  | succ i ih =>
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      exact (chain_fg y (.cons (h.cutLaw y hy i c hc) (.nil _)) ih).1
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact ih

/-- **An honest signing `fg_attest(C)` is the FG update's**: the cut before is the node's
`ac_to_fg` at the same time, which returned `C`, and the FG state is the same at both. -/
theorem attest_source (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {C : A.Blk} {a : FG.Att P.n} (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel A, tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧
      tr.time j' = tr.time j ∧ (A.toFG (tr.state y j').ac ℓ.frame (tr.time j')).2.1 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j₀, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨k', rfl, st₁, hch, hk', hC⟩ := attest_prev dg y _ _ e hk
  have hlen := (List.getElem?_eq_some_iff.1 hk').1
  have hst : tr.state y (j₀ + k') = st₁ := by
    have := cutChain_run h hy hch j₀ rfl fun m hm => by
      rw [List.length_take] at hm
      obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 m (by omega)
      exact ⟨hn, ht, by rw [hl, List.getElem_take]⟩
    rwa [List.length_take, min_eq_left hlen.le] at this
  obtain ⟨hc', ht⟩ := group_cut hg hk'
  refine ⟨j₀ + k', by omega, _, hc', rfl, ht, by rw [hst, ht]; exact hC, ?_⟩
  rw [show j₀ + (k' + 1) = j₀ + k' + 1 by omega, tr.state_succ_of_call hc']
  exact (h.cutLaw y hy _ _ hc').2.2.1

/-- **A block call is a delivery, or the own proposal in a tick** at its third cut, after two
AC cuts, so at the FG state before the tick. -/
theorem blockCall_cases (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : A.Blk} {acc : Bool} (hc : tr.CallAt y i (.fg (.block B acc))) :
    tr.GroupAt dg y i (tr.time i) (.block B) ∨
    ∃ j x, i = j + 2 ∧ tr.GroupAt dg y j (tr.time i) (.tick x) ∧ Proposes y (tr.time i) ∧ ∃ d p,
      (acProposal (tickStep dg y (tr.state y j) (tr.time i) x .acTick).1 (tr.time i)).2.2 =
        some (d, p) ∧
      B = mkBlock dg y (tr.state y j).fg (tr.time i) x d.head p ∧
      (acc = true ↔ ∃ fg', (tr.state y j).fg.onBlock B = some fg') ∧
      (∃ ℓ : ACLabel A, tr.CallAt y j (.ac ℓ)) ∧ (∃ ℓ : ACLabel A, tr.CallAt y (j + 1) (.ac ℓ)) ∧
      (tr.state y i).fg = (tr.state y j).fg := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  rcases exec_block dg y _ _ e hk with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl, hp, d, p, hdp, hB, hacc,
    ⟨ℓ₀, h₀⟩, ℓ₁, h₁⟩
  · exact Or.inl hg
  have c₀ := (group_cut hg h₀).1
  have c₁ := (group_cut hg h₁).1
  rw [Nat.add_zero] at c₀
  refine Or.inr ⟨j, x, rfl, hg, hp, d, p, hdp, hB, hacc, ⟨_, c₀⟩, ⟨_, c₁⟩, ?_⟩
  rw [show j + 2 = j + 1 + 1 by omega, tr.state_succ_of_call c₁, (h.cutLaw y hy _ _ c₁).2.2.1,
    tr.state_succ_of_call c₀, (h.cutLaw y hy _ _ c₀).2.2.1]

/-- **An AC message call is in the delivery of that message.** -/
theorem msgCall_group (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel A} {m : A.Msg} (hc : tr.CallAt y i (.ac ℓ)) (hm : ℓ.call = .message m) :
    ∃ j, tr.GroupAt dg y j (tr.time i) (.message m) := by
  obtain ⟨j, e, k, hg, -, hk⟩ := call_in_group h hy hc
  obtain rfl := exec_message dg y _ _ e (List.mem_of_getElem? hk) hm
  exact ⟨j, hg⟩

/-- **An `fg_attest` call is in a tick.** -/
theorem attestCall_tick (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {C : A.Blk} {s : Option (FG.Att P.n)} (hc : tr.CallAt y i (.fg (.attest C s))) :
    ∃ j, j ≤ i ∧ tr.TickAt dg y j (tr.time i) := by
  obtain ⟨j, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨x, rfl⟩ := exec_attest dg y _ _ e (List.mem_of_getElem? hk)
  exact ⟨j, by omega, x, hg⟩

/-- **Before the tick of a time, a node's cuts at that time are restarts.** -/
theorem before_tick (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j k : Nat}
    {t : Time} {c : Cut A} (hg : tr.TickAt dg y j t) (hc : tr.CallAt y k c) (hk : k < j)
    (ht : tr.time k = t) : ∃ ℓ : ACLabel A, c = .ac ℓ ∧ ℓ.call = .restart := by
  obtain ⟨j', e, m, hg', rfl, hm⟩ := call_in_group h hy hc
  obtain ⟨x, hg⟩ := hg
  rw [ht] at hg' hm
  have hph := h.phase_order y hy y hy j' j t e (.tick x) hg' hg (by omega)
  cases e with
  | tick x' => exact absurd (h.tick_unique y hy j' j t ⟨x', hg'⟩ ⟨x, hg⟩) (by omega)
  | restart =>
    rcases m with _ | m <;> simp [exec, restart, acCall] at hm
    exact ⟨_, hm.symm, rfl⟩
  | _ => simp [Event.phase] at hph

/-- **The FG cuts of a node at the time of its `fg_attest` and before it are its own
proposal's** (the tick's proposal step). -/
theorem fg_before_attest (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {i j : Nat}
    {ℓ : FGLabel P A.Payload} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hc : tr.CallAt y j (.fg (.attest C s))) (hi : tr.CallAt y i (.fg ℓ)) (hij : i < j)
    (ht : tr.time i = tr.time j) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.time j := by
  obtain ⟨j₀, e, k₂, hg, rfl, hk₂⟩ := call_in_group h hy hc
  obtain ⟨x, rfl⟩ := exec_attest dg y _ _ e (List.mem_of_getElem? hk₂)
  by_cases hlt : i < j₀
  · obtain ⟨ℓ', he, -⟩ := before_tick h hy ⟨x, hg⟩ hi hlt ht
    cases he
  have hlen := (List.getElem?_eq_some_iff.1 hk₂).1
  obtain ⟨hn, -, -, -, hl⟩ := hg.2.1 (i - j₀) (by omega)
  rw [Nat.add_sub_cancel' (not_lt.1 hlt), hi.2] at hl
  exact tick_before_attest dg y _ _ x (m := i - j₀)
    (by rw [List.getElem?_eq_getElem (by omega), ← hl]) hk₂ (by omega)

/-- **An accepted block in a restart or a tick is the node's own proposal of that time.** -/
theorem accept_in_tick (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j₀ k : Nat}
    {t : Time} {e : Event A} (hg : tr.GroupAt dg y j₀ t e) (he : e.phase ≤ 1) (hk : j₀ ≤ k)
    (hk' : k < j₀ + (exec dg y (tr.state y j₀) t e).2.length) {B : A.Blk}
    (hc : tr.CallAt y k (.fg (.block B true))) : B.proposer = y ∧ P.slotTime B.slot = t := by
  have htk : tr.time k = t := by
    have := (hg.2.1 (k - j₀) (by omega)).2.1
    rwa [Nat.add_sub_cancel' hk] at this
  rcases blockCall_cases h hy hc with hd | ⟨j, x, -, -, hp, d, p, -, rfl, -⟩
  · obtain rfl := group_start hg hd hk hk'
    have := group_phase hg hd
    rw [this] at he
    simp [Event.phase] at he
  · exact ⟨rfl, htk ▸ hp.2.1.symm⟩

end Consensus.Goldilocks.Compose

end
