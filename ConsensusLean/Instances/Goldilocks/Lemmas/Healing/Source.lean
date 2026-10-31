module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks Healing: a source is attested in the same tick

The forward half of `Compose.attest_source`: an honest node's `ac_to_fg` cut is the FG update's
first cut (no other handler calls `ac_to_fg`), so when it returns a source `C`, the next cut is
the update's `fg_attest(C)`, at the same time and the same FG state (an AC cut changes only `𝒜`).
`HS.4`'s current-source arm is read through it (`historical_source_rows`). -/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P}
variable (proposer : Nat → Fin P.n)

/-- Only the FG update calls `ac_to_fg`: the AC's tick and the proposal step do not. -/
private theorem toFG_not_mem (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {ℓ : ACLabel A} (hc : ℓ.call = .toFG)
    (h : Cut.ac ℓ ∈ (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2) :
    False := by
  rcases List.mem_append.1 h with h | h
  · simp only [tickStep, acCall, List.mem_singleton, Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  · revert h
    simp only [tickStep]
    split_ifs
    · split
      · simp only [acProposal, List.mem_singleton, Cut.ac.injEq]
        rintro rfl
        cases hc
      · simp only [proposeBlock, onBlock]
        split_ifs
        · intro h
          simp only [acProposal, acCall, List.mem_cons, Cut.ac.injEq, List.not_mem_nil,
            or_false] at h
          subst h
          cases hc
        · split
          · intro h
            simp only [acProposal, acCall, List.mem_cons, Cut.ac.injEq, reduceCtorEq,
              List.not_mem_nil, or_false] at h
            subst h
            cases hc
          · intro h
            simp only [acProposal, acCall, List.mem_cons, Cut.ac.injEq, reduceCtorEq,
              List.not_mem_nil, or_false, false_or] at h
            rcases h with rfl | rfl <;> cases hc
    · simp

/-- **The cut after an `ac_to_fg` cut of a handler is its `fg_attest`** of the returned source:
the `ac_to_fg` cut is the FG update's first, at the state `st₁` its cuts start from. -/
private theorem toFG_next (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {ℓ : ACLabel A}
    (hk : (exec proposer dg y st t e).2[k]? = some (.ac ℓ)) (hc : ℓ.call = .toFG) :
    ∃ st₁, CutChain y t st ((exec proposer dg y st t e).2.take k) st₁ ∧ ℓ.frame = frame st₁ ∧
      ∀ C, (A.toFG st₁.ac (frame st₁) t).2.1 = some C →
        ∃ s, (exec proposer dg y st t e).2[k + 1]? = some (.fg (.attest C s)) := by
  cases e with
  | block B =>
    have h := List.mem_of_getElem? hk
    simp only [exec, onBlock, acCall] at h
    split_ifs at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.mem_cons, reduceCtorEq, Cut.ac.injEq, false_or] at h
        rcases h with h | h
        · rw [h] at hc
          cases hc
        · simp at h
  | message m =>
    have h := List.mem_of_getElem? hk
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  | attestation a =>
    have h := List.mem_of_getElem? hk
    simp [exec, onAttestation] at h
  | restart =>
    have h := List.mem_of_getElem? hk
    simp only [exec, restart, acCall, List.mem_singleton, Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  | tick x =>
    have hcuts : (exec proposer dg y st t (.tick x)).2 =
        (tickStep proposer dg y st t x .acTick).2 ++
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
        (tickStep proposer dg y
          (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
          t x .fgUpdate).2 := by
      simp [exec, onTick, runSteps, tickSteps]
    rw [hcuts] at hk ⊢
    set l := (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 with hl
    set st₁ := (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
    have hch : CutChain y t st l st₁ :=
      Compose.chain_append y (Compose.tickStep_chain proposer dg y st t x _)
        (Compose.tickStep_chain proposer dg y _ t x _)
    have hn : l.length ≤ k := by
      by_contra hlt
      rw [List.getElem?_append_left (by omega)] at hk
      exact toFG_not_mem proposer dg y st t x hc (List.mem_of_getElem? hk)
    rw [List.getElem?_append_right hn] at hk
    rw [List.getElem?_append_right (by omega)]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_sub_cancel_left] at hk
    rw [show l.length + m + 1 - l.length = m + 1 by omega]
    simp only [tickStep, acToFG] at hk ⊢
    -- the update's first cut is the `ac_to_fg` cut; its later cuts are FG cuts
    have hm : m = 0 := by
      split at hk
      · rcases m with _ | m <;> simp_all
      · simp only [attest] at hk
        split at hk
        · rcases m with _ | _ | m <;> simp_all
        · rcases m with _ | _ | _ | m <;> simp_all [onAttestation]
    subst hm
    refine ⟨st₁, by rw [Nat.add_zero, List.take_left' rfl]; exact hch, ?_, fun C hC => ?_⟩
    · split at hk
      all_goals
        simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
        subst hk
        rfl
    · rw [hC]
      simp only [attest]
      split <;> simp

variable {proposer} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- **An honest `ac_to_fg` cut that returns `C` is followed by `fg_attest(C)`**, at the same
time, with the FG state unchanged. -/
theorem toFG_attest (h : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel A} {C : A.Blk} (hk : tr.CallAt y k (.ac ℓ)) (hc : ℓ.call = .toFG)
    (hC : (A.toFG (tr.state y k).ac ℓ.frame (tr.time k)).2.1 = some C) :
    ∃ s, tr.CallAt y (k + 1) (.fg (.attest C s)) ∧ tr.time (k + 1) = tr.time k ∧
      (tr.state y (k + 1)).fg = (tr.state y k).fg := by
  obtain ⟨j₀, e, k', hg, rfl, hk'⟩ := Compose.call_in_group h hy hk
  obtain ⟨st₁, hch, hfr, hnext⟩ := toFG_next proposer dg y _ _ e hk' hc
  have hlen := (List.getElem?_eq_some_iff.1 hk').1
  have hst : tr.state y (j₀ + k') = st₁ := by
    have := Compose.cutChain_run h hy hch j₀ rfl fun m hm => by
      rw [List.length_take] at hm
      obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 m (by omega)
      exact ⟨hn, ht, by rw [hl, List.getElem_take]⟩
    rwa [List.length_take, min_eq_left hlen.le] at this
  rw [hst, hfr] at hC
  obtain ⟨s, hs⟩ := hnext C hC
  obtain ⟨hs', hc'⟩ := List.getElem?_eq_some_iff.1 hs
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 (k' + 1) hs'
  obtain ⟨-, ht₀, -, -, -⟩ := hg.2.1 k' hlen
  refine ⟨s, ⟨by rw [← add_assoc] at hn; exact hn, ?_⟩, by rw [← add_assoc] at ht; rw [ht, ht₀],
    ?_⟩
  · rw [← add_assoc] at hl
    rw [hl, hc']
  · rw [tr.state_succ_of_call hk]
    exact (h.cutLaw y hy _ _ hk).2.2.1

end Consensus.Goldilocks.Healing

end
