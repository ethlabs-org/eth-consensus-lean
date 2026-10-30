module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks runs: reads between AC calls

The confirmed output and the head read the AC state `𝒜` and the frame `fg_to_ac(Σ)`, and the
frame reads only the tree and the finality caches of `Σ`, not its pool. Of the FG cuts,
`fg_on_attestation` changes only the pool, `fg_attest` only the record, and a refused
`fg_on_block` nothing; an accepted `fg_on_block` is followed in its event by its `ac_on_block`
(`accept_next`, at a position `≠ 0`, `accept_next_pos`). So at a point between two events of an
honest node (cut `j` is not a later cut of an event of the node), its AC state and frame are those
after its last AC call before `j` (with that call's frame), or the initial ones when it has made
none (`read_between_calls`; the mapping's "Reads between AC calls", consensus-lean#91). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- **A quiet stretch keeps the reads**: when no cut of an honest `y` in `[k, j)` is an AC cut
or an accepted block, its AC state and its frame before `j` are those before `k`. -/
theorem state_quiet (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {k j : Nat}
    (hkj : k ≤ j)
    (hq : ∀ m, k ≤ m → m < j → ∀ c, tr.CallAt y m c →
      (∀ ℓ, c ≠ .ac ℓ) ∧ ∀ B, c ≠ .fg (.block B true)) :
    (tr.state y j).ac = (tr.state y k).ac ∧ frame (tr.state y j) = frame (tr.state y k) := by
  induction j, hkj using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ j hkj ih =>
    obtain ⟨iha, ihf⟩ := ih fun m h₁ h₂ => hq m h₁ (h₂.trans (Nat.lt_succ_self j))
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      obtain ⟨hna, hnb⟩ := hq j hkj (Nat.lt_succ_self j) c hc
      have hlaw := h.cutLaw y hy j c hc
      rw [tr.state_succ_of_call hc]
      refine (show (tr.post j).ac = (tr.state y j).ac ∧
          frame (tr.post j) = frame (tr.state y j) from ?_).imp (·.trans iha) (·.trans ihf)
      cases c with
      | ac ℓ => exact absurd rfl (hna ℓ)
      | fg ℓ =>
        cases ℓ with
        | block B acc =>
          cases acc with
          | true => exact absurd rfl (hnb B)
          | false => rw [hlaw.2]; exact ⟨rfl, rfl⟩
        | attestation a =>
          obtain ⟨atts, he⟩ := (tr.state y j).fg.onAttestation_eq a
          refine ⟨hlaw.2.1, ?_⟩
          unfold frame
          rw [hlaw.1, he]
          rfl
        | attest C s =>
          cases s with
          | none => rw [hlaw.2]; exact ⟨rfl, rfl⟩
          | some a =>
            refine ⟨hlaw.2.2, ?_⟩
            unfold frame
            rw [hlaw.2.1]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact ⟨iha, ihf⟩

/-- **Reads between AC calls.** At a cut `j` of a run between two events of an honest `y` (cut
`j` is not a later cut of an event of `y`): either `y` made no AC call before `j` and its AC state
and frame are those of its initial state, or its last AC call before `j` is at `k`, with label
`ℓ`, and its AC state before `j` is the one that call leaves, and its frame is that call's frame
`ℓ.frame`. -/
theorem read_between_calls (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    (hb : tr.IsCall y j → tr.pos j = 0) :
    ((∀ k < j, ∀ ℓ, ¬ tr.CallAt y k (.ac ℓ)) ∧ (tr.state y j).ac = (tr.state y 0).ac ∧
        frame (tr.state y j) = frame (tr.state y 0)) ∨
      ∃ k < j, ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ) ∧
        (∀ m, k < m → m < j → ∀ ℓ', ¬ tr.CallAt y m (.ac ℓ')) ∧
        (tr.state y j).ac = (tr.state y (k + 1)).ac ∧ frame (tr.state y j) = ℓ.frame := by
  -- an accepted block before `j` after the last AC call is impossible
  have quiet : ∀ k₀, k₀ ≤ j → (∀ m, k₀ ≤ m → m < j → ∀ ℓ, ¬ tr.CallAt y m (.ac ℓ)) →
      ∀ m, k₀ ≤ m → m < j → ∀ c, tr.CallAt y m c →
        (∀ ℓ, c ≠ .ac ℓ) ∧ ∀ B, c ≠ .fg (.block B true) := by
    intro k₀ _ hn m h₁ h₂ c hc
    refine ⟨fun ℓ he => hn m h₁ h₂ ℓ (he ▸ hc), fun B he => ?_⟩
    subst he
    obtain ⟨ℓ, hc', -, -⟩ := accept_next h hy hc
    rcases Nat.lt_or_ge (m + 1) j with hlt | hge
    · exact hn (m + 1) (by omega) hlt ℓ hc'
    · obtain rfl : j = m + 1 := by omega
      exact accept_next_pos h hy hc (hb ⟨_, hc'⟩)
  by_cases hex : ∃ k < j, ∃ ℓ, tr.CallAt y k (.ac ℓ)
  · -- the last AC call before `j`
    classical
    let k := Nat.findGreatest (fun k => ∃ ℓ, tr.CallAt y k (.ac ℓ)) (j - 1)
    obtain ⟨k₀, hk₀, hk₀c⟩ := hex
    have hkspec : ∃ ℓ, tr.CallAt y k (.ac ℓ) :=
      Nat.findGreatest_spec (P := fun k => ∃ ℓ, tr.CallAt y k (.ac ℓ)) (by omega : k₀ ≤ j - 1)
        hk₀c
    have hkle : k ≤ j - 1 := Nat.findGreatest_le _
    have hk₀k : k₀ ≤ k := Nat.le_findGreatest (by omega) hk₀c
    obtain ⟨ℓ, hcl⟩ := hkspec
    have hlast : ∀ m, k < m → m < j → ∀ ℓ', ¬ tr.CallAt y m (.ac ℓ') := fun m h₁ h₂ ℓ' hm =>
      Nat.findGreatest_is_greatest h₁ (by omega) ⟨ℓ', hm⟩
    have hkj : k < j := by omega
    obtain ⟨hac, hfr⟩ := state_quiet h hy hkj (quiet (k + 1) hkj fun m h₁ h₂ => hlast m h₁ h₂)
    have hlaw := h.cutLaw y hy k _ hcl
    refine Or.inr ⟨k, hkj, ℓ, hcl, hlast, hac, hfr.trans ?_⟩
    rw [tr.state_succ_of_call hcl, hlaw.1]
    unfold frame
    rw [hlaw.2.2.1]
  · push Not at hex
    have hn : ∀ m, 0 ≤ m → m < j → ∀ ℓ, ¬ tr.CallAt y m (.ac ℓ) := fun m _ hm => hex m hm
    exact Or.inl ⟨fun k hk => hex k hk, state_quiet h hy (Nat.zero_le j)
      (quiet 0 (Nat.zero_le j) hn)⟩

end Consensus.Goldilocks.Compose

end
