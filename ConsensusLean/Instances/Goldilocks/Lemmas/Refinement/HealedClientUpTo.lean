module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.HealedClient

public section

/-! # Goldilocks Refinement: fresh honest records through a finite horizon (N0⁺, #137)

consensus-lean#137 (finite-horizon port). The N0⁺ lemmas of `Healing.Outcome.HealedClient` from
`HealedRecordsUpTo … b`: every conclusion is at a cut `i` with `t_i ≤ b`. The proofs use only
rows signed before that cut (so by `b`) and the lock at that cut. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g b : Time} {h₀ : Nat}
  {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}

/-- `create_attestation` signs `(h, T_h)` of its input and records it; a timeout only on a
recorded timeout or another target at that height (copy of the private `HealedClient` lemma). -/
private theorem createAtt_timeout' {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
    {σe : FG.ChainState n} {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.h = σe.h ∧ a.T = σe.Th ∧ Λ' = Λ.recordAtt a ∧
      (a.timeout = true → Λ.timeout σe.h ≠ ∅ ∨ ∃ T', Λ.target σe.h = some T' ∧ T' ≠ σe.Th) := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · cases h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := Store.heightPair_eq hp
  refine ⟨rfl, rfl, rfl, fun hτ => ?_⟩
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  · exact Or.inl h2
  · simp_all
  · push Not at h3
    obtain ⟨T'', hT''⟩ := Option.ne_none_iff_exists'.1 h3.1
    exact Or.inr ⟨T'', hT'', fun e => h3.2 (hT''.trans (by rw [e]))⟩

/-- An honest record changes only when the node signs (copy of the private lemma). -/
private theorem record_step' (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ att, tr.SignAt y i att ∧
        (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt att := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    have hsucc := tr.state_succ_of_call hc
    cases c with
    | ac ℓ => exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
    | fg ℓ =>
      rcases ℓ with ⟨B, _ | _⟩ | a' | ⟨C, _ | a'⟩
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2)
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ (createAtt_timeout' hlaw.1).2.2.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- **N0⁺, targets, through the horizon.** At a cut `i` with `t_i ≤ b` and a height `h ≥ h₀`,
an honest record's target is `⊥` or the entry `E h`. -/
theorem HealedRecordsUpTo.target_entry (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hib : tr.time i ≤ b) (h : Nat) (hh : h₀ ≤ h) :
    (tr.state y i).record.target h = none ∨ (tr.state y i).record.target h = some (E h).root := by
  rcases ht : (tr.state y i).record.target h with _ | r
  · exact Or.inl rfl
  · obtain ⟨k, hki, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hrun hy h r i).1 (Or.inl ht)
    refine Or.inr (congrArg some ?_)
    rw [← har, hR.rows y hy k att hs ((hrun.time_mono hki.le).trans hib) (hah ▸ hh), hah]

/-- With no timeout recorded at its height `≥ h₀`, an honest row signed by `b` is a target. -/
private theorem HealedRecordsUpTo.sign_target_of (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : h₀ ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hah, haT, -, hτ⟩ := createAtt_timeout' hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · rcases hR.target_entry hrun hy hkb att.h hh with h0 | h1
    · rw [h0] at hT'
      cases hT'
    · rw [h1] at hT'
      obtain rfl := Option.some.inj hT'
      exact hne (hR.rows y hy k att ⟨src, hc⟩ hkb hh).symm

/-- **N0⁺, timeouts, through the horizon.** At a cut `i` with `t_i ≤ b` and a height `h ≥ h₀`,
every honest timeout set is empty. -/
theorem HealedRecordsUpTo.timeout_empty (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i h, tr.time i ≤ b → h₀ ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, h, _, _ => by
    rw [Trace.state, hrun.init y hy]
    rfl
  | i + 1, h, hib, hh => by
    have hib' : tr.time i ≤ b := (hrun.time_mono (Nat.le_succ i)).trans hib
    rcases record_step' hrun hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact hR.timeout_empty hrun hy i h hib' hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := hR.sign_target_of hrun hy hs hib' hh
            (hR.timeout_empty hrun hy i _ hib' hh)
          simp_all
        · exact hR.timeout_empty hrun hy i h hib' hh
      · exact hR.timeout_empty hrun hy i h hib' hh

/-- **N0⁺, rows, through the horizon.** Every honest row signed by `b` at a height `≥ h₀` is a
target. -/
theorem HealedRecordsUpTo.sign_target (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : h₀ ≤ att.h) :
    att.timeout = false :=
  hR.sign_target_of hrun hy hs hkb hh (hR.timeout_empty hrun hy k _ hkb hh)

/-- **N0⁺, permits, through the horizon.** At a cut `i` with `t_i ≤ b` and a height `h ≥ h₀`,
every honest record permits the entry `E h`. -/
theorem HealedRecordsUpTo.permits_entry (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hib : tr.time i ≤ b) (h : Nat) (hh : h₀ ≤ h) :
    (tr.state y i).record.permits h (E h).root :=
  ⟨hR.target_entry hrun hy hib h hh,
    by rw [hR.timeout_empty hrun hy i h hib hh]; exact Finset.empty_subset _,
    hR.locks y hy i h hib hh⟩

/-- **N0⁺ for `create_attestation`, through the horizon** (`HealedRecords.createAtt_target` at
a cut `i` with `t_i ≤ b`). -/
theorem HealedRecordsUpTo.createAtt_target (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hib : tr.time i ≤ b)
    {σe : FG.ChainState sp.n} (hh : h₀ ≤ σe.h) (hT : σe.Th = (E σe.h).root)
    (hs : ∀ b ∈ (tr.state y i).record.sent, b.1 ≠ σe.h) :
    (tr.state y i).record.createAtt y σe =
      some (⟨y, σe.h, σe.Th, false, (tr.state y i).record.finalityPair σe⟩,
        (tr.state y i).record.recordAtt
          ⟨y, σe.h, σe.Th, false, (tr.state y i).record.finalityPair σe⟩) :=
  FG.Record.createAtt_target (by rw [hT]; exact hR.locks y hy i _ hib hh)
    (hR.timeout_empty hrun hy i _ hib hh) (by rw [hT]; exact hR.target_entry hrun hy hib _ hh) hs

/-- **The first own row at a height `≥ h₀`, through the horizon**
(`HealedRecords.first_sign_target` for a row signed at a cut `k` with `t_k ≤ b`). -/
theorem HealedRecordsUpTo.first_sign_target (hR : HealedRecordsUpTo tr H g b h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : h₀ ≤ att.h)
    (hfirst : ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ att.h) :
    ∃ src, tr.CallAt y k (.fg (.attest src (some att))) ∧
      att = ⟨y, ((tr.state y k).fg.σ ((tr.state y k).fg.σ src.root).Th).h,
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ src.root).Th).Th, false,
        (tr.state y k).record.finalityPair
          ((tr.state y k).fg.σ ((tr.state y k).fg.σ src.root).Th)⟩ := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hah, haT, -, -⟩ := createAtt_timeout' hcl
  have hT := hR.rows y hy k att ⟨src, hc⟩ hkb hh
  have ha := hR.createAtt_target hrun hy hkb (by rw [← hah]; exact hh)
    (by rw [← haT, hT, hah]) (by rw [← hah]; exact sent_ne_of_no_sign hrun hy k hfirst)
  rw [ha] at hcl
  exact ⟨src, hc, (congrArg Prod.fst (Option.some.inj hcl)).symm⟩

end Consensus.Goldilocks.Healing

end
