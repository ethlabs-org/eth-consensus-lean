module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live

public section

/-! # Goldilocks Healing: fresh honest records (r14 s5, N0⁺; WI-18)

consensus-lean#135, WI-18; workbench `notes/fg-liveness/r14-end-to-end/s5-justify.md` §2,
Lemma N0⁺. From the record half of the Healed bundle (`HealedRecords`: C2*⁺ (i) rows and
(ii) locks from a height `h₀` on) and the client rules, at every height `h ≥ h₀` and every cut,
every honest record has

* `Λ.target[h] ∈ {⊥, E h}` (`HealedRecords.target_entry`: a target is an own row, C2*⁺ (i));
* `Λ.timeout[h] = ∅` (`HealedRecords.timeout_empty`: first-timeout induction);
* `permits(Λ, h, E h)` (`HealedRecords.permits_entry`, with the lock of C2*⁺ (ii)).

So every honest row at `h ≥ h₀` is a target (`HealedRecords.sign_target`), and
`create_attestation` on the entry state of `E h` sends the target row
(`HealedRecords.createAtt_target`, the premises of `FG.Record.createAtt_target`). The fourth
premise of `FG.Record.createAtt_target`, "nothing sent at `h`", stays explicit there: it is
false after the first own row at `h` (then `create_attestation` returns `⊥`), and
`sign_target` does not need it. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g : Time} {h₀ : Nat}
  {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}

/-- `create_attestation` signs `(h, T_h)` of its input and records it; a timeout only on a
recorded timeout or another target at that height. -/
private theorem createAtt_timeout {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
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

/-- An honest record changes only when the node signs, by recording the signed attestation. -/
private theorem record_step (hrun : GoldilocksRun proposer dg H tr)
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
      · exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ (createAtt_timeout hlaw.1).2.2.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- **N0⁺, targets.** At a height `h ≥ h₀`, an honest record's target is `⊥` or the entry
`E h`: a recorded target is an own earlier row at `h`, which names `E h` (C2*⁺ (i)). -/
theorem HealedRecords.target_entry (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) (i h : Nat)
    (hh : h₀ ≤ h) :
    (tr.state y i).record.target h = none ∨ (tr.state y i).record.target h = some (E h).root := by
  rcases ht : (tr.state y i).record.target h with _ | r
  · exact Or.inl rfl
  · obtain ⟨k, -, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hrun hy h r i).1 (Or.inl ht)
    refine Or.inr (congrArg some ?_)
    rw [← har, hR.rows y hy k att hs (hah ▸ hh), hah]

/-- With no timeout recorded at its height `≥ h₀`, an honest row is a target. -/
private theorem HealedRecords.sign_target_of (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : h₀ ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hah, haT, -, hτ⟩ := createAtt_timeout hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · rcases hR.target_entry hrun hy k att.h hh with h0 | h1
    · rw [h0] at hT'
      cases hT'
    · rw [h1] at hT'
      obtain rfl := Option.some.inj hT'
      exact hne (hR.rows y hy k att ⟨src, hc⟩ hh).symm

/-- **N0⁺, timeouts.** At a height `h ≥ h₀`, every honest timeout set stays empty
(first-timeout induction: the first timeout row would need another target at `h`). -/
theorem HealedRecords.timeout_empty (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i h, h₀ ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, h, _ => by
    rw [Trace.state, hrun.init y hy]
    rfl
  | i + 1, h, hh => by
    rcases record_step hrun hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact hR.timeout_empty hrun hy i h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := hR.sign_target_of hrun hy hs hh (hR.timeout_empty hrun hy i _ hh)
          simp_all
        · exact hR.timeout_empty hrun hy i h hh
      · exact hR.timeout_empty hrun hy i h hh

/-- **N0⁺, rows.** Every honest row at a height `≥ h₀` is a target (`timeout = false`). -/
theorem HealedRecords.sign_target (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : h₀ ≤ att.h) : att.timeout = false :=
  hR.sign_target_of hrun hy hs hh (hR.timeout_empty hrun hy k _ hh)

/-- **N0⁺, permits.** At a height `h ≥ h₀`, every honest record permits the entry `E h` at
every cut (R0 at every such height). -/
theorem HealedRecords.permits_entry (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) (i h : Nat)
    (hh : h₀ ≤ h) : (tr.state y i).record.permits h (E h).root :=
  ⟨hR.target_entry hrun hy i h hh,
    by rw [hR.timeout_empty hrun hy i h hh]; exact Finset.empty_subset _, hR.locks y hy i h hh⟩

/-- **N0⁺ for `create_attestation`.** On a state `σe` with height `h ≥ h₀` and entry `E h`, an
honest record that has sent nothing at `h` sends the target row of `σe`
(`FG.Record.createAtt_target`). The "nothing sent" premise stays: after an own row at `h`,
`create_attestation` returns `⊥`. -/
theorem HealedRecords.createAtt_target (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {σe : FG.ChainState sp.n} (hh : h₀ ≤ σe.h) (hT : σe.Th = (E σe.h).root)
    (hs : ∀ b ∈ (tr.state y i).record.sent, b.1 ≠ σe.h) :
    (tr.state y i).record.createAtt y σe =
      some (⟨y, σe.h, σe.Th, false, (tr.state y i).record.finalityPair σe⟩,
        (tr.state y i).record.recordAtt
          ⟨y, σe.h, σe.Th, false, (tr.state y i).record.finalityPair σe⟩) :=
  FG.Record.createAtt_target (by rw [hT]; exact hR.locks y hy i _ hh)
    (hR.timeout_empty hrun hy i _ hh) (by rw [hT]; exact hR.target_entry hrun hy i _ hh) hs

/-- **Nothing sent at `h` before the first own row at `h`.** If an honest `y` signs no row of
height `h` at any cut before `k`, its record at cut `k` has sent nothing at `h` (the record
changes only by recording a signed attestation, `record_step`). -/
theorem sent_ne_of_no_sign (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {h : Nat} : ∀ k, (∀ k' < k, ∀ att, tr.SignAt y k' att → att.h ≠ h) →
      ∀ b ∈ (tr.state y k).record.sent, b.1 ≠ h
  | 0, _ => by
    rw [Trace.state, hrun.init y hy]
    intro b hb
    cases hb
  | k + 1, hn => by
    have ih := sent_ne_of_no_sign hrun hy k fun k' hk' => hn k' (by omega)
    rcases record_step hrun hy k with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact ih
    · intro b hb
      simp only [FG.Record.recordAtt, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact ih b hb
      · exact hn k (by omega) att hs

/-- **The first own row at a height `≥ h₀` is the target row of its entry state.** Under
`HealedRecords`, if an honest `y` signs `att` at cut `k` with `h₀ ≤ att.h` and signs no row of
height `att.h` before `k`, then `att` is `(y, σe.h, σe.T_h, target, Λ.finality_pair(σe))` for the
entry state `σe` of its source and the record `Λ` of `y` at cut `k`. -/
theorem HealedRecords.first_sign_target (hR : HealedRecords tr H g h₀ E)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : h₀ ≤ att.h)
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
  obtain ⟨hah, haT, -, -⟩ := createAtt_timeout hcl
  have hT := hR.rows y hy k att ⟨src, hc⟩ hh
  have ha := hR.createAtt_target hrun hy k (by rw [← hah]; exact hh)
    (by rw [← haT, hT, hah]) (by rw [← hah]; exact sent_ne_of_no_sign hrun hy k hfirst)
  rw [ha] at hcl
  exact ⟨src, hc, (congrArg Prod.fst (Option.some.inj hcl)).symm⟩

end Consensus.Goldilocks.Healing

end
