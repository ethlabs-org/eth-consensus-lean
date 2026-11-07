module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix

public section

/-! # Uniqueness of a signing within one honest client prefix -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

private theorem createAtt_spec {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ Λ' = Λ.recordAtt a ∧ ∀ b ∈ Λ.sent, ¬ (b.1 = a.h ∧ b.2.1 = a.T) := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h with hany
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun b hb hb' => hany ?_⟩
    rw [List.any_eq_true]
    exact ⟨b, hb, by simp [hb'.1, hb'.2]⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem sent_succ (hrun : GoldilocksRun proposer dg H tr)
    {v : Fin sp.n} (hv : v ∈ H)
    (c : Nat) {b : FG.Content} (hb : b ∈ (tr.state v c).record.sent) :
    b ∈ (tr.state v (c + 1)).record.sent := by
  by_cases hc : ∃ cut, tr.CallAt v c cut
  · obtain ⟨cut, hc⟩ := hc
    have hlaw := hrun.cutLaw v hv c cut hc
    rw [tr.state_succ_of_call hc]
    cases cut with
    | ac ell => rw [hlaw.2.2.2]; exact hb
    | fg ell =>
      cases ell with
      | block B acc =>
        cases acc with
        | true => rw [hlaw.2.2.2]; exact hb
        | false => rw [hlaw.2]; exact hb
      | attestation a' => rw [hlaw.2.2]; exact hb
      | attest C s =>
        cases s with
        | none => rw [hlaw.2]; exact hb
        | some a' =>
          rw [(createAtt_spec hlaw.1).2.1]
          exact List.mem_append_left _ hb
  · rw [tr.state_succ_of_not fun cut hc' => hc ⟨cut, hc'⟩]
    exact hb

/-- A client executing honestly throughout a prefix signs an attestation at most once. -/
theorem sign_unique (hrun : GoldilocksRun proposer dg H tr)
    {v : Fin sp.n} (hv : v ∈ H)
    {d d' : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hs' : tr.SignAt v d' att) :
    d = d' := by
  have key : ∀ {d d'}, tr.SignAt v d att → tr.SignAt v d' att → d < d' → False := by
    intro d d' hs hs' hlt
    obtain ⟨C, hc⟩ := hs
    obtain ⟨C', hc'⟩ := hs'
    have h₀ : att.content ∈ (tr.state v (d + 1)).record.sent := by
      rw [tr.state_succ_of_call hc, (createAtt_spec (hrun.cutLaw v hv d _ hc).1).2.1]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hmem : ∀ c, d + 1 ≤ c → att.content ∈ (tr.state v c).record.sent := by
      intro c hc
      induction c, hc using Nat.le_induction with
      | base => exact h₀
      | succ c _ ih => exact sent_succ hrun hv c ih
    exact (createAtt_spec (hrun.cutLaw v hv d' _ hc').1).2.2 _ (hmem d' hlt) ⟨rfl, rfl⟩
  rcases lt_trichotomy d d' with h | h | h
  · exact (key hs hs' h).elim
  · exact h
  · exact (key hs' hs h).elim

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
