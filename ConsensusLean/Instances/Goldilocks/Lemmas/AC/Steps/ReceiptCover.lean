module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: a received block's votes are covered when the pool after the call is

Two steps of the writer-pool condition (A1.8 (d)) that read SA states and the schedule only. A
vote of a block received at `t`, of slot `slot(t) − 1` or `slot(t)`, is admitted by the receipt
or refused for two other votes of its validator, and the optimistic confirmation and the vote
attempt keep the pools: so a cover of the pool after the call (each vote held by a writer's state
`C` or making its validator an equivocator there) covers the vote (`receipt_vote_covered`). A
slot-`s` vote forwarded at a time `τ ∈ [t_s, t_s + 5Δ]` is admitted throughout `[τ, τ + Δ)`
(`slot_window_of_forward`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

private theorem mem_admitVote_pool {A : SAState sp.n} {t : Time} {v x : Vote sp.n} {σ : Nat}
    (h : x ∈ A.pool σ) : x ∈ (admitVote sp A t v).pool σ := by
  unfold admitVote
  split_ifs
  · exact h
  · exact h
  · simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.mem_append_left _ h
    · exact h

private theorem tryVote_pool {wm : WriteMode} {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (σ : Nat) :
    A.pool σ ⊆ (tryVoteWithM sp wm x L A Φ t).1.pool σ := by
  unfold tryVoteWithM
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  all_goals
    intro w hw
    rw [optimisticConfirmationM_keep _ optimistic_pool_eq]
    exact mem_admitVote_pool hw

private theorem foldl_admit_pool {t : Time} {σ : Nat} :
    ∀ (l : List (Vote sp.n)) (A : SAState sp.n),
      A.pool σ ⊆ (l.foldl (fun A v => admitVote sp A t v) A).pool σ
  | [], _ => List.Subset.refl _
  | _ :: l, _ => fun _ hw => foldl_admit_pool l _ (mem_admitVote_pool hw)

/-- The receipt of a block admits each of its votes of the slot of `t` or the previous one: the
node holds it after the receipt, or two other votes of its validator. -/
private theorem blockReceipt_held (A : SAState sp.n) {t : Time} {B : Blk sp.n FGP}
    {v : Vote sp.n} (hv : v ∈ blockVotes B) (h₁ : (sp.slot t : Int) - 1 ≤ v.slot)
    (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (blockReceipt sp A t B).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (blockReceipt sp A t B).pool v.slot} := by
  unfold blockReceipt
  generalize ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  generalize blockVotes B = l at hv
  induction l generalizing A' with
  | nil => simp at hv
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · have hs := foldl_admit_pool (t := t) (σ := v.slot) l (admitVote sp A' t v)
      rcases admitVote_held A' _ _ h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · exact Or.inl (hs h)
      · exact Or.inr ⟨a, hs ha, b, hs hb, hab, hav, hbv⟩
    · exact ih _ hv

/-- **A received block's vote is covered** by `C.pool s` (held there, or its validator an
equivocator there) when every slot-`s` vote of the state after the receipt at `t`, the
optimistic confirmation and the vote attempt of `x` is, and the vote's slot `s` is `slot(t) − 1`
or `slot(t)`. -/
theorem receipt_vote_covered {wm : WriteMode} {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) {t : Time} {B : Blk sp.n FGP} {v : Vote sp.n} {s : Nat}
    {C : SAState sp.n} (hvB : v ∈ blockVotes B) (hvs : v.slot = s)
    (h₁ : (sp.slot t : Int) - 1 ≤ s) (h₂ : s ≤ sp.slot t)
    (hw : ∀ w ∈ (tryVoteWithM sp wm x L (optimisticConfirmationM sp wm
        (blockReceipt sp A t B) Φ t) Φ t).1.pool s,
      w ∈ C.pool s ∨ w.val ∈ equivocators {u | u ∈ C.pool s}) :
    v ∈ C.pool s ∨ v.val ∈ equivocators {u | u ∈ C.pool s} := by
  have hsub : ∀ w ∈ (blockReceipt sp A t B).pool s, w ∈ (tryVoteWithM sp wm x L
      (optimisticConfirmationM sp wm (blockReceipt sp A t B) Φ t) Φ t).1.pool s := fun w hw =>
    tryVote_pool _ _ _ _ _ (by rw [optimisticConfirmationM_keep _ optimistic_pool_eq]; exact hw)
  subst hvs
  rcases blockReceipt_held A hvB h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact hw v (hsub v h)
  · rcases hw a (hsub a ha) with ha' | ha'
    · rcases hw b (hsub b hb) with hb' | hb'
      · exact Or.inr ⟨a, ha', b, hb', hab, hav, hbv⟩
      · exact Or.inr (hbv ▸ hb')
    · exact Or.inr (hav ▸ ha')

/-- A slot-`s` vote forwarded at a time `τ ∈ [t_s, t_s + 5Δ]` is of the slot of every time of
`[τ, τ + Δ)` or the previous one. -/
theorem slot_window_of_forward {s : Nat} {τ τ' : Time} (hτ : 0 ≤ τ) (hsτ : sp.ts s ≤ τ)
    (hττ' : τ ≤ τ') (hτ' : τ' ≤ sp.ts s + 5 * sp.Δ) :
    ∀ t, τ ≤ t → t < τ + sp.Δ → (sp.slot t : Int) - 1 ≤ s ∧ s ≤ sp.slot t := by
  intro t h₁ h₂
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : 0 ≤ t := hτ.trans h₁
  have ha := (ts_le_iff_le_slot sp ht s).1 (hsτ.trans h₁)
  have hb : ¬ ((s + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
    have h' := (ts_le_iff_le_slot sp ht _).2 h
    have h2 : sp.ts ((s + 2 : Nat) : Int) = sp.ts s + 8 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rw [h2] at h'; linarith only [h', h₂, hττ', hτ', hΔ]
  omega

end Consensus.Goldilocks.SA

end
