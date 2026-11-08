module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # The votes an honest proposal carries

On an AC trace with the unlock given at any write mode (`ACLocalRunU wm u`) whose honest signers
are unforgeable (`HonestObjects`), the payload an honest node's `ac_proposal` returns carries at
most `|H| + 2·|Hᶜ|` distinct votes (`carried_votes_le`): the payload is read off the pool of the
previous slot (both its lists), the pool keeps at most two distinct votes per validator and slot
(`pool_capU`), and the pooled votes of an honest validator of one slot are its one emitted vote of
that slot (`HonestObjects.pool_vote`, `one_vote_per_slotU`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {wm : WriteMode}
  {u : Nat → Set Lock} {proposer : Nat → Fin sp.n} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- The payload `ac_proposal` returns is read off the pool of the previous slot. -/
private theorem mem_pool_of_proposal {L : Set Lock} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hp : (acProposalWith sp L A Φ t).2 = some (d, pay)) {v : Vote sp.n}
    (hv : v ∈ pay.1 ∨ v ∈ pay.2) : v ∈ A.poolAt ((sp.slot t : Int) - 1) := by
  unfold acProposalWith at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  unfold voteViewList at hv
  simp only [List.mem_filter] at hv
  rcases hv with ⟨hv, -⟩ | ⟨⟨hv, -⟩, -⟩ <;> exact hv

/-- The distinct votes of one pool of an honest node's state: at most one per honest validator,
at most two per other validator. -/
private theorem pool_card_le (h : ACLocalRunU wm u H U tr) (hobj : HonestObjects proposer tr H)
    {y : Fin sp.n} (hy : y ∈ H) (k σ : Nat) :
    ((tr.state y k).pool σ).toFinset.card ≤ H.ncard + 2 * Hᶜ.ncard := by
  classical
  set L := (tr.state y k).pool σ
  have hcap : (∀ x ∈ L, x.slot = σ) ∧
      ∀ i : Fin sp.n, (L.filter (fun x => x.val = i)).dedup.length ≤ 2 := by
    rcases state_reachableU sp h hy k with hinit | ⟨Φ, t, hr, -⟩
    · simp [L, hinit, SAState.initial]
    · exact pool_capU sp FGP ro y U h.coherent _ Φ t hr σ
  have hfib : ∀ i : Fin sp.n, (L.toFinset.filter (fun x => x.val = i)).card ≤
      if i ∈ H then 1 else 2 := by
    intro i
    have h2 : (L.toFinset.filter (fun x => x.val = i)).card ≤ 2 := by
      have he : L.toFinset.filter (fun x => x.val = i) =
          (L.filter (fun x => decide (x.val = i))).toFinset := by
        ext x
        simp
      rw [he, List.card_toFinset]
      exact hcap.2 i
    split_ifs with hi
    · refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [Finset.mem_filter, List.mem_toFinset] at ha hb
      obtain ⟨ja, -, ea, hva, hea⟩ := hobj.pool_vote y hy k σ a ha.1 (ha.2 ▸ hi)
      obtain ⟨jb, -, eb, hvb, heb⟩ := hobj.pool_vote y hy k σ b hb.1 (hb.2 ▸ hi)
      rw [ha.2] at hva
      rw [hb.2] at hvb
      have hs : ea.msg.slot = eb.msg.slot := by rw [hea, heb, hcap.1 a ha.1, hcap.1 b hb.1]
      obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr h i hi ja jb ea eb hva hvb hs
      exact hea.symm.trans heb
    · exact h2
  calc L.toFinset.card
      = ∑ i : Fin sp.n, (L.toFinset.filter (fun x => x.val = i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.val)
    _ ≤ ∑ i : Fin sp.n, (if i ∈ H then 1 else 2) := Finset.sum_le_sum fun i _ => hfib i
    _ = H.ncard + 2 * Hᶜ.ncard := by
        rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card', Finset.sum_ite]
        have e₁ : Finset.univ.filter (fun i => i ∈ H) = H.toFinset := by
          ext i
          simp
        have e₂ : Finset.univ.filter (fun i => i ∉ H) = Hᶜ.toFinset := by
          ext i
          simp
        rw [e₁, e₂, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        omega

/-- **An honest proposal carries at most `|H| + 2·|Hᶜ|` distinct votes.** -/
theorem carried_votes_le (h : ACLocalRunU wm u H U tr) (hobj : HonestObjects proposer tr H)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {L : Set Lock} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hp : (acProposalWith sp L (tr.state y k) Φ t).2 = some (d, pay)) :
    {v : Vote sp.n | v ∈ pay.1 ∨ v ∈ pay.2}.encard ≤ (H.ncard + 2 * Hᶜ.ncard : ℕ) := by
  classical
  have hsub := fun v (hv : v ∈ {v : Vote sp.n | v ∈ pay.1 ∨ v ∈ pay.2}) =>
    mem_pool_of_proposal hp hv
  unfold SAState.poolAt at hsub
  split_ifs at hsub with hneg
  · have : {v : Vote sp.n | v ∈ pay.1 ∨ v ∈ pay.2} = ∅ :=
      Set.eq_empty_of_forall_notMem fun v hv => by simpa using hsub v hv
    rw [this, Set.encard_empty]
    exact zero_le
  · set σ := ((sp.slot t : Int) - 1).toNat
    calc {v : Vote sp.n | v ∈ pay.1 ∨ v ∈ pay.2}.encard
        ≤ (((tr.state y k).pool σ).toFinset : Set (Vote sp.n)).encard :=
          Set.encard_le_encard fun v hv => by simpa using hsub v hv
      _ = (((tr.state y k).pool σ).toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
      _ ≤ _ := by exact_mod_cast pool_card_le h hobj hy k σ

end Consensus.Goldilocks.SA

end
