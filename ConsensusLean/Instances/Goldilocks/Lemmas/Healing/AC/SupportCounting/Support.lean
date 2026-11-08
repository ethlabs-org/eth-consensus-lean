module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.SupportCounting
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # Same-row support (proofs)

Paper `ae83bd82`, §7. Both counters count identities with a vote in the row-`j` pool of the
reader's state whose head extends the block in the reader's frame (`counted_pool`). An honest
identity's pool vote is its own emission (`HonestObjects.pool_vote`), of slot `j` (the pool-row
invariant at the mode, `state_pool_slotU`), with its head a block of the frame, hence of `U`
(`frameIn_of_callAtU`): `counted_honest_in_rowSupport`. One vote per slot at the mode
(`one_vote_per_slotU`) and injective roots in `U` give one head per honest identity and row, so
conflicting blocks have disjoint supports (`rowSupport_disjoint`). Counting the honest and faulty
parts gives `no_conflicting_half_origins`. The faulty part's pool provenance is
`pool_originU` (`counted_faulty_admitted`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- Both counters count identities with a row-`j` pool vote whose head extends the block. -/
private theorem counted_pool {A : SAState sp.n} {Φ : Frm sp.n FGP} {j : Nat} {X : Blk sp.n FGP}
    {κ : Counter} {x : Fin sp.n} (hx : x ∈ counted sp A Φ j X κ) :
    ∃ v ∈ A.pool j, v.val = x ∧ AncR Φ X v.head := by
  cases κ with
  | fast =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, hv.1, rfl, hv.2.2.2⟩
  | optimistic => exact hx

theorem counted_honest_in_rowSupport : CountedHonestInRowSupport := by
  intro sp FGP ro H U tr proposer m u hr hobj y hy i ℓ hc κ j X _ x ⟨hxc, hxH⟩
  obtain ⟨v, hv, rfl, R, hR, hRr, hXR⟩ := counted_pool hxc
  obtain ⟨k, -, e, he, hev⟩ := hobj.pool_vote y hy i j v hv hxH
  have hslot := state_pool_slotU sp hr hy i j v hv
  have hU := (frameIn_of_callAtU hr hy hc).2
  exact ⟨hxH, k, e, he, by rw [hev]; exact hslot, R, hU hR, by rw [hev]; exact hRr,
    hXR.mono hU⟩

theorem rowSupport_disjoint : RowSupportDisjoint := by
  intro sp FGP ro H U tr m u hr j X Y hX hY hXY hYX
  rw [Set.disjoint_left]
  rintro x ⟨hxH, i, e, he, hes, Hd, hHd, hHdr, hXHd⟩ ⟨-, i', e', he', hes', Hd', hHd', hHdr', hYHd'⟩
  obtain ⟨rfl, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr x hxH i i' e e' he he'
    (hes.trans hes'.symm)
  have hHH : Hd = Hd' := hr.coherent.1 hHd hHd' (hHdr.trans hHdr'.symm)
  subst hHH
  rcases anc_total hr.coherent hXHd hYHd' with h | h
  · exact hXY h
  · exact hYX h

theorem no_conflicting_half_origins : NoConflictingHalfOrigins := by
  intro sp FGP ro H U tr proposer m u h hr hobj hh y hy y' hy' i i' ℓ ℓ' hc hc' κ κ' j X Y hX hY
    hXY hYX hE hE' ⟨hn, hn'⟩
  have hUX := (frameIn_of_callAtU hr hy hc).2 hX
  have hUY := (frameIn_of_callAtU hr hy' hc').2 hY
  set E := counted sp (tr.state y i) ℓ.frame j X κ
  set E' := counted sp (tr.state y' i') ℓ'.frame j Y κ'
  have hsub : E ∩ H ⊆ rowSupport tr H U j X :=
    counted_honest_in_rowSupport sp FGP ro H U tr proposer m u hr hobj y hy i ℓ hc κ j X hX
  have hsub' : E' ∩ H ⊆ rowSupport tr H U j Y :=
    counted_honest_in_rowSupport sp FGP ro H U tr proposer m u hr hobj y' hy' i' ℓ' hc' κ' j Y hY
  have hdis := rowSupport_disjoint sp FGP ro H U tr m u hr j X Y hUX hUY hXY hYX
  have hQ : (rowSupport tr H U j X).ncard + (rowSupport tr H U j Y).ncard ≤ H.ncard := by
    rw [← Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _)]
    exact Set.ncard_le_ncard (Set.union_subset (fun x hx => hx.1) fun x hx => hx.1)
      (Set.toFinite _)
  have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard E H (Set.toFinite _)
  have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard E' H (Set.toFinite _)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 := Set.ncard_le_ncard hsub' (Set.toFinite _)
  have hn0 := Set.ncard_add_ncard_compl H
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hn0
  omega

theorem counted_faulty_admitted : CountedFaultyAdmitted := by
  intro sp FGP ro H U tr m u hr y hy i ℓ hc κ j X _ x hx
  obtain ⟨v, hv, rfl, -⟩ := counted_pool hx.1
  have hslot := state_pool_slotU sp hr hy i j v hv
  refine ⟨v, rfl, hslot, y, hy, ?_⟩
  rcases pool_originU hr hy i v (by rw [hslot]; exact hv) with ⟨k, hk, hsa, -⟩ |
    ⟨k, hk, ℓ', hc', hrs, -, B, hB, hvB⟩
  · exact ⟨k, hk, Or.inl hsa⟩
  · exact ⟨k, hk, Or.inr ⟨ℓ', hc', hrs, B, hB, hvB⟩⟩

end Consensus.Goldilocks.SA

end
