module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSARun.Proofs.NamedScope
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainKitFG.FinalizedOccurrence
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! WC plan §6.3; DC signed origins and low finalized occurrences in named run scope. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §5; DC the pure adapter has exactly the reviewed crossing proposition. -/
theorem wc_finalizedCrossing : WCFinalizedCrossingStatement :=
  @KitFG.finalizedOccurrence_preceq_of_crossing

/-- WC plan §6.3; DC original source evidence enters through its lane premise. -/
theorem wc_sourceOrigin : WCSourceOriginStatement p c E rho := fun hemitted => hemitted

/-- WC plan §6.3; DC source labels refer to the original emission. -/
theorem wc_sourceLabel : WCSourceLabelStatement p c E rho := fun hlabel => hlabel

/-- WC plan §§5, 6.3; DC the historical carrier keeps the exact finality key. -/
theorem wc_finalizedOccurrence : WCFinalizedOccurrenceStatement p c E rho := by
  intro hscopeRows hnoslash D X h hscope hF hh
  refine ⟨hF, hh, hscope, ?_, ?_, hscopeRows D hscope, hnoslash⟩
  · intro hz
    exact hF.symm.trans ((fgCertificateLaws p).finalized_zero D (hh.trans hz))
  · intro hn
    simpa only [hF, hh] using
      (fgCertificateLaws p).finality_origin D (fun hz => hn (hh.symm.trans hz))

/-- WC plan §§5, 6.3; DC both compared carriers have explicit named run scope. -/
theorem wc_lowFinalized [Fintype V] {w : HealingWitness} {iStar : Nat} :
    WCLowFinalizedStatement p c E rho w iStar := by
  classical
  intro hlinked hfaultX hroots hscopeRows hnoslash hs D X h hf hlow
  obtain ⟨W, hW, hheight, hscope, _⟩ := hs.carrier
  let bad := Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base .fg) k ∉ rho.honest)
  have hsub : bad.image (rho.seatOf (.base .fg)) ⊆ Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ((@Finset.mem_filter (Fin p.n)
      (fun k => rho.seatOf (.base .fg) k ∉ rho.honest)
      (fun _ => @instDecidableNot _ (Classical.propDecidable _)) Finset.univ k).mp hk).2
  have hinj : Function.Injective (rho.seatOf (.base .fg)) :=
    (hlinked.toCStar (.base .fg) trivial).1
  have hcard : bad.card ≤ (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective bad hinj).symm.trans_le (Finset.card_le_card hsub)
  have hw : p.E.weightOf bad = bad.card := by
    change (∑ _ ∈ bad, (1 : Nat)) = _
    simp
  have ht : p.E.totalWeight = p.n := by
    change (∑ _ : Fin p.n, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n := by
    change (2 * p.E.totalWeight + 2) / 3 = Gen.Pure.qF p.n
    rw [ht, Gen.Pure.qF_def]
  have hcap : p.E.weightOf bad + p.E.totalWeight < 2 * p.E.q := by
    rw [hw, ht, hq]
    exact (Nat.add_le_add_right hcard _).trans_lt hfaultX.lt
  have hsafe : ∀ a ∈ chainRows W, ∀ b ∈ chainRows D,
      a.signer ∉ bad → ¬ Slashable a b := by
    intro a ha b hb hgood hab
    have hsign : a.signer = b.signer := by
      change ((sameSigner a b && e1Fields a b) ||
        (sameSigner a b && e2Fields a b)) = true at hab
      have hsame : sameSigner a b = true := by
        rcases Bool.or_eq_true_iff.mp hab with h | h
        · exact (Bool.and_eq_true_iff.mp h).1
        · exact (Bool.and_eq_true_iff.mp h).1
      exact of_decide_eq_true hsame
    have hz : rho.seatOf (.base .fg) a.signer ∈ rho.honest := by
      by_contra hn
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    obtain ⟨ja, ra, wa, hea, hda, _⟩ := hscopeRows W hscope a ha hz
    obtain ⟨jb, rb, wb, heb, hdb, _⟩ := hf.rows b hb (hsign ▸ hz)
    rw [← hsign] at heb
    exact hnoslash _ hz wa wb ⟨ja, p.actionTime ra, hea.2.1, hea.2.2⟩
      ⟨jb, p.actionTime rb, heb.2.1, heb.2.2⟩ a b hda hdb hab
  have hX := finalizedOccurrence_preceq_of_crossing p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) D W X h hf.value hf.height
    (rootInjectiveOn_run E rho hroots hf.scope hscope) bad hcap hsafe
    (by rw [hheight]; exact Nat.lt_succ_of_le hlow)
  have hXC : Block.Preceq (eraseFG X) w.CStar := hW ▸ eraseFG_preceq hX
  exact ⟨hXC, Gen.Pure.block_preceq_trans hXC hs.sourcePrefix⟩

end AvailableChain.FGSA.Run
end
