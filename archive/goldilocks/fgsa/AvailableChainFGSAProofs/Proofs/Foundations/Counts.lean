module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainKitFG.HeightConsumeTransfer
public import AvailableChainFGSA.Model.Objects

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure SimplexFG

/-- P3 D40: the claim-local `a ≤ f` is `a ≤ (p.n - 1) / 3`.
The sole FaultX producer is Gen.Pure.count_rec. -/
theorem fgsa_faultX_count_rec (p : Params) {a : Nat} (hf : a ≤ (p.n - 1) / 3) :
    FaultX p.n a := count_rec p.nPos hf

/-- Recovery quorum membership from count_rec. Gen has no FaultX-to-FaultQ lemma;
only the projection arithmetic is local. This is not a Clean producer. -/
theorem fgsa_faultQ_of_count (p : Params) {a : Nat} (hf : a ≤ (p.n - 1) / 3) :
    FaultQ p.n a := by
  have hx := (fgsa_faultX_count_rec p hf).lt
  constructor
  rw [qF_def] at hx ⊢
  omega

private theorem fgsa_target_fold_covered (p : Params) (rows : List (Row (Fin p.n)))
    (σ : ChainState (Fin p.n)) (i : Fin p.n)
    (hi : i ∈ σ.target_participation ∨ ∃ r ∈ rows, r.signer = i ∧
      r.height_pair = .vote σ.h σ.T_h.root false) :
    i ∈ (rows.foldl process_row σ).target_participation := by
  induction rows generalizing σ with
  | nil =>
    rcases hi with hi | ⟨r, hr, _⟩
    · exact hi
    · cases hr
  | cons r rows ih =>
    apply ih
    have fields := KitFG.process_row_fields σ r
    rcases hi with hi | ⟨a, ha, hs, hp⟩
    · left
      rw [KitFG.process_row_target]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi
    · rcases List.mem_cons.mp ha with rfl | ha
      · left
        rw [KitFG.process_row_target, ite_eq_left hp, hs]
        exact Finset.mem_insert_self _ _
      · right
        exact ⟨a, ha, hs, by rw [fields.2.2.1, fields.2.2.2.1]; exact hp⟩

/-- ROOT-DIGEST W2b. 22 I7, target part: exact rows or existing bits for at least `n - a`
identities justify the parent's entry and advance once. The FG chain state has
no `nj` field; the target test is unconditional. No restriction on δt. -/
theorem fgsa_target_exact_quorum (p : Params) {a : Nat}
    (hf : a ≤ (p.n - 1) / 3) (H : Finset (Fin p.n)) (hH : p.n - a ≤ H.card)
    (B : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (x : Nat) (rows : List (Row (Fin p.n)))
    (hcov : ∀ i ∈ H, i ∈ (derive p.E p.cfg B).target_participation ∨
      ∃ r ∈ rows, r.signer = i ∧
        r.height_pair = .vote (derive p.E p.cfg B).h (derive p.E p.cfg B).T_h.root false) :
    (derive p.E p.cfg (.node B s root x rows)).J = (derive p.E p.cfg B).T_h ∧
    (derive p.E p.cfg (.node B s root x rows)).h_j = (derive p.E p.cfg B).h ∧
    (derive p.E p.cfg (.node B s root x rows)).h = (derive p.E p.cfg B).h + 1 := by
  have hq : p.E.q = qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  have hw : p.E.weightOf H = H.card := by
    change (∑ _i ∈ H, (1 : Nat)) = H.card
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
  have hbound : qF p.n ≤ p.n - a := by
    have hn := p.nPos
    rw [qF_def]
    omega
  have hquorum : p.E.IsQuorum H := by
    change p.E.q ≤ p.E.weightOf H
    rw [hq, hw]
    exact hbound.trans hH
  have hc := KitFG.derive_target_of_cover_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) B s root x rows H hquorum
    (by simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
      using hcov)
  simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
    using And.intro hc.2.1 (And.intro hc.2.2 hc.1)

end AvailableChain.FGSA.Run
end
