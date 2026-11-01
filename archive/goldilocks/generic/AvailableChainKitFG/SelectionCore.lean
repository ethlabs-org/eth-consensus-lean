module
public import AvailableChainKitFG.CertificateSelectionDef
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- Membership in the library pruning operation. -/
theorem mem_pruneCertEntries (h : Height) (entries : List (FGCertEntry V)) (e : FGCertEntry V) :
    e ∈ pruneCertEntries h entries ↔ e ∈ entries ∧ h < e.j := by
  rw [pruneCertEntries_def]
  simp only [List.mem_filter, decide_eq_true_eq]

omit [Fintype V] [RowCodec V] in
/-- Ordered entries give ancestry at each lower key, with no quorum premise. -/
theorem certEntry_preceq_of_le (entries : List (FGCertEntry V))
    (hord : entries.Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X))
    (e d : FGCertEntry V) (he : e ∈ entries) (hd : d ∈ entries) (hle : e.j ≤ d.j) :
    FGBlock.Preceq e.X d.X := by
  induction entries with
  | nil => simp at he
  | cons a entries ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hord
      rcases List.mem_cons.mp he with rfl | heTail
      · rcases List.mem_cons.mp hd with rfl | hdTail
        · exact preceq_refl _
        · exact (hhead d hdTail).2
      · rcases List.mem_cons.mp hd with rfl | hdTail
        · exact ((Nat.not_lt_of_ge hle) (hhead e heTail).1).elim
        · exact ih htail heTail hdTail

/-- Build selection laws and derive coverage from the supplied core fields. -/
theorem FGSelectionLaws.of_core (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (r : FGSelectionView V)
    (initial : r.before .genesis = [] ∧ r.chosen .genesis = none ∧
      r.afterPrune .genesis = [])
    (ordered : ∀ B, (r.before B).Pairwise
      (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X))
    (bounds : ∀ B e, e ∈ r.before B →
      (f B.parent).h_F < e.j ∧ e.j ≤ (H B.parent).h_j ∧
      FGBlock.Preceq (f B.parent).F e.X ∧ FGBlock.Preceq e.X (H B.parent).J)
    (entry_origin : ∀ B e, e ∈ r.before B → ∃ C,
      StrictPrefix C B ∧ JustificationBirth E H C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a, StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩)
    (none_iff : ∀ B, r.chosen B = none ↔ ∀ e ∈ r.before B, ¬ E.IsQuorum e.Q)
    (greatest : ∀ B e, r.chosen B = some e →
      e ∈ r.before B ∧ E.IsQuorum e.Q ∧
      ∀ d ∈ r.before B, E.IsQuorum d.Q → d.j ≤ e.j)
    (write : ∀ B, B ≠ .genesis → f B =
      match r.chosen B with
      | none => f B.parent
      | some e => ⟨e.X, e.j⟩)
    (prune : ∀ B, r.afterPrune B =
      (r.before B).filter (fun e => decide ((f B).h_F < e.j))) :
    FGSelectionLaws E H f r where
  initial := initial
  ordered := ordered
  bounds := bounds
  entry_origin := entry_origin
  none_iff := none_iff
  greatest := greatest
  write := write
  prune := prune
  pruned_covered := by
    intro B e he hle
    have hB : B ≠ .genesis := by
      intro h
      subst B
      rw [initial.1] at he
      exact List.not_mem_nil he
    have hw := write B hB
    cases hc : r.chosen B with
    | none =>
        rw [hc] at hw
        have hb := (bounds B e he).1
        rw [hw] at hle
        exact ((Nat.not_lt_of_ge hle) hb).elim
    | some d =>
        rw [hc] at hw
        rw [hw] at hle ⊢
        exact certEntry_preceq_of_le _ (ordered B) e d he (greatest B d hc).1 hle

variable (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hs : FGSelectionLaws E H f r)

include hs

/-- Link the selection pruning field to the library operation. -/
theorem FGSelectionLaws.prune_eq (B : FGBlock V) :
    r.afterPrune B = pruneCertEntries (f B).h_F (r.before B) :=
  hs.prune B

/-- Selection writes the chosen pair and strictly raises the certificate height. -/
theorem selection_chosen_spec (B : FGBlock V) (e : FGCertEntry V)
    (he : r.chosen B = some e) :
    e ∈ r.before B ∧ E.IsQuorum e.Q ∧
      (f B.parent).h_F < e.j ∧ f B = ⟨e.X, e.j⟩ := by
  have hB : B ≠ .genesis := by
    intro h
    subst B
    rw [hs.initial.2.1] at he
    cases he
  obtain ⟨hmem, hq, _⟩ := hs.greatest B e he
  exact ⟨hmem, hq, (hs.bounds B e hmem).1, by simpa only [he] using hs.write B hB⟩

/-- A ready entry is covered by the selected entry, even when it is not selected. -/
theorem selection_ready_covered (B : FGBlock V) (e : FGCertEntry V)
    (he : e ∈ r.before B) (hq : E.IsQuorum e.Q) :
    e.j ≤ (f B).h_F ∧ FGBlock.Preceq e.X (f B).F := by
  cases hc : r.chosen B with
  | none => exact ((hs.none_iff B).mp hc e he hq).elim
  | some d =>
      have hle := (hs.greatest B d hc).2.2 e he hq
      have hw := (selection_chosen_spec E H f r hs B d hc).2.2.2
      have hj : e.j ≤ (f B).h_F := by simpa only [hw] using hle
      exact ⟨hj, hs.pruned_covered B e he hj⟩

/-- The selected QC is read before pruning removes its entry. -/
theorem selection_chosen_removed (B : FGBlock V) (e : FGCertEntry V)
    (he : r.chosen B = some e) : e ∉ r.afterPrune B := by
  have hw := (selection_chosen_spec E H f r hs B e he).2.2.2
  rw [hs.prune B]
  simp only [List.mem_filter, decide_eq_true_eq, hw, lt_self_iff_false, and_false,
    not_false_eq_true]

/-- An entry is retained exactly while it is above finality. -/
theorem selection_retained_iff (B : FGBlock V) (e : FGCertEntry V) :
    e ∈ r.afterPrune B ↔ e ∈ r.before B ∧ (f B).h_F < e.j := by
  rw [FGSelectionLaws.prune_eq E H f r hs B]
  exact mem_pruneCertEntries _ _ _

/-- Every removed pre-finality entry is covered. Eviction is outside this statement. -/
theorem selection_removed_covered (B : FGBlock V) (e : FGCertEntry V)
    (he : e ∈ r.before B) (hremoved : e ∉ r.afterPrune B) :
    e.j ≤ (f B).h_F ∧ FGBlock.Preceq e.X (f B).F := by
  have hle : e.j ≤ (f B).h_F := by
    by_contra hn
    exact hremoved ((selection_retained_iff E H f r hs B e).mpr ⟨he, Nat.lt_of_not_ge hn⟩)
  exact ⟨hle, hs.pruned_covered B e he hle⟩

/-- Selection preserves the zero anchor until a positive entry is selected. -/
theorem selection_finalized_zero (hinit : f .genesis = ⟨.genesis, 0⟩)
    (B : FGBlock V) (hz : (f B).h_F = 0) : (f B).F = .genesis := by
  induction B with
  | genesis => rw [hinit]
  | node p s r_s x rs ih =>
      have hw := hs.write (.node p s r_s x rs) (by simp)
      cases hc : r.chosen (.node p s r_s x rs) with
      | none =>
          rw [hc] at hw
          rw [hw] at hz ⊢
          exact ih hz
      | some e =>
          obtain ⟨_, _, hlt, heq⟩ := selection_chosen_spec E H f r hs _ e hc
          rw [heq] at hz
          exact (Nat.ne_zero_of_lt hlt hz).elim

/-- Finality height and ancestry are monotone along the immutable chain. -/
theorem selection_finalized_mono {A B : FGBlock V} (hAB : FGBlock.Preceq A B) :
    (f A).h_F ≤ (f B).h_F ∧ FGBlock.Preceq (f A).F (f B).F := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact ⟨le_rfl, preceq_refl _⟩
  | node p s r_s x rs ih =>
      by_cases he : A = .node p s r_s x rs
      · subst A
        exact ⟨le_rfl, preceq_refl _⟩
      obtain ⟨hh, hF⟩ := ih (preceq_parent_of_preceq_node hAB he)
      have hw := hs.write (.node p s r_s x rs) (by simp)
      cases hc : r.chosen (.node p s r_s x rs) with
      | none =>
          rw [hc] at hw
          rw [hw]
          exact ⟨hh, hF⟩
      | some e =>
          obtain ⟨hmem, _, hlt, heq⟩ := selection_chosen_spec E H f r hs _ e hc
          rw [heq]
          exact ⟨hh.trans (Nat.le_of_lt hlt), preceq_trans hF (hs.bounds _ e hmem).2.2.1⟩

/-- The generic historical origin induction keeps the exact birth and selected QC. -/
theorem selection_finality_origin (hinit : f .genesis = ⟨.genesis, 0⟩)
    (B : FGBlock V) (hnz : (f B).h_F ≠ 0) :
    ∃ C D, StrictPrefix C D ∧ FGBlock.Preceq D B ∧
      JustificationBirth E H C (f B).h_F (f B).F ∧
      (f D.parent).h_F < (f D).h_F ∧ f D = f B ∧
      FinalityQCAfter E C D (f B).h_F (f B).F := by
  induction B with
  | genesis => exact (hnz (by rw [hinit])).elim
  | node p s r_s x rs ih =>
      have hw := hs.write (.node p s r_s x rs) (by simp)
      cases hc : r.chosen (.node p s r_s x rs) with
      | none =>
          rw [hc] at hw
          rw [hw] at hnz ⊢
          obtain ⟨C, D, hCD, hDp, hb, hinc, heq, hqc⟩ := ih hnz
          exact ⟨C, D, hCD, preceq_node_of_preceq s r_s x rs hDp, hb, hinc, heq, hqc⟩
      | some e =>
          obtain ⟨hmem, hq, hlt, heq⟩ := selection_chosen_spec E H f r hs _ e hc
          obtain ⟨C, hCB, hb, hrows⟩ := hs.entry_origin _ e hmem
          refine ⟨C, .node p s r_s x rs, hCB, preceq_refl _, ?_, ?_, rfl, ?_⟩
          · simpa only [heq] using hb
          · simpa only [heq] using hlt
          · rw [heq]
            exact ⟨e.Q, hq, hrows⟩

/-- Assemble certificates from selection. Height laws do not order `J` or `h_j`;
the instance supplies the two finality-to-justification bounds explicitly. -/
theorem FGCertificateLaws.of_selection (hH : FGHeightLaws E H)
    (hinit : f .genesis = ⟨.genesis, 0⟩)
    (hzero : ∀ B, (H B).h_j = 0 → (H B).J = .genesis)
    (hFJ : ∀ B, FGBlock.Preceq (f B).F (H B).J)
    (horder : ∀ B, (f B).h_F ≤ (H B).h_j) : FGCertificateLaws E H f where
  height := hH
  initial := hinit
  justified_zero := hzero
  finalized_zero := selection_finalized_zero E H f r hs hinit
  finalized_preceq_justified := hFJ
  heights_ordered := horder
  finalized_mono := selection_finalized_mono E H f r hs
  finality_origin := selection_finality_origin E H f r hs hinit

end AvailableChain.KitFG
end
