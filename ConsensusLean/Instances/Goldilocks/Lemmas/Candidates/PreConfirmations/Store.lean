module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.Statements
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # ½ pre-confirmations: the store, the base and the anchor

The facts of one PC store, for the statements of `Candidates/PreConfirmations/Statements`:

* the evaluation (`refreshIdem`), the authoritative keys (`authorityCompatible`,
  `authorityWindow`) and the window arithmetic (`ackSendsWindow`, `onAckWindow`, `recordWindow`);
* the D21 projection, the base and the anchor (`pcProjFacts`, `pcBaseFacts`, `pcAnchorFacts`);
* the memoryless walk (`pcPathSameState`): a walk from a block on the walk from `a₀` that extends
  `a₀` ends where the walk from `a₀` ends (`ghost_visits`, `ghost_add`, `ghost_stopped`,
  `ghost_fuel_stable`). -/

namespace Consensus.Goldilocks.PreConfirmations

open SA

variable {sp : SAParams} {FGP : Type}

/-! ## Field lemmas -/

theorem refresh_acks (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (refresh sp P Φ t).acks = P.acks := rfl

theorem refresh_votes (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (refresh sp P Φ t).votes = P.votes := rfl

theorem refresh_myAcks (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (refresh sp P Φ t).myAcks = P.myAcks := rfl

theorem mem_refresh_pcs {P : PCStore sp.n} {Φ : Frm sp.n FGP} {t : Time} {k : Nat × Nat} :
    k ∈ (refresh sp P Φ t).pcs ↔ k ∈ P.pcs ∧ InWindow sp t k := Iff.rfl

theorem mem_refresh_dead {P : PCStore sp.n} {Φ : Frm sp.n FGP} {t : Time} {k : Nat × Nat} :
    k ∈ (refresh sp P Φ t).dead ↔ (k ∈ P.dead ∧ k ∈ (refresh sp P Φ t).pcs) ∨
      (k ∈ (refresh sp P Φ t).pcs ∧ InTree Φ k.2 ∧
        ∃ k' : Nat × Nat, (k' ∈ (refresh sp P Φ t).pcs ∧ InTree Φ k'.2) ∧
          ConflictsR sp Φ k.2 k'.2) := by
  simp only [refresh, Set.mem_union, Set.mem_ofPred_eq, and_assoc]

theorem mem_refresh_valid {P : PCStore sp.n} {Φ : Frm sp.n FGP} {t : Time} {k : Nat × Nat} :
    k ∈ (refresh sp P Φ t).valid ↔ (k ∈ P.valid ∧ k ∈ (refresh sp P Φ t).pcs) ∨
      (k ∈ (refresh sp P Φ t).pcs ∧ InTree Φ k.2 ∧ pairOk sp Φ P k) := by
  simp only [refresh, Set.mem_union, Set.mem_ofPred_eq, and_assoc]

theorem mem_authority {P : PCStore sp.n} {Φ : Frm sp.n FGP} {t : Time} {k : Nat × Nat} :
    k ∈ authority sp P Φ t ↔ k ∈ (refresh sp P Φ t).pcs ∧ InTree Φ k.2 ∧
      k ∈ (refresh sp P Φ t).valid ∧ k ∉ (refresh sp P Φ t).dead := Iff.rfl

theorem pairOk_refresh (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) (k : Nat × Nat) :
    pairOk sp Φ (refresh sp P Φ t) k ↔ pairOk sp Φ P k := Iff.rfl

/-! ## The evaluation and the authoritative keys -/

theorem pcStore_ext {Q R : PCStore sp.n} (h₁ : Q.acks = R.acks) (h₂ : Q.pcs = R.pcs)
    (h₃ : Q.valid = R.valid) (h₄ : Q.dead = R.dead) (h₅ : Q.votes = R.votes)
    (h₆ : Q.myAcks = R.myAcks) : Q = R := by
  cases Q
  cases R
  subst_vars
  rfl

/-- **Evaluation is idempotent.** -/
theorem refreshIdem : RefreshIdem sp FGP := by
  intro P Φ t
  have hpcs : (refresh sp (refresh sp P Φ t) Φ t).pcs = (refresh sp P Φ t).pcs := by
    ext k
    simp only [mem_refresh_pcs]
    tauto
  have hdead : (refresh sp (refresh sp P Φ t) Φ t).dead = (refresh sp P Φ t).dead := by
    ext k
    rw [mem_refresh_dead, hpcs, mem_refresh_dead]
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact Or.inr h
    · intro h
      refine Or.inl ⟨h, ?_⟩
      rcases h with ⟨-, h⟩ | ⟨h, -⟩ <;> exact h
  have hvalid : (refresh sp (refresh sp P Φ t) Φ t).valid = (refresh sp P Φ t).valid := by
    ext k
    rw [mem_refresh_valid, hpcs, mem_refresh_valid, pairOk_refresh]
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact Or.inr h
    · intro h
      refine Or.inl ⟨h, ?_⟩
      rcases h with ⟨-, h⟩ | ⟨h, -⟩ <;> exact h
  exact pcStore_ext rfl hpcs hvalid hdead rfl rfl

/-- **Authoritative targets are compatible.** -/
theorem authorityCompatible : AuthorityCompatible sp FGP := by
  intro P Φ t k hk k' hk' X hX X' hX' hXr hX'r
  by_contra hc
  obtain ⟨hkp, hkt, -, hkd⟩ := mem_authority.1 hk
  obtain ⟨hk'p, hk't, -, -⟩ := mem_authority.1 hk'
  exact hkd (mem_refresh_dead.2 (Or.inr ⟨hkp, hkt, k', ⟨hk'p, hk't⟩,
    X, hX, X', hX', hXr, hX'r, hc⟩))

/-- **Authoritative keys are in the window.** -/
theorem authorityWindow : AuthorityWindow sp FGP :=
  fun _ _ _ _ hk => (mem_refresh_pcs.1 (mem_authority.1 hk).1).2

/-! ## The window arithmetic -/

/-- **The sends' window.** -/
theorem ackSendsWindow : AckSendsWindow sp := by
  intro P self s a ha
  simp only [ackSends, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨j, hj, ha⟩ := ha
  split_ifs at ha with hjs
  · obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 ha
    have h3 : 3 ≤ pcWindow sp := le_max_right _ _
    refine ⟨rfl, ?_, ?_, ?_, hX⟩
    · rcases hj with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · change s - j + j = s
      omega
    · change s ≤ s - j + pcWindow sp
      rcases hj with rfl | rfl <;> omega

/-- **The admission's window.** -/
theorem onAckWindow : OnAckWindow sp := by
  intro P t a h
  unfold onAck
  split_ifs with hc
  · rfl
  · exact absurd (by rcases h with h | h <;> simp [h]) hc

/-- **The record's window.** -/
theorem recordWindow : RecordWindow sp := by
  intro P t v h
  unfold recordVote
  split_ifs with hc
  · omega
  · rfl

/-! ## The D21 projection, the base and the anchor -/

/-- **The D21 projection.** -/
theorem pcProjFacts : PCProjFacts sp FGP := by
  intro Φ hΦ V b s X hX
  unfold pcProj
  split_ifs with hsb
  · set S := {Y | Y ∈ Φ.tree ∧ Φ.Anc Y X ∧ (d21Opponents sp Φ V Y).ncard < pcMu sp}
    have hSt : S ⊆ Φ.tree := fun Y hY => hY.1
    have hch : ∀ Y ∈ S, ∀ Z ∈ S, Compatible Φ.tree Y Z :=
      fun Y hY Z hZ => anc_total hΦ.coherent hY.2.1 hZ.2.1
    rcases hd : deepest Φ S with _ | D <;> simp only [Option.getD_none, Option.getD_some]
    · have hempty : ∀ Z ∈ Φ.tree, Φ.Anc Z X → ¬ (d21Opponents sp Φ V Z).ncard < pcMu sp := by
        intro Z hZ hZX hlt
        obtain ⟨D, hD⟩ := exists_deepest hΦ hSt ⟨Z, hZ, hZX, hlt⟩
        rw [hd] at hD
        cases hD
      refine ⟨hΦ.rooted.1, hΦ.rooted.2 X hX, fun _ => ⟨Or.inr trivial, ?_⟩, ?_⟩
      · intro Z hZ _ _ hZX
        exact not_lt.1 (hempty Z hZ hZX)
      · intro Z hZ hZX hlt
        exact absurd hlt (hempty Z hZ hZX)
    · obtain ⟨⟨hDt, hDX, hDo⟩, hDmax⟩ := deepest_mem hd
      refine ⟨hDt, hDX, fun _ => ⟨Or.inl hDo, ?_⟩, ?_⟩
      · intro Z hZ hDZ hne hZX
        by_contra hlt
        have hlt := not_le.1 hlt
        have h1 := depth_lt_of_anc hΦ hDZ (Ne.symm hne) hZ
        rcases hDmax Z ⟨hZ, hZX, hlt⟩ hne with h2 | ⟨h2, -⟩ <;> omega
      · intro Z hZ hZX hlt
        exact anc_deepest hΦ hSt hch hd Z ⟨hZ, hZX, hlt⟩
  · exact ⟨hX, .refl, fun h => absurd h hsb, fun _ _ hZX _ => hZX⟩

theorem deepest_empty (Φ : Frm sp.n FGP) : deepest Φ (∅ : Set (Blk sp.n FGP)) = none := by
  unfold deepest
  split_ifs with h
  · obtain ⟨B, hB, -⟩ := h
    exact absurd hB (Set.notMem_empty B)
  · rfl

/-- **The base.** -/
theorem pcBaseFacts : PCBaseFacts sp FGP := by
  intro Φ hΦ P t V b
  set S := {Y | ∃ k ∈ authority sp P Φ t, ∃ X ∈ Φ.tree, X.root = k.2 ∧
    Y = pcProj sp Φ V b k.1 X}
  have hSt : S ⊆ Φ.tree := by
    rintro Y ⟨k, -, X, hX, -, rfl⟩
    exact (pcProjFacts hΦ V b k.1 X hX).1
  have hbase : pcBase sp P Φ t V b = deepest Φ S := rfl
  refine ⟨?_, ?_⟩
  · rw [hbase]
    constructor
    · intro hd
      by_contra hne
      obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨X, hX, hXr⟩ := (mem_authority.1 hk).2.1
      obtain ⟨D, hD⟩ := exists_deepest hΦ hSt ⟨_, k, hk, X, hX, hXr, rfl⟩
      rw [hd] at hD
      cases hD
    · intro he
      have : S = ∅ := by
        ext Y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, S]
        rintro ⟨k, hk, -⟩
        rw [he] at hk
        exact hk
      rw [this, deepest_empty]
  · intro Y hY
    rw [hbase] at hY
    obtain ⟨⟨k, hk, X, hX, hXr, rfl⟩, hmax⟩ := deepest_mem hY
    refine ⟨k, hk, X, hX, hXr, rfl, fun k' hk' X' hX' hX'r => ?_⟩
    by_cases he : pcProj sp Φ V b k'.1 X' = pcProj sp Φ V b k.1 X
    · rw [he]
    · rcases hmax _ ⟨k', hk', X', hX', hX'r, rfl⟩ he with h | ⟨h, -⟩ <;> omega

/-- **The PC anchor.** -/
theorem pcAnchorFacts : PCAnchorFacts sp FGP := by
  intro Φ hΦ A t Y hY
  set S := {B | B ∈ liveLockBlocks sp A.locks Φ t ∧ Φ.Anc Y B} ∪ {Y}
  have hSt : S ⊆ Φ.tree := by
    rintro B (⟨hB, -⟩ | hB)
    · exact hB.1
    · exact (Set.mem_singleton_iff.1 hB) ▸ hY
  obtain ⟨D, hD⟩ := exists_deepest hΦ hSt ⟨Y, Or.inr rfl⟩
  have ha : pcAnchor sp A Φ t Y = D := by
    change (deepest Φ S).getD Y = D
    rw [hD, Option.getD_some]
  obtain ⟨hDS, hmax⟩ := deepest_mem hD
  rw [ha]
  refine ⟨?_, ?_, ?_⟩
  · rcases hDS with ⟨-, h⟩ | h
    · exact h
    · exact (Set.mem_singleton_iff.1 h) ▸ .refl
  · rcases hDS with ⟨h, -⟩ | h
    · exact Or.inr h
    · exact Or.inl (Set.mem_singleton_iff.1 h)
  · intro B hB hYB
    by_cases he : B = D
    · rw [he]
    · rcases hmax B (Or.inl ⟨hB, hYB⟩) he with h | ⟨h, -⟩ <;> omega

/-- **Same-state PC path**: the memoryless walk. -/
theorem pcPathSameState : PCPathSameState sp FGP := by
  intro Φ hΦ a₀ a₁ t tree V s htree h01 h1H
  unfold headFrom at h1H ⊢
  set N := Φ.tree.ncard
  obtain ⟨k, hkN, hk⟩ := ghost_visits (S := Φ.tree) hΦ.coherent htree N h01 h1H
  have hadd : ghost sp tree (goldfishScore sp Φ V s) (goldfishEligible sp Φ t V s) N a₀ =
      ghost sp tree (goldfishScore sp Φ V s) (goldfishEligible sp Φ t V s) (N - k) a₁ := by
    rw [← hk, ← ghost_add, Nat.add_sub_cancel' hkN]
  have hle : tree.ncard ≤ N := Set.ncard_le_ncard htree hΦ.finite
  have hstop := ghost_stopped (S := Φ.tree) hΦ.coherent htree (hΦ.finite.subset htree)
    (sc := goldfishScore sp Φ V s) (el := goldfishEligible sp Φ t V s) hle a₀
  rw [hadd] at hstop ⊢
  exact ghost_fuel_stable (Nat.sub_le N k) hstop

end Consensus.Goldilocks.PreConfirmations

end
