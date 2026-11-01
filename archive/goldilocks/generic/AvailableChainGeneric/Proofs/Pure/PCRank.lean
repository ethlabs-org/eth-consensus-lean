module
public import AvailableChainGeneric.Statements.Pure.PCRank
public import AvailableChainGeneric.Proofs.Pure.PCQuorum

public section

/-! Proofs for the PC record: the rank order is a total preorder, `preferPC`
keeps the rank-maximal PC (total, monotone and idempotent), a fold of
`preferPC` dominates every candidate, and two formed PCs of one slot have one
target. Templates: `AvailableChainSAPC/Proofs/Rank.lean:11–37` and
`AvailableChainSAPC/Proofs/FrozenCertificates.lean:94`. -/

namespace AvailableChain.Gen.Pure

variable {n : Nat} {Target K : Type} [LinearOrder K] {key : PC n Target → K}

theorem rankLT_irrefl (c : PC n Target) : ¬ RankLT key c c := by
  rw [RankLT_def]
  rintro (h | ⟨_, k⟩)
  · omega
  · exact lt_irrefl _ k

theorem rankLT_trans {c d e : PC n Target} (hcd : RankLT key c d) (hde : RankLT key d e) :
    RankLT key c e := by
  rw [RankLT_def] at hcd hde ⊢
  rcases hcd with h1 | ⟨h1, k1⟩ <;> rcases hde with h2 | ⟨h2, k2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, lt_trans k1 k2⟩

theorem rankLE_refl (c : PC n Target) : RankLE key c c := by
  rw [RankLE_def]
  exact Or.inr ⟨rfl, le_refl _⟩

theorem rankLE_trans {c d e : PC n Target} (hcd : RankLE key c d) (hde : RankLE key d e) :
    RankLE key c e := by
  rw [RankLE_def] at hcd hde ⊢
  rcases hcd with h1 | ⟨h1, k1⟩ <;> rcases hde with h2 | ⟨h2, k2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, le_trans k1 k2⟩

/-- The rank is total: any two PCs are comparable. -/
theorem rankLE_total (c d : PC n Target) : RankLE key c d ∨ RankLE key d c := by
  rw [RankLE_def, RankLE_def]
  rcases Nat.lt_trichotomy c.slot d.slot with hs | hs | hs
  · exact Or.inl (Or.inl hs)
  · rcases le_total (key c) (key d) with k | k
    · exact Or.inl (Or.inr ⟨hs, k⟩)
    · exact Or.inr (Or.inr ⟨hs.symm, k⟩)
  · exact Or.inr (Or.inl hs)

theorem rankLE_iff_not_rankLT (c d : PC n Target) : RankLE key c d ↔ ¬ RankLT key d c := by
  rw [RankLE_def, RankLT_def]
  constructor
  · rintro (h | ⟨h, k⟩) (h' | ⟨h', k'⟩)
    · omega
    · omega
    · omega
    · exact absurd k' (not_lt.mpr k)
  · intro h
    rcases Nat.lt_trichotomy c.slot d.slot with hs | hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨hs, not_lt.mp fun k => h (Or.inr ⟨hs.symm, k⟩)⟩
    · exact absurd (Or.inl hs) h

theorem rankLE_of_rankLT {c d : PC n Target} (h : RankLT key c d) : RankLE key c d := by
  rw [RankLT_def] at h
  rw [RankLE_def]
  rcases h with h | ⟨h, k⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, le_of_lt k⟩

theorem pickPC_of_rankLT {held cand : PC n Target} (h : RankLT key held cand) :
    pickPC key held cand = cand := by
  rw [RankLT_def] at h
  rw [pickPC_def, ite_eq_left h]

theorem pickPC_of_not_rankLT {held cand : PC n Target} (h : ¬ RankLT key held cand) :
    pickPC key held cand = held := by
  rw [RankLT_def] at h
  rw [pickPC_def, ite_eq_right h]

theorem pickPC_self (c : PC n Target) : pickPC key c c = c :=
  pickPC_of_not_rankLT (rankLT_irrefl c)

theorem pickPC_held_le (held cand : PC n Target) : RankLE key held (pickPC key held cand) := by
  by_cases h : RankLT key held cand
  · rw [pickPC_of_rankLT h]
    exact rankLE_of_rankLT h
  · rw [pickPC_of_not_rankLT h]
    exact rankLE_refl held

theorem pickPC_cand_le (held cand : PC n Target) : RankLE key cand (pickPC key held cand) := by
  by_cases h : RankLT key held cand
  · rw [pickPC_of_rankLT h]
    exact rankLE_refl cand
  · rw [pickPC_of_not_rankLT h]
    exact (rankLE_iff_not_rankLT cand held).mpr h

theorem preferPC_none (cand : PC n Target) : preferPC key none cand = some cand := by
  rw [preferPC_def]
  rfl

theorem preferPC_some (held cand : PC n Target) :
    preferPC key (some held) cand = some (pickPC key held cand) := by
  rw [preferPC_def]
  rfl

/-- `preferPC` is total: it always holds a PC. -/
theorem preferPC_isSome (held : Option (PC n Target)) (cand : PC n Target) :
    ∃ d, preferPC key held cand = some d := by
  rw [preferPC_def]
  exact ⟨_, rfl⟩

/-- The held PC after the offer is the old held PC or the candidate. -/
theorem preferPC_eq_or {held : Option (PC n Target)} {cand d : PC n Target}
    (h : preferPC key held cand = some d) : held = some d ∨ cand = d := by
  cases held with
  | none =>
      rw [preferPC_none] at h
      exact Or.inr (Option.some.inj h)
  | some c =>
      rw [preferPC_some] at h
      have h := Option.some.inj h
      by_cases hr : RankLT key c cand
      · rw [pickPC_of_rankLT hr] at h
        exact Or.inr h
      · rw [pickPC_of_not_rankLT hr] at h
        exact Or.inl (congrArg some h)

/-- The held PC after the offer has at least the candidate's rank. -/
theorem preferPC_cand_le (held : Option (PC n Target)) (cand : PC n Target) :
    ∃ d, preferPC key held cand = some d ∧ RankLE key cand d := by
  cases held with
  | none => exact ⟨cand, preferPC_none cand, rankLE_refl cand⟩
  | some c => exact ⟨_, preferPC_some c cand, pickPC_cand_le c cand⟩

theorem optRankLE_refl (c : Option (PC n Target)) : OptRankLE key c c := by
  rw [OptRankLE_def]
  intro d hd
  exact ⟨d, hd, rankLE_refl d⟩

theorem optRankLE_trans {a b c : Option (PC n Target)}
    (hab : OptRankLE key a b) (hbc : OptRankLE key b c) : OptRankLE key a c := by
  rw [OptRankLE_def] at hab hbc ⊢
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hab x hx
  obtain ⟨z, hz, hyz⟩ := hbc y hy
  exact ⟨z, hz, rankLE_trans hxy hyz⟩

/-- An offer never lowers the rank of the held PC. -/
theorem preferPC_held_le (held : Option (PC n Target)) (cand : PC n Target) :
    OptRankLE key held (preferPC key held cand) := by
  rw [OptRankLE_def]
  intro c hc
  subst hc
  exact ⟨_, preferPC_some c cand, pickPC_held_le c cand⟩

/-- `preferPC` is monotone in the held PC. -/
theorem preferPC_mono {held held' : Option (PC n Target)} (h : OptRankLE key held held')
    (cand : PC n Target) : OptRankLE key (preferPC key held cand) (preferPC key held' cand) := by
  rw [OptRankLE_def]
  intro x hx
  obtain ⟨d, hd, hcd⟩ := preferPC_cand_le (key := key) held' cand
  refine ⟨d, hd, ?_⟩
  rcases preferPC_eq_or hx with hold | rfl
  · rw [OptRankLE_def] at h
    obtain ⟨e, he, hxe⟩ := h x hold
    have hed := preferPC_held_le (key := key) held' cand
    rw [OptRankLE_def] at hed
    obtain ⟨d', hd', hed'⟩ := hed e he
    rw [hd] at hd'
    cases hd'
    exact rankLE_trans hxe hed'
  · exact hcd

theorem preferPC_self (c : PC n Target) : preferPC key (some c) c = some c := by
  rw [preferPC_some, pickPC_self]

/-- `preferPC` is idempotent: a repeated offer changes nothing. -/
theorem preferPC_idem (held : Option (PC n Target)) (cand : PC n Target) :
    preferPC key (preferPC key held cand) cand = preferPC key held cand := by
  cases held with
  | none => rw [preferPC_none, preferPC_self]
  | some c =>
      rw [preferPC_some, preferPC_some]
      by_cases h : RankLT key c cand
      · rw [pickPC_of_rankLT h, pickPC_self]
      · rw [pickPC_of_not_rankLT h, pickPC_of_not_rankLT h]

/-- A fold of offers never lowers the rank of the held PC. -/
theorem foldl_preferPC_held_le (cs : List (PC n Target)) (held : Option (PC n Target)) :
    OptRankLE key held (cs.foldl (preferPC key) held) := by
  induction cs generalizing held with
  | nil => exact optRankLE_refl held
  | cons x xs ih => exact optRankLE_trans (preferPC_held_le held x) (ih _)

/-- After a fold of offers, the held PC has at least the rank of each offer. -/
theorem foldl_preferPC_cand_le {cs : List (PC n Target)} {c : PC n Target} (hc : c ∈ cs)
    (held : Option (PC n Target)) :
    ∃ d, cs.foldl (preferPC key) held = some d ∧ RankLE key c d := by
  induction cs generalizing held with
  | nil => cases hc
  | cons x xs ih =>
      rcases List.mem_cons.mp hc with rfl | hxs
      · obtain ⟨d, hd, hcd⟩ := preferPC_cand_le (key := key) held c
        have hf := foldl_preferPC_held_le (key := key) xs (preferPC key held c)
        rw [OptRankLE_def] at hf
        obtain ⟨e, he, hde⟩ := hf d hd
        exact ⟨e, he, rankLE_trans hcd hde⟩
      · exact ih hxs _

/-- After a fold of offers, the held PC is the initial one or an offer. -/
theorem foldl_preferPC_eq_or {cs : List (PC n Target)} {held : Option (PC n Target)}
    {d : PC n Target} (h : cs.foldl (preferPC key) held = some d) :
    held = some d ∨ d ∈ cs := by
  induction cs generalizing held with
  | nil => exact Or.inl h
  | cons x xs ih =>
      rcases ih h with h1 | h1
      · rcases preferPC_eq_or h1 with h2 | rfl
        · exact Or.inl h2
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem x h1)

/-- A formed PC has an acker outside a set of fewer than `q_A` seats. -/
theorem PC.Formed.honest_acker {c : PC n Target} (hc : c.Formed) {F : Finset (Fin n)}
    (hF : F.card < qA n) : ∃ v ∈ c.ackers, v ∉ F := by
  rw [PC.Formed_def] at hc
  exact qA_honest hF hc

theorem pc_same_slot_target_statement : PCSameSlotTargetStatement := by
  rw [PCSameSlotTargetStatement_def]
  intro n B sent acked F c d hone hack hF hc hd hca hda
  obtain ⟨v, hv, hvF⟩ := hc.honest_acker hF
  obtain ⟨w, hw, hwF⟩ := hd.honest_acker hF
  obtain ⟨S, hS, hSs⟩ := hack v hvF c.target (hca v hv)
  obtain ⟨S', hS', hSs'⟩ := hack w hwF d.target (hda w hw)
  exact qN_head_unique sent F S S' c.target d.target hone hF hSs hSs' hS hS'

/-- Two formed PCs of one slot have the same target. -/
theorem pc_same_slot_target {B : Type} (sent acked : Fin n → B → Prop) (F : Finset (Fin n))
    (c d : PC n B)
    (hone : ∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y)
    (hack : ∀ v, v ∉ F → ∀ b, acked v b →
      ∃ S : Finset (Fin n), qN n ≤ S.card ∧ ∀ w ∈ S, sent w b)
    (hF : F.card < qA n) (hc : c.Formed) (hd : d.Formed)
    (hca : ∀ v ∈ c.ackers, acked v c.target) (hda : ∀ v ∈ d.ackers, acked v d.target) :
    c.target = d.target :=
  pc_same_slot_target_statement sent acked F c d hone hack hF hc hd hca hda

end AvailableChain.Gen.Pure
