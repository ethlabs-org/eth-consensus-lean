module
public import AvailableChainGeneric.Statements.Pure.CommonAncestor
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.Gen.Pure

/-- The walk returns a prefix of both inputs. -/
theorem meet_prefix_statement : MeetPrefixStatement := by
  rw [MeetPrefixStatement_def]
  intro B C
  induction B with
  | genesis => exact ⟨block_preceq_refl _, block_genesis_preceq C⟩
  | node p s r x ih =>
      rw [Block.meet_def]
      by_cases h : Block.Preceq (.node p s r x) C
      · simp only [ite_eq_left h]
        exact ⟨block_preceq_refl _, h⟩
      · simp only [ite_eq_right h]
        refine ⟨?_, ih.2⟩
        change (decide (Block.meet p C = Block.node p s r x) ||
          Block.preceq (Block.meet p C) p) = true
        exact Bool.or_eq_true_iff.mpr (Or.inr ih.1)

theorem meet_preceq_left (B C : Block) : Block.Preceq (Block.meet B C) B :=
  (meet_prefix_statement B C).1

theorem meet_preceq_right (B C : Block) : Block.Preceq (Block.meet B C) C :=
  (meet_prefix_statement B C).2

/-- The walk retains every common prefix. -/
theorem meet_maximal_statement : MeetMaximalStatement := by
  rw [MeetMaximalStatement_def]
  intro X B C
  induction B with
  | genesis => intro h _; exact h
  | node p s r x ih =>
      intro hXB hXC
      rw [Block.meet_def]
      by_cases h : Block.Preceq (.node p s r x) C
      · simpa only [ite_eq_left h] using hXB
      · simp only [ite_eq_right h]
        apply ih _ hXC
        change (decide (X = Block.node p s r x) || Block.preceq X p) = true at hXB
        rcases Bool.or_eq_true_iff.mp hXB with he | hp
        · have heq : X = Block.node p s r x := of_decide_eq_true he
          exact (h (heq ▸ hXC)).elim
        · exact hp

theorem meet_maximal {X B C : Block} (hXB : Block.Preceq X B)
    (hXC : Block.Preceq X C) : Block.Preceq X (Block.meet B C) :=
  meet_maximal_statement X B C hXB hXC

theorem meet_comm_statement : MeetCommStatement := by
  rw [MeetCommStatement_def]
  intro B C
  apply block_preceq_antisymm
  · exact meet_maximal (meet_preceq_right B C) (meet_preceq_left B C)
  · exact meet_maximal (meet_preceq_right C B) (meet_preceq_left C B)

/-- The deepest common ancestor is independent of input order. -/
theorem meet_comm (B C : Block) : Block.meet B C = Block.meet C B :=
  meet_comm_statement B C

theorem meet_inclusion_statement : MeetInclusionStatement := by
  rw [MeetInclusionStatement_def]
  intro X B C
  constructor
  · intro h
    exact ⟨block_preceq_trans h (meet_preceq_left B C),
      block_preceq_trans h (meet_preceq_right B C)⟩
  · rintro ⟨hXB, hXC⟩
    exact meet_maximal hXB hXC

/-- A block precedes the meet exactly when it precedes both inputs. -/
theorem preceq_meet_iff (X B C : Block) : Block.Preceq X (Block.meet B C) ↔
    Block.Preceq X B ∧ Block.Preceq X C :=
  meet_inclusion_statement X B C

theorem meet_of_preceq_statement : MeetOfPreceqStatement := by
  rw [MeetOfPreceqStatement_def]
  intro B C h
  exact block_preceq_antisymm (meet_preceq_left B C)
    (meet_maximal (block_preceq_refl B) h)

/-- The meet of a prefix and its extension is the prefix. -/
theorem meet_of_preceq_left {B C : Block} (h : Block.Preceq B C) : Block.meet B C = B :=
  meet_of_preceq_statement B C h

theorem meet_of_preceq_right {B C : Block} (h : Block.Preceq C B) : Block.meet B C = C := by
  rw [meet_comm]
  exact meet_of_preceq_left h

theorem meet_self (B : Block) : Block.meet B B = B :=
  meet_of_preceq_left (block_preceq_refl B)

theorem meet_compatibility_transfer_statement : MeetCompatibilityTransferStatement := by
  rw [MeetCompatibilityTransferStatement_def]
  intro K C H X hK hX
  rw [hK] at hX
  obtain ⟨hXC, hXH⟩ := (preceq_meet_iff X C H).mp hX
  constructor
  · exact block_compatible_of_common hXC (block_preceq_refl C)
  · exact block_compatible_of_common hXH (block_preceq_refl H)

/-- A prefix of the common ancestor is compatible with each input. -/
theorem compatible_of_preceq_meet {K C H X : Block} (hK : K = Block.meet C H)
    (hX : Block.Preceq X K) : Block.Compatible X C ∧ Block.Compatible X H :=
  meet_compatibility_transfer_statement K C H X hK hX

end AvailableChain.Gen.Pure
