module
public import AvailableChainKitFG.Ancestry

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type}

/-! ## Local ancestry steps and the chain pool -/

section Ancestry
variable [DecidableEq V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:18-24
/-- [helper] An ancestor of the parent is an ancestor of the node. -/
theorem preceq_node_of_preceq {A p : FGBlock V} (s : Slot) (r_s : BlockId) (x : Nat) (rs : List
  (Row V))
    (h : FGBlock.Preceq A p) : FGBlock.Preceq A (.node p s r_s x rs) := by
  simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:66-70 (preceq_node)
/-- [helper] A block's parent precedes it. -/
theorem preceq_parent_node (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row
  V)) :
    FGBlock.Preceq p (.node p s r_s x rs) :=
  preceq_node_of_preceq s r_s x rs (preceq_refl p)

/-- [helper] A strict ancestor of a node is an ancestor of its parent. -/
theorem preceq_parent_of_preceq_node {A p : FGBlock V} {s : Slot} {r_s : BlockId} {x : Nat}
    {rs : List (Row V)} (h : FGBlock.Preceq A (.node p s r_s x rs))
    (hne : A ≠ .node p s r_s x rs) : FGBlock.Preceq A p := by
  simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h hne
  · exact h

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:16-17
/-- [helper] The row `a` is carried by a block of the chain that ends at `B`. -/
def OnChain (B : FGBlock V) (a : Row V) : Prop :=
  ∃ carrier : FGBlock V, FGBlock.Preceq carrier B ∧ a ∈ carrier.rows

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:134-141
/-- [helper] A row on the parent's chain is on the node's chain. -/
theorem onChain_parent {p : FGBlock V} (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    {a : Row V} (h : OnChain p a) : OnChain (.node p s r_s x rs) a := by
  obtain ⟨carrier, hc, ha⟩ := h
  exact ⟨carrier, preceq_node_of_preceq s r_s x rs hc, ha⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:144-145
/-- [helper] A block's own rows are on its chain. -/
theorem onChain_own (B : FGBlock V) {a : Row V} (h : a ∈ B.rows) : OnChain B a :=
  ⟨B, preceq_refl B, h⟩

end Ancestry

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Certificates.lean:23-25
/-- [helper] A superset of a quorum is a quorum. -/
theorem isQuorum_of_subset [Fintype V] (E : Electorate V) {S T : Finset V} (h : E.IsQuorum S)
    (hST : S ⊆ T) : E.IsQuorum T := by
  unfold Electorate.IsQuorum Electorate.weightOf at *
  exact h.trans (Finset.sum_le_sum_of_subset hST)

/-! ## The row fold, field by field
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:110-175) -/

section RowFold
variable [DecidableEq V] [RowCodec V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:112-121
/-- [helper] `process_row` writes only the three quorum sets. -/
theorem process_row_fields (σ : ChainState V) (a : Row V) :
    (process_row σ a).L = σ.L ∧ (process_row σ a).s = σ.s ∧
      (process_row σ a).h = σ.h ∧ (process_row σ a).T_h = σ.T_h ∧
      (process_row σ a).J = σ.J ∧ (process_row σ a).h_j = σ.h_j ∧
      (process_row σ a).F = σ.F ∧ (process_row σ a).h_F = σ.h_F := by
  unfold process_row
  dsimp only
  split_ifs <;> (try split) <;> (try split_ifs) <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:149-157
/-- [helper] `finalize` gains the signer exactly under the finality guard. -/
theorem process_row_finalize (σ : ChainState V) (a : Row V) :
    (process_row σ a).finalize =
      if decide (σ.h_F < σ.h_j) && decide (a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) then
        insert a.signer σ.finalize
      else σ.finalize := by
  unfold process_row
  dsimp only
  split_ifs <;> (try split) <;> (try split_ifs) <;> rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:136-145
/-- [helper] `progress` gains the signer exactly on a height pair that matches the
entry: a target or a timeout. -/
theorem process_row_progress (σ : ChainState V) (a : Row V) :
    (process_row σ a).progress =
      if a.height_pair.matchesEntry σ.h σ.T_h.root then insert a.signer σ.progress
      else σ.progress := by
  obtain ⟨i, hp, fp⟩ := a
  cases hp with
  | empty =>
      simp only [process_row, NamedHeightPair.matchesEntry]
      split_ifs <;> first | rfl | simp_all
  | vote k e t =>
      cases t <;> simp only [process_row] <;> split_ifs <;> rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:125-132
/-- [helper] `target_participation` gains the signer exactly on the target pair
`(σ.h, σ.T_h.root)` that is not a timeout. -/
theorem process_row_target (σ : ChainState V) (a : Row V) :
    (process_row σ a).target_participation =
      if a.height_pair = .vote σ.h σ.T_h.root false then
        insert a.signer σ.target_participation
      else σ.target_participation := by
  obtain ⟨i, hp, fp⟩ := a
  cases hp with
  | empty =>
      simp only [process_row, NamedHeightPair.matchesEntry]
      split_ifs <;> first | rfl | simp_all
  | vote k e t =>
      cases t <;> simp only [process_row, NamedHeightPair.matchesEntry] <;> split_ifs <;>
        first | rfl | simp_all

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:18-32
/-- [helper] The row fold writes only the three quorum sets. -/
theorem foldl_process_row_fields (rows : List (Row V)) (σ : ChainState V) :
    (rows.foldl process_row σ).L = σ.L ∧ (rows.foldl process_row σ).h = σ.h ∧
      (rows.foldl process_row σ).T_h = σ.T_h ∧ (rows.foldl process_row σ).J = σ.J ∧
      (rows.foldl process_row σ).h_j = σ.h_j ∧ (rows.foldl process_row σ).F = σ.F ∧
      (rows.foldl process_row σ).h_F = σ.h_F := by
  induction rows generalizing σ with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a rows ih =>
      obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := process_row_fields σ a
      obtain ⟨g1, g3, g4, g5, g6, g7, g8⟩ := ih (process_row σ a)
      exact ⟨g1.trans h1, g3.trans h3, g4.trans h4, g5.trans h5, g6.trans h6,
        g7.trans h7, g8.trans h8⟩

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:587-594 (the fold half of `transition`)
/-- [helper] The state after the row fold of `transition` and before its height
events (DC `fold_rows`). -/
def foldRows (σ : ChainState V) (B : FGBlock V) (rows : List (Row V)) : ChainState V :=
  { rows.foldl process_row { σ with s := B.slot } with L := B }

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:18-32
/-- [helper] The fold of `transition` sets `L` and keeps the height and anchor
fields. -/
theorem foldRows_fields (σ : ChainState V) (B : FGBlock V) (rows : List (Row V)) :
    (foldRows σ B rows).L = B ∧ (foldRows σ B rows).h = σ.h ∧
      (foldRows σ B rows).T_h = σ.T_h ∧ (foldRows σ B rows).J = σ.J ∧
      (foldRows σ B rows).h_j = σ.h_j ∧ (foldRows σ B rows).F = σ.F ∧
      (foldRows σ B rows).h_F = σ.h_F := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := foldl_process_row_fields rows { σ with s := B.slot }
  exact ⟨rfl, h2, h3, h4, h5, h6, h7⟩

/-- [helper] `process_row` keeps `s`, so the row fold keeps it. -/
theorem foldl_process_row_s (rows : List (Row V)) (σ : ChainState V) :
    (rows.foldl process_row σ).s = σ.s := by
  induction rows generalizing σ with
  | nil => rfl
  | cons a rows ih => exact (ih _).trans (process_row_fields σ a).2.1

/-- [helper] The row fold of `transition` sets `s` to the block's slot. -/
theorem foldRows_s (σ : ChainState V) (B : FGBlock V) (rows : List (Row V)) :
    (foldRows σ B rows).s = B.slot :=
  foldl_process_row_s rows { σ with s := B.slot }

end RowFold

/-! ## `process_height_events`, split at its finality branch
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:186-339) -/

section HeightEvents
variable [Fintype V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:226-227
/-- [helper] The state after the finality branch of `process_height_events` and
before its two height branches. -/
def afterFin (E : Electorate V) (σ : ChainState V) : ChainState V :=
  if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ

section AfterFin
variable (E : Electorate V) (σ : ChainState V)

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:232-233
/-- [helper] The finality branch keeps the height `h`. -/
theorem afterFin_h : (afterFin E σ).h = σ.h := by unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:236-237
/-- [helper] The finality branch keeps the entry `T_h`. -/
theorem afterFin_T_h : (afterFin E σ).T_h = σ.T_h := by unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:240-241
/-- [helper] The finality branch keeps the latest block `L`. -/
theorem afterFin_L : (afterFin E σ).L = σ.L := by unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:244-245
/-- [helper] The finality branch keeps the justified block `J`. -/
theorem afterFin_J : (afterFin E σ).J = σ.J := by unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:249-250
/-- [helper] The finality branch keeps the justified height `h_j`. -/
theorem afterFin_h_j : (afterFin E σ).h_j = σ.h_j := by unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:254-256
/-- [helper] The finality branch keeps the target-participation set. -/
theorem afterFin_target_participation :
    (afterFin E σ).target_participation = σ.target_participation := by
  unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:259-260
/-- [helper] The finality branch keeps the progress set. -/
theorem afterFin_progress : (afterFin E σ).progress = σ.progress := by
  unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:263-264
/-- [helper] The finality branch keeps the finality set. -/
theorem afterFin_finalize : (afterFin E σ).finalize = σ.finalize := by
  unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:298-300
/-- [helper] The finality branch sets `F := J` under `finalityReady`; else `F` stays. -/
theorem afterFin_F : (afterFin E σ).F = if finalityReady E σ then σ.J else σ.F := by
  unfold afterFin; split_ifs <;> rfl
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:303-305
/-- [helper] The finality branch sets `h_F := h_j` under `finalityReady`; else `h_F` stays. -/
theorem afterFin_h_F : (afterFin E σ).h_F = if finalityReady E σ then σ.h_j else σ.h_F := by
  unfold afterFin; split_ifs <;> rfl
/-- [helper] The finality branch keeps the slot `s`. -/
theorem afterFin_s : (afterFin E σ).s = σ.s := by unfold afterFin; split_ifs <;> rfl

end AfterFin

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:272-282
/-- [helper] `process_height_events`, split at its finality branch. The
justification branch has the guard `targetQuorum` alone: no `nj`. -/
theorem process_height_events_eq (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    process_height_events E cfg σ =
      if (afterFin E σ).targetQuorum E then
        advance_height
          { afterFin E σ with
            J := (afterFin E σ).T_h
            h_j := (afterFin E σ).h
            finalize := ∅ }
      else if progReady E cfg (afterFin E σ) then advance_height (afterFin E σ)
      else afterFin E σ := rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:71-74
/-- [helper] The height events keep the latest block. -/
theorem process_height_events_L (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    (process_height_events E cfg σ).L = σ.L := by
  rw [process_height_events_eq]
  split_ifs <;> exact afterFin_L E σ

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:286-295
/-- [helper] Only the finality branch writes `F` and `h_F`. -/
theorem process_height_events_F (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    (process_height_events E cfg σ).F = (afterFin E σ).F ∧
      (process_height_events E cfg σ).h_F = (afterFin E σ).h_F := by
  rw [process_height_events_eq]
  split_ifs <;> exact ⟨rfl, rfl⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:310-314
/-- [helper] `finalityReady` carries a finality quorum. -/
theorem isQuorum_of_finalityReady (E : Electorate V) {σ : ChainState V}
    (h : finalityReady E σ = true) : E.IsQuorum σ.finalize := by
  simp only [finalityReady, Bool.and_eq_true, ChainState.finalityQuorum,
    decide_eq_true_eq] at h
  exact h.2

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:317-320
/-- [helper] `finalityReady` carries `h_F < h_j`. -/
theorem lt_of_finalityReady (E : Electorate V) {σ : ChainState V}
    (h : finalityReady E σ = true) : σ.h_F < σ.h_j := by
  simp only [finalityReady, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:323-327
/-- [helper] The justification guard carries a target quorum. -/
theorem isQuorum_of_targetQuorum (E : Electorate V) {σ : ChainState V}
    (h : σ.targetQuorum E = true) : E.IsQuorum σ.target_participation := by
  simp only [ChainState.targetQuorum, decide_eq_true_eq] at h
  exact h

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:331-339
/-- [helper] `progReady` carries a target quorum, or a mature progress quorum. -/
theorem quorum_of_progReady (E : Electorate V) (cfg : FGConfig) {σ : ChainState V}
    (h : progReady E cfg σ = true) :
    E.IsQuorum σ.target_participation ∨
      (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s ∧ E.IsQuorum σ.progress) := by
  simp only [progReady, Bool.or_eq_true, Bool.and_eq_true, ChainState.targetQuorum,
    ChainState.progQuorum, decide_eq_true_eq] at h
  exact h

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:181-199
-- (certificate_step, without its quorum half; finality_certificate has that half)
/-- [helper] The finalization pair is kept, or the finality branch copies the
justification pair under `finalityReady`. -/
theorem finality_pair_cases (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    ((process_height_events E cfg σ).F = σ.F ∧
        (process_height_events E cfg σ).h_F = σ.h_F) ∨
      ((process_height_events E cfg σ).F = σ.J ∧
        (process_height_events E cfg σ).h_F = σ.h_j ∧ finalityReady E σ = true) := by
  obtain ⟨hF, hhF⟩ := process_height_events_F E cfg σ
  rw [hF, hhF, afterFin_F, afterFin_h_F]
  by_cases hf : finalityReady E σ = true
  · rw [ite_eq_left hf, ite_eq_left hf]
    exact Or.inr ⟨rfl, rfl, hf⟩
  · rw [ite_eq_right hf, ite_eq_right hf]
    exact Or.inl ⟨rfl, rfl⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/JustificationCertificates.lean:183-195
/-- [helper] The justification pair is kept, or the justification branch writes
`(J, h_j) ← (T_h, h)` under a target quorum. -/
theorem justification_pair_cases (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    ((process_height_events E cfg σ).J = σ.J ∧
        (process_height_events E cfg σ).h_j = σ.h_j) ∨
      ((process_height_events E cfg σ).J = σ.T_h ∧
        (process_height_events E cfg σ).h_j = σ.h ∧ E.IsQuorum σ.target_participation) := by
  rw [process_height_events_eq]
  split_ifs with ht
  · refine Or.inr ⟨afterFin_T_h E σ, afterFin_h E σ, ?_⟩
    have hq := isQuorum_of_targetQuorum E ht
    rwa [afterFin_target_participation] at hq
  · exact Or.inl ⟨afterFin_J E σ, afterFin_h_j E σ⟩
  · exact Or.inl ⟨afterFin_J E σ, afterFin_h_j E σ⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Certificates.lean:43-59
/-- [helper] One transition raises the height by at most one, and only on a
progress quorum. -/
theorem height_advance_step (E : Electorate V) (cfg : FGConfig) {σ : ChainState V}
    (hsub : σ.target_participation ⊆ σ.progress) :
    (process_height_events E cfg σ).h = σ.h ∨
      ((process_height_events E cfg σ).h = σ.h + 1 ∧ E.IsQuorum σ.progress) := by
  rw [process_height_events_eq]
  split_ifs with h1 h2
  · refine Or.inr ⟨congrArg (· + 1) (afterFin_h E σ), ?_⟩
    have hq := isQuorum_of_targetQuorum E h1
    rw [afterFin_target_participation] at hq
    exact isQuorum_of_subset E hq hsub
  · refine Or.inr ⟨congrArg (· + 1) (afterFin_h E σ), ?_⟩
    rcases quorum_of_progReady E cfg h2 with hq | ⟨-, hq⟩
    · rw [afterFin_target_participation] at hq
      exact isQuorum_of_subset E hq hsub
    · rwa [afterFin_progress] at hq
  · exact Or.inl (afterFin_h E σ)

end HeightEvents

/-! ## Chain order
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:421-495,
DerivationGeometry.lean:36-111) -/

section ChainOrderSec
variable [DecidableEq V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:421-432
/-- [helper] The ancestry and height order of a chain state:
`F ⪯ J ⪯ T_h ⪯ L` and `h_F ≤ h_j < h`. -/
structure ChainOrder (σ : ChainState V) : Prop where
  target_preceq_latest : FGBlock.Preceq σ.T_h σ.L
  justified_preceq_target : FGBlock.Preceq σ.J σ.T_h
  finalized_preceq_justified : FGBlock.Preceq σ.F σ.J
  heights_ordered : σ.h_F ≤ σ.h_j
  justified_below_height : σ.h_j < σ.h

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:435-438
/-- [helper] The finalized block is on the chain. -/
theorem ChainOrder.finalized_preceq_latest {σ : ChainState V} (h : ChainOrder σ) :
    FGBlock.Preceq σ.F σ.L :=
  preceq_trans h.finalized_preceq_justified
    (preceq_trans h.justified_preceq_target h.target_preceq_latest)

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:442-444
/-- [helper] A chain state that finalized at `h_F` has left that height. -/
theorem ChainOrder.finalized_below_height {σ : ChainState V} (h : ChainOrder σ) :
    σ.h_F < σ.h :=
  Nat.lt_of_le_of_lt h.heights_ordered h.justified_below_height

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:447-452
/-- [helper] The initial chain state has the chain order. -/
theorem chainOrder_initial : ChainOrder (ChainState.initial : ChainState V) :=
  { target_preceq_latest := preceq_refl _
    justified_preceq_target := preceq_refl _
    finalized_preceq_justified := preceq_refl _
    heights_ordered := Nat.le_refl 0
    justified_below_height := Nat.zero_lt_one }

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:36-67
/-- [helper] The row fold keeps the chain order when the new latest block extends
the old one. -/
theorem chainOrder_foldRows [RowCodec V] {σ : ChainState V} (B : FGBlock V) (rows : List (Row V))
    (h : ChainOrder σ) (hL : FGBlock.Preceq σ.L B) : ChainOrder (foldRows σ B rows) := by
  obtain ⟨hL', hh, hT, hJ, hhj, hF, hhF⟩ := foldRows_fields σ B rows
  refine
    { target_preceq_latest := ?_
      justified_preceq_target := ?_
      finalized_preceq_justified := ?_
      heights_ordered := ?_
      justified_below_height := ?_ }
  · rw [hT, hL']
    exact preceq_trans h.target_preceq_latest hL
  · rw [hJ, hT]
    exact h.justified_preceq_target
  · rw [hF, hJ]
    exact h.finalized_preceq_justified
  · rw [hhF, hhj]
    exact h.heights_ordered
  · rw [hhj, hh]
    exact h.justified_below_height

end ChainOrderSec

/-! ## Row witnesses of the quorum sets
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:19-159,
FinalityCertificates.lean:59-156, JustificationCertificates.lean:59-172) -/

variable [RowCodec V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:19-22
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:60-62
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/JustificationCertificates.lean:60-62
/-- [helper] Each member of a quorum set of `σ` has a row in `pool` that put it
there, and `target_participation ⊆ progress`. DC keeps three predicates
(`MatchingWitnesses`, `FinalizeRows`, `TargetRows`); this one bundles them. -/
structure RowWitnesses (pool : Row V → Prop) (σ : ChainState V) : Prop where
  target_sub : σ.target_participation ⊆ σ.progress
  target : ∀ i ∈ σ.target_participation, ∃ a, pool a ∧ a.signer = i ∧
    a.height_pair = .vote σ.h σ.T_h.root false
  progress : ∀ i ∈ σ.progress, ∃ a, pool a ∧ a.signer = i ∧
    a.height_pair.matchesEntry σ.h σ.T_h.root = true
  finalize : ∀ i ∈ σ.finalize, ∃ a, pool a ∧ a.signer = i ∧
    a.finality_pair = some ⟨σ.h_j, σ.J.root⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:45-50
/-- [helper] Empty quorum sets have witnesses in every pool. -/
theorem witnesses_empty {pool : Row V → Prop} {τ : ChainState V}
    (ht : τ.target_participation = ∅) (hp : τ.progress = ∅) (hf : τ.finalize = ∅) :
    RowWitnesses pool τ := by
  refine ⟨by rw [ht]; exact Finset.empty_subset _, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · rw [ht] at hi
    simp at hi
  · rw [hp] at hi
    simp at hi
  · rw [hf] at hi
    simp at hi

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:53-58
/-- [helper] Witnesses stay witnesses in a larger pool. -/
theorem witnesses_mono {pool next : Row V → Prop} {σ : ChainState V}
    (h : RowWitnesses pool σ) (hsub : ∀ a, pool a → next a) : RowWitnesses next σ := by
  refine ⟨h.target_sub, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨a, ha, hs, hp⟩ := h.target i hi
    exact ⟨a, hsub a ha, hs, hp⟩
  · obtain ⟨a, ha, hs, hp⟩ := h.progress i hi
    exact ⟨a, hsub a ha, hs, hp⟩
  · obtain ⟨a, ha, hs, hp⟩ := h.finalize i hi
    exact ⟨a, hsub a ha, hs, hp⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:61-70
/-- [helper] Witnesses transfer to a state with the same read fields. -/
theorem witnesses_congr {pool : Row V → Prop} {σ τ : ChainState V}
    (h : RowWitnesses pool σ) (hh : τ.h = σ.h) (hT : τ.T_h = σ.T_h) (hJ : τ.J = σ.J)
    (hhj : τ.h_j = σ.h_j) (ht : τ.target_participation = σ.target_participation)
    (hp : τ.progress = σ.progress) (hf : τ.finalize = σ.finalize) :
    RowWitnesses pool τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht, hp]
    exact h.target_sub
  · rw [ht, hh, hT]
    exact h.target
  · rw [hp, hh, hT]
    exact h.progress
  · rw [hf, hhj, hJ]
    exact h.finalize

/-- [helper] `advance_height` clears target and progress, and keeps the finality
witnesses. -/
theorem witnesses_advance {pool : Row V → Prop} {σ : ChainState V}
    (hf : ∀ i ∈ σ.finalize, ∃ a, pool a ∧ a.signer = i ∧
      a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) :
    RowWitnesses pool (advance_height σ) := by
  refine ⟨Finset.empty_subset _, fun i hi => ?_, fun i hi => ?_, hf⟩
  · simp [advance_height] at hi
  · simp [advance_height] at hi

section WitnessesRowFold
variable [DecidableEq V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:74-90
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:88-98
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/JustificationCertificates.lean:88-114
/-- [helper] A row of the pool keeps the witnesses. -/
theorem witnesses_process {pool : Row V → Prop} {σ : ChainState V} {a : Row V}
    (ha : pool a) (h : RowWitnesses pool σ) : RowWitnesses pool (process_row σ a) := by
  obtain ⟨-, -, hh, hT, hJ, hhj, -, -⟩ := process_row_fields σ a
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · intro i hi
    rw [process_row_target] at hi
    rw [process_row_progress]
    split_ifs at hi with ht
    · have hm : a.height_pair.matchesEntry σ.h σ.T_h.root = true := by
        rw [ht]
        simp [NamedHeightPair.matchesEntry]
      rw [ite_eq_left hm]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h.target_sub hi)
    · split_ifs
      · exact Finset.mem_insert_of_mem (h.target_sub hi)
      · exact h.target_sub hi
  · rw [process_row_target] at hi
    rw [hh, hT]
    split_ifs at hi with ht
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨a, ha, rfl, ht⟩
      · exact h.target i hi
    · exact h.target i hi
  · rw [process_row_progress] at hi
    rw [hh, hT]
    split_ifs at hi with hm
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨a, ha, rfl, hm⟩
      · exact h.progress i hi
    · exact h.progress i hi
  · rw [process_row_finalize] at hi
    rw [hhj, hJ]
    split_ifs at hi with hc
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨a, ha, rfl, hc.2⟩
      · exact h.finalize i hi
    · exact h.finalize i hi

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:94-103
/-- [helper] A fold of pool rows keeps the witnesses. -/
theorem witnesses_fold {pool : Row V → Prop} (rows : List (Row V)) {σ : ChainState V}
    (hrows : ∀ a ∈ rows, pool a) (h : RowWitnesses pool σ) :
    RowWitnesses pool (rows.foldl process_row σ) := by
  induction rows generalizing σ with
  | nil => exact h
  | cons a rows ih =>
      exact ih (fun b hb => hrows b (List.mem_cons_of_mem a hb))
        (witnesses_process (hrows a (List.mem_cons_self ..)) h)

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:107-113
/-- [helper] The fold of `transition` keeps the witnesses. -/
theorem witnesses_foldRows {pool : Row V → Prop} {σ : ChainState V} (B : FGBlock V)
    (rows : List (Row V)) (hrows : ∀ a ∈ rows, pool a) (h : RowWitnesses pool σ) :
    RowWitnesses pool (foldRows σ B rows) :=
  witnesses_congr (σ := rows.foldl process_row { σ with s := B.slot })
    (witnesses_fold rows hrows
      (witnesses_congr (τ := { σ with s := B.slot }) h rfl rfl rfl rfl rfl rfl rfl))
    rfl rfl rfl rfl rfl rfl rfl

end WitnessesRowFold

section WitnessesHeightEvents
variable [Fintype V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:115-127
/-- [helper] The height events keep the witnesses: both height branches clear
target and progress, and the justification branch clears `finalize`. -/
theorem witnesses_height_events (E : Electorate V) (cfg : FGConfig) {pool : Row V → Prop}
    {σ : ChainState V} (h : RowWitnesses pool σ) :
    RowWitnesses pool (process_height_events E cfg σ) := by
  have hτ : RowWitnesses pool (afterFin E σ) :=
    witnesses_congr h (afterFin_h E σ) (afterFin_T_h E σ) (afterFin_J E σ)
      (afterFin_h_j E σ) (afterFin_target_participation E σ) (afterFin_progress E σ)
      (afterFin_finalize E σ)
  rw [process_height_events_eq]
  split_ifs
  · exact witnesses_advance (fun i hi => by simp at hi)
  · exact witnesses_advance hτ.finalize
  · exact hτ

end WitnessesHeightEvents

/-! ## The derivation -/

variable [DecidableEq V] [Fintype V]

-- port: DC/DecoupledConsensusProofs/Protocol/Handlers/BlockProcessingDefaults.lean:22-27
/-- [helper] One step of `derive`: the row fold, then the height events. -/
theorem derive_node (E : Electorate V) (cfg : FGConfig) (p : FGBlock V) (s : Slot) (r_s : BlockId)
    (x : Nat) (rs : List (Row V)) :
    derive E cfg (.node p s r_s x rs) =
      process_height_events E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs) := rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:82-87
/-- [helper] The latest block of `derive E cfg B` is `B`. -/
theorem derive_L (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    (derive E cfg B).L = B := by
  cases B with
  | genesis => rfl
  | node p s r_s x rs =>
      rw [derive_node, process_height_events_L]
      rfl

omit [RowCodec V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:460-470
/-- [helper] The finality branch keeps the chain order: `F ← J` is the reflexive
case of `F ⪯ J`. -/
theorem chainOrder_afterFin (E : Electorate V) {σ : ChainState V} (h : ChainOrder σ) :
    ChainOrder (afterFin E σ) := by
  unfold afterFin
  split_ifs
  · exact
      { target_preceq_latest := h.target_preceq_latest
        justified_preceq_target := h.justified_preceq_target
        finalized_preceq_justified := preceq_refl _
        heights_ordered := Nat.le_refl _
        justified_below_height := h.justified_below_height }
  · exact h

omit [RowCodec V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:475-495
/-- [helper] `process_height_events` keeps the chain order: the justification
branch uses `J ⪯ T_h` and `h_j < h`, and `advance_height` uses `T_h ⪯ L`. -/
theorem chainOrder_process_height_events (E : Electorate V) (cfg : FGConfig)
    {σ : ChainState V} (h : ChainOrder σ) : ChainOrder (process_height_events E cfg σ) := by
  have h' := chainOrder_afterFin E h
  rw [process_height_events_eq]
  split_ifs
  · exact
      { target_preceq_latest := preceq_refl _
        justified_preceq_target := h'.target_preceq_latest
        finalized_preceq_justified :=
          preceq_trans h'.finalized_preceq_justified h'.justified_preceq_target
        heights_ordered := Nat.le_of_lt h'.finalized_below_height
        justified_below_height := Nat.lt_succ_self _ }
  · exact
      { target_preceq_latest := preceq_refl _
        justified_preceq_target :=
          preceq_trans h'.justified_preceq_target h'.target_preceq_latest
        finalized_preceq_justified := h'.finalized_preceq_justified
        heights_ordered := h'.heights_ordered
        justified_below_height := Nat.lt_succ_of_lt h'.justified_below_height }
  · exact h'

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:91-102
/-- [helper] Every derived chain state has the chain order. -/
theorem chainOrder_derive (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    ChainOrder (derive E cfg B) := by
  induction B with
  | genesis => exact chainOrder_initial
  | node p s r_s x rs ih =>
      rw [derive_node]
      apply chainOrder_process_height_events
      apply chainOrder_foldRows _ _ ih
      rw [derive_L]
      exact preceq_parent_node p s r_s x rs

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/DerivationGeometry.lean:104-111
/-- [helper] `F ⪯ D` and `J ⪯ D`. -/
theorem derive_anchors_preceq (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    FGBlock.Preceq (derive E cfg D).F D ∧ FGBlock.Preceq (derive E cfg D).J D := by
  have h := chainOrder_derive E cfg D
  refine ⟨?_, ?_⟩
  · have hF := h.finalized_preceq_latest
    rwa [derive_L] at hF
  · have hJ := preceq_trans h.justified_preceq_target h.target_preceq_latest
    rwa [derive_L] at hJ

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:427
/-- [helper] `F ⪯ J`. -/
theorem derive_F_preceq_J (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    FGBlock.Preceq (derive E cfg D).F (derive E cfg D).J :=
  (chainOrder_derive E cfg D).finalized_preceq_justified

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:429
/-- [helper] `h_F ≤ h_j`. -/
theorem heights_ordered (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    (derive E cfg D).h_F ≤ (derive E cfg D).h_j :=
  (chainOrder_derive E cfg D).heights_ordered

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:432
/-- [helper] `h_j < h`: `advance_height` leaves `h_j` at the height it left. -/
theorem justified_below_height (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    (derive E cfg D).h_j < (derive E cfg D).h :=
  (chainOrder_derive E cfg D).justified_below_height

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:442-444
/-- [helper] A chain that finalized at `h_F` has left that height (port: DC
`ChainOrder.finalized_below_height`, Chain.lean:442). -/
theorem finalized_below_height (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    (derive E cfg D).h_F < (derive E cfg D).h :=
  (chainOrder_derive E cfg D).finalized_below_height

/-- [helper] Every derived state height is at least 1. -/
theorem one_le_h (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    1 ≤ (derive E cfg D).h := by
  have := justified_below_height E cfg D
  simp only [Height] at *
  omega

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:109-113
/-- [helper] The entry is on the chain: `T_h ⪯ D`. -/
theorem entry_preceq (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    FGBlock.Preceq (derive E cfg D).T_h D := by
  have h := (chainOrder_derive E cfg D).target_preceq_latest
  rwa [derive_L] at h

/-! ## Entry geometry
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:39-151) -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:41-62
/-- [helper] A block keeps the height and the entry of its parent, or it raises
the height by one and is the new entry. -/
theorem derive_node_height_entry_cases (E : Electorate V) (cfg : FGConfig) (p : FGBlock V)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) :
    ((derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h ∧
        (derive E cfg (.node p s r_s x rs)).T_h = (derive E cfg p).T_h) ∨
      ((derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h + 1 ∧
        (derive E cfg (.node p s r_s x rs)).T_h = .node p s r_s x rs) := by
  obtain ⟨hL, hh, hT, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
  rw [derive_node, process_height_events_eq]
  split_ifs
  · exact Or.inr ⟨congrArg (· + 1) ((afterFin_h E _).trans hh), (afterFin_L E _).trans hL⟩
  · exact Or.inr ⟨congrArg (· + 1) ((afterFin_h E _).trans hh), (afterFin_L E _).trans hL⟩
  · exact Or.inl ⟨(afterFin_h E _).trans hh, (afterFin_T_h E _).trans hT⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:64-73
/-- [helper] A block raises the height of its parent by at most one. -/
theorem derive_node_height_cases (E : Electorate V) (cfg : FGConfig) (p : FGBlock V)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) :
    (derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h ∨
      (derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h + 1 := by
  rcases derive_node_height_entry_cases E cfg p s r_s x rs with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:77-91
/-- [helper] The state height does not decrease along the chain. -/
theorem h_mono (E : Electorate V) (cfg : FGConfig) {A B : FGBlock V}
    (hAB : FGBlock.Preceq A B) : (derive E cfg A).h ≤ (derive E cfg B).h := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact le_refl _
  | node p s r_s x rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hp
      · exact le_refl _
      · have hle := ih hp
        rcases derive_node_height_cases E cfg p s r_s x rs with h | h <;>
          (simp only [Height] at *; omega)

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:95-107
/-- [helper] The entry has the state height of the chain. -/
theorem entry_same_height (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    (derive E cfg (derive E cfg B).T_h).h = (derive E cfg B).h := by
  induction B with
  | genesis => rfl
  | node p s r_s x rs ih =>
      rcases derive_node_height_entry_cases E cfg p s r_s x rs with h | h
      · rw [h.2, h.1]
        exact ih
      · rw [h.2]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:116-129
/-- [helper] Equal child and parent heights force equal entries. -/
theorem node_entry_eq_of_height_eq (E : Electorate V) (cfg : FGConfig) (p : FGBlock V)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hh : (derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h) :
    (derive E cfg (.node p s r_s x rs)).T_h = (derive E cfg p).T_h := by
  rcases derive_node_height_entry_cases E cfg p s r_s x rs with h | h
  · exact h.2
  · exfalso
    have := h.1
    simp only [Height] at *
    omega

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:131-151
/-- [helper] Two blocks of one chain at one state height have one entry. -/
theorem entry_eq_on_plateau (E : Electorate V) (cfg : FGConfig) {A B : FGBlock V}
    (hAB : FGBlock.Preceq A B) (hh : (derive E cfg A).h = (derive E cfg B).h) :
    (derive E cfg A).T_h = (derive E cfg B).T_h := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      rfl
  | node p s r_s x rs ih =>
      by_cases hAe : A = .node p s r_s x rs
      · subst hAe
        rfl
      · have hp := preceq_parent_of_preceq_node hAB hAe
        have hlow := h_mono E cfg hp
        have hhigh := h_mono E cfg (preceq_parent_node p s r_s x rs)
        have hpar : (derive E cfg p).h = (derive E cfg (.node p s r_s x rs)).h := by
          simp only [Height] at *; omega
        exact (ih hp (hh.trans hpar.symm)).trans
          (node_entry_eq_of_height_eq E cfg p s r_s x rs hpar.symm).symm

/-- [helper] The entry of an entry is itself. -/
theorem entry_idem (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    (derive E cfg (derive E cfg B).T_h).T_h = (derive E cfg B).T_h :=
  entry_eq_on_plateau E cfg (entry_preceq E cfg B) (entry_same_height E cfg B)

/-- [helper] A non-genesis entry is a block that raised the height: its parent
has a smaller state height than the chain. -/
theorem entry_parent_height (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hT : (derive E cfg D).T_h ≠ .genesis) :
    (derive E cfg (derive E cfg D).T_h.parent).h < (derive E cfg D).h := by
  induction D with
  | genesis => exact absurd rfl hT
  | node p s r_s x rs ih =>
      rcases derive_node_height_entry_cases E cfg p s r_s x rs with h | h
      · rw [h.2] at hT ⊢
        rw [h.1]
        exact ih hT
      · rw [h.2, h.1]
        exact Nat.lt_succ_self _

/-! ## Witnesses on the chain -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:147-159
/-- [helper] Every quorum set of `derive E cfg B` has witnesses on the chain of
`B`. -/
theorem derive_witnesses (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    RowWitnesses (OnChain B) (derive E cfg B) := by
  induction B with
  | genesis => exact witnesses_empty rfl rfl rfl
  | node p s r_s x rs ih =>
      rw [derive_node]
      exact witnesses_height_events E cfg
        (witnesses_foldRows _ rs (fun _ ha => onChain_own (.node p s r_s x rs) ha)
          (witnesses_mono ih (fun _ ha => onChain_parent s r_s x rs ha)))

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:147-156
/-- [helper] The folded state of a node has witnesses on the node's chain. -/
theorem folded_witnesses (E : Electorate V) (cfg : FGConfig) (p : FGBlock V) (s : Slot) (r_s :
  BlockId)
    (x : Nat) (rs : List (Row V)) :
    RowWitnesses (OnChain (.node p s r_s x rs)) (foldRows (derive E cfg p) (.node p s r_s x rs)
      rs) :=
  witnesses_foldRows _ rs (fun _ ha => onChain_own (.node p s r_s x rs) ha)
    (witnesses_mono (derive_witnesses E cfg p) (fun _ ha => onChain_parent s r_s x rs ha))

/-! ## The height crossing
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:161-189,
FinalityCertificates.lean:266-307) -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/MatchingProgress.lean:161-189
/-- [helper] A block that raises the height carries, on its chain, a quorum of
rows that match the parent's height and entry. -/
theorem crossing_matching_quorum (E : Electorate V) (cfg : FGConfig) (p : FGBlock V)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hAdvance : (derive E cfg (.node p s r_s x rs)).h ≠ (derive E cfg p).h) :
    ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ carrier : FGBlock V, ∃ a : Row V,
        FGBlock.Preceq carrier (.node p s r_s x rs) ∧ a ∈ carrier.rows ∧ a.signer = i ∧
        a.height_pair.matchesEntry (derive E cfg p).h (derive E cfg p).T_h.root = true := by
  have hw := folded_witnesses E cfg p s r_s x rs
  obtain ⟨-, hh, hT, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
  rcases height_advance_step E cfg hw.target_sub with hstay | ⟨-, hq⟩
  · exfalso
    apply hAdvance
    rw [derive_node]
    exact hstay.trans hh
  · refine ⟨_, hq, fun i hi => ?_⟩
    obtain ⟨a, ⟨carrier, hc, ha⟩, hs, hm⟩ := hw.progress i hi
    rw [hh, hT] at hm
    exact ⟨carrier, a, hc, ha, hs, hm⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:266-307
/-- [helper] Every height `1 ≤ h` below the state height of `C` was left on `C`'s
chain: its entry `X` is on the chain, and a quorum of rows on the chain matches
`(h, X.root)`. -/
theorem height_crossing (E : Electorate V) (cfg : FGConfig) (C : FGBlock V) (h : Height)
    (hpos : 1 ≤ h) (hlt : h < (derive E cfg C).h) :
    ∃ X : FGBlock V, FGBlock.Preceq X C ∧ (derive E cfg X).h = h ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier : FGBlock V, ∃ a : Row V,
          FGBlock.Preceq carrier C ∧ a ∈ carrier.rows ∧ a.signer = i ∧
          a.height_pair.matchesEntry h X.root = true := by
  induction C with
  | genesis =>
      change h < 1 at hlt
      simp only [Height] at *
      omega
  | node p s r_s x rs ih =>
      by_cases hp : h < (derive E cfg p).h
      · obtain ⟨X, hX, hXh, Q, hQ, hw⟩ := ih hp
        refine ⟨X, preceq_node_of_preceq s r_s x rs hX, hXh, Q, hQ, fun i hi => ?_⟩
        obtain ⟨carrier, a, hc, ha, hs, hm⟩ := hw i hi
        exact ⟨carrier, a, preceq_node_of_preceq s r_s x rs hc, ha, hs, hm⟩
      · have hParent : (derive E cfg p).h = h := by
          rcases derive_node_height_cases E cfg p s r_s x rs with h1 | h1 <;>
            (simp only [Height] at *; omega)
        have hAdvance : (derive E cfg (.node p s r_s x rs)).h ≠ (derive E cfg p).h := by
          simp only [Height] at *; omega
        obtain ⟨Q, hQ, hw⟩ := crossing_matching_quorum E cfg p s r_s x rs hAdvance
        refine ⟨(derive E cfg p).T_h, preceq_node_of_preceq s r_s x rs (entry_preceq E cfg p),
          (entry_same_height E cfg p).trans hParent, Q, hQ, fun i hi => ?_⟩
        obtain ⟨carrier, a, hc, ha, hs, hm⟩ := hw i hi
        rw [hParent] at hm
        exact ⟨carrier, a, hc, ha, hs, hm⟩

/-! ## Certificates
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:201-264,
JustificationCertificates.lean:232-298) -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:201-221
/-- [helper] A zero finalized height names genesis. -/
theorem finalized_zero_is_genesis (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hz : (derive E cfg D).h_F = 0) : (derive E cfg D).F = .genesis := by
  induction D with
  | genesis => rfl
  | node p s r_s x rs ih =>
      obtain ⟨-, -, -, -, -, hF, hhF⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      rw [derive_node] at hz ⊢
      rcases finality_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs) with
        ⟨h1, h2⟩ | ⟨-, h2, hf⟩
      · rw [h1, hF]
        exact ih (hhF.symm.trans (h2.symm.trans hz))
      · have := lt_of_finalityReady E hf
        simp only [Height] at *
        omega

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:223-264
/-- [helper] A nonzero finalized height has, on the chain, a quorum of rows with
the finality pair `(h_F, F.root)`. -/
theorem finality_certificate (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_F ≠ 0) :
    ∃ F : FGBlock V, FGBlock.Preceq F D ∧ F = (derive E cfg D).F ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier : FGBlock V, ∃ a : Row V,
          FGBlock.Preceq carrier D ∧ a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨(derive E cfg D).h_F, F.root⟩ := by
  refine ⟨_, (derive_anchors_preceq E cfg D).1, rfl, ?_⟩
  induction D with
  | genesis => exact absurd rfl hnz
  | node p s r_s x rs ih =>
      obtain ⟨-, -, -, -, -, hF, hhF⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      have hw := folded_witnesses E cfg p s r_s x rs
      rw [derive_node] at hnz ⊢
      rcases finality_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs) with
        ⟨h1, h2⟩ | ⟨h1, h2, hf⟩
      · rw [h1, h2, hF, hhF]
        rw [h2, hhF] at hnz
        obtain ⟨Q, hQ, hw'⟩ := ih hnz
        refine ⟨Q, hQ, fun i hi => ?_⟩
        obtain ⟨carrier, a, hc, ha, hs, hp⟩ := hw' i hi
        exact ⟨carrier, a, preceq_node_of_preceq s r_s x rs hc, ha, hs, hp⟩
      · rw [h1, h2]
        refine ⟨_, isQuorum_of_finalityReady E hf, fun i hi => ?_⟩
        obtain ⟨a, ⟨carrier, hc, ha⟩, hs, hp⟩ := hw.finalize i hi
        exact ⟨carrier, a, hc, ha, hs, hp⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/JustificationCertificates.lean:232-253
/-- [helper] A zero justified height names genesis. -/
theorem justified_zero_is_genesis (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hz : (derive E cfg D).h_j = 0) : (derive E cfg D).J = .genesis := by
  induction D with
  | genesis => rfl
  | node p s r_s x rs ih =>
      obtain ⟨-, hh, -, hJ, hhj, -, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      have hpos := justified_below_height E cfg p
      rw [derive_node] at hz ⊢
      rcases justification_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs)
        with ⟨h1, h2⟩ | ⟨-, h2, -⟩
      · rw [h1, hJ]
        exact ih (hhj.symm.trans (h2.symm.trans hz))
      · simp only [Height] at *; omega

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/JustificationCertificates.lean:255-298
/-- [helper] A nonzero justified height has a target quorum on the chain for
`(h_j, J.root)`. -/
theorem justification_certificate (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_j ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ carrier a,
      FGBlock.Preceq carrier D ∧ a ∈ carrier.rows ∧ a.signer = i ∧
      a.height_pair = .vote (derive E cfg D).h_j (derive E cfg D).J.root false := by
  induction D with
  | genesis => exact absurd rfl hnz
  | node p s r_s x rs ih =>
      obtain ⟨-, hh, hT, hJ, hhj, -, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      have hw := folded_witnesses E cfg p s r_s x rs
      rw [derive_node] at hnz ⊢
      rcases justification_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs)
        with ⟨h1, h2⟩ | ⟨h1, h2, hq⟩
      · rw [h1, h2, hJ, hhj]
        rw [h2, hhj] at hnz
        obtain ⟨Q, hQ, hw'⟩ := ih hnz
        refine ⟨Q, hQ, fun i hi => ?_⟩
        obtain ⟨carrier, a, hc, ha, hs, hp⟩ := hw' i hi
        exact ⟨carrier, a, preceq_node_of_preceq s r_s x rs hc, ha, hs, hp⟩
      · rw [h1, h2]
        refine ⟨_, hq, fun i hi => ?_⟩
        obtain ⟨a, ⟨carrier, hc, ha⟩, hs, hp⟩ := hw.target i hi
        exact ⟨carrier, a, hc, ha, hs, hp⟩

/-! ## Entry geometry of the justification -/

/-- [helper] The justified block is an entry: its own entry is itself. -/
theorem J_is_entry (E : Electorate V) (cfg : FGConfig) (D : FGBlock V) :
    (derive E cfg (derive E cfg D).J).T_h = (derive E cfg D).J := by
  induction D with
  | genesis => rfl
  | node p s r_s x rs ih =>
      obtain ⟨-, -, hT, hJ, -, -, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      rw [derive_node]
      rcases justification_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs)
        with ⟨h1, -⟩ | ⟨h1, -, -⟩
      · rw [h1, hJ]
        exact ih
      · rw [h1, hT]
        exact entry_idem E cfg p

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/EntryHeight.lean:93-107
-- (NamedEntryHeight.entry_ancestor_same_height, read at the justified entry)
/-- [pin fg.frameCompat.v1] (step 1) The entry of a justified pair at a nonzero
height h has state height h. -/
theorem entry_height (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_j ≠ 0) :
    (derive E cfg (derive E cfg D).J).h = (derive E cfg D).h_j := by
  induction D with
  | genesis => exact absurd rfl hnz
  | node p s r_s x rs ih =>
      obtain ⟨-, hh, hT, hJ, hhj, -, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      rw [derive_node E cfg p s r_s x rs] at hnz ⊢
      rcases justification_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s x rs) rs)
        with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
      · rw [h1, h2, hJ, hhj]
        rw [h2, hhj] at hnz
        exact ih hnz
      · rw [h1, h2, hT, hh]
        exact entry_same_height E cfg p

/-- [pin fg.frameCompat.v1] (step 1) A non-genesis entry is the first block of its
height on its chain: every strict ancestor has a smaller state height. -/
theorem entry_first (E : Electorate V) (cfg : FGConfig) (D A : FGBlock V)
    (hT : (derive E cfg D).T_h ≠ .genesis)
    (hA : FGBlock.Preceq A (derive E cfg D).T_h) (hne : A ≠ (derive E cfg D).T_h) :
    (derive E cfg A).h < (derive E cfg D).h := by
  have hlt := entry_parent_height E cfg D hT
  generalize (derive E cfg D).T_h = X at hT hA hne hlt
  cases X with
  | genesis => exact absurd rfl hT
  | node p s r_s x rs =>
      exact lt_of_le_of_lt (h_mono E cfg (preceq_parent_of_preceq_node hA hne)) hlt

/-- [helper] A block C at state height m that extends an entry J justified at m
has entry J (used by `inBandLock`). -/
theorem entry_eq_of_preceq (E : Electorate V) (cfg : FGConfig) (K C : FGBlock V)
    (hnz : (derive E cfg K).h_j ≠ 0)
    (hC : (derive E cfg C).h = (derive E cfg K).h_j)
    (hJC : FGBlock.Preceq (derive E cfg K).J C) :
    (derive E cfg C).T_h = (derive E cfg K).J :=
  (entry_eq_on_plateau E cfg hJC ((entry_height E cfg K hnz).trans hC.symm)).symm.trans
    (J_is_entry E cfg K)

/-- [helper] Equal finalized and justified heights mean F = J: the finality
branch copies J, and a new J has a greater height. -/
theorem F_eq_J_of_heights (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (h : (derive E cfg D).h_F = (derive E cfg D).h_j) :
    (derive E cfg D).F = (derive E cfg D).J := by
  induction D with
  | genesis => rfl
  | node p s r_s x rs ih =>
      obtain ⟨-, -, -, hJ, hhj, hF, hhF⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      have hord := chainOrder_afterFin E (chainOrder_foldRows (.node p s r_s x rs) rs
        (chainOrder_derive E cfg p) (by rw [derive_L]; exact preceq_parent_node p s r_s x rs))
      rw [derive_node E cfg p s r_s x rs] at h ⊢
      set σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs with hσ
      have key : (afterFin E σ).h_F = (afterFin E σ).h_j →
          (afterFin E σ).F = (afterFin E σ).J := by
        intro hx
        unfold afterFin at hx ⊢
        split_ifs at hx ⊢
        · rfl
        · rw [hF, hJ]
          exact ih (hhF.symm.trans (hx.trans hhj))
      rw [process_height_events_eq] at h ⊢
      split_ifs at h ⊢
      · exact absurd h (Nat.ne_of_lt hord.finalized_below_height)
      · exact key h
      · exact key h

/-! ## Chain-state fold order (E-15; from fgsa-t7w dd4d00d ChainOrder.lean) -/

/-! The chain-state fold is order-free (T7.W extra item). `process_row` only
inserts the signer into `finalize`, `target_participation` and `progress`; its
tests read `h_F`, `h_j`, `J.root`, `h` and `T_h.root`, which the fold does not
write. So the fold commutes and is idempotent, and `transition` depends only on
the set of rows. -/

section ChainStateFoldOrder
omit [Fintype V]

/-- [helper; T7.W] Insert `i` into `S` when `c` holds. -/
def insertIf (c : Bool) (i : V) (S : Finset V) : Finset V := if c then insert i S else S

omit [RowCodec V] in
/-- [helper] The equation for conditional insertion. -/
theorem insertIf_def (c : Bool) (i : V) (S : Finset V) :
    insertIf c i S = if c then insert i S else S := by
  rw [insertIf]

omit [RowCodec V] in
/-- [helper] Two conditional inserts commute. -/
theorem insertIf_comm (c d : Bool) (i j : V) (S : Finset V) :
    insertIf c i (insertIf d j S) = insertIf d j (insertIf c i S) := by
  cases c <;> cases d <;> simp [insertIf, Finset.insert_comm]

omit [RowCodec V] in
/-- [helper] A conditional insert is idempotent. -/
theorem insertIf_idem (c : Bool) (i : V) (S : Finset V) :
    insertIf c i (insertIf c i S) = insertIf c i S := by
  cases c <;> simp [insertIf]

/-- [helper; T7.W] The finality test of `process_row`. It reads `h_F`, `h_j`
and `J`. -/
def finHit (σ : ChainState V) (row : Row V) : Bool :=
  decide (σ.h_F < σ.h_j) && decide (row.finality_pair = some ⟨σ.h_j, σ.J.root⟩)

/-- [helper; T7.W] The progress test of `process_row`. It reads `h` and `T_h`. -/
def progHit (σ : ChainState V) (row : Row V) : Bool :=
  row.height_pair.matchesEntry σ.h σ.T_h.root

/-- [helper; T7.W] The target test of `process_row`: the progress test and not a
timeout. -/
def targetHit (σ : ChainState V) (row : Row V) : Bool :=
  progHit σ row && match row.height_pair with
    | .vote _ _ timeout => !timeout
    | .empty => false

/-- [helper; T7.W] The normal form of a row step: three conditional inserts. The
tests read only fields that the step does not write. -/
theorem process_row_eq (σ : ChainState V) (row : Row V) :
    process_row σ row = { σ with
      finalize := insertIf (finHit σ row) row.signer σ.finalize
      target_participation := insertIf (targetHit σ row) row.signer σ.target_participation
      progress := insertIf (progHit σ row) row.signer σ.progress } := by
  rcases row with ⟨i, hp, fp⟩
  cases σ
  unfold process_row finHit targetHit progHit insertIf
  cases hp with
  | empty =>
      simp only [NamedHeightPair.matchesEntry]
      split_ifs <;> simp_all
  | vote h e t =>
      simp only [NamedHeightPair.matchesEntry]
      cases t <;> split_ifs <;> simp_all

/-- [T7.W] Two row steps commute. -/
theorem process_row_comm (σ : ChainState V) (a b : Row V) :
    process_row (process_row σ a) b = process_row (process_row σ b) a := by
  simp only [process_row_eq]
  congr 1 <;> exact insertIf_comm _ _ _ _ _

/-- [T7.W] A row step is idempotent. -/
theorem process_row_idem (σ : ChainState V) (a : Row V) :
    process_row (process_row σ a) a = process_row σ a := by
  simp only [process_row_eq]
  congr 1 <;> exact insertIf_idem _ _ _

/-- [helper] The row fold with a row moved to the end. -/
theorem foldl_process_row_push (σ : ChainState V) (a : Row V) (l : List (Row V)) :
    l.foldl process_row (process_row σ a) = process_row (l.foldl process_row σ) a := by
  induction l generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [process_row_comm σ a x, ih]

/-- [helper] A row that is in the list has no further effect on the fold. -/
theorem foldl_process_row_absorb (σ : ChainState V) {a : Row V} {l : List (Row V)}
    (ha : a ∈ l) : process_row (l.foldl process_row σ) a = l.foldl process_row σ := by
  induction l generalizing σ with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 ha with rfl | hm
      · rw [foldl_process_row_push, process_row_idem]
      · exact ih _ hm

/-- [helper] The row fold equals the fold over the list without duplicates. -/
theorem foldl_process_row_dedup (σ : ChainState V) (l : List (Row V)) :
    l.foldl process_row σ = l.dedup.foldl process_row σ := by
  induction l generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x ∈ xs
      · rw [List.dedup_cons_of_mem hx, List.foldl_cons, foldl_process_row_push,
          foldl_process_row_absorb σ hx, ih]
      · rw [List.dedup_cons_of_notMem hx, List.foldl_cons, List.foldl_cons, ih]

/-- [helper] The row fold does not depend on the order of the rows. -/
theorem foldl_process_row_perm (σ : ChainState V) {rs rs' : List (Row V)} (h : rs.Perm rs') :
    rs.foldl process_row σ = rs'.foldl process_row σ :=
  h.foldl_eq' (fun x _ y _ z => process_row_comm z x y) σ

end ChainStateFoldOrder

/-- [T7.W] `transition` does not depend on the order of the rows. -/
theorem transition_perm (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : rs.Perm rs') :
    transition E cfg σ g rs = transition E cfg σ g rs' := by
  unfold transition
  rw [foldl_process_row_perm _ h]

/-- [T7.W] `transition` depends only on the members of the row list (no order,
no multiplicity). -/
theorem transition_eq_of_mem_iff (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : ∀ x, x ∈ rs ↔ x ∈ rs') :
    transition E cfg σ g rs = transition E cfg σ g rs' := by
  have hp : rs.dedup.Perm rs'.dedup :=
    (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2
      (fun x => by rw [List.mem_dedup, List.mem_dedup, h])
  unfold transition
  rw [foldl_process_row_dedup _ rs, foldl_process_row_dedup _ rs',
    foldl_process_row_perm _ hp]

/-- [T7.W] `transition` depends only on the row set. -/
theorem transition_eq_of_toFinset (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : rs.toFinset = rs'.toFinset) :
    transition E cfg σ g rs = transition E cfg σ g rs' :=
  transition_eq_of_mem_iff E cfg σ g (fun x => by
    rw [← List.mem_toFinset, h, List.mem_toFinset])

end AvailableChain.KitFG
end
