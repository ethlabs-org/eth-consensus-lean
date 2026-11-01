module
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [helper] A quorum covered by stored target bits and matching target rows
justifies the entry and advances the height. -/
theorem transition_target_of_cover (E : Electorate V) (cfg : FGConfig)
    (σ : ChainState V) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ σ.target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧ a.height_pair = .vote σ.h σ.T_h.root false) :
    (transition E cfg σ B rs).h = σ.h + 1 ∧
      (transition E cfg σ B rs).J = σ.T_h ∧
      (transition E cfg σ B rs).h_j = σ.h := by
  have hfold (rows : List (Row V)) (σ : ChainState V) (i : V)
      (hi : i ∈ σ.target_participation ∨
        ∃ a ∈ rows, a.signer = i ∧ a.height_pair = .vote σ.h σ.T_h.root false) :
      i ∈ (rows.foldl process_row σ).target_participation := by
    induction rows generalizing σ with
    | nil => simpa using hi
    | cons a rows ih =>
        apply ih
        rw [(process_row_fields σ a).2.2.1, (process_row_fields σ a).2.2.2.1]
        rcases hi with hi | ⟨b, hb, hbi, hm⟩
        · left
          rw [process_row_target]
          split_ifs
          · exact Finset.mem_insert_of_mem hi
          · exact hi
        · rcases List.mem_cons.mp hb with rfl | hb
          · left
            rw [process_row_target, ite_eq_left hm]
            exact Finset.mem_insert.mpr (Or.inl hbi.symm)
          · exact Or.inr ⟨b, hb, hbi, hm⟩
  have hq : E.IsQuorum (foldRows σ B rs).target_participation :=
    isQuorum_of_subset E hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
  have ht : (afterFin E (foldRows σ B rs)).targetQuorum E = true := by
    change decide (E.q ≤ E.weightOf (afterFin E (foldRows σ B rs)).target_participation) = true
    rw [decide_eq_true_eq, afterFin_target_participation]
    exact hq
  change (process_height_events E cfg (foldRows σ B rs)).h = σ.h + 1 ∧
    (process_height_events E cfg (foldRows σ B rs)).J = σ.T_h ∧
    (process_height_events E cfg (foldRows σ B rs)).h_j = σ.h
  rw [process_height_events_eq, ite_eq_left ht]
  have hh := (afterFin_h E (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
  have he := (afterFin_T_h E (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.2.1
  exact ⟨congrArg (· + 1) hh, he, hh⟩

/-- [helper] At timeout maturity, a quorum covered by stored progress bits
and matching height rows advances the height. -/
theorem transition_progress_of_cover (E : Electorate V) (cfg : FGConfig)
    (σ : ChainState V) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ σ.progress ∨
      ∃ a ∈ rs, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true)
    (hmature : σ.T_h.slot + cfg.timeoutDelay ≤ B.slot) :
    (transition E cfg σ B rs).h = σ.h + 1 := by
  have hfold (rows : List (Row V)) (σ : ChainState V) (i : V)
      (hi : i ∈ σ.progress ∨
        ∃ a ∈ rows, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true) :
      i ∈ (rows.foldl process_row σ).progress := by
    induction rows generalizing σ with
    | nil => simpa using hi
    | cons a rows ih =>
        apply ih
        rw [(process_row_fields σ a).2.2.1, (process_row_fields σ a).2.2.2.1]
        rcases hi with hi | ⟨b, hb, hbi, hm⟩
        · left
          rw [process_row_progress]
          split_ifs
          · exact Finset.mem_insert_of_mem hi
          · exact hi
        · rcases List.mem_cons.mp hb with rfl | hb
          · left
            rw [process_row_progress, ite_eq_left hm]
            exact Finset.mem_insert.mpr (Or.inl hbi.symm)
          · exact Or.inr ⟨b, hb, hbi, hm⟩
  have hq : E.IsQuorum (foldRows σ B rs).progress :=
    isQuorum_of_subset E hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
  have hp : progReady E cfg (afterFin E (foldRows σ B rs)) = true := by
    simp only [progReady, Bool.or_eq_true, Bool.and_eq_true]
    right
    constructor
    · simpa only [afterFin_T_h, afterFin_s, (foldRows_fields σ B rs).2.2.1,
        foldRows_s, decide_eq_true_eq] using hmature
    · change decide (E.q ≤ E.weightOf (afterFin E (foldRows σ B rs)).progress) = true
      rw [decide_eq_true_eq, afterFin_progress]
      exact hq
  change (process_height_events E cfg (foldRows σ B rs)).h = σ.h + 1
  rw [process_height_events_eq]
  have hh := (afterFin_h E (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
  split_ifs with ht
  · exact congrArg (· + 1) hh
  · exact congrArg (· + 1) hh

/-- [helper] Target coverage in a child justifies the parent's entry and
advances the parent's height. -/
theorem derive_target_of_cover (E : Electorate V) (cfg : FGConfig)
    (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (derive E cfg p).target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote (derive E cfg p).h (derive E cfg p).T_h.root false) :
    (derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h + 1 ∧
      (derive E cfg (.node p s r_s x rs)).J = (derive E cfg p).T_h ∧
      (derive E cfg (.node p s r_s x rs)).h_j = (derive E cfg p).h :=
  transition_target_of_cover E cfg (derive E cfg p) (.node p s r_s x rs) rs S hS hcover

/-- [helper] Mature progress coverage in a child advances the parent's height. -/
theorem derive_progress_of_cover (E : Electorate V) (cfg : FGConfig)
    (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (derive E cfg p).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (derive E cfg p).h (derive E cfg p).T_h.root = true)
    (hmature : (derive E cfg p).T_h.slot + cfg.timeoutDelay ≤ s) :
    (derive E cfg (.node p s r_s x rs)).h = (derive E cfg p).h + 1 :=
  transition_progress_of_cover E cfg (derive E cfg p) (.node p s r_s x rs) rs S hS hcover hmature

end AvailableChain.KitFG
end
