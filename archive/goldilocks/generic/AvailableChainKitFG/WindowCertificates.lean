module
public import AvailableChainKitFG.WindowViewsDef
public import AvailableChainKitFG.WindowInvariant -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Birth uses only the height fields supplied by the landed bridge. -/
theorem justificationBirth_window_iff_simplex (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK :
  2 ≤ K)
    (C : FGBlock V) (j : Height) (X : FGBlock V) :
    JustificationBirth E (certificateHeight E cfg K) C j X ↔
      JustificationBirth E (simplexHeightView E cfg) C j X := by
  have hv : certificateHeight E cfg K = simplexHeightView E cfg :=
    funext (windowHeightBridge E cfg K hK)
  rw [hv]

/-- The transported birth is this node when its justification height is
its parent's height. A proper ancestor has a smaller justification height. -/
private theorem cert_birth_at_target (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hj : (derive E cfg K (.node P s r_s x rs)).h_j = (derive E cfg K P).h)
    (hJ : (derive E cfg K (.node P s r_s x rs)).J = (derive E cfg K P).T_h) :
    JustificationBirth E (certificateHeight E cfg K) (.node P s r_s x rs)
      (derive E cfg K P).h (derive E cfg K P).T_h := by
  let B := FGBlock.node P s r_s x rs
  change (derive E cfg K B).h_j = (derive E cfg K P).h at hj
  change (derive E cfg K B).J = (derive E cfg K P).T_h at hJ
  have hg := windowHeightLaws E cfg K hK
  have hlt := hg.justified_below_height B
  change (derive E cfg K B).h_j < (derive E cfg K B).h at hlt
  have hh : (derive E cfg K B).h = (derive E cfg K P).h + 1 := by
    rcases hg.node_cases P s r_s x rs with hn | hn
    · have he := hn.1
      change (derive E cfg K B).h = (derive E cfg K P).h at he
      rw [hj, he] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact hn.1
  refine ⟨(by intro h; cases h), rfl, rfl, hj, hJ, hh, ?_⟩
  have hnz : (certificateHeight E cfg K B).h_j ≠ 0 := by
    change (derive E cfg K B).h_j ≠ 0
    rw [hj]
    exact Nat.ne_of_gt (hg.one_le_h P)
  have hq := hg.justification_certificate B hnz
  change TargetQCAt E B (derive E cfg K B).h_j (derive E cfg K B).J at hq
  rw [hj, hJ] at hq
  exact hq

private theorem cert_prefinal_of_parent (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hp : ∀ e ∈ (derive E cfg K P).W, EntryOriginAt E cfg K P e)
    (e : Entry V) (he : e ∈ (certificateFolded E cfg K (.node P s r_s x rs)).W) :
    ∃ C, StrictPrefix C (.node P s r_s x rs) ∧
      JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier (.node P s r_s x rs) ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  obtain ⟨d, hd, hj, hX, hbits⟩ :=
    (window_fold_sources rs { derive E cfg K P with s := s }).2.2 e he
  obtain ⟨C, hCP, hb, hw⟩ := hp d hd
  refine ⟨C, window_strict_node s r_s x rs hCP, ?_, ?_⟩
  · simpa only [hj, hX] using hb
  · intro i hi
    rcases hbits i hi with hi | ⟨a, ha, hai, haf⟩
    · obtain ⟨carrier, a, hCc, hcP, ha, hai, haf⟩ := hw i hi
      exact ⟨carrier, a, hCc, preceq_node_of_preceq s r_s x rs hcP, ha, hai,
        by simpa only [hj, hX] using haf⟩
    · exact ⟨.node P s r_s x rs, a, window_strict_node s r_s x rs hCP,
        preceq_refl _, ha, hai, haf⟩

/-- [bp §3.1–3.2] Every retained entry has a birth on this chain and exact
finality rows strictly after that birth. A new entry has no bits. -/
theorem window_entry_origin (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock V) (e : Entry V)
    (he : e ∈ (derive E cfg K B).W) : EntryOriginAt E cfg K B e := by
  induction B generalizing e with
  | genesis => exact (List.not_mem_nil he).elim
  | node P s r_s x rs ih =>
      let B := FGBlock.node P s r_s x rs
      let w := certificateFolded E cfg K B
      let f := finalizeWindow E w
      have hf : f.h = w.h ∧ f.T_h = w.T_h ∧ f.W ⊆ w.W := by
        dsimp only [f]
        rw [finalizeWindow_def]
        cases greatestReady E w <;> simp
      have ff := window_fold_sources rs { derive E cfg K P with s := s }
      have fh : f.h = (derive E cfg K P).h := hf.1.trans ff.1
      have fT : f.T_h = (derive E cfg K P).T_h := hf.2.1.trans ff.2.1
      have old (d : Entry V) (hd : d ∈ f.W) : EntryOriginAt E cfg K B d := by
        obtain ⟨C, hC, hb, hw⟩ := cert_prefinal_of_parent E cfg K P s r_s x rs ih d (hf.2.2 hd)
        exact ⟨C, hC.1, hb, hw⟩
      change e ∈ (process_height_events E cfg K w).W at he
      rw [process_height_events_def] at he
      change e ∈ (if targetQuorum E f then
        advance_height { f with
          J := f.T_h
          h_j := f.h
          W := (f.W ++ [Entry.mk f.h f.T_h ∅]).drop ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) }
        else if progReady E cfg f then advance_height f else f).W at he
      split_ifs at he with ht
      · rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
        · exact old e he
        · obtain rfl := List.mem_singleton.mp he
          have hnew : derive E cfg K B = advance_height { f with
              J := f.T_h, h_j := f.h,
              W := (f.W ++ [Entry.mk f.h f.T_h ∅]).drop
                ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) } := by
            change process_height_events E cfg K w = _
            rw [process_height_events_def, ite_eq_left ht]
          refine ⟨B, preceq_refl _, ?_, ?_⟩
          · rw [fh, fT]
            apply cert_birth_at_target E cfg K hK P s r_s x rs
            · rw [hnew]; exact fh
            · rw [hnew]; exact fT
          · intro i hi; exact (Finset.notMem_empty i hi).elim
      · exact old e he
      · exact old e he

/-- [spec 1220–1227] An entry available to finality was born strictly
before this block; rows in its birth block cannot set its bits. -/
theorem window_prefinal_entry_origin (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock V) (e : Entry V)
    (he : e ∈ (certificateFolded E cfg K B).W) :
    ∃ C, StrictPrefix C B ∧
      JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  cases B with
  | genesis => exact (List.not_mem_nil he).elim
  | node P s r_s x rs =>
      exact cert_prefinal_of_parent E cfg K P s r_s x rs (window_entry_origin E cfg K hK P) e he

end AvailableChain.KitFG.Window
end
