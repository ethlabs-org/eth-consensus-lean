module
public import AvailableChainKitFG.WindowCertificates
public import AvailableChainKitFG.SelectionCore

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem sel_fold_keys (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W.map (fun e => (e.j, e.X)) =
      w.W.map (fun e => (e.j, e.X)) ∧
    projectFinality (rs.foldl process_row w) = projectFinality w := by
  have h := window_fold_fields rs w
  constructor
  · rw [h.1, List.map_map]
    apply List.map_congr_left
    intro e _
    exact Prod.ext (window_fold_entry rs e).1 (window_fold_entry rs e).2.1
  · simp only [projectFinality_def, h.2.2.2.2.2.1, h.2.2.2.2.2.2]

variable [Fintype V]

private theorem sel_folded_keys (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) :
    (certificateFolded E cfg K B).W.map (fun e => (e.j, e.X)) =
      (derive E cfg K B.parent).W.map (fun e => (e.j, e.X)) ∧
    projectFinality (certificateFolded E cfg K B) = certificateFinality E cfg K B.parent :=
  sel_fold_keys B.rows { derive E cfg K B.parent with s := B.slot }

private theorem sel_before_ordered (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
  E.IsQuorum ∅) (hK : 2 ≤ K)
    (B : FGBlock V) :
    ((certificateSelection E cfg K).before B).Pairwise
      (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X) := by
  have ho : ((derive E cfg K B.parent).W.map (fun e => (e.j, e.X))).Pairwise
      (fun e d => e.1 < d.1 ∧ FGBlock.Preceq e.2 d.2) := by
    simpa only [List.pairwise_map] using window_ordered E cfg K hne hK B.parent
  rw [← (sel_folded_keys E cfg K B).1] at ho
  simpa only [List.pairwise_map, certificateSelection_def, projectCertEntry_def] using ho

private theorem sel_before_bounds (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
  E.IsQuorum ∅) (hK : 2 ≤ K)
    (B : FGBlock V) (e : FGCertEntry V)
    (he : e ∈ (certificateSelection E cfg K).before B) :
    (certificateFinality E cfg K B.parent).h_F < e.j ∧
    e.j ≤ (certificateHeight E cfg K B.parent).h_j ∧
    FGBlock.Preceq (certificateFinality E cfg K B.parent).F e.X ∧
    FGBlock.Preceq e.X (certificateHeight E cfg K B.parent).J := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have hk : (d.j, d.X) ∈ (certificateFolded E cfg K B).W.map (fun e => (e.j, e.X)) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [(sel_folded_keys E cfg K B).1] at hk
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp hk
  have hj := congrArg Prod.fst heq
  have hX := congrArg Prod.snd heq
  dsimp only at hj hX
  simpa only [projectCertEntry_def, certificateFinality_def, projectFinality_def,
    certificateHeight_def, projectHeight_def, ← hj, ← hX] using
    window_bounds E cfg K hne hK B.parent c hc


omit [DecidableEq V] [RowCodec V] in
private theorem sel_events_finality (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (w : State V) :
    projectFinality (process_height_events E cfg K w) =
      projectFinality (finalizeWindow E w) := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> rfl

private theorem sel_finality_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) :
    certificateFinality E cfg K B = projectFinality (finalizeWindow E (certificateFolded E cfg K
      B)) := by
  cases B with
  | genesis => rfl
  | node P s r_s x rs => exact sel_events_finality E cfg K _

/-- [spec 1222–1227] The window supplies the core selection laws; KitFG derives coverage. -/
theorem windowSelectionLaws (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
  (hK : 2 ≤ K) :
    FGSelectionLaws E (certificateHeight E cfg K) (certificateFinality E cfg K)
      (certificateSelection E cfg K) := by
  apply FGSelectionLaws.of_core
  · exact ⟨rfl, rfl, rfl⟩
  · exact sel_before_ordered E cfg K hne hK
  · exact sel_before_bounds E cfg K hne hK
  · intro B e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact window_prefinal_entry_origin E cfg K hK B d hd
  · intro B
    change (greatestReady E (certificateFolded E cfg K B)).map projectCertEntry = none ↔ _
    rw [Option.map_eq_none_iff]
    constructor
    · intro hn e he hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      have hb := (sel_before_bounds E cfg K hne hK B _ (List.mem_map.mpr ⟨d, hd, rfl⟩)).1
      have hf : (certificateFolded E cfg K B).h_F < d.j := by
        simpa only [← (sel_folded_keys E cfg K B).2, projectFinality_def, projectCertEntry_def]
          using hb
      obtain ⟨c, hc, _⟩ := (window_greatest_spec E _).2 d hd hf hq
      rw [hn] at hc
      cases hc
    · intro hn
      cases hc : greatestReady E (certificateFolded E cfg K B) with
      | none => rfl
      | some e =>
          have he := (window_greatest_spec E _).1 e hc
          exact (hn _ (List.mem_map.mpr ⟨e, he.1, rfl⟩) he.2.2).elim
  · intro B e he
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp he
    have hs := window_greatest_spec E (certificateFolded E cfg K B)
    have hm := hs.1 c hc
    refine ⟨List.mem_map.mpr ⟨c, hm.1, rfl⟩, hm.2.2, ?_⟩
    intro d hd hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    have hb := (sel_before_bounds E cfg K hne hK B _ (List.mem_map.mpr ⟨a, ha, rfl⟩)).1
    have hf : (certificateFolded E cfg K B).h_F < a.j := by
      simpa only [← (sel_folded_keys E cfg K B).2, projectFinality_def, projectCertEntry_def]
        using hb
    obtain ⟨b, hb, hle⟩ := hs.2 a ha hf hq
    have heq : b = c := Option.some.inj (hb.symm.trans hc)
    exact heq ▸ hle
  · intro B _
    rw [sel_finality_eq, finalizeWindow_def, certificateSelection_def]
    dsimp only
    cases greatestReady E (certificateFolded E cfg K B) with
    | none => exact (sel_folded_keys E cfg K B).2
    | some e => rfl
  · intro B
    rw [sel_finality_eq]
    change (finalizeWindow E (certificateFolded E cfg K B)).W.map projectCertEntry = _
    rw [finalizeWindow_def]
    cases greatestReady E (certificateFolded E cfg K B) <;>
      simp only [projectFinality_def, certificateSelection_def, List.filter_map] <;> rfl

/-- [design §5] Height and finality bounds complete the generic certificate constructor. -/
theorem windowCertificateLaws (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
  (hK : 2 ≤ K) :
    FGCertificateLaws E (certificateHeight E cfg K) (certificateFinality E cfg K) := by
  apply FGCertificateLaws.of_selection E _ _ _ (windowSelectionLaws E cfg K hne hK)
  · exact windowHeightLaws E cfg K hK
  · rfl
  · intro B hz
    have hbridge := windowHeightBridge E cfg K hK B
    dsimp only at hbridge
    have hz' : (SimplexFG.derive E cfg B).h_j = 0 := by
      change (projectHeight (derive E cfg K B)).h_j = 0 at hz
      rw [hbridge] at hz
      exact hz
    change (projectHeight (derive E cfg K B)).J = .genesis
    rw [hbridge]
    exact justified_zero_is_genesis E cfg B hz'
  · exact window_F_preceq_J E cfg K hne hK
  · exact window_hF_le_hj E cfg K hne hK

/-- [design §5] Assemble the certificate and selection laws. -/
theorem windowChainCertificate (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
  ∅) (hK : 2 ≤ K) :
    FGChainCertificate E (certificateHeight E cfg K) (certificateFinality E cfg K)
      (certificateSelection E cfg K) :=
  ⟨windowCertificateLaws E cfg K hne hK, windowSelectionLaws E cfg K hne hK⟩

end AvailableChain.KitFG.Window
end
