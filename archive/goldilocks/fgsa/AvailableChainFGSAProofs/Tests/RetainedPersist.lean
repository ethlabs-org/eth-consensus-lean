module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedPersist

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

/-- Blueprint 21 H.5:891–902, H.6:942–958 (design 747–758,798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; finite parameters for the witness tests. -/
private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; retained cut and live lease target. -/
private def cutFG : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; parent strictly above the retained cut. -/
private def parentFG : FGBlock (Fin 1) := .node cutFG 2 ⟨2⟩ 0 []
/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; old child at the inclusive endpoint. -/
private def oldFG : FGBlock (Fin 1) := .node parentFG 3 ⟨3⟩ 0 []

/-- Blueprint 21 H.17:3008–3011 (design 2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; the admitted current proposal shares A with the old child. -/
private def proposalFG : FGBlock (Fin 1) := .node parentFG 4 ⟨4⟩ 0 []

/-- Blueprint 21 H.6:927–958 (design 783–814); spec 1373–1385, 1290–1297. Class (iii).
DC: INTENTIONAL; a source with a live lease above its root. -/
private def source : State 1 :=
  { initial 1 with
    base := { (initial 1).base with
      now := 16
      votes := [⟨.seat 3 0, .head (eraseFG parentFG).root⟩]
      voteStamp := [(⟨.seat 3 0, .head (eraseFG parentFG).root⟩, 0)]
      blocks := [.genesis, eraseFG cutFG, eraseFG parentFG]
      blockStamp := [(.genesis, 0), (eraseFG cutFG, 0), (eraseFG parentFG, 0)]
      obligations := [(eraseFG cutFG, 0, 100)] }
    fg := {
      TF := {.genesis, cutFG, parentFG}
      F := .genesis
      J := .genesis
      h_j := 0
      h_max := 1 } }

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; the frozen old child is absent from the source fixture. -/
private def target : State 1 :=
  { source with
    base := { source.base with
      blocks := source.base.blocks ++ [eraseFG oldFG, eraseFG proposalFG]
      obligations := []
      blockStamp := source.base.blockStamp ++ [(eraseFG oldFG, 0), (eraseFG proposalFG, 16)] }
    fg := { source.fg with TF := {.genesis, cutFG, parentFG, oldFG, proposalFG} } }

/-- Blueprint 21 H.6:942–953 (design 798–809); spec 1290–1297. Class (iii).
DC: INTENTIONAL; use the height-law bridge without reducing the active view. -/
private theorem fixture_height (st : State 1) (hmax : st.fg.h_max = 1)
    (W : FGBlock (Fin 1)) : (controls params st).lo ≤ (heightView params W).h := by
  have hlo : (controls params st).lo ≤ 1 := by
    unfold Controls.lo
    change (if _ then st.fg.h_max else st.fg.h_max - 1) ≤ 1
    rw [hmax]
    split <;> decide
  apply hlo.trans
  rw [(KitFG.heightBridge_fields params.E params.cfg
    (heightView params) (heightView_bridge params) W).1]
  exact KitFG.one_le_h params.E params.cfg W

/-- Blueprint 21 H.6:927–958 (design 783–814); spec 616–633. Class (iii).
DC: INTENTIONAL; both branches select the common genesis F/J, without height reduction. -/
private theorem fixture_root (st : State 1) (hF : st.fg.F = .genesis)
    (hJ : st.fg.J = .genesis) : (controls params st).Z = .genesis := by
  unfold Controls.Z
  change (if _ then st.fg.J else st.fg.F) = .genesis
  rw [hF, hJ]
  split <;> rfl

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; concrete full-domain membership from the internal witness. -/
private theorem fixture_full_mem (st : State 1) (hF : st.fg.F = .genesis)
    (hJ : st.fg.J = .genesis) (hmax : st.fg.h_max = 1)
    (B : FGBlock (Fin 1)) (hB : B ∈ st.fg.TF) : B ∈ fullTree params st := by
  apply (KitFG.mem_filteredFromView (heightView params) (controls params st) st.fg.TF B).mpr
  refine ⟨hB, ?_, ?_, B, hB, KitFG.preceq_refl _, fixture_height st hmax B⟩
  · change FGBlock.Preceq st.fg.F B
    rw [hF]
    exact KitFG.genesis_preceq B
  · rw [fixture_root st hF hJ]
    exact KitFG.genesis_preceq B

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; finite erasure correspondence without computing heightView. -/
private theorem target_base (C : Block) :
    C ∈ target.base.blocks ↔ ∃ B ∈ target.fg.TF, eraseFG B = C := by
  simp only [target, source, Finset.mem_insert, Finset.mem_singleton, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((rfl | rfl | rfl) | rfl | rfl)
    all_goals first | exact ⟨.genesis, by simp, rfl⟩ | exact ⟨cutFG, by simp, rfl⟩ |
      exact ⟨parentFG, by simp, rfl⟩ | exact ⟨oldFG, by simp, rfl⟩ |
      exact ⟨proposalFG, by simp, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> simp [eraseFG]

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; the admitted finite path is parent closed. -/
private theorem target_parent_mem : ∀ B ∈ target.fg.TF, B.parent ∈ target.fg.TF := by
  intro B hB
  have hb : B = .genesis ∨ B = cutFG ∨ B = parentFG ∨ B = oldFG ∨ B = proposalFG := by
    simpa only [target, source, Finset.mem_insert, Finset.mem_singleton] using hB
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Blueprint 21 H.6:927–953 (design 783–809); spec 1373–1385. Class (iii).
DC: INTENTIONAL; the target has no leases, so its live start is Z. -/
private theorem target_start : ay params target = .genesis := by
  unfold ay liveRoot
  rw [fixture_root target rfl rfl]
  rfl

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; source A is the first permitted witness choice. -/
private theorem parent_witness :
    ∃ W : FGBlock (Fin 1),
      ((W ∈ source.fg.TF ∧ eraseFG W = (eraseFG proposalFG).parent) ∨
        (W ∈ target.fg.TF ∧ eraseFG W = eraseFG proposalFG)) ∧
      (controls params target).lo ≤ (heightView params W).h :=
  ⟨parentFG, Or.inl ⟨by decide +kernel, rfl⟩, fixture_height target rfl parentFG⟩

/-- Blueprint 21 H.6:935–953, H.17:3008–3011
(design 791–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; E.proposal_mem instance with source A, absent new b at source. -/
private theorem proposal_mem_source_parent :
    eraseFG proposalFG ∈ T params target 4 ∧ proposalFG ∉ source.fg.TF := by
  refine ⟨fgsa_retained_proposal_mem params source target target_base target_parent_mem
    ?_ 4 (eraseFG proposalFG) (by decide +kernel) rfl ?_ parent_witness, by decide +kernel⟩
  all_goals rw [target_start]; exact block_genesis_preceq _

/-- Blueprint 21 H.6:935–953, H.17:3008–3011
(design 791–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; E.proposal_mem instance with admitted target b itself. -/
private theorem proposal_mem_target_proposal : eraseFG proposalFG ∈ T params target 4 := by
  apply fgsa_retained_proposal_mem params source target target_base target_parent_mem
    ?_ 4 (eraseFG proposalFG) (by decide +kernel) rfl ?_
    ⟨proposalFG, Or.inr ⟨by decide +kernel, rfl⟩, fixture_height target rfl proposalFG⟩
  all_goals rw [target_start]; exact block_genesis_preceq _

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1350–1360. Class (iii).
DC: INTENTIONAL; source candidates have a majority at both reads. -/
private theorem fixture_eligibility (C : Block) (hm : C ∈ source.base.blocks) :
    es params source 4 C = true ∧ et params target 4 C = true := by
  have hc : C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG := by
    simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using hm
  have majority :
      GridCO.voterCount (proposerVotes source 4) < 2 * ss source 4 C ∧
      GridCO.voterCount (headVotes params target 4) < 2 * ts params target 4 C := by
    rcases hc with rfl | rfl | rfl <;> decide +kernel
  dsimp only [es, et]
  rw [fgsa_eligible_eq, fgsa_eligible_eq]
  simp only [majority.1, majority.2, decide_true, Bool.or_true, Bool.true_or, and_self]

/-- Blueprint 21 H.6:942–953, H.17:2971–2984
(design 798–809,2832–2845); spec 1286–1293,1330–1360. Class (iii).
DC: INTENTIONAL; a W.persists instance uses path S3 and eligibility. -/
private theorem persists_instance :
    SuffixPersists (eraseFG cutFG) (eraseFG parentFG) (S params source) (T params target 4)
      (ss source 4) (es params source 4) (et params target 4) := by
  apply fgsa_retained_persists_of_path
  · intro X C _ _ _ hCA
    apply fgsa_retained_path_mem params source target target_base target_parent_mem
      ?_ 4 (eraseFG proposalFG) C (by decide +kernel) rfl ?_ ?_ parent_witness
    · rw [target_start]; exact block_genesis_preceq _
    · rw [target_start]; exact block_genesis_preceq _
    · exact block_preceq_trans hCA (by decide +kernel)
  · intro X C _ _ _ hm _
    have he := fixture_eligibility C (List.mem_filter.mp hm).1
    exact he.1.trans he.2.symm

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1286–1293,1330–1360. Class (iii).
DC: INTENTIONAL; the persistence antecedent holds for a real selected edge. -/
private theorem selected_edge :
    Block.Prec (eraseFG cutFG) (eraseFG parentFG) ∧
    GridCO.ghostStep (S params source) (ss source 4) (es params source 4)
      (eraseFG cutFG) = some (eraseFG parentFG) := by
  have hs : S params source = source.base.blocks := by
    apply List.filter_eq_self.mpr
    intro C hm
    have hc : C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG := by
      simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using hm
    rcases hc with rfl | rfl | rfl
    · exact decide_eq_true ⟨.genesis, fixture_full_mem source rfl rfl rfl .genesis
        (by decide +kernel), rfl⟩
    · exact decide_eq_true ⟨cutFG, fixture_full_mem source rfl rfl rfl cutFG
        (by decide +kernel), rfl⟩
    · exact decide_eq_true ⟨parentFG, fixture_full_mem source rfl rfl rfl parentFG
        (by decide +kernel), rfl⟩
  have ha := (fixture_eligibility (eraseFG parentFG) (by decide +kernel)).1
  have hchildren : source.base.blocks.filter
      (fun B => B.parent? == some (eraseFG cutFG) && es params source 4 B) =
      [eraseFG parentFG] := by
    change [.genesis, eraseFG cutFG, eraseFG parentFG].filter _ = _
    simp only [List.filter_cons, List.filter_nil,
      show ((.genesis : Block).parent? == some (eraseFG cutFG)) = false from rfl,
      show ((eraseFG cutFG).parent? == some (eraseFG cutFG)) = false from by decide,
      show ((eraseFG parentFG).parent? == some (eraseFG cutFG)) = true from by decide,
      ha, Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false, ite_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [hs]
  unfold GridCO.ghostStep
  rw [hchildren]
  rfl

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1286–1293,1330–1360. Class (iii).
DC: INTENTIONAL; apply W.persists on Kc < A, rather than an empty interval. -/
private theorem persisted_selected_child :
    eraseFG parentFG ∈ T params target 4 ∧ et params target 4 (eraseFG parentFG) = true :=
  persists_instance _ _ (block_preceq_refl _) selected_edge.1 selected_edge.2 (block_preceq_refl _)

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1286–1293. Class (iii).
DC: INTENTIONAL; an old child exists at A in the actual target domain. -/
private theorem old_endpoint :
    (eraseFG oldFG).parent? = some (eraseFG parentFG) ∧ (eraseFG oldFG).slot < 4 ∧
    eraseFG oldFG ∈ T params target 4 := by
  refine ⟨rfl, by decide, ?_⟩
  apply fgsa_walk_domain_of_witness_tree_view params target
    (voterBlocks params target 4) oldFG oldFG
    (fun B hB => (target_base _).mpr ⟨B, hB, rfl⟩)
    (fun _ h => Next.tree_subset_TF params target ((Finset.mem_filter.mp h).1))
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ (KitFG.preceq_refl _) (fixture_height target rfl oldFG)
  rw [fixture_root target rfl rfl]
  exact KitFG.genesis_preceq _

/-- Blueprint 21 H.6:927–939, H.17:2957–2964
(design 783–795,2818–2825); spec 1373–1385. Class (iii).
DC: INTENTIONAL; the actual source start differs from its FG root. -/
private theorem source_start_above_root :
    RetainedWalk.ap params source ≠ RetainedWalk.z params source := by
  have hm := fixture_full_mem source rfl rfl rfl cutFG (by decide +kernel)
  have ht : decide (∃ B ∈ fullTree params source, eraseFG B = eraseFG cutFG) = true :=
    decide_eq_true ⟨cutFG, hm, rfl⟩
  have hz := fixture_root source rfl rfl
  change liveRoot params source ≠ eraseFG (controls params source).Z
  unfold liveRoot
  rw [hz]
  change ([ (eraseFG cutFG, (0 : Time), (100 : Time)) ].filterMap
    (fun row => if source.base.now < row.2.2 &&
      decide (∃ B ∈ fullTree params source, eraseFG B = row.1) then some row.1 else none)).foldl
      (fun best b => if best.depth < b.depth || (best.depth == b.depth && best.root < b.root)
        then b else best) .genesis ≠ .genesis
  simp only [List.filterMap_cons, List.filterMap_nil, ht]
  decide +kernel

end AvailableChain.FGSA.Run.Tests.RetainedPersist
