module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedReflect

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedReflect

open AvailableChain.SimplexFG
open Gen.Pure

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

/-- Blueprint 21 H.6:927–958 (design 783–814); spec 1373–1385, 1290–1297. Class (iii).
DC: INTENTIONAL; a source with a live lease above its root. -/
private def source : State 1 :=
  { initial 1 with
    base := { (initial 1).base with
      now := 16
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
      blocks := source.base.blocks ++ [eraseFG oldFG]
      votes := [⟨.seat 3 0, .head (eraseFG oldFG).root⟩]
      voteStamp := [(⟨.seat 3 0, .head (eraseFG oldFG).root⟩, 0)]
      blockStamp := source.base.blockStamp ++ [(eraseFG oldFG, 0)] }
    fg := { source.fg with TF := {.genesis, cutFG, parentFG, oldFG} } }

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

/-- Blueprint 21 H.5:891–902, H.6:942–958 (design 747–758,798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; source-tree witness is a strict descendant of the candidate. -/
private theorem source_witness :
    ReflectedDomainWitness params source target 4 (eraseFG cutFG) := by
  rw [ReflectedDomainWitness_def]
  refine ⟨cutFG, parentFG, ?_, rfl, ?_, fixture_height source rfl parentFG, Or.inl ?_⟩
  all_goals decide +kernel

/-- Blueprint 21 H.5:891–902, H.6:942–958 (design 747–758,798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; frozen witness is stored only at the target and meets the strict deadline. -/
private theorem frozen_witness :
    ReflectedDomainWitness params source target 4 (eraseFG oldFG) ∧ oldFG ∉ source.fg.TF := by
  rw [ReflectedDomainWitness_def]
  refine ⟨⟨oldFG, oldFG, ?_, rfl, KitFG.preceq_refl _,
    fixture_height source rfl oldFG, Or.inr ⟨?_, ?_⟩⟩, ?_⟩
  all_goals decide +kernel

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; the strict retained interval contains a target candidate. -/
private theorem strict_retained_case :
    Block.Prec (eraseFG cutFG) (eraseFG parentFG) ∧
    eraseFG parentFG ∈ RetainedWalk.T params target 4 := by
  refine ⟨by decide +kernel, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨by decide +kernel, decide_eq_true ⟨parentFG, ?_, rfl⟩⟩
  apply (KitFG.mem_filteredFromView (heightView params) (controls params target)
    (voterBlocks params target 4) parentFG).mpr
  refine ⟨by decide +kernel, by decide +kernel, ?_, parentFG,
    by decide +kernel, KitFG.preceq_refl _, fixture_height target rfl parentFG⟩
  rw [fixture_root target rfl rfl]
  exact KitFG.genesis_preceq _

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297, 1330–1360. Class (iii).
DC: INTENTIONAL; X = A has a real old child, not the new slot-4 proposal. -/
private theorem endpoint_old_case :
    (eraseFG oldFG).parent? = some (eraseFG parentFG) ∧ (eraseFG oldFG).slot < 4 ∧
    eraseFG oldFG ∈ RetainedWalk.T params target 4 := by
  refine ⟨rfl, by decide, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨by decide +kernel, decide_eq_true ⟨oldFG, ?_, rfl⟩⟩
  apply (KitFG.mem_filteredFromView (heightView params) (controls params target)
    (voterBlocks params target 4) oldFG).mpr
  refine ⟨by decide +kernel, by decide +kernel, ?_, oldFG,
    by decide +kernel, KitFG.preceq_refl _, fixture_height target rfl oldFG⟩
  rw [fixture_root target rfl rfl]
  exact KitFG.genesis_preceq _

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1350–1360. Class (iii).
DC: INTENTIONAL; the old endpoint rival is eligible by a real majority. -/
private theorem endpoint_old_eligible :
    RetainedWalk.et params target 4 (eraseFG oldFG) = true := by
  dsimp only [RetainedWalk.et]
  rw [fgsa_eligible_eq]
  have hmajor : GridCO.voterCount (headVotes params target 4) <
      2 * GridCO.goldfishScore target.base.blocks (headVotes params target 4)
        (headSupport params target 4) (eraseFG oldFG) := by decide +kernel
  simp only [hmajor, decide_true, Bool.or_true, Bool.true_or]

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

end AvailableChain.FGSA.Run.Tests.RetainedReflect
