module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedEndpoint

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

/-- Blueprint 21 H.6:947–958 (design 798–814); spec 1387–1401, 1555–1581. Class (iii).
DC: INTENTIONAL; the retained interval is nonempty. -/
private theorem strict_cut : Block.Prec (eraseFG cutFG) (eraseFG parentFG) := by decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1387–1401, 1555–1581. Class (iii).
DC: INTENTIONAL; the old rival is in the target domain but is not eligible.
The band arm is excluded through the height bridge, without height reduction. -/
private theorem old_ineligible : et params target 4 (eraseFG oldFG) = false := by
  have hband : ¬ ∃ P ∈ target.fg.TF, eraseFG P = (eraseFG oldFG).parent ∧
      (heightView params P).h < (controls params target).lo := by
    rintro ⟨P, -, -, hh⟩
    exact Nat.not_lt_of_ge (fixture_height target rfl P) hh
  unfold et eligible
  simp only [hband, decide_false, Bool.false_or]
  decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1387–1401, 1555–1581. Class (iii).
DC: INTENTIONAL; all eight endpoint fields for the concrete finite stores. -/
private theorem endpoint_instance :
    RetainedEndpointGeometry params source target 4 (eraseFG proposalFG) := by
  have members (C : Block) (hm : C ∈ T params target 4) :
      C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG ∨
        C = eraseFG oldFG ∨ C = eraseFG proposalFG := by
    have hb := (List.mem_filter.mp hm).1
    simpa only [target, source, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc] using hb
  refine ⟨?_, proposal_mem_target_proposal, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro C hm hp hs he
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    · cases hp
    · have hn : (eraseFG cutFG).parent? ≠ some (eraseFG proposalFG).parent := by decide +kernel
      exact (hn hp).elim
    · have hn : (eraseFG parentFG).parent? ≠ some (eraseFG proposalFG).parent := by decide +kernel
      exact (hn hp).elim
    · rw [old_ineligible] at he
      cases he
    · exact (Nat.lt_irrefl 4 hs).elim
  · intro C hm hs
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | (exfalso; revert hs; decide +kernel)
  · intro C hm
    rcases members C hm with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro C hm hp
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    all_goals exfalso; revert hp; decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1387–1401, 1555–1581. Class (iii).
DC: INTENTIONAL; apply S7 to a terminal source with a real old target child. -/
private theorem exact_geometry_instance :
    ExactHeadGeometry params target 4 (eraseFG proposalFG) := by
  apply fgsa_exactHeadGeometry_of_retained_endpoint params source target 4 _ ?_ endpoint_instance
  intro C hm hp
  have hb := (List.mem_filter.mp hm).1
  have hc : C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG := by
    simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using hb
  rcases hc with rfl | rfl | rfl
  all_goals exfalso; revert hp; decide +kernel

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 00:126–142; 21 H.22:3109–3114. Class (iii).
DC: INTENTIONAL; compile the full supplier-to-schedule application.
This is a conditional run instance; the fixture has no certified heights. -/
private theorem scheduled_instance
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some N.erase := by
  exact exactService_head_of_retained_proposal E rho hE hDelta s hip N hem D
    (fgsa_retainedExactHead_geometry_on_run (hroots := hroots) E rho hE hN hDelta s hWalkSync
        hScoreSync
      hx hip hseat N hem D hreads)

/-- Blueprint 21 H.6:937–942. Class (iii).
DC: INTENTIONAL; identify the finite source's actual live start. -/
private theorem consumer_source_start : ap params source = eraseFG cutFG := by
  have hm := fixture_full_mem source rfl rfl rfl cutFG (by decide +kernel)
  have ht : decide (∃ B ∈ fullTree params source, eraseFG B = eraseFG cutFG) = true :=
    decide_eq_true ⟨cutFG, hm, rfl⟩
  change liveRoot params source = eraseFG cutFG
  unfold liveRoot
  rw [fixture_root source rfl rfl]
  change ([ (eraseFG cutFG, (0 : Time), (100 : Time)) ].filterMap
    (fun row => if source.base.now < row.2.2 &&
      decide (∃ B ∈ fullTree params source, eraseFG B = row.1) then some row.1 else none)).foldl
      (fun best b => if best.depth < b.depth || (best.depth == b.depth && best.root < b.root)
        then b else best) .genesis = eraseFG cutFG
  simp only [List.filterMap_cons, List.filterMap_nil, ht]
  decide +kernel

/-- Blueprint 21 H.6:937–942. Class (iii).
DC: INTENTIONAL; prior honest support gives the real source prefix. -/
private theorem consumer_source_prefix :
    BestAncestry (z params source) (ap params source)
      (S params source) (ss source 4) (es params source 4) := by
  rw [BestAncestry_def, consumer_source_start]
  intro X _ hprec
  have hne : X ≠ eraseFG cutFG := by
    intro he
    have hn := (Bool.and_eq_true_iff.mp hprec).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  have hle := (Bool.and_eq_true_iff.mp hprec).2
  change (decide (X = eraseFG cutFG) || decide (X = .genesis)) = true at hle
  have hX : X = .genesis := of_decide_eq_true
    ((Bool.or_eq_true_iff.mp hle).resolve_left (by simpa only [decide_eq_true_eq] using hne))
  subst X
  refine ⟨eraseFG cutFG, rfl, block_preceq_refl _, ?_, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨by decide +kernel, decide_eq_true
      ⟨cutFG, fixture_full_mem source rfl rfl rfl cutFG (by decide +kernel), rfl⟩⟩
  · have hm : GridCO.voterCount (proposerVotes source 4) < 2 * ss source 4 (eraseFG cutFG) :=
      by decide +kernel
    unfold es eligible
    change (_ || decide (GridCO.voterCount (proposerVotes source 4) <
      2 * ss source 4 (eraseFG cutFG)) || _) = true
    simp only [hm, decide_true, Bool.or_true, Bool.true_or]
  · intro B hB hp _
    have hmem : B = .genesis ∨ B = eraseFG cutFG ∨ B = eraseFG parentFG := by
      simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using (List.mem_filter.mp hB).1
    rcases hmem with rfl | rfl | rfl
    · cases hp
    · exact ⟨le_refl _, fun _ => le_refl _⟩
    · have hn : (eraseFG parentFG).parent? ≠ some Block.genesis := by decide +kernel
      exact (hn hp).elim

/-- Blueprint 21 H.6:937–963; design job 7 K7. Class (iii).
DC: INTENTIONAL; a finite instance of all ten fields with the ordinary-root pivot.
The source has a strict live lease, the cut is strictly below A, and the target
has a real frozen old child. These stores are not claimed to be reachable runs. -/
private theorem consumer_H6_instance :
    RetainedReadPremises params source target 4 (controls params source).Z
      (eraseFG proposalFG) (z params source) := by
  have hz : z params source = .genesis := congrArg eraseFG (fixture_root source rfl rfl)
  have hcut : Block.Preceq (z params source) (eraseFG proposalFG).parent := by
    rw [hz]
    exact block_genesis_preceq _
  have hparent : Block.Preceq (ay params target) (eraseFG proposalFG).parent := by
    rw [target_start]
    exact block_genesis_preceq _
  refine ⟨hcut, consumer_source_prefix, hparent, block_preceq_refl _, ?_, hcut,
    ?_, parent_witness, ?_, ?_⟩
  · rw [hz, target_start]
    exact block_preceq_refl _
  · rw [BestAncestry_def, hz, target_start]
    intro X hX hprec
    have he := block_preceq_antisymm hX (Bool.and_eq_true_iff.mp hprec).2
    have hn := (Bool.and_eq_true_iff.mp hprec).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  · intro X C _ _ hm hp hold _
    have hmem : C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG ∨
        C = eraseFG oldFG ∨ C = eraseFG proposalFG := by
      simpa only [target, source, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, or_assoc] using (List.mem_filter.mp hm).1
    rw [ReflectedDomainWitness_def]
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · cases hp
    · exact ⟨cutFG, cutFG, by decide +kernel, rfl, KitFG.preceq_refl _,
        fixture_height source rfl _, Or.inl (by decide +kernel)⟩
    · exact ⟨parentFG, parentFG, by decide +kernel, rfl, KitFG.preceq_refl _,
        fixture_height source rfl _, Or.inl (by decide +kernel)⟩
    · exact ⟨oldFG, oldFG, by decide +kernel, rfl, KitFG.preceq_refl _,
        fixture_height source rfl _, Or.inr ⟨by decide +kernel, by decide +kernel⟩⟩
    · exact (Nat.lt_irrefl 4 hold).elim
  · intro X C _ _ _ _ _ _
    rw [retainedBand_def, retainedBand_def]
    constructor
    · rintro ⟨P, _, _, hh⟩
      exact (Nat.not_lt_of_ge (fixture_height source rfl P) hh).elim
    · rintro ⟨P, _, _, hh⟩
      exact (Nat.not_lt_of_ge (fixture_height target rfl P) hh).elim

/-- Blueprint 21 H.5:884–886. Class (iii).
DC: INTENTIONAL; a genesis justification cannot have a conflicting carrier. -/
private theorem consumer_floor_zero (st : State 1) (hJ : st.fg.J = .genesis)
    (hmax : st.fg.h_max = 1) : (controls params st).lo = 0 := by
  have hn : ¬ ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
      (heightView params W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W := by
    rintro ⟨W, _, _, _, hnot⟩
    exact hnot (hJ.symm ▸ KitFG.genesis_preceq W)
  rw [hmax] at hn
  unfold controls Controls.lo
  rw [KitFG.treeStoreControlsView_def]
  simp only [hn, decide_false, Bool.and_false, Bool.false_eq_true, ite_false, hmax]

/-- Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a concrete clean preceding vote gives the prior-support input. -/
private theorem consumer_prior_instance :
    RetainedPriorSupport params source 4 (ap params source) := by
  rw [consumer_source_start]
  refine ⟨?_, ⟨parentFG, by decide +kernel, by decide +kernel,
    fixture_height source rfl _⟩, ?_, ?_⟩
  · change Block.Compatible (eraseFG (controls params source).Z) (eraseFG cutFG)
    rw [fixture_root source rfl rfl]
    exact Bool.or_eq_true_iff.mpr (Or.inl (block_genesis_preceq _))
  · decide +kernel
  · intro B hconflict
    have hs : proposerSupport source 4 = proposerVotes source 4 := by decide +kernel
    have hclean : ∀ i, GridCO.equivocates (proposerVotes source 4) i = false := by
      intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      decide +kernel
    have hh := Gen.AC.Root.conflicting_score_sum_le source.base.blocks
      (proposerVotes source 4) (eraseFG cutFG) B hclean hconflict
    have hc : GridCO.goldfishScore source.base.blocks (proposerVotes source 4)
        (proposerVotes source 4) (eraseFG cutFG) = 1 := by decide +kernel
    have hn : GridCO.voterCount (proposerVotes source 4) = 1 := by decide +kernel
    change GridCO.goldfishScore _ _ (proposerSupport source 4) B <
      GridCO.goldfishScore _ _ (proposerSupport source 4) (eraseFG cutFG)
    rw [hs, hc]
    rw [hc, hn] at hh
    omega

/-- Blueprint 21 H.3, H.5, H.6; design job 7 K7. Class (iii).
DC: INTENTIONAL; the same finite stores inhabit the lane inputs and all ten outputs.
There is no reachable execution or positive-height certificate in this fixture. -/
private theorem consumer_H6_inputs : RetainedH6Input params source target 4 := by
  have hz : z params source = .genesis := congrArg eraseFG (fixture_root source rfl rfl)
  have hnot : ¬ Block.Prec (ay params target) (z params source) := by
    rw [target_start, hz]
    decide +kernel
  refine ⟨⟨?_, ?_, fun h => (hnot h).elim, fun h => (hnot h).elim⟩,
    Or.inr consumer_prior_instance, Or.inl ?_⟩
  · rw [consumer_floor_zero source rfl rfl, consumer_floor_zero target rfl rfl]
  · refine ⟨parentFG, by decide +kernel, ?_, fixture_height source rfl _⟩
    rw [consumer_source_start]
    decide +kernel
  · rw [target_start, hz]
    exact block_preceq_refl _

#print axioms consumer_H6_inputs

#print axioms consumer_H6_instance

end AvailableChain.FGSA.Run.Tests.RetainedEndpoint
