module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Shadow P-U run suppliers

The store facts are instances of the finality-parametric cache invariant. The run
wrappers do not identify shadow reachability with stock reachability.
-/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem tree_mono' (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k i : Nat} (hki : k ≤ i) : (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  induction i, hki using Nat.le_induction with
  | base => exact subset_rfl
  | succ i _ ih =>
    refine ih.trans ?_
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      rcases Node.cutStep_fg (h.cutLaw y hy i c hc) with he | hs
      · rw [he]
      · rcases (Store.step_iff _ _).1 hs with ⟨B, hB⟩ | ⟨a, ha⟩
        · rw [Store.onBlock_eq_onBlockWith] at hB
          rw [(Store.tree_grows_with Store.finalitySpec_updateFinality).1 B _ hB]
          exact Set.subset_insert _ _
        · rw [ha, (Store.tree_grows_with Store.finalitySpec_updateFinality).2 a]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

theorem frameOK_state' (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) : FrameOK (Node.frame (tr.state y i)) := by
  rw [Node.frame_eq]
  exact Store.frameOK_toFrame (Node.fg_reachable_at h hy i).puSnapshot

/-- Accepted blocks pass the AC payload requirement, from the wire or their own proposal. -/
theorem own_block_payload (hpay : ∀ y ∈ H, A.ReqPayloadFrom (ini y) y)
    (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {B : A.Blk} (hacc : tr.CallAt y i (.fg (.block B true))) : A.validPayload B := by
  rcases Coherence.blockCall_cases h hy hacc with hg |
      ⟨j, x, f, -, hg, hp, d, p, hdp, rfl, -⟩
  · exact (h.wire y hy i _ _ hg).2.2
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step' h hy hg
  obtain ⟨hcoh, t₀, ht₀, hR⟩ := ac_states_reachable' proposer dg y (hpay y hy) hreach
  have hfg : cfg.st.fg.Reachable A.genesisPayload := by
    rw [hst]
    exact Node.fg_reachable_at h hy j
  have hs := (Node.step_iff _ _ _ _ _ _ _).mp hstep
  have hR' := ACInterface.ReachableAtFrom.step .tick hR (ht₀.trans hs.1)
    ⟨⟨by simpa only [Node.frame_eq] using Store.frame_realization' _ _ hfg,
      fun _ hX => by rw [Node.frame_eq, Store.toFrame_tree] at hX; exact hX.1⟩, rfl⟩
  rw [← hst] at hdp
  have hts : tr.time i = P.slotTime (P.slotOf (tr.time i)) := hp.2.1
  refine hpay y hy _ hcoh _ _ _ hR' (P.slotOf (tr.time i)) hts.le d p ?_ _ rfl rfl
  rw [← hts]
  simpa only [Node.acProposal_eq, Node.tickStep_eq, Node.acCall_eq,
    Node.frame_eq] using hdp

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Healing

open Node

section OwnBlock

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- The own block of a shadow proposal is accepted immediately after its proposal cut. -/
theorem own_block_accepted' (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hq : ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat} {fgDue : Bool}
    (hg : tr.GroupAt proposer dg y j t (.tick x fgDue)) (hP : Proposes proposer y t)
    {d : DutyHead P.n (List (FG.Att P.n)) A.Payload} {pay : A.Payload}
    (hr : (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.2 =
      some (d, pay)) :
    tr.AcceptAt y (j + 2) (mkBlock dg y
      (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).1.fg
        t x d.head pay) ∧ tr.time (j + 2) = t := by
  let st := (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).1
  let B := mkBlock dg y st.fg t x d.head pay
  have hs : ¬ P.slotOf t < B.slot := lt_irrefl _
  have cuts (acc : Bool) (hb : (onBlock y st t B).2[0]? = some (.fg (.block B acc))) :
      (exec proposer dg y (tr.state y j) t (.tick x fgDue)).2[2]? =
        some (.fg (.block B acc)) := by
    have hp : (tickStep proposer dg y
        (tickStep proposer dg y (tr.state y j) t x .acTick).1 t x .proposal).2 =
        (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 ::
          (onBlock y st t B).2 := by
      simp only [tickStep_eq proposer dg y _ t x .proposal, hP, ↓reduceIte, hr,
        proposeBlock_eq, st, B]
    have h0 : (tickStep proposer dg y (tr.state y j) t x .acTick).2.length = 1 := by
      simp only [tickStep_eq, List.length_singleton]
    have hlen : 2 < ((tickStep proposer dg y (tr.state y j) t x .acTick).2 ++
        (acProposal (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 ::
          (onBlock y st t B).2).length := by
      have := (List.getElem?_eq_some_iff.mp hb).1
      simp only [List.length_append, List.length_cons, h0]
      omega
    cases fgDue <;>
      simp only [exec_eq, onTick_eq, runSteps_eq, tickSteps, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, List.foldl_nil]
    all_goals simp only [List.nil_append, hp]
    · rw [List.getElem?_append_right (by omega)]
      simpa only [h0, Nat.reduceSub, List.getElem?_cons_succ] using hb
    · rw [List.getElem?_append_left hlen, List.getElem?_append_right (by omega)]
      simpa only [h0, Nat.reduceSub, List.getElem?_cons_succ] using hb
  have hoc : tr.Occurs B := by
    cases hb : st.fg.onBlock B with
    | none =>
      exact ⟨y, j + 2, false, (Compose.group_cut hg (cuts false (by
        simp [onBlock_eq, hs, hb]))).1⟩
    | some fg' =>
      exact ⟨y, j + 2, true, (Compose.group_cut hg (cuts true (by
        simp [onBlock_eq, hs, hb]))).1⟩
  obtain ⟨cfg, hR, hst, hS⟩ := Compose.group_step' h hy hg
  have hacc := Compose.honest_block_accepted_from' proposer dg y hq hroot
    cfg _ t x fgDue hR hS hP d pay (by rw [hst]; exact hr)
  simp only [hst] at hacc
  have hsub : insert B st.fg.tree ⊆
      insert (P.genesisBlock A.genesisPayload) {B | tr.Occurs B} := by
    have he : st.fg = (tr.state y j).fg := by
      simp [st, acProposal_eq, tickStep_eq, acCall_eq]
    rw [he]
    exact Set.insert_subset (Set.mem_insert_of_mem _ hoc) (Coherence.tree_subset_run h hy j)
  obtain ⟨-, fg', hb⟩ := hacc.2.2.2.2.2.2 (Compose.NoCollOn.mono hnc hsub)
  change st.fg.onBlock B = some fg' at hb
  exact Compose.group_cut hg (cuts true (by simp [onBlock_eq, hs, hb]))

end OwnBlock

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem σ_eq_honest' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Goldilocks.Store.σ_eq_of_mem_with
    (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
    Goldilocks.Store.finalitySpec_updateFinality
    (Node.fg_reachable_at hrun.toLocalRun hz j).reachableWith
    (Coherence.honest_blocks_coherent hrun.toLocalRun hnc).1
    (fun _ hX => ⟨y, hy, i, hX⟩) (fun _ hX => ⟨z, hz, j, hX⟩) hBy hBz

theorem hj_lt_hmax' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
  have hr := (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
  obtain ⟨_, _, _, ⟨Bj, hBj, _, hBjhj⟩, hge, _, _⟩ :=
    Goldilocks.Store.cache_invariants_with Goldilocks.Store.finalitySpec_updateFinality hr
  exact hBjhj ▸ (Goldilocks.Store.hj_lt_h_with
    Goldilocks.Store.finalitySpec_updateFinality hr hBj).trans_le (hge Bj hBj)

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {y : Fin sp.n} {i : Nat} {d : Time}

theorem tree_held_at' (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hB => ⟨y, i, d, hd, hi, hy, hB⟩

theorem reachable_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  have h := Node.fg_reachable_at (hrun.upTo hd).toLocalRun hy i
  rwa [Trace.upTo_state tr y hi] at h

theorem frameOK_at' {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    FrameOK (Node.frame (tr.state y i)) := by
  rw [Node.frame_eq]
  exact Store.frameOK_toFrame (reachable_at' hrun hd hy hi).puSnapshot

theorem tree_mono_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) {k : Nat} (hki : k ≤ i) :
    (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  have h := tree_mono' (hrun.upTo hd).toLocalRun hy hki
  rwa [Trace.upTo_state tr y hi, Trace.upTo_state tr y fun k' hk' => hi k' (by omega)] at h

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.RunTrace

open AC (ACParams ReplayOrder Payload)

theorem anc_upTo_of_right' {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini} {d : Time}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hd : 0 ≤ d) {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : C ∈ (tr.upTo d).HonestBlocks (H d)) (h : Anc (tr.HonestBlocksAt H) B C) :
    Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  obtain ⟨y, hy, i, hC⟩ := hC
  obtain ⟨j, _, hj, he⟩ := Trace.upTo_state_exists tr hrun.time_mono y i (d := d)
  rw [he] at hC
  exact (Coherence.held_anc_at hrun hnc hd hy hj h hC).mono fun _ hX =>
    ⟨y, hy, i, by rw [he]; exact hX⟩

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem store_anc_of_honest_anc_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc A C :=
  Coherence.held_anc_at hrun hnc ht hy hle h hC

theorem mem_of_honest_anc_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc_at' hrun hnc ht hle hy h hC) he).1

theorem σ_eq_honest_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Goldilocks.Store.σ_eq_of_mem_with
    (Compose.Growing.reachable_at' hrun ht hy hle).reachableWith
    Goldilocks.Store.finalitySpec_updateFinality
    (Compose.Growing.reachable_at' hrun hu hz hle').reachableWith
    (Coherence.honest_blocks_coherent_at hrun hnc).1
    (Compose.Growing.tree_held_at' ht hy hle)
    (Compose.Growing.tree_held_at' hu hz hle') hBy hBz

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Finalized tips advance along ancestry on shadow executions. -/
theorem run_F_mono' (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i i' : Nat} (hii : i ≤ i') :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F (tr.state y i').fg.F := by
  induction i', hii using Nat.le_induction with
  | base => exact .refl
  | succ i' _ ih =>
    refine ih.trans ?_
    by_cases hc : ∃ c, tr.CallAt y i' c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      rcases Node.cutStep_fg (h.cutLaw y hy i' c hc) with he | hs
      · rw [he]
      · rcases (Store.step_iff _ _).mp hs with ⟨B, hB⟩ | ⟨att, hatt⟩
        · rw [Store.onBlock_eq_onBlockWith] at hB
          obtain ⟨pr, σ, -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some hB
          obtain ⟨atts, hatt⟩ := Store.addAtts_eq _ B.fgPayload
          have hF := ((Store.finalitySpec_iff _).mp Store.finalitySpec_updateFinality
            { (tr.state y i').fg with
              blocks := Function.update (tr.state y i').fg.blocks B.root (some B),
              σ := Function.update (tr.state y i').fg.σ B.root σ } σ).2.2.2.2.2
          rw [he, hatt]
          rcases hF with hF | ⟨-, hF, -, -⟩
          · rw [hF]
          · exact hF.mono (by
              intro X hX
              refine ⟨y, hy, i' + 1, ?_⟩
              rw [tr.state_succ_of_call hc]
              rw [(Store.tree_grows_with Store.finalitySpec_updateFinality).1 B _ hB]
              change Function.update (tr.state y i').fg.blocks B.root (some B) X.root =
                some X at hX
              by_cases hrB : X.root = B.root
              · simp only [Function.update_apply, hrB, ↓reduceIte] at hX
                exact Set.mem_insert_iff.mpr (Or.inl (Option.some.inj hX).symm)
              · simp only [Function.update_apply, hrB, ↓reduceIte] at hX
                exact Set.mem_insert_of_mem _ hX)
        · obtain ⟨atts, he⟩ := Store.onAttestation_eq (tr.state y i').fg att
          rw [hatt, he]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- The AC block call follows an FG acceptance at the same time, without restarting. -/
theorem ac_block_after' (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {B : A.Blk} (ha : tr.AcceptAt y k B) :
    tr.projAC.AcceptAt y (k + 1) B ∧ tr.time (k + 1) = tr.time k ∧
      ¬ tr.RestartAt y (k + 1) := by
  obtain ⟨ℓ, hcall, hc, ht⟩ := Coherence.accept_next h hy ha
  refine ⟨⟨ℓ, Compose.projAC_callAt.2 hcall, hc⟩, ht, ?_⟩
  rintro ⟨ℓ', hc', hr⟩
  have := hc'.2.symm.trans hcall.2
  simp only [Option.some.injEq, Cut.ac.injEq] at this
  rw [this, hc] at hr
  cases hr

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Growing.LocalRun

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem finalized_mono_on_prefix' (h : LocalRun proposer dg H sg tr ini) {d : Time}
    (hd : 0 ≤ d) {y : Fin P.n} {i j : Nat} (hy : y ∈ H d) (hij : i ≤ j)
    (hj : ∀ k < j, tr.time k ≤ d) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y j).fg.F := by
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ j hij ih =>
    refine (ih (fun k hk => hj k (by omega))).trans ?_
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      rcases Node.cutStep_fg (h.cutLaw y j c hc (h.antitone (hj j (by omega)) hy)) with he | hs
      · rw [he]
      · rcases (Store.step_iff _ _).mp hs with ⟨B, hB⟩ | ⟨a, ha⟩
        · exact ((Store.finalized_monotone' _).1 B _ hB).mono fun X hX =>
            ⟨y, j + 1, d, hd, hj, hy, by rw [tr.state_succ_of_call hc]; exact hX⟩
        · rw [ha, (Store.finalized_monotone' _).2 a]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

private theorem acBlock_prev' (h : LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel A} {B : A.Blk}
    (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.AcceptAt y i' B ∧ tr.time i' = tr.time i := by
  obtain ⟨j, e, hg⟩ := h.grouped y i _ hc hy
  rw [RunTrace.inGroup_iff] at hg
  obtain ⟨hg, hji, hij⟩ := hg
  have hk : (Node.exec proposer dg y (tr.state y j) (tr.time i) e).2[i - j]? =
      some (.ac ℓ) := by
    have hc' := Compose.group_cut hg (k := i - j) (List.getElem?_eq_some_iff.mpr
      ⟨by omega, rfl⟩)
    rw [Nat.add_sub_cancel' hji] at hc'
    exact List.getElem?_eq_some_iff.mpr ⟨by omega,
      Option.some.inj (hc'.1.2.symm.trans hc.2)⟩
  obtain ⟨k, hk', hacc⟩ := Coherence.exec_acBlock_prev proposer dg y _ _ _ hk hb
  obtain ⟨hc', ht⟩ := Compose.group_cut hg hacc
  exact ⟨j + k, by omega, hc', ht⟩

private theorem accept_next' (h : LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} (hy : y ∈ H (tr.time i)) {B : A.Blk}
    (hc : tr.AcceptAt y i B) :
    ∃ ℓ : ACLabel A, tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  obtain ⟨j, e, hg⟩ := h.grouped y i _ hc hy
  rw [RunTrace.inGroup_iff] at hg
  obtain ⟨hg, hji, hij⟩ := hg
  have hk : (Node.exec proposer dg y (tr.state y j) (tr.time i) e).2[i - j]? =
      some (.fg (.block B true)) := by
    have hc' := Compose.group_cut hg (k := i - j)
      (List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩)
    rw [Nat.add_sub_cancel' hji] at hc'
    exact List.getElem?_eq_some_iff.mpr ⟨by omega,
      Option.some.inj (hc'.1.2.symm.trans hc.2)⟩
  obtain ⟨ℓ, hnext, hb⟩ := Coherence.exec_accept_next proposer dg y _ _ _ hk
  obtain ⟨hc', ht⟩ := Compose.group_cut hg hnext
  have he : j + (i - j + 1) = i + 1 := by omega
  rw [he] at hc' ht
  exact ⟨ℓ, hc', hb, ht⟩

theorem acRelayAt' (hrun : LocalRun proposer dg H sg tr ini)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A} {σ : Time}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B)
    (relay : ∀ k, tr.time k = tr.time i → x ∈ H (tr.time k) → tr.AcceptAt x k B →
      tr.IsCall y j → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j σ B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ := by
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  have hc := Compose.projAC_callAt.mp hc
  obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev' hrun hx (Compose.projAC_callAt.mp hc₀) hb
  have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
    rw [((Node.cutStep_ac _ _ _ _ _).mp (hrun.cutLaw y j _ hc hy)).1, Node.frame_eq]
    exact Store.toFrame_F _
  exact Compose.acRelay_of_acceptNext (Compose.projAC_callAt.mpr hc)
    (relay i' hti (hti ▸ hx) hi' ⟨_, hc⟩ (hfr ▸ hanc))
    (fun _ hkj => accept_next' hrun (hrun.antitone (hrun.time_mono hkj) hy))

theorem fgCatchAt' (hrun : LocalRun proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk}
    (hx : x ∈ H (tr.time i)) (ha : tr.AcceptAt x i B) (hi : tr.time i < AC.gbar g)
    (hy : y ∈ H (tr.time j)) (hj : AC.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ := by
  exact Healing.accept_before_snapshot hj fun q hq hfirst =>
    hcatch x i B hx ha hi y q (hrun.antitone hj hy) hfirst
      ((finalized_mono_on_prefix' hrun (hrun.time_nonneg j) hy hq
        (fun k hk => hrun.time_mono hk.le)).trans hanc)

theorem acCatchAt' (hrun : LocalRun proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i B) (hi : tr.time i < AC.gbar g)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ) (hj : AC.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ := by
  obtain ⟨ℓ₀, hc₀, hb⟩ := ha
  obtain ⟨q, _, hq, ht⟩ := acBlock_prev' hrun hx (Compose.projAC_callAt.mp hc₀) hb
  have hF : ℓ.frame.F = (tr.state y j).fg.F := by
    rw [((Node.cutStep_ac _ _ _ _ _).mp
      (hrun.cutLaw y j _ (Compose.projAC_callAt.mp hc) hy)).1, Node.frame_eq]
    exact Store.toFrame_F _
  obtain ⟨k, hk, hak, hkt⟩ := fgCatchAt' hrun hcatch (ht ▸ hx) hq (ht ▸ hi) hy hj (hF ▸ hanc)
  obtain ⟨ℓ', hc', hb', ht'⟩ :=
    accept_next' hrun (hrun.antitone (hrun.time_mono hk.le) hy) hak
  exact ⟨k + 1, hk, ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ht'.symm ▸ hkt⟩

end Consensus.Goldilocks.Growing.LocalRun

end
