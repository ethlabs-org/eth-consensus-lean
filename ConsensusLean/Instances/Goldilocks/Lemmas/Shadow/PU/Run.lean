module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo

public section

/-! # Shadow P-U run suppliers

The store facts are instances of the finality-parametric cache invariant. The run
wrappers do not identify shadow reachability with stock reachability.
-/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem tree_mono' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k i : Nat} (hki : k ≤ i) : (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  induction i, hki using Nat.le_induction with
  | base => exact subset_rfl
  | succ i _ ih =>
    refine ih.trans ?_
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      rcases Node.cutStep'_fg (h.cutLaw y hy i c hc) with he | hs
      · rw [he]
      · rcases (Store.step'_iff _ _).1 hs with ⟨B, hB⟩ | ⟨a, ha⟩
        · rw [Store.onBlock'_eq_onBlockWith] at hB
          rw [(Store.tree_grows_with Store.finalitySpec_updateFinality').1 B _ hB]
          exact Set.subset_insert _ _
        · rw [ha, (Store.tree_grows_with Store.finalitySpec_updateFinality').2 a]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

theorem frameOK_state' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) : FrameOK (Node.frame' (tr.state y i)) := by
  rw [Node.frame'_eq]
  exact Store.frameOK_toFrame' (Node.fg_reachable_at' h hy i).puSnapshot

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

theorem σ_eq_honest' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Goldilocks.Store.σ_eq_of_mem_with
    (Node.fg_reachable_at' hrun.toLocalRun' hy i).reachableWith
    Goldilocks.Store.finalitySpec_updateFinality'
    (Node.fg_reachable_at' hrun.toLocalRun' hz j).reachableWith
    (Compose.honest_blocks_coherent' hrun.toLocalRun' hnc).1
    (fun _ hX => ⟨y, hy, i, hX⟩) (fun _ hX => ⟨z, hz, j, hX⟩) hBy hBz

theorem hj_lt_hmax' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
  have hr := (Node.fg_reachable_at' hrun.toLocalRun' hy i).reachableWith
  obtain ⟨_, _, _, ⟨Bj, hBj, _, hBjhj⟩, hge, _, _⟩ :=
    Goldilocks.Store.cache_invariants_with Goldilocks.Store.finalitySpec_updateFinality' hr
  exact hBjhj ▸ (Goldilocks.Store.hj_lt_h_with
    Goldilocks.Store.finalitySpec_updateFinality' hr hBj).trans_le (hge Bj hBj)

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {y : Fin sp.n} {i : Nat} {d : Time}

theorem tree_held_at' (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hB => ⟨y, i, d, hd, hi, hy, hB⟩

theorem reachable_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.Reachable' (goldilocksNode' sp ro).genesisPayload := by
  have h := Node.fg_reachable_at' (hrun.upTo hd).toLocalRun' hy i
  rwa [Trace.upTo_state tr y hi] at h

theorem frameOK_at' {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    FrameOK (Node.frame' (tr.state y i)) := by
  rw [Node.frame'_eq]
  exact Store.frameOK_toFrame' (reachable_at' hrun hd hy hi).puSnapshot

theorem tree_mono_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) {k : Nat} (hki : k ≤ i) :
    (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  have h := tree_mono' (hrun.upTo hd).toLocalRun' hy hki
  rwa [Trace.upTo_state tr y hi, Trace.upTo_state tr y fun k' hk' => hi k' (by omega)] at h

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace' sp ro) (H : Time → Set (Fin sp.n))

/-- The shared shadow reset bundle: only the execution contract differs from the stock bundle. -/
structure ResetPremisesUpTo' (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a b : Time)
    (committee : Time → Finset (Fin sp.n)) (beta : ℚ) (hold : Time := 0) : Prop where
  beta_le : beta ≤ 1 / 2
  run : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
    (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp committee))
  committee_pos : 0 < sp.committeeSize
  committeeFacts : Compose.Growing.CommitteeFacts tr H (Generic.dictOfTime sp committee)
  committeeFaults : Generic.CommitteeFaultsUpTo beta committee H g b
  noColl : Compose.NoCollRun dg tr
  sync : ResetService tr H g ΔF b hold
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b
  catchUp : CatchRun tr H g (2 * sp.Δ)
  noRestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k →
    tr.time k ≤ b → tr.time k ≤ gbar g
  timeoutDelay : ∀ s, sp.toParams.slotTime s + 6 * sp.Δ + ΔF ≤
    sp.toParams.slotTime (s + sp.toParams.δt)
  nonempty : (H b).Nonempty
  deepCover : ∀ D, sp.deepDepth = some D →
    b ≤ cutZ sp.toParams g + 4 * D * sp.Δ ∨ HighSourceCover tr H g a b

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.RunTrace

open AC (ACParams ReplayOrder Payload)

theorem anc_upTo_of_right' {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {ini} {d : Time}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hd : 0 ≤ d) {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : C ∈ (tr.upTo d).HonestBlocks (H d)) (h : Anc (tr.HonestBlocksAt H) B C) :
    Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  obtain ⟨y, hy, i, hC⟩ := hC
  obtain ⟨j, _, hj, he⟩ := Trace.upTo_state_exists tr hrun.time_mono y i (d := d)
  rw [he] at hC
  exact (Coherence.held_anc_at' hrun hnc hd hy hj h hC).mono fun _ hX =>
    ⟨y, hy, i, by rw [he]; exact hX⟩

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

theorem store_anc_of_honest_anc_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc A C :=
  Coherence.held_anc_at' hrun hnc ht hy hle h hC

theorem mem_of_honest_anc_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc_at' hrun hnc ht hle hy h hC) he).1

theorem σ_eq_honest_at' {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Goldilocks.Store.σ_eq_of_mem_with
    (Compose.Growing.reachable_at' hrun ht hy hle).reachableWith
    Goldilocks.Store.finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun hu hz hle').reachableWith
    (Coherence.honest_blocks_coherent_at' hrun hnc).1
    (Compose.Growing.tree_held_at' ht hy hle)
    (Compose.Growing.tree_held_at' hu hz hle') hBy hBz

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Interface pending the shadow store finalization monotonicity lift. -/
theorem run_F_mono' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i i' : Nat} (hii : i ≤ i') :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F (tr.state y i').fg.F := by
  sorry

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Growing.LocalRun'

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem finalized_mono_on_prefix' (h : LocalRun' proposer dg H sg tr ini) {d : Time}
    (hd : 0 ≤ d) {y : Fin P.n} {i j : Nat} (hy : y ∈ H d) (hij : i ≤ j)
    (hj : ∀ k < j, tr.time k ≤ d) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y j).fg.F := by
  sorry

theorem acRelayAt' (hrun : LocalRun' proposer dg H sg tr ini)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A} {σ : Time}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B)
    (relay : ∀ k, tr.time k = tr.time i → x ∈ H (tr.time k) → tr.AcceptAt x k B →
      tr.IsCall y j → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j σ B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ := by
  sorry

theorem fgCatchAt' (hrun : LocalRun' proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk}
    (hx : x ∈ H (tr.time i)) (ha : tr.AcceptAt x i B) (hi : tr.time i < AC.gbar g)
    (hy : y ∈ H (tr.time j)) (hj : AC.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ := by
  sorry

theorem acCatchAt' (hrun : LocalRun' proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i B) (hi : tr.time i < AC.gbar g)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ) (hj : AC.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ := by
  sorry

end Consensus.Goldilocks.Growing.LocalRun'

end
