module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer

public section

/-! # Run facts derived from `GoldilocksRunCore`

The run facts the healing kernel reads (`Growing/Sleepy/Node/Lift`, `Retention/Rows`), derived once
from the run-facts bundle, so that they hold for every run with a core (the stock and the P-U
shadow run): the AC run of a prefix, reachability and the trees at a read time, the frame of an
honest call, the cast law, transfer of states and ancestry between honest observations, and the
committee bound of the casts. -/

namespace Consensus.Goldilocks.GoldilocksRunCore

open AC (ACParams ReplayOrder Payload)
open Compose.Growing (ac_castAt_upTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
  (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)

include rc

omit rc in
/-- A block of the tree of a node honest at a read time after its cut is held while honest. -/
theorem tree_held_at {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hB => ⟨y, i, d, hd, hi, hy, hB⟩

/-- The prefix's honest blocks are held while honest. -/
theorem upTo_subset {d : Time} (hd : 0 ≤ d) :
    (tr.upTo d).HonestBlocks (H d) ⊆ tr.HonestBlocksAt H :=
  RunTrace.honestBlocks_upTo_subset rc.time_mono hd

/-- **The AC run of the prefix** through `d ≥ 0` (`Compose.Growing.acRun_upTo`). -/
theorem acRun_upTo (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := (rc.upTo hd).acRun (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- The store of a node honest at a read time after its cut is reachable
(`Compose.Growing.reachable_at`). -/
theorem reachable_at {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) :
    Store.ReachableWith u (goldilocksNode sp ro).genesisPayload (tr.state y i).fg := by
  have h := (rc.upTo hd).reachable y hy i
  rwa [Trace.upTo_state tr y hi] at h

/-- The tree of a node honest at a read time grows (`Compose.Growing.tree_mono_at`). -/
theorem tree_mono_at {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {k i : Nat}
    (hi : ∀ q < i, tr.time q ≤ d) (hki : k ≤ i) :
    (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  have h := (rc.upTo hd).tree_mono y hy hki
  rwa [Trace.upTo_state tr y hi,
    Trace.upTo_state tr y fun q hq => hi q (lt_of_lt_of_le hq hki)] at h

/-- The frame of a node honest at a read time is well formed (`Compose.Growing.frameOK_at`). -/
theorem frameOK_at {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) : FrameOK (frameOf (tr.state y i)) := by
  have h := (rc.upTo hd).frameOK y hy i
  rwa [Trace.upTo_state tr y hi] at h

/-- The AC state of a node honest at its cut is its projection
(`Compose.Growing.projAC_state_at`). -/
theorem projAC_state_at {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    tr.projAC.state y i = (tr.state y i).ac := by
  have h := (rc.upTo (rc.time_nonneg i)).projAC_state y hy i
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => rc.time_mono hk.le),
    RunTrace.upTo_state_of_le rc.time_mono le_rfl] at h

/-- The frame of an AC call of a node honest at it is the node's frame
(`Compose.Growing.frame_of_projAC_at`). -/
theorem frame_of_projAC_at {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ) :
    ℓ.frame = frameOf (tr.state y i) := by
  have hc' : tr.CallAt y i (.ac ℓ) := by
    rcases hc with ⟨hn, hl⟩
    refine ⟨hn, ?_⟩
    change (tr.label i).bind RunTrace.acLabel = some ℓ at hl
    cases he : tr.label i with
    | none => simp [he] at hl
    | some c =>
      cases c with
      | fg f => simp [he, RunTrace.acLabel] at hl
      | ac a =>
        have ha : a = ℓ := by simpa [he, RunTrace.acLabel] using hl
        simp [ha]
  exact ((cutStepWith_ac ℓ).1 (rc.cutLaw y i _ hc' hy)).1

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest
(`Compose.Growing.frameIn_at`). -/
theorem frameIn_at (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H :=
  have h := AC.frameIn_of_callAt (rc.acRun_upTo hnc (rc.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  ⟨h.1, h.2.trans (rc.upTo_subset (rc.time_nonneg i))⟩

/-- The frame of a call of a node honest then is well formed, inside its tree
(`frame_tree_subset_at`). -/
theorem frame_tree_subset_at (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ (tr.state y i).fg.tree :=
  ⟨(rc.frameIn_at hnc hy hc).1, fun B hB =>
    ((rc.frameOf_tree _ B).1 (rc.frame_of_projAC_at hy hc ▸ hB)).1⟩

/-- The cast law at a node honest at the cast (`Compose.Growing.castAt_spec_at`). -/
theorem castAt_spec_at (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ AC.joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (AC.getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (AC.voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  AC.castAt_specU (rc.acRun_upTo hnc (rc.time_nonneg i)).localRun.toU hy
    (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

/-- The head of a cast extends the frame's root, by `Δ` after its slot
(`Compose.Growing.cast_head_fcRoot_at`). -/
theorem cast_head_fcRoot_at (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ :=
  have ha := rc.acRun_upTo hnc (rc.time_nonneg i)
  Compose.cast_head_fcRoot ha.localRun ha.vstart hy (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

/-- Ancestry in the blocks held while honest, ending in a held block, is held ancestry, so its
start is held (`mem_of_honest_anc_at`). -/
theorem mem_of_honest_anc_at (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d)
    {y : Fin sp.n} (hy : y ∈ H d) {i : Nat} (hi : ∀ k < i, tr.time k ≤ d)
    {A W : AC.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocksAt H) A W)
    (hW : W ∈ (tr.state y i).fg.tree) : A ∈ (tr.state y i).fg.tree := by
  have hA := rc.held_anc_at hnc hd hy hi h hW
  by_cases he : A = W
  · exact he ▸ hW
  · exact (Anc.mem hA he).1

/-- A held block's state is the same at two independently honest observations
(`σ_eq_honest_at`). -/
theorem σ_eq_honest_at (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t t' : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (ht' : 0 ≤ t') (hle' : ∀ q < j, tr.time q ≤ t') (hz : z ∈ H t')
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Store.σ_eq_of_mem_with (rc.reachable_at ht hy hle) rc.finalitySpec
    (rc.reachable_at ht' hz hle') (rc.coherent hnc).1
    (tree_held_at ht hy hle) (tree_held_at ht' hz hle') hBy hBz

/-- **Committee bound of the honest casts** (`CommitteeFacts.committeeTAt`). -/
theorem committeeTAt {K : AC.CommitteeDict sp.n} (hKB : Compose.Growing.CommitteeFacts tr H K)
    (hnc : Compose.NoCollRun dg tr) : AC.CommitteeTAt K tr.projAC H := by
  intro y i ℓ e hy hc m v hv
  have hacr := rc.acRun_upTo hnc (rc.time_nonneg i)
  have hb : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    rc.time_mono (Nat.lt_succ_iff.mp hk)
  have hcU := ac_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hpool : ∀ k, ∀ w ∈ e.readPoint.pool k, w.slot = k := fun k w hw =>
    AC.state_pool_slotU _ hacr.localRun.toU hacr.vstart hy (i + 1) k w
      (AC.readPoint_poolU hacr.localRun.toU hy hcU hw).1
  have hmem : ∀ w ∈ e.readPoint.pool v.slot, w.val = v.val → v.val ∈ K.committee v.slot := by
    intro w hw hwv
    have hp := (AC.readPoint_poolU hacr.localRun.toU hy hcU hw).1
    rw [Trace.upTo_state tr.projAC y hb] at hp
    exact hwv ▸ hKB.hP.1 (tr.time i) y hy (i + 1) hb _ w hp
  rcases AC.merged_declared_backing_at_vote_slot hpool hv with h | ⟨w, hw, -, -, -, hwv, -⟩
  · exact hmem v h rfl
  · exact hmem w hw hwv

/-- **An awake, joined, permitted node votes in its slot** by `t_s + Δ`
(`Compose.Growing.vote_of_awake_joined_at`). -/
theorem vote_of_awake_joined_at (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {s : Nat}
    (hy : y ∈ H (sp.ts s + sp.Δ))
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ sp.ts s + sp.Δ) → (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, Compose.Growing.HVoteAt tr H y k e ∧ e.msg.slot = s ∧ tr.time k ≤ sp.ts s + sp.Δ := by
  have hd := Compose.Growing.ts_add_delta_nonneg (sp := sp) s
  obtain ⟨k, e, hv, hs, hk⟩ := (rc.upTo hd).vote_of_awake_joined (hnc.upTo _) y hy
    (fun i => by
      obtain ⟨i₀, -, hb, h⟩ := Trace.upTo_state_exists tr rc.time_mono y i
      rw [h]
      exact hmv i₀ hb)
    ⟨hw, le_rfl⟩ (Compose.Growing.joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hv
  obtain ⟨hkd, hv⟩ := Compose.Growing.ac_voteAt_upTo.mp hv
  exact ⟨k, e, Compose.Growing.hVoteAt_iff.2 ⟨rc.antitone hkd hy, hv⟩, hs, hk⟩

end Consensus.Goldilocks.GoldilocksRunCore

end
