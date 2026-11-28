module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the node-local facts at a cut, from the run bundle

The read-time facts of a node `y` at a cut `i`, read at a time `d ≥ 0` at which `y` is honest and
after every cut before `i` (`Growing/Outage/Local`, `Growing/Sleepy/Node/Lift`), derived from
`GoldilocksRunCore` and its prefix cores (`core.upTo`), for the stock run and the shadow run alike.
Each is the stock lemma of the same name over `Growing.GoldilocksRun`. -/

namespace Consensus.Goldilocks.GoldilocksRunCore

open AC (ACParams Payload Vote)
open Consensus.Goldilocks.Compose Consensus.Goldilocks.Compose.Growing

variable {sp : ACParams}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
  (core : GoldilocksRunCore u frameOf proposer dg H tr ini)
  {y : Fin sp.n} {i : Nat} {d : Time}

include core

/-- A block held by a node honest at its cut is held while honest (`mem_honestBlocksAt`). -/
theorem mem_honestBlocksAt {B : AC.Blk sp.n (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hB : B ∈ (tr.state y i).fg.tree) : B ∈ tr.HonestBlocksAt H :=
  ⟨y, i, tr.time i, core.time_nonneg i, fun _ hk => core.time_mono hk.le, hy, hB⟩

/-- The AC state of the prefix before a cut at a time `≤ d` is the run's (`projAC_upTo_state`). -/
theorem projAC_upTo_state (hi : tr.time i ≤ d) :
    (tr.projAC.upTo d).state y i = tr.projAC.state y i :=
  ac_state_upTo (trA := tr.projAC) core.time_mono hi

theorem state_pool_slot_at (hnc : NoCollRun dg tr) (hy : y ∈ H (tr.time i)) (σ : Nat) :
    ∀ v ∈ (tr.projAC.state y i).pool σ, v.slot = σ := by
  have h := AC.state_pool_slotU sp (core.acRun_upTo hnc (core.time_nonneg i)).localRun.toU
    core.vstart hy i σ
  rwa [core.projAC_upTo_state le_rfl] at h

/-- **Lemma G at a pool**: a vote of the pool of a node honest at cut `i` whose validator is honest
at `i` was cast by it, at a cut at which it was honest (`pool_vote_at`). -/
theorem pool_vote_at (hnc : NoCollRun dg tr) (hy : y ∈ H (tr.time i)) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (tr.projAC.state y i).pool σ) (hvH : v.val ∈ H (tr.time i)) :
    ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  obtain ⟨j, hj, e, hve, hev⟩ :=
    (core.acRun_upTo hnc (core.time_nonneg i)).honest.pool_vote y hy i σ v
      (by rw [core.projAC_upTo_state le_rfl]; exact hv) hvH
  obtain ⟨hjd, hve⟩ := ac_voteAt_upTo.mp hve
  exact ⟨j, hj, e, hVoteAt_iff.2 ⟨core.antitone hjd hvH, hve⟩, hev⟩

/-- A permission held before every cut whose earlier cuts are at times `≤ d` holds at every state
of the prefix through `d` (`mayVote_upTo`). -/
theorem mayVote_upTo {s : Nat}
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ d) → (tr.state y i).ac.mayVote s = true) :
    ∀ i, ((tr.upTo d).state y i).ac.mayVote s = true := fun i => by
  obtain ⟨i₀, -, hb, h⟩ := Trace.upTo_state_exists tr core.time_mono y i
  rw [h]
  exact hmv i₀ hb

/-- Awake and joined at the AC projection is awake and joined at the run
(`mem_awakeJoined_projAC`). -/
theorem mem_awakeJoined_projAC {t : Time} :
    (tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t) ↔ (tr.awake y t ∧ tr.JoinedAt y t) :=
  and_congr Iff.rfl (projAC_joinedAt_iff core.time_nonneg y t).symm

/-- Every block held while honest descends from genesis (`honestAt_genesis_anc`). -/
theorem honestAt_genesis_anc {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∈ tr.HonestBlocksAt H ∧
      Anc (tr.HonestBlocksAt H)
        (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload) B := by
  obtain ⟨y, k, t, ht, hle, hy, hBt⟩ := hB
  have hr := core.reachable_at ht hy hle
  have hsub := tree_held_at ht hy hle
  exact ⟨hsub (Store.genesis_mem_with core.finalitySpec hr),
    ((Store.accepted_tree_with core.finalitySpec hr).2.2.2 B hBt).mono hsub⟩

/-- A block held while honest with the genesis root is genesis (`honestAt_eq_genesis`). -/
theorem honestAt_eq_genesis (hU : Coherent (tr.HonestBlocksAt H))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
    (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload :=
  hU.1 hB (core.honestAt_genesis_anc hB).1 hr

/-- **Transport of the finite service** to the prefix through `d ≥ 0`
(`SleepyServiceBefore.upTo`). -/
theorem sleepyServiceBefore_upTo {ΔF b : Time} (h : SleepyServiceBefore tr H ΔF b)
    (hd : 0 ≤ d) : Compose.SleepyServiceBefore (tr.upTo d) (H d) ΔF (min b d) := by
  have hm := core.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => core.antitone ht
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  refine ⟨h.deltaF, ?_⟩
  rw [RunTrace.upTo_projAC]
  refine ⟨fun x hx i v hv h0 y hy j ℓ hc hdb hdj => ?_,
    fun x hx i B hB h0 y hy j ℓ hc hdb hdj ha => ?_⟩
  · obtain ⟨hid, hv⟩ := (ac_sendOrAdmit_upTo hm).mp hv
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdb hdj
    exact ac_messageServedBefore_upTo hm hjd
      (h.message x i v (anti hid hx) hv h0 y j ℓ (anti hjd hy) hc (hdb.trans (min_le_left _ _))
        hdj)
  · obtain ⟨hid, hB⟩ := (ac_acceptAt_upTo _).mp hB
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdb hdj
    obtain ⟨k, hkj, hk, hkt⟩ := h.acRelay x i B (anti hid hx) hB h0 y j ℓ (anti hjd hy) hc
      (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
    have hkd : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (ac_acceptAt_upTo _).mpr ⟨hkd, hk⟩,
      by rw [ac_deadline_upTo hm hkd]; exact hkt⟩

/-- Ancestry among the blocks held while honest, ending in a block of the prefix through `d`, is
ancestry in the prefix (`RunTrace.anc_upTo_of_right`). -/
theorem anc_upTo_of_right (hnc : NoCollRun dg tr) (hd : 0 ≤ d)
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (h : Anc (tr.HonestBlocksAt H) B C) : Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  obtain ⟨y, hy, i, hC⟩ := hC
  obtain ⟨j, _, hj, he⟩ := Trace.upTo_state_exists tr core.time_mono y i (d := d)
  rw [he] at hC
  exact (core.held_anc_at hnc hd hy hj h hC).mono fun _ hX =>
    ⟨y, hy, i, by rw [he]; exact hX⟩

/-- Ancestry in the frame is ancestry in the store's tree above `F`. -/
theorem frame_anc_iff (st : NodeState (goldilocksNode sp))
    {A B : AC.Blk sp.n (List (FG.Att sp.n))} :
    (frameOf st).Anc A B ↔ Anc {X | X ∈ st.fg.tree ∧ st.fg.Anc st.fg.F X} A B := by
  have h : (frameOf st).tree = {X | X ∈ st.fg.tree ∧ st.fg.Anc st.fg.F X} :=
    Set.ext (core.frameOf_tree st)
  change Anc (frameOf st).tree A B ↔ _
  rw [h]

end Consensus.Goldilocks.GoldilocksRunCore

end
