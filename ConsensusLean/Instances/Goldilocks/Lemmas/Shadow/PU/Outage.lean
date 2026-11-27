module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.S5Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Geometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Candidate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Geometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal

public section

/-! # P-U shadow, V-B7: the Outage lock premises and the run-level Hi walk

The stock premise package and cut invariant (`Growing/Outage/Defs`) at the shadow run bundle
`Growing.GoldilocksRun'.toCore` (`Shadow/PU/RunCore`): `hrun` is a `Growing.GoldilocksRun'` and the
viability field is over `Node.frame'`; the chain of `Growing/Outage/{Count,Locks,Prot,Induction}`
is shared, and `outage_lock_inv_at'` below supplies the one shadow step. The shadow trace type is
the stock one (`GoldilocksTrace' = GoldilocksTrace`), so every trace-level notion
(`HVoteAt`, `HonestBlocksAt`, `PrevBaseAt`, `CommitteeFacts`, `HiAt`) is reused.

The run-level Hi walk `anc_getHead_of_hi'` is the snapshot core of `Shadow/PU/S5Walk` with the
shadow run facts it reads. Those facts that are not yet proved are the named stubs of
`Shadow/PU/Outage` section `RunFacts'` (each is the stock fact over `GoldilocksRun'`). -/

namespace Consensus.Goldilocks.Shadow.PU

open Consensus.Goldilocks.Compose Consensus.Goldilocks.Compose.Growing
open Consensus.Goldilocks.Coherence
open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- Membership in the shadow frame's tree is the store's tree above `F`. -/
theorem mem_frame_tree {st : NodeState (goldilocksNode sp ro)}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} :
    B ∈ (Node.frame st).tree ↔ B ∈ st.fg.tree ∧ st.fg.Anc st.fg.F B := by
  rw [Node.frame_eq, Store.toFrame_tree]; exact Iff.rfl

/-- Ancestry in the shadow frame is ancestry in the store's tree above `F`. -/
theorem frame_anc_iff {st : NodeState (goldilocksNode sp ro)}
    {A B : AC.Blk sp.n (List (FG.Att sp.n))} :
    (Node.frame st).Anc A B ↔ Anc {X | X ∈ st.fg.tree ∧ st.fg.Anc st.fg.F X} A B := by
  change Anc (Node.frame st).tree A B ↔ _
  rw [Node.frame_eq, Store.toFrame_tree]

theorem frame_F (st : NodeState (goldilocksNode sp ro)) : (Node.frame st).F = st.fg.F := by
  rw [Node.frame_eq, Store.toFrame_F]

/-- **The premise package of the outage lock module under growing faults**, at trace level, from
the starts `ini`, on a shadow run: the generic package `OutageLockPremisesOver` at the shadow run
bundle `Growing.GoldilocksRun'.toCore` (`Store.updateFinality'`, `Node.frame'`). -/
abbrev OutageLockPremises (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (ini : Fin sp.n → (goldilocksNode sp ro).State) :=
  OutageLockPremisesOver (R := Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (u := Store.updateFinality) (frameOf := Node.frame) tr H proposer dg ini
    (fun h => h.toCore)

/-- The vote half of the invariant at the cuts before `i`. -/
abbrev OutageVoteInv (D : OutageLockPremises tr H proposer dg ini) (i : Nat) : Prop :=
  OutageVoteInvOver D i

/-- **The outage lock invariant** at the cuts before `i`. -/
abbrev OutageLockInv (D : OutageLockPremises tr H proposer dg ini) (i : Nat) : Prop :=
  OutageLockInvOver D i

/-- The restored-vote step that the lock module consumes. -/
abbrev OutageS5StepAt (D : OutageLockPremises tr H proposer dg ini) : Prop :=
  OutageS5StepAtOver D

/-- The AC state of the prefix before a cut at a time `≤ d` is the run's. -/
theorem projAC_upTo_state
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {d : Time}
    {y : Fin sp.n} {i : Nat} (hi : tr.time i ≤ d) :
    (tr.projAC.upTo d).state y i = tr.projAC.state y i :=
  hrun.toCore.projAC_upTo_state hi

/-! ## Run facts over the shadow run (`RunFacts'`)

The stock facts the Hi walk reads, restated over `Growing.GoldilocksRun'`, each with the stock
signature (`Growing/Outage/Local`, `Count`, `S5Geometry`; `Healing/M1/FrameKey`). A proof still to
be written is a `sorry` here; none is assumed elsewhere. -/

section RunFacts'

variable {d : Time} {y : Fin sp.n} {i : Nat}

/-- A shadow-reachable store has a block of state height `h_max` (lane C0's `cache_invariants'`). -/
theorem hmax_block_of_reachable {acp₀ : Payload sp.n}
    {st : Store sp.toParams (Payload sp.n)} (h : st.Reachable acp₀) :
    ∃ B ∈ st.tree, (st.σ B.root).h = st.hmax :=
  (Store.cache_invariants' h).2.2.2.2.2.1

/-- `h_j < h_max` at a shadow-reachable store: the cached justification is the state of a held
block, whose `h_j` is below its height, which is at most `h_max`. -/
theorem hj_lt_hmax_of_reachable {acp₀ : Payload sp.n}
    {st : Store sp.toParams (Payload sp.n)} (h : st.Reachable acp₀) : st.hj < st.hmax := by
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := Store.cache_invariants' h
  exact hBjhj ▸ (Store.hj_lt_h_with Store.finalitySpec_updateFinality h.reachableWith hBj).trans_le
    (hge Bj hBj)

/-- `h_j < h_max` at the shadow store of a node honest at `d`. -/
theorem hj_lt_hmax_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  hj_lt_hmax_of_reachable (reachable_at hrun hd hy hi)

end RunFacts'

/-- **The rows are sourced by compatible blocks, at a read time** (stock `rows_sourced_by`): with
every FG source, at a cut before `n` of a node honest then, compatible with `B`, every attestation
of the tree at cut `n` of a node honest at a time `t ≥ 0` after every cut before `n`, by a
validator honest at `t`, has a source compatible with `B`, held by that validator at its signing
cut. The frame enters only through the signed source lying in the signer's tree, which is the
store's tree above `F` (`Store.toFrame'_tree`). Uses `Coherence.attest_source'`. -/
theorem rows_sourced_by {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {B : AC.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x k, k < n → x ∈ H (tr.time k) → ∀ ℓ C, AC.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocksAt H) C B)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) :
    HonestRowsSourcedBy tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n t := by
  have hr := hrun.upTo ht0
  refine honestRowsSourcedBy_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmn, -, k, hkm, src, hcall⟩ :=
    honest_row_signed_before' hr (hnc.upTo _) hy (by rw [Trace.upTo_state tr y ht]; exact hX) ha
      hav
  obtain ⟨j, rfl, ℓ, hcj, hcl, -, hC, hfg⟩ := Coherence.attest_source hr.toLocalRun hav hcall
  have hj1 : j + 1 < n := by omega
  have hjt : ∀ k' < j + 1, tr.time k' ≤ t := fun k' hk' => ht k' (by omega)
  have hjt' : ∀ k' < j, tr.time k' ≤ t := fun k' hk' => ht k' (by omega)
  obtain ⟨hjd, hcj⟩ := (Trace.upTo_callAt _).mp hcj
  obtain ⟨-, hcall⟩ := (Trace.upTo_callAt _).mp hcall
  rw [Trace.upTo_state tr a.val hjt'] at hC
  rw [Trace.upTo_state tr a.val hjt, Trace.upTo_state tr a.val hjt'] at hfg
  have hav' : a.val ∈ H (tr.time j) := hrun.antitone hjd hav
  have hav1 : a.val ∈ H (tr.time (j + 1)) := hrun.antitone (ht _ hj1) hav
  have hfr := ((Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw a.val j _ hcj hav')).1
  have hto : AC.ToFGAt tr.projAC a.val j ℓ src :=
    ⟨projAC_callAt.2 hcj, hcl, by
      rw [Consensus.Goldilocks.Shadow.PU.Growing.projAC_state_at hrun hav']
      exact hC⟩
  have hst' : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := (AC.toFG_source_below_lock hC).1.1
    rw [hfr, Node.frame_eq, Store.toFrame_tree] at h'
    rw [hfg]
    exact h'.1
  have hR := Node.fg_reachable_at hr.toLocalRun hav (j + 1)
  rw [Trace.upTo_state tr a.val hjt] at hR
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source_with Store.finalitySpec_updateFinality hR.reachableWith _ hst'
  have hT := createAtt_T ((Node.cutStep_attest_some _ _ _ _ _ _).1
    (hrun.cutLaw a.val (j + 1) _ hcall hav1)).1
  rw [← hEr, hET] at hT
  exact ⟨src, hsrc a.val j (by omega) hav' ℓ src hto,
    isHonestSourceAt_iff.2 ⟨a.val, j + 1, hav, hjt, hst', hT.symm⟩⟩

/-- The rows sourced at a read time, in the prefix through it, as shadow-geometry rows
(`FrameGeometry.HonestRowsSourced`), sourced by `G`-blocks held in the prefix. -/
theorem honestRowsSourcedBy_toFrame {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : ∀ k' < k, tr.time k' ≤ t)
    (hsrc : HonestRowsSourcedBy tr H G y k t) :
    FrameGeometry.HonestRowsSourced (tr.upTo t) (H t)
      (fun D' => G D' ∧ D' ∈ (tr.upTo t).HonestBlocks (H t)) y k :=
  FrameGeometry.honestRowsSourced_iff.2 fun X hX a ha hav => by
    obtain ⟨D', hD', hDs⟩ := Compose.honestRowsSourced_iff.1 (hsrc.upTo_held ht) X hX a ha hav
    exact ⟨D', hD', FrameGeometry.isHonestSource_iff.2 (Compose.isHonestSource_iff.1 hDs)⟩

/-- **G3′ over the shadow run.** Under Hi at cut `k`, read at a time `t` at which the node is
honest after every earlier cut, with `2 f_t < n`, every block of its tree at state height at least
`h_j + 1` is strictly above `P` (stock `above_of_hi_height_at`). The stock proof reads only the
accepted tree, the states `σ` and their entries, so it ports with the primed geometry of
`Shadow/PU/Geometry`; it never reads viability. -/
theorem above_of_hi_height_at (D : OutageLockPremises tr H proposer dg ini) {i : Nat}
    (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat} {t : Time} (hk : k ≤ i) (ht0 : 0 ≤ t)
    (ht : ∀ k' < k, tr.time k' ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hHi : HiAt tr H D.P y k) {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree)
    (hh : (tr.state y k).fg.hj + 1 ≤ ((tr.state y k).fg.σ X.root).h) :
    Anc (tr.HonestBlocksAt H) D.P X ∧ X.root ≠ D.P.root := by
  have hU := Coherence.honestBlocksAt_coherent D.hrun D.hnc
  have hr := D.hrun.upTo ht0
  have hnc' := D.hnc.upTo t
  have hfg := projFG_localRun' hr hnc'
  have hsub : (tr.upTo t).HonestBlocks (H t) ⊆ tr.HonestBlocksAt H :=
    RunTrace.honestBlocks_upTo_subset D.hrun.time_mono ht0
  have hst := Trace.upTo_state tr y ht
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  rw [← hst] at hX hh hPJ hJP
  obtain ⟨-, hJt, -, -⟩ := Store.cache_invariants' (Node.fg_reachable_at hr.toLocalRun hy k)
  -- `h_j ≥ 1`: at `h_j = 0`, `Σ.J` is genesis, and nothing is strictly below genesis
  have hj1 : 1 ≤ ((tr.upTo t).state y k).fg.hj := by
    by_contra h0
    have hJg := FrameGeometry.justified_genesis' hr.toLocalRun (i := k) (by omega) hy
    by_cases hPJe : D.P = ((tr.upTo t).state y k).fg.J
    · exact hJP (by rw [hPJe])
    have := (Anc.slot_le hU hPJ).2 hPJe
    rw [hJg] at this
    exact Nat.not_lt_zero _ this
  -- the height-`h_j` entry below `X`, with a source compatible with `P`, held while honest at `t`
  have hsrcF := honestRowsSourcedBy_toFrame ht (rows_sourced_by D.hrun D.hnc (B := D.P) (n := k)
    (fun x k' hk' hx => hinv.sources x k' (by omega) hx) ht0 ht hy)
  obtain ⟨E, hEt, hEX, hEh, hET, D', ⟨hD'P, -⟩, hD's⟩ :=
    FrameGeometry.frame_crossing_source_before' hr.toLocalRun hf hy hsrcF hX hj1
      (Nat.lt_of_succ_le hh)
  have hEU : E ∈ (tr.upTo t).HonestBlocks (H t) := FrameGeometry.fg_tree_subset_honest hy k hEt
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ :=
    FrameGeometry.honest_source_entry' hr.toLocalRun hfg hD's hEU rfl
  have hED : Anc (tr.HonestBlocksAt H) E D' :=
    hED'.mono ((FrameGeometry.fg_tree_subset_honest hx k').trans hsub)
  have hEP : Compatible (tr.HonestBlocksAt H) E D.P := by
    rcases hD'P with h | h
    · exact Or.inl (hED.trans h)
    · exact Anc.total hU hED h
  have hEXU : Anc (tr.HonestBlocksAt H) E X :=
    hEX.mono ((FrameGeometry.fg_tree_subset_honest hy k).trans hsub)
  -- `E` is not below `P`: else `E ⪯ Σ.J`, two entries of height `h_j` below `Σ.J`, so `E = Σ.J`
  have hnot : ¬ Anc (tr.HonestBlocksAt H) E D.P := by
    intro hE
    have hEJ := FrameGeometry.honest_held_anc' hr.toLocalRun hfg hy
      (Consensus.Goldilocks.RunTrace.anc_upTo_of_right D.hrun.toLocalRun D.hnc
        ht0 ⟨y, hy, k, hJt⟩ (hE.trans hPJ)) hJt
    obtain ⟨hJh, hJT, -⟩ :=
      FrameGeometry.justified_honest_source_before' hr.toLocalRun hfg hf hy hsrcF hj1
    have hEJe : E = ((tr.upTo t).state y k).fg.J :=
      FrameGeometry.held_entry_unique' hr.toLocalRun hfg hy hJt hEJ Relation.ReflTransGen.refl
        (hEh.trans hJh.symm) hET hJT
    subst hEJe
    exact hJP (congrArg (·.root) (Anc.antisymm hU hE hPJ))
  have hPE : Anc (tr.HonestBlocksAt H) D.P E := hEP.resolve_left hnot
  refine ⟨hPE.trans hEXU, fun hXr => hnot ?_⟩
  have hXP : X = D.P :=
    hU.1 (hsub (FrameGeometry.fg_tree_subset_honest hy k hX)) D.hP.1 hXr
  exact hXP ▸ hEXU

/-- **The Hi walk over the shadow run.** Under Hi at cut `i`, `w` honest at `t_i` with
`2 f_{t_i} < n`, a head walk of the shadow frame over the viable tree of an ancestor-closed domain
extends `P`, when the live lock blocks of the walked state are compatible with `P` and the
domain's viable tree is nonempty or the domain is the whole tree.

The stock `anc_getHead_of_hi` with its `hcond` branch collapsed (`anc_getHead_of_hi'_core`). -/
theorem anc_getHead_of_hi (D : OutageLockPremises tr H proposer dg ini) {i : Nat}
    (hinv : OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) (hHi : HiAt tr H D.P w i) (A : AC.ACState sp.n)
    (t : Time) (V : AC.View sp.n) (σ : Int)
    {dom : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hdom : dom ⊆ (Node.frame (tr.state w i)).tree)
    (hdomA : ∀ B ∈ dom, ∀ X, (Node.frame (tr.state w i)).Anc X B → X ∈ dom)
    (hne : ((Node.frame (tr.state w i)).viableTree dom).Nonempty ∨
      (Node.frame (tr.state w i)).tree ⊆ dom)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp A.locks (Node.frame (tr.state w i)) t,
      Compatible (tr.HonestBlocksAt H) L D.P) :
    Anc (tr.HonestBlocksAt H) D.P
      (AC.getHead sp A (Node.frame (tr.state w i)) t
        ((Node.frame (tr.state w i)).viableTree dom) V σ) := by
  have hd := D.hrun.time_nonneg i
  have ht : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => D.hrun.time_mono hk.le
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  rw [Node.frame_eq] at hdom hdomA hne hlocks ⊢
  refine anc_getHead_of_hi_core (Coherence.honestBlocksAt_coherent D.hrun D.hnc)
    (by simpa [Node.frame_eq] using frameOK_at D.hrun hd hw ht) (tree_held_at hd hw ht)
    (hj_lt_hmax_at D.hrun hd hw ht) (hmax_block_of_reachable (reachable_at D.hrun hd hw ht))
    hPJ hJP (fun hX hh => above_of_hi_height_at D hinv le_rfl hd ht hw hf hHi hX hh)
    (hinv.caches_at_cut le_rfl hw).1
    (fun hY hXY => Coherence.held_anc_at D.hrun D.hnc hd hw ht hXY hY) A t V σ hdom hdomA hne hlocks


/-! ## The candidate step of the invariant (`viable`, OB-F)

The only place where the shadow frame enters the cut induction: at a cut `n` of a node honest at a
read time `t`, with the FG sources of the earlier cuts compatible with `P`, the caches are
compatible with `P` and `P`, when in the shadow frame, is a candidate of it. -/

section Candidate'

variable {d : Time} {y : Fin sp.n} {i : Nat}

/-- A block held by a node honest at its cut is held while honest (`mem_honestBlocksAt`). -/
theorem mem_honestBlocksAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hB : B ∈ (tr.state y i).fg.tree) : B ∈ tr.HonestBlocksAt H :=
  ⟨y, i, tr.time i, hrun.time_nonneg i, fun _ hk => hrun.time_mono hk.le, hy, hB⟩

/-- Every block held while honest descends from genesis (`honestAt_genesis_anc`). -/
theorem honestAt_genesis_anc
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈ tr.HonestBlocksAt H ∧
      Anc (tr.HonestBlocksAt H)
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := by
  obtain ⟨t, ht, hBt⟩ := exists_upTo_of_mem hB
  obtain ⟨hg, hanc⟩ := FrameGeometry.honest_genesis_anc' (hrun.upTo ht).toLocalRun hBt
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht
  exact ⟨hsub hg, hanc.mono hsub⟩

/-- The AC run of the prefix through `d ≥ 0` (`acRun_upTo`). -/
theorem acRun_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := Compose.goldilocks_ac_projection_from' (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest
(`frameIn_at`). -/
theorem frameIn_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H :=
  have h := AC.frameIn_of_callAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  ⟨h.1, h.2.trans (RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg i))⟩

/-- **(SRC)**: an FG source at a cut `k` of a node honest then is compatible with `B` when every
lock stored at `k` names a held block compatible with `B` (`source_compatible_at`). The source is
the viable ancestor of a live lock block in the call's frame, which is the shadow frame. -/
theorem source_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {k : Nat} (hy : y ∈ H (tr.time k))
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ (tr.state y k).ac.locks, ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧
      Compatible (tr.HonestBlocksAt H) L B)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : AC.ToFGAt tr.projAC y k ℓ C) : Compatible (tr.HonestBlocksAt H) C B := by
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hpc
  rw [Consensus.Goldilocks.Shadow.PU.Growing.projAC_state_at hrun hy] at hC
  obtain ⟨-, a, ha, hCa⟩ := AC.toFG_source_below_lock hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := AC.mem_liveLockBlocks hΦ ha
  obtain ⟨-, hva⟩ := AC.viableAncestor_anc hΦ hB₀
  obtain ⟨L, hL, hLr, hLB⟩ := hlocks l₀ hl₀
  obtain rfl : B₀ = L :=
    hU.1 (hΦU hB₀) (mem_honestBlocksAt hrun hy hL) (hB₀r.trans hLr.symm)
  have hCB : ℓ.frame.Anc C B₀ := hCa.trans hva
  exact compatible_of_head_anc hU (hCB.mono hΦU) hLB

/-- **`Σ.J` is compatible with a block compatible with every source satisfying `G`**, at a cut `i`
of a node honest at a time `t ≥ 0` after every cut before `i`, with `2 f_t < n`
(`J_compatible_by`). -/
theorem J_compatible_by (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedBy tr H G y i t)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B) (hB : B ∈ tr.HonestBlocksAt H) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B := by
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  have hr := hrun.upTo ht0
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht0
  have hst := Trace.upTo_state tr y ht
  by_cases h0 : (tr.state y i).fg.hj = 0
  · have hJ := FrameGeometry.justified_genesis' hr.toLocalRun (i := i) (by rw [hst]; exact h0) hy
    rw [hst] at hJ
    rw [hJ]
    exact Or.inl (honestAt_genesis_anc hrun hB).2
  obtain ⟨-, -, D, ⟨hD, -⟩, hDs⟩ :=
    FrameGeometry.justified_honest_source_before' hr.toLocalRun
      (projFG_localRun' hr (hnc.upTo _)) hf hy (honestRowsSourcedBy_toFrame ht hsrc)
      (by rw [hst]; omega)
  rw [hst] at hDs
  have hJ := (Store.cache_invariants' (Node.fg_reachable_at hr.toLocalRun hy i)).2.1
  rw [hst] at hJ
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := FrameGeometry.honest_source_entry' hr.toLocalRun
    (projFG_localRun' hr (hnc.upTo _)) hDs ⟨y, hy, i, by rw [hst]; exact hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D :=
    (hJD.mono (FrameGeometry.fg_tree_subset_honest hx k)).mono hsub
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hU hJDU h

/-- **OB-F at a read time**: at a cut `n` of a node honest at a time `t ≥ 0` after every cut
before `n`, with `2 f_t < n` and the rows sourced by blocks compatible with a block `B` held while
honest, `Σ.F` and `Σ.J` are compatible with `B` (`caches_compatible_by`). -/
theorem caches_compatible_by
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hsrc : HonestRowsSourcedBy tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n t) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.J B := by
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  have hst := Trace.upTo_state tr y ht
  have hJ := J_compatible_by hrun hnc ht0 ht hy hf hsrc (fun _ h => h) hBU
  have hR := Node.fg_reachable_at (hrun.upTo ht0).toLocalRun hy n
  rw [hst] at hR
  obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants' hR
  have hsub : (tr.state y n).fg.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht0 ⟨y, hy, n, by rw [hst]; exact hX⟩
  exact ⟨compatible_of_head_anc hU (hFJ.mono hsub) hJ, hJ⟩

/-- **A held block compatible with every source stays a shadow candidate**, at a cut `i` of a node
honest at a time `t ≥ 0` after every cut before `i`, with `2 f_t < n`
(`held_candidate_of_rows_by`). -/
theorem held_candidate_of_rows_by
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourcedBy tr H G y i t)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hst := Trace.upTo_state tr y ht
  have hBt' := hBt
  rw [Node.frame_eq, Store.toFrame_tree] at hBt'
  have hBU : B ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hst]; exact hBt'.1⟩
  have h := FrameGeometry.held_candidate_of_rows' (hrun.upTo ht0).toLocalRun
    (projFG_localRun' (hrun.upTo ht0) (hnc.upTo _)) hf hy i (honestRowsSourcedBy_toFrame ht hsrc)
    (fun D ⟨hD, hDU⟩ => (hGB D hD).imp (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hBU)
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hDU))
    (by rw [hst]; exact hBt)
  rwa [hst] at h

/-- **The caches and the candidate at a cut, from the earlier sources.** At a cut `n` of a node
honest at a time `t ≥ 0` after every cut before `n`, with `2 f_t < n` and every FG source of the
earlier cuts compatible with `P`: `Σ.F` and `Σ.J` are compatible with `P` (OB-F), and `P`, when in
the shadow frame, is a candidate of it (VA). The induction step of `outage_lock_inv_at` for the
two state fields. -/
theorem caches_and_viable_at (D : OutageLockPremises tr H proposer dg ini) {n : Nat}
    (hsrc : ∀ x k, k < n → x ∈ H (tr.time k) → ∀ ℓ C, AC.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocksAt H) C D.P)
    {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : 2 * (H t)ᶜ.ncard < sp.n) :
    (Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.J D.P) ∧
    (D.P ∈ (Node.frame (tr.state y n)).tree →
      (Node.frame (tr.state y n)).AncestorCandidate D.P) :=
  ⟨caches_compatible_by D.hrun D.hnc ht0 ht hy hf D.hP.1
      (rows_sourced_by D.hrun D.hnc hsrc ht0 ht hy),
    fun hPt => held_candidate_of_rows_by D.hrun D.hnc ht0 ht hy hf
      (rows_sourced_by D.hrun D.hnc hsrc ht0 ht hy) (fun _ h => h) hPt⟩

end Candidate'

/-- **The outage lock invariant at every cut**: from the premise package and the step
`OutageS5StepAt'` at each cut. -/
theorem outage_lock_inv_at (D : OutageLockPremises tr H proposer dg ini)
    (hS5 : OutageS5StepAt D) :
    ∀ i, OutageLockInv D i :=
  outage_lock_inv_at_with D hS5 fun _ _ hsrc _ ht0 ht hy hf =>
    caches_and_viable_at D hsrc ht0 ht hy hf

end Consensus.Goldilocks.Shadow.PU

end
