module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: consumers of the invariant

From the invariant at every cut (`outage_lock_inv`):

* `liveLockBlocks_compatible` ((i) at the reader, `outage_reader_locks`): the
  live lock blocks of an honest stored lock set, in the node's frame, are compatible with every
  block `B ⪯ P` (the read tip is below the origin);
* `reader_frame` (`outage_reader_frame`): `fc_root` is compatible with `B`, and `B`,
  when in the frame, is below the anchor or in the full viable tree; the live-lock chain holds
  at every honest cut (`lockInv_state`, `liveBlocks_chain_at`);
* `fastLock_compatible`: every honest fast lock block (update or optimistic
  selection) is compatible with `P`;
* `readPoint_liveLockBlocks_compatible_at` (live-lock compatibility at a cast's read point): the
  live lock blocks of an honest vote's read point are compatible with every block `B ⪯ P` (the
  read-point locks sit below stored locks or below the cut's optimistic selection,
  `SA.readPoint_locks_provenance`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- **Transfer to a block below `P`**: a block compatible with `P` is compatible with every block
`B ⪯ P` (the read tip is below the origin). -/
theorem compatible_of_anc_right (hU : Coherent (tr.HonestBlocks H))
    {X B P : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B P)
    (hX : Compatible (tr.HonestBlocks H) X P) : Compatible (tr.HonestBlocks H) X B := by
  rcases hX with h | h
  · exact Anc.total hU h hBP
  · exact Or.inr (hBP.trans h)

/-- **(i) at a reader** (`outage_reader_locks`): at every honest cut and time, the live lock
blocks of the stored locks in the node's frame are compatible with every block `B ⪯ P`. -/
theorem liveLockBlocks_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) (τ : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      Compatible (tr.HonestBlocks H) X B := by
  intro X hX
  have hU := D.coherent
  have hΦ := frameOK_state D.hrun.toLocalRun hy m
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, m, hZ.1⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hX
  obtain ⟨L, hL, hLr, hLP⟩ := (hinv m).locks y hy m le_rfl l hl
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) ⟨y, hy, m, hL⟩ (hB₀r.trans hLr.symm)
  exact compatible_of_anc_right hU hBP
    (compatible_of_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) hLP)

/-- **The lock invariant at every honest cut**, in the cut's own frame: the stored record names a
block of the node's tree above every stored lock block (`lockInv_of_reachable` at the last AC
call, or none at the initial state), and the record is in the frame once `Σ.F` is below it. -/
theorem lockInv_state {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  have hst := projAC_state hrun.toLocalRun hy m
  obtain ⟨E, hEt, hEr, -⟩ := record_origin hrun hnc hy m
  have hEU : E ∈ tr.HonestBlocks H := ⟨y, hy, m, hEt⟩
  refine SA.lockInv_iff.2 ⟨E, hEU, hEr,
    fun hFE => ⟨hEt, honest_held_anc hrun hnc hy hFE hEt⟩, fun l hl X hX hXr => ?_⟩
  rw [← hst] at hl
  rcases SA.state_reachable sp hr hy m with h0 | ⟨Φ, t, hreach, -⟩
  · obtain ⟨_, hs⟩ := SA.voteStart_iff.1 (hrun.vstart y)
    rw [h0, hs] at hl
    exact absurd hl (Set.notMem_empty l)
  · obtain ⟨-, -, hli⟩ := SA.lockInv_of_reachable_from hU (hrun.vstart y) hreach
    obtain ⟨E', hE'U, hE'r, -, hlE⟩ := SA.lockInv_iff.1 hli
    obtain rfl : E' = E := hU.1 hE'U hEU (hE'r.trans (by rw [hst]; exact hEr.symm))
    exact hlE l hl X hX hXr

/-- **The live lock blocks of an honest node lie on one chain** at every cut and time, in the
cut's frame (`lockInv_state`). -/
theorem liveBlocks_chain_at (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) (τ : Time) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      ∀ Y ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
        Compatible (Node.frame (tr.state y m)).tree X Y :=
  (lockInv_state hrun hnc hy m).liveBlocks_chain
    (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
    (frameOK_state hrun.toLocalRun hy m) fun _ hX => ⟨y, hy, m, hX.1⟩

/-- **The reader frame** (`outage_reader_frame`): at an honest cut, for every block
`B ⪯ P`, `fc_root` is compatible with `B`, and `B`, when in the frame, is below the anchor or in
the full viable tree (the live-lock chain by `liveBlocks_chain_at`). -/
theorem reader_frame (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) (m : Nat)
    (t : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B D.P) :
    Compatible (tr.HonestBlocks H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp (tr.state y m).ac (Node.frame (tr.state y m)) t) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) := by
  have hU := D.coherent
  have hΦ := frameOK_state D.hrun.toLocalRun hy m
  refine ⟨?_, fun hBt => ?_⟩
  · change Compatible _ (tr.state y m).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact compatible_of_anc_right hU hBP ((hinv m).caches y hy m le_rfl).2
    · exact compatible_of_anc_right hU hBP ((hinv m).caches y hy m le_rfl).1
  have hsrc : ∀ x ∈ H, ∀ k < m, ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C D.P := fun x hx k hk => (hinv m).sources x hx k hk
  rcases held_candidate_of_rows D.hrun D.hnc D.two_faults_lt hy m
    (rows_sourced D.hrun D.hnc hsrc hy) (fun _ h => compatible_of_anc_right hU hBP h) hBt with
    h | h
  · exact Or.inl (h.trans ((SA.anc_getAnchor hΦ
      (liveBlocks_chain_at D.hrun D.hnc hy m t)).2 _ (Or.inr rfl)))
  · exact Or.inr h

/-- **An honest fast lock block is compatible with `P`, cut-indexed**: a fast update
lock or an optimistic selection of an honest node at cut `c`, whose counted honest votes were
cast at cuts before `n`, from (H)/S5V at the cuts before `n` (`OutageVoteInv D n`) only. -/
theorem fastLock_compatible_at {n : Nat} (hvi : OutageVoteInv D n) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H → ∃ j < n, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v) :
    Compatible (tr.HonestBlocks H) B D.P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hcount, hCV⟩ := SA.fastLock_counted hrun' hy hfl
  rw [D.stock] at hcount -- §S S14
  by_cases hs : s < D.j₀
  · -- an update or a selection of a label `< j₀` is within `b₀`
    have hj₀ := D.hj₀.1
    have hsj := ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rcases hfl with ⟨ℓ, C, hu, hC, hD, -⟩ | hO
    · have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
      obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hrun'.localRun hy hu.1
      have hBC : ℓ.frame.Anc B C := (SA.deepest_mem hD).1.1.2.2
      have hCU : C ∈ tr.HonestBlocks H := hΦU (SA.deepest_mem hC).1.1
      exact compatible_of_anc hU (hBC.mono hΦU) (D.compatible_of_within
        (originWithin_iff.2 ⟨y, hy, c, _, by linarith, Or.inl ⟨ℓ, hu, hC, rfl⟩⟩) hCU)
    · obtain ⟨ℓ, A, hpt, hslot, hsel, -⟩ := id hO
      have hlt : tr.time c < sp.ts (s + 1 : Nat) := by
        by_contra h
        have := (SA.ts_le_iff_le_slot sp (hrun'.localRun.time_nonneg c) ((s + 1 : Nat) : Int)).1
          (not_lt.1 h)
        rw [hslot] at this
        omega
      obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hrun'.localRun hy hpt.1
      have hBt : B ∈ ℓ.frame.tree := by
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (SA.deepest_mem hsel).1.1
      exact D.compatible_of_within (originWithin_iff.2 ⟨y, hy, c, CV, by linarith, Or.inr hO⟩)
        (hΦU hBt)
  refine by_contra fun hB => ?_
  have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ Hᶜ ∪ D.W := by
    rintro u ⟨v, hv, rfl⟩
    by_contra hu
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
    obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
    obtain ⟨j', hj', e, hve, rfl⟩ := hcut v hv hu.1
    exact hB (compatible_of_voteCompat hU hRU hRr hBR
      (hvi.voteCompat_of_not_lateWaker hu.1 hu.2 hj' hve (by omega)))
  have := Set.ncard_le_ncard hsub
  have := D.two_mul_lt
  omega


/-- **Every honest fast lock block is compatible with `P`**: a fast update lock or an
optimistic selection of an honest node. -/
theorem fastLock_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) : Compatible (tr.HonestBlocks H) B D.P :=
  fastLock_compatible_at (hinv (c + 1)).toOutageVoteInv hy hfl fun _ hv hvH =>
    let ⟨j', hj', e, hve, he⟩ := fastLock_honest_vote D.hrun D.hnc hy hfl hv hvH
    ⟨j', Nat.lt_succ_of_le hj', e, hve, he⟩

/-- **(i) at a read point, cut-indexed** (live-lock compatibility inside the cut induction):
at an honest vote of a slot `> 0` cast at cut `i`, the live lock blocks of the read point are
compatible with every block `B ⪯ P`, from the invariant at the cast cut `i` only. The stored locks
are the `locks` field at `i`; the read point's optimistic lock is written by the receipt's check
before the call's own vote, so its counted honest votes were cast at cuts before `i`
(`SA.readPoint_locks_provenance_strict`) and (H)/S5V at the cuts before `i` (`OutageVoteInv`) decide
it. -/
theorem readPoint_liveLockBlocks_compatible_at {i : Nat} (hinv : OutageLockInv D i)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  intro L hL
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hr := hrun'.localRun
  have hU := D.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨l', hl', B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨B', hB', hB'r, h⟩ := SA.readPoint_locks_provenance_strict hrun' hy hc hpos l' hl'
  obtain rfl : B₀ = B' := hΦ.coherent.1 hB₀ hB' (hB₀r.trans hB'r.symm)
  refine compatible_of_anc_right hU hBP
    (compatible_of_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) ?_)
  rcases h with ⟨l, hl, B₁, hB₁, hB₁r, hanc⟩ | ⟨B₁, CV, hfl, hcut, hanc⟩
  · rw [projAC_state D.hrun.toLocalRun hy] at hl
    obtain ⟨L', hL', hL'r, hcomp⟩ := hinv.locks y hy i le_rfl l hl
    obtain rfl : B₁ = L' := hU.1 (hΦU hB₁) ⟨y, hy, i, hL'⟩ (hB₁r.trans hL'r.symm)
    exact compatible_of_anc hU (hanc.mono hΦU) hcomp
  · exact compatible_of_anc hU (hanc.mono hΦU)
      (fastLock_compatible_at hinv.toOutageVoteInv hy (Or.inr hfl) hcut)

end Consensus.Goldilocks.Compose

end
