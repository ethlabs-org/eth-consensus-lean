module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint

public section

/-! # Outage lock safety: consumers of the invariant (card §8, §9; O4 read-back d8f2833 §1)

From the invariant at every cut (`outage_lock_inv`):

* `liveLockBlocks_compatible` ((i) at the reader, S5-G's lock half, `outage_reader_locks`): the
  live lock blocks of an honest stored lock set, in the node's frame, are compatible with every
  block `B ⪯ P` (the read tip is below the origin);
* `reader_frame` (S5-G1/G2, `outage_reader_frame`): `fc_root` is compatible with `B`, and `B`,
  when in the frame, is below the anchor or in the full viable tree; the live-lock chain holds
  at every honest cut (`lockInv_state`, `liveBlocks_chain_at`);
* `fastLock_compatible` (§5.2(a)(b)): every honest fast lock block (update or optimistic
  selection) is compatible with `P`;
* `readPoint_liveLockBlocks_compatible` (S5's `LiveLocksCompatible` at a cast's read point): the
  live lock blocks of an honest vote's read point are compatible with every block `B ⪯ P` (the
  read-point locks sit below stored locks or below the cut's optimistic selection,
  `SA.readPoint_locks_provenance`);
* `veto_record_above` ((iii), §8): an update with a result above `P` that a live lock vetoes has a
  stored record above `P`;
* `effective_record_above` (§8): a stored record above `P` makes the effective record above `P`,
  given OB-F. -/

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

/-- **(i) at a reader** (S5-G, `outage_reader_locks`): at every honest cut and time, the live lock
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
theorem lockInv_state (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hst := projAC_state hrun.toLocalRun hy m
  obtain ⟨E, hEt, hEr, -⟩ := record_origin hrun hnc hy m
  have hEU : E ∈ tr.HonestBlocks H := ⟨y, hy, m, hEt⟩
  refine SA.lockInv_iff.2 ⟨E, hEU, hEr,
    fun hFE => ⟨hEt, honest_held_anc hrun hnc hy hFE hEt⟩, fun l hl X hX hXr => ?_⟩
  rw [← hst] at hl
  rcases SA.state_reachable sp hr hy m with h0 | ⟨Φ, t, hreach, -⟩
  · rw [h0] at hl
    exact absurd hl (Set.notMem_empty l)
  · obtain ⟨-, -, hli⟩ := SA.lockInv_of_reachable hU hreach
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

/-- **The reader frame** (S5-G1/G2, `outage_reader_frame`): at an honest cut, for every block
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

/-- **Every honest fast lock block is compatible with `P`** (§5.2(a)(b)): a fast update lock or an
optimistic selection of an honest node. -/
theorem fastLock_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) : Compatible (tr.HonestBlocks H) B D.P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hU := D.coherent
  have hvi := (hinv (c + 1)).toOutageVoteInv
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hcount, hCV⟩ := SA.fastLock_counted hrun' hy hfl
  by_cases hs : s < D.j₀
  · -- an update or a selection of a label `< j₀` is within `b₀`
    have hj₀ := D.hj₀.1
    have hsj := ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rcases hfl with ⟨ℓ, C, hu, hC, -, hD, -⟩ | hO
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
    obtain ⟨j', hj', e, hve, rfl⟩ := fastLock_honest_vote D.hrun D.hnc hy hfl hv hu.1
    exact hB (compatible_of_voteCompat hU hRU hRr hBR
      (hvi.voteCompat_of_not_lateWaker hu.1 hu.2 (by omega) hve (by omega)))
  have := Set.ncard_le_ncard hsub
  have := D.two_mul_lt
  omega

/-- **(i) at a read point** (S5's `LiveLocksCompatible`): at an honest vote of a slot `> 0`, the
live lock blocks of the read point are compatible with every block `B ⪯ P`. -/
theorem readPoint_liveLockBlocks_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  intro L hL
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hU := D.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨l', hl', B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨B', hB', hB'r, h⟩ := SA.readPoint_locks_provenance hr hy hc hpos l' hl'
  obtain rfl : B₀ = B' := hΦ.coherent.1 hB₀ hB' (hB₀r.trans hB'r.symm)
  refine compatible_of_anc_right hU hBP
    (compatible_of_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) ?_)
  rcases h with ⟨l, hl, B₁, hB₁, hB₁r, hanc⟩ | ⟨B₁, CV, hfl, hanc⟩
  · rw [projAC_state D.hrun.toLocalRun hy] at hl
    obtain ⟨L', hL', hL'r, hcomp⟩ := (hinv i).locks y hy i le_rfl l hl
    obtain rfl : B₁ = L' := hU.1 (hΦU hB₁) ⟨y, hy, i, hL'⟩ (hB₁r.trans hL'r.symm)
    exact compatible_of_anc hU (hanc.mono hΦU) hcomp
  · exact compatible_of_anc hU (hanc.mono hΦU) (fastLock_compatible hinv hy (Or.inr hfl))

/-- **(iii) veto-harmless** (§8): at an honest update whose result `C ⪰ P` a live lock vetoes, the
stored record names a block above `P`. -/
theorem veto_record_above (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H)
    {c m : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hu : SA.UpdateAt tr.projAC w c m ℓ)
    (hC : SA.getConfirmation sp (tr.state w c).ac ℓ.frame m = some C)
    (hPC : Anc (tr.HonestBlocks H) D.P C)
    (hveto : SA.conflictsWithLock sp (tr.state w c).ac.locks ℓ.frame (tr.time c) C) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state w c).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) D.P E := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hU := D.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hw hu.1
  have hfr : ℓ.frame = Node.frame (tr.state w c) :=
    (D.hrun.cutLaw w hw c _ (projAC_callAt.1 hu.1)).1
  obtain ⟨L, hL, hCL⟩ := hveto
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨L', hL', hL'r, hL'P⟩ := (hinv c).locks w hw c le_rfl l hl
  obtain rfl : B₀ = L' := hU.1 (hΦU hB₀) ⟨w, hw, c, hL'⟩ (hB₀r.trans hL'r.symm)
  have hva := SA.viableAncestor_anc hΦ hB₀
  have hCt : C ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  have hPL : Anc (tr.HonestBlocks H) D.P (ℓ.frame.viableAncestor B₀) := by
    rcases compatible_of_anc hU (hva.2.mono hΦU) hL'P with h | h
    · exact absurd (Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hva.1 (h.trans hPC) hCt)) hCL
    · exact h
  obtain ⟨Φp, tp, hreach, -, hok⟩ := pre_reachable hr hw hu.1
  obtain ⟨hin, -, hli⟩ := SA.lockInv_of_reachable hr.coherent hreach
  have hli' := hli.callOK hr.coherent hin hok
  rw [projAC_state D.hrun.toLocalRun hw] at hli'
  obtain ⟨E, hE, hEr, hLE⟩ := hli'.liveBlock_anc hU hΦ hΦU hL
  exact ⟨E, hΦU hE, hEr, hPL.trans (hLE.mono hΦU)⟩

/-- **The effective record** (§8): at an honest cut whose `Σ.F` is compatible with `P` (OB-F), a
stored record naming a block above `P` makes the effective record
`(lookup Φ latestConfirmed).getD Φ.F` a block above `P`. -/
theorem effective_record_above (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) {E : SA.Blk sp.n (List (FG.Att sp.n))} (hEU : E ∈ tr.HonestBlocks H)
    (hEr : E.root = (tr.state y m).ac.latestConfirmed) (hPE : Anc (tr.HonestBlocks H) D.P E) :
    Anc (tr.HonestBlocks H) D.P ((SA.lookup (Node.frame (tr.state y m))
      (tr.state y m).ac.latestConfirmed).getD (tr.state y m).fg.F) := by
  have hU := D.coherent
  have hΦ := frameOK_state D.hrun.toLocalRun hy m
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, m, hZ.1⟩
  cases he : SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed with
  | some E' =>
    obtain ⟨hE't, hE'r⟩ := SA.lookup_eq_some he
    obtain rfl : E' = E := hU.1 (hΦU hE't) hEU (hE'r.trans hEr.symm)
    exact hPE
  | none =>
    change Anc _ D.P (tr.state y m).fg.F
    rcases ((hinv m).caches y hy m le_rfl).1 with hFP | hPF
    · -- `Σ.F ⪯ P ⪯ E`: the record is in the frame, against `lookup = none`
      have hEt : E ∈ (Node.frame (tr.state y m)).tree := by
        obtain ⟨E', hE't, hE'r, -⟩ := record_origin D.hrun D.hnc hy m
        obtain rfl : E' = E := hU.1 ⟨y, hy, m, hE't⟩ hEU (hE'r.trans hEr.symm)
        exact ⟨hE't, honest_held_anc D.hrun D.hnc hy (hFP.trans hPE) hE't⟩
      exact absurd ⟨E, hEt, hEr⟩ (SA.lookup_eq_none he)
    · exact hPF

end Consensus.Goldilocks.Compose

end
