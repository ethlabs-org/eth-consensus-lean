module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilySources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyReadPoint

public section

/-! # Concrete instances of the family counts

The original declarations can use these instances without strengthening their statements.
The collision premise is always the original explicit `hnc`, or `D.hnc`.
-/

namespace Consensus.Goldilocks.FamilySafety

set_option backward.isDefEq.respectTransparency false

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- The original counted-vote hypotheses already discharge every family premise. -/
theorem counted_honest_vote_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {X : Fin sp.n} (hX : X ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i s C CV) {v : SA.Vote sp.n}
    (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ tr.HonestBlocks H, R.root = v.head ∧ Anc (tr.HonestBlocks H) C R :=
  counted_honest_vote_family (hr.family hnc) (poolFacts_goldilocks hr hnc) hX hR hv hvH

/-- Result membership needs no new collision premise. -/
theorem result_mem_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {X : Fin sp.n} (hX : X ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i s C CV) : C ∈ tr.HonestBlocks H :=
  result_mem_family (hr.family hnc) hX hR

/-- Result compatibility uses the collision premise already in the outage package. -/
theorem result_compatible_instance {D : Compose.OutageLockPremises tr H proposer dg}
    {i : Nat} (hinv : Compose.OutageVoteInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {m : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt tr.projAC y i m C CV) (hm : m ≤ D.j₀ ∨ D.r ≤ m) :
    Compatible (tr.HonestBlocks H) C D.P := by
  have hm' : m ≤ D.family.j₀ ∨ D.family.r ≤ m := by
    simpa only [Compose.OutageLockPremises.family_j₀, Compose.OutageLockPremises.family_r] using hm
  simpa only [Compose.OutageLockPremises.family_P] using
    OutageVoteInv.result_compatible (poolFacts_goldilocks D.hrun D.hnc)
    (voteTiming_goldilocks D.hrun D.hnc) (participants_goldilocks D.hrun D.hnc)
    (Compose.OutageVoteInv.family_iff.mpr hinv) hy hR hm'

/-- The full invariant's conversion reads `D.hnc`, not a new theorem hypothesis. -/
theorem liveLockBlocks_compatible_instance {D : Compose.OutageLockPremises tr H proposer dg}
    (hinv : ∀ i, Compose.OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) (τ : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      Compatible (tr.HonestBlocks H) X B := by
  rw [← Compose.projAC_state D.hrun.toLocalRun hy m]
  exact liveLockBlocks_compatible_family
    (fun i => Compose.OutageLockInv.family_iff.mpr (hinv i)) hy m τ
    (by simpa only [Compose.OutageLockPremises.family_P] using hBP)

/-- The stored-lock instance changes no premise. -/
theorem lockInv_state_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  rw [← Compose.projAC_state hr.toLocalRun hy m]
  exact lockInv_state_family (lockInvariant_goldilocks hr hnc) hy m

/-- The chain reader uses the same explicit collision premise as its original. -/
theorem liveBlocks_chain_at_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (m : Nat) (τ : Time) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      ∀ Y ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
        Compatible (Node.frame (tr.state y m)).tree X Y := by
  rw [← Compose.projAC_state hr.toLocalRun hy m]
  exact liveBlocks_chain_at_family (hr.family hnc) (lockInvariant_goldilocks hr hnc) hy m τ

/-- The source branch is supplied by the concrete source theorem only here. -/
theorem source_compatible_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ (tr.state y k).ac.locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L B)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.ToFGAt tr.projAC y k ℓ C) :
    Compatible (tr.HonestBlocks H) C B := by
  exact source_compatible_family (hr.family hnc) (sourceLockAt_goldilocks hr hnc) hy
    (fun l hl => hlocks l ((Compose.projAC_state hr.toLocalRun hy k) ▸ hl))
    (fun _ he => False.elim he) h

/-- Actual source events specialize without adding a collision or viability premise. -/
theorem rows_sourced_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x ∈ H, ∀ k < n, ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C B) {y : Fin sp.n} (hy : y ∈ H) :
    Compose.HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n := by
  apply Compose.honestRowsSourced_iff.mpr
  have h := honestRowsSourced_iff.mp (rows_sourced_family (hr.family hnc)
    (Compose.projFG_localRun hr hnc) (sourceViableAt_goldilocks hr) hsrc hy)
  intro X hX a ha hav
  obtain ⟨D, hD, hs⟩ := h X hX a ha hav
  exact ⟨D, hD, Compose.isHonestSource_iff.mpr (isHonestSource_iff.mp hs)⟩

theorem reader_frame_instance {D : Compose.OutageLockPremises tr H proposer dg}
    (hinv : ∀ i, Compose.OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) (m : Nat)
    (t : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B D.P) :
    Compatible (tr.HonestBlocks H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp (tr.state y m).ac (Node.frame (tr.state y m)) t) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) := by
  rw [← Compose.projAC_state D.hrun.toLocalRun hy m]
  exact reader_frame_family (Compose.projFG_localRun D.hrun D.hnc)
    (sourceViableAt_goldilocks D.hrun) (lockInvariant_goldilocks D.hrun D.hnc)
    (fun i => Compose.OutageLockInv.family_iff.mpr (hinv i)) hy m t
    (by simpa only [Compose.OutageLockPremises.family_P] using hBP)

theorem fastLock_compatible_at_instance {D : Compose.OutageLockPremises tr H proposer dg}
    {n : Nat} (hvi : Compose.OutageVoteInv D n) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H → ∃ j < n, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v) :
    Compatible (tr.HonestBlocks H) B D.P := by
  simpa only [Compose.OutageLockPremises.family_P] using
    fastLock_compatible_at_family (lockFacts_goldilocks D.hrun D.hnc)
      (voteTiming_goldilocks D.hrun D.hnc) (Compose.OutageVoteInv.family_iff.mpr hvi) hy hfl hcut

theorem readPoint_liveLockBlocks_compatible_at_instance
    {D : Compose.OutageLockPremises tr H proposer dg}
    {i : Nat} (hinv : Compose.OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) {ℓ}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B :=
  readPoint_liveLockBlocks_compatible_at_family (lockFacts_goldilocks D.hrun D.hnc)
    (voteTiming_goldilocks D.hrun D.hnc) (readPointOrigin_goldilocks D.hrun D.hnc)
    (Compose.OutageLockInv.family_iff.mpr hinv) hy hc hpos
    (by simpa only [Compose.OutageLockPremises.family_P] using hBP)

theorem locks_compatible_instance {D : Compose.OutageLockPremises tr H proposer dg}
    {n : Nat} (hvi : Compose.OutageVoteInv D n)
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
      (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P)
    {y : Fin sp.n} (hy : y ∈ H) {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
  have hres' : ∀ y ∈ H, ∀ k < n, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
      (m ≤ D.family.j₀ ∨ D.family.r ≤ m) → Compatible (tr.HonestBlocks H) C D.family.P := by
    simpa only [Compose.OutageLockPremises.family_j₀, Compose.OutageLockPremises.family_r,
      Compose.OutageLockPremises.family_P] using hres
  simpa only [Compose.OutageLockPremises.family_P] using
    OutageVoteInv.locks_compatible (lockFacts_goldilocks D.hrun D.hnc)
      (voteTiming_goldilocks D.hrun D.hnc) (Compose.OutageVoteInv.family_iff.mpr hvi) hres' hy
      ((Compose.projAC_state D.hrun.toLocalRun hy n).symm ▸ hl)

theorem held_candidate_of_rows_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : Compose.HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hs : HonestRowsSourced (A := SA.goldilocksOperations sp _ ro) tr H G y i :=
    (honestRowsSourced_iff
      (A := SA.goldilocksOperations sp _ ro) (tr := tr) (H := H) (G := G) (y := y) (i := i)).mpr (by
    intro X hX a ha hav
    obtain ⟨D, hD, hs⟩ := (Compose.honestRowsSourced_iff.mp hsrc) X hX a ha hav
    exact ⟨D, hD, isHonestSource_iff.mpr (Compose.isHonestSource_iff.mp hs)⟩)
  exact held_candidate_of_rows_family hr.toLocalRun (Compose.projFG_localRun hr hnc)
    hf hy i hs hGB hBt

theorem caches_compatible_instance (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {n : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H)
    (hsrc : Compose.HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n) :
    Compatible (tr.HonestBlocks H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y n).fg.J B := by
  have hs : HonestRowsSourced (A := SA.goldilocksOperations sp _ ro) tr H
      (fun D => Compatible (tr.HonestBlocks H) D B) y n := by
    apply (honestRowsSourced_iff (A := SA.goldilocksOperations sp _ ro)
      (tr := tr) (H := H) (y := y) (i := n)).mpr
    intro X hX a ha hav
    obtain ⟨D, hD, hs⟩ := (Compose.honestRowsSourced_iff.mp hsrc) X hX a ha hav
    exact ⟨D, hD, isHonestSource_iff.mpr (Compose.isHonestSource_iff.mp hs)⟩
  exact caches_compatible_family hr.toLocalRun (Compose.projFG_localRun hr hnc) hf hy hBU hs

end Consensus.Goldilocks.FamilySafety

end
