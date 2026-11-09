module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilySources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked

public section

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- Frame geometry is independent of the candidate's execution. -/
theorem reader_frame_family {D : OutageLockPremises F tr H proposer dg sg}
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hs5 : SourceViableAt tr H) (hli : LockInvariant F tr H)
    (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) (m : Nat)
    (t : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B D.P) :
    Compatible (tr.HonestBlocks H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp ((F.proj tr.projAC).state y m) (Node.frame (tr.state y m)) t) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) := by
  have hU := D.coherent
  have hΦ := Compose.frameOK_state D.hrun.toLocalRun hy m
  refine ⟨?_, fun hBt => ?_⟩
  · change Compatible _ (tr.state y m).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact compatible_of_anc_right_family hU hBP ((hinv m).caches y hy m le_rfl).2
    · exact compatible_of_anc_right_family hU hBP ((hinv m).caches y hy m le_rfl).1
  have hsrc := fun x hx k hk => (hinv m).sources x hx k hk
  rcases held_candidate_of_rows_family D.hrun.toLocalRun hfg D.two_faults_lt hy m
    (rows_sourced_family D.hrun hfg hs5 hsrc hy)
    (fun _ h => compatible_of_anc_right_family hU hBP h) hBt with h | h
  · exact Or.inl (h.trans ((SA.anc_getAnchor hΦ
      (liveBlocks_chain_at_family D.hrun hli hy m t)).2 _ (Or.inr rfl)))
  · exact Or.inr h

/-- Fast lock compatibility needs only count/provenance exits, not handler equations. -/
theorem fastLock_compatible_at_family (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) {D : OutageLockPremises F tr H proposer dg sg}
    {n : Nat} (hvi : OutageVoteInv D n) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt (F.proj tr.projAC) y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H → ∃ j < n, ∃ e,
      SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v) :
    Compatible (tr.HonestBlocks H) B D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hcount, hCV⟩ := hf.counted y hy c s B CV hfl
  by_cases hs : s < D.j₀
  · have hj₀ := D.hj₀.1
    have hsj := Compose.ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rcases hfl with ⟨ℓ, C, hu, hC, hD, -⟩ | hO
    · have htt : tr.time c = sp.ts s + 6 * sp.Δ := by
        simpa only [F.time, RunTrace.projAC] using hu.2.2.1
      obtain ⟨hΦ, hΦU⟩ := D.hrun.observation.frameIn hy hu.1
      have hBC : ℓ.frame.Anc B C := (SA.deepest_mem hD).1.1.2.2
      have hCU := hΦU (SA.deepest_mem hC).1.1
      exact compatible_of_anc_family hU (hBC.mono hΦU)
        (D.compatible_of_within ⟨y, hy, c, _, by linarith, Or.inl ⟨ℓ, hu, hC, rfl⟩⟩ hCU)
    · obtain ⟨ℓ, A, hpt, hslot, hsel, -⟩ := id hO
      have hslot' : sp.slot (tr.time c) = s := by
        simpa only [F.time, RunTrace.projAC] using hslot
      have hlt : tr.time c < sp.ts (s + 1 : Nat) := by
        by_contra h
        have hh := (SA.ts_le_iff_le_slot sp (D.hrun.time_nonneg c) ((s + 1 : Nat) : Int)).1
          (not_lt.mp h)
        rw [hslot'] at hh
        omega
      obtain ⟨hΦ, hΦU⟩ := D.hrun.observation.frameIn hy hpt.1
      have hBt : B ∈ ℓ.frame.tree := by
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (SA.deepest_mem hsel).1.1
      exact D.compatible_of_within ⟨y, hy, c, CV, by linarith, Or.inr hO⟩ (hΦU hBt)
  refine by_contra fun hB => ?_
  have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ Hᶜ ∪ D.W := by
    rintro u ⟨v, hv, rfl⟩
    by_contra hu
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
    obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
    obtain ⟨j', hj', e, hve, rfl⟩ := hcut v hv hu.1
    exact hB (compatible_of_voteCompat_family hU hRU hRr hBR
      (hvi.voteCompat_of_not_lateWaker ht hu.1 hu.2 hj' hve (by omega)))
  have hh := Set.ncard_le_ncard hsub
  have hh' := D.two_mul_lt
  omega

theorem fastLock_compatible_family (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) {D : OutageLockPremises F tr H proposer dg sg}
    (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt (F.proj tr.projAC) y c s B CV) : Compatible (tr.HonestBlocks H) B D.P :=
  fastLock_compatible_at_family hf ht (hinv (c + 1)).toOutageVoteInv hy hfl fun _ hv hvH =>
    let ⟨j, hj, e, he, hm⟩ := hf.honest y hy c s B CV hfl _ hv hvH
    ⟨j, Nat.lt_succ_of_le hj, e, he, hm⟩

/-- S2/S3's backward-release consequence, including receipt-before-cast provenance.
It is an exit statement, not an equation with the Goldilocks message handler. -/
def ReadPointOrigin (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ i ℓ e, SA.CastAt (F.proj tr.projAC) y i ℓ e →
    0 < sp.slot (tr.time i) → ∀ l' ∈ e.readPoint.locks,
    ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ ((F.proj tr.projAC).state y i).locks, ∃ B ∈ ℓ.frame.tree,
          B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
        ∃ B CV, SA.OptimisticLockAt (F.proj tr.projAC) y i (sp.slot (tr.time i)) B CV ∧
          (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e',
            SA.VoteAt (F.proj tr.projAC) v.val j e' ∧ e'.msg = v) ∧ ℓ.frame.Anc B' B)

theorem readPointOrigin_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    ReadPointOrigin (SA.goldilocksFamily sp _ ro) tr H := by
  intro y hy i ℓ e hc hp
  exact SA.readPoint_locks_provenance_strict
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc) hy hc hp

theorem readPoint_liveLockBlocks_compatible_at_family (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) (hp : ReadPointOrigin F tr H)
    {D : OutageLockPremises F tr H proposer dg sg} {i : Nat} (hinv : OutageLockInv D i)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt (F.proj tr.projAC) y i ℓ e) (hpos : 0 < sp.slot (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  intro L hL
  have hU := D.coherent
  obtain ⟨hΦ, hΦU⟩ := D.hrun.observation.frameIn hy hc.1
  obtain ⟨l', hl', B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨B', hB', hB'r, h⟩ := hp y hy i ℓ e hc hpos l' hl'
  obtain rfl : B₀ = B' := hΦ.coherent.1 hB₀ hB' (hB₀r.trans hB'r.symm)
  refine compatible_of_anc_right_family hU hBP
    (compatible_of_anc_family hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) ?_)
  rcases h with ⟨l, hl, B₁, hB₁, hB₁r, hanc⟩ | ⟨B₁, CV, hfl, hcut, hanc⟩
  · obtain ⟨L', hL', hL'r, hcomp⟩ := hinv.locks y hy i le_rfl l hl
    obtain rfl : B₁ = L' := hU.1 (hΦU hB₁) ⟨y, hy, i, hL'⟩ (hB₁r.trans hL'r.symm)
    exact compatible_of_anc_family hU (hanc.mono hΦU) hcomp
  · exact compatible_of_anc_family hU (hanc.mono hΦU)
      (fastLock_compatible_at_family hf ht hinv.toOutageVoteInv hy (Or.inr hfl) hcut)

end Consensus.Goldilocks.FamilySafety

end
