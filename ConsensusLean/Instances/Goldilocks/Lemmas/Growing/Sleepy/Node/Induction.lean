module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VotesBelow
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance

public section

/-! # Goldilocks under `Sleepy` with growing faults: the record invariant up to `b`

The bounded frontier under growing faults: `P_0` and `V_0` hold vacuously;
`P_s, V_s ⊢ P_{s+1}` (`origins_below_succ_at`) and `P_{s+1}, V_s ⊢ V_{s+1}`
(`votes_below_succ_at`), so every finite frontier holds (`frontier_at`). With the provenance of
records, caches, locks and sources, and full viability at the read time, this is
`SleepyInvariantUpTo` (`sleepy_invariant_at`). Every quantifier of the induction ranges over events
of nodes honest at them, so a later compromise removes nothing from it.

The `_stub` declarations are stand-ins, with the exact statements, for the provenance results
(`record_origin_at`, `caches_on_chain_at`, `source_on_chain_at`) and the origin step
(`origins_below_succ_at`) of the dynamic node layer's other files. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### Stand-ins -/

/-- Stand-in: the record of a reader honest at `t` names genesis or an origin within `b`. -/
theorem record_origin_at_stub (_hrun : Growing.GoldilocksRun proposer dg H tr)
    (_hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t b : Time} (_ht0 : 0 ≤ t)
    (_hi : ∀ k < i, tr.time k ≤ t) (_htb : t ≤ b) (_hy : y ∈ H t) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b) := by
  sorry

/-- Stand-in: an FG source of a node honest at its cut is on the chain of the origins within
`b`. -/
theorem source_on_chain_at_stub (_hrun : Growing.GoldilocksRun proposer dg H tr)
    (_hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {b : Time} (_hy : y ∈ H (tr.time i))
    (_hi : ∀ k < i, tr.time k ≤ b) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (_h : SA.ToFGAt tr.projAC y i ℓ C) :
    OnOriginChainWithin tr H C b := by
  sorry

/-- Stand-in: the caches of a reader honest at `t` are on the chain of the origins within `b`. -/
theorem caches_on_chain_at_stub (_hrun : Growing.GoldilocksRun proposer dg H tr)
    (_hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t b : Time} (_ht0 : 0 ≤ t)
    (_hi : ∀ k < i, tr.time k ≤ t) (_htb : t ≤ b) (_hy : y ∈ H t)
    (_hf : 2 * (H t)ᶜ.ncard < sp.n) :
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b := by
  sorry

/-- Stand-in: `P_s` and `V_s` up to `b` give `P_{s+1}` up to `b`. -/
theorem origins_below_succ_at_stub (_hrun : Growing.GoldilocksRun proposer dg H tr)
    (_hnc : NoCollRun dg tr) {b : Time} (_hb : 0 ≤ b) (_hsync : SleepyServiceBefore tr H ΔF b)
    (_hB : SleepyBounds tr H b) {s : Nat} (_hP : OriginsBelowUpTo tr H s b)
    (_hV : VotesBelowUpTo tr H s b) : OriginsBelowUpTo tr H (s + 1) b := by
  sorry

/-! ### The frontier and the invariant -/

/-- **Every finite frontier up to `b`** under growing faults. -/
theorem frontier_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b) :
    ∀ s, OriginsBelowUpTo tr H s b ∧ VotesBelowUpTo tr H s b := by
  intro s
  induction s with
  | zero =>
    exact ⟨originsBelowUpTo_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowUpTo_iff.2 fun _ _ _ _ _ _ _ _ h₁ h₂ => by omega⟩
  | succ s ih =>
    have hP := origins_below_succ_at_stub hrun hnc hb hsync hB ih.1 ih.2
    exact ⟨hP, votes_below_succ_at hrun hnc hb hsync hB hP ih.2⟩

/-- **S3 at a held origin, read at `t`**: a reader honest at `t ∈ [0, b]` (every earlier cut at or
before `t`), holding a block compatible with every origin before the cut, when the origins within
`t` are pairwise compatible (`held_origin_viable_before` on the prefix through `t`). -/
private theorem held_origin_viable_read (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hP : ∀ C s C' s', OriginWithin tr H C s t → OriginWithin tr H C' s' t →
      Compatible (tr.HonestBlocksAt H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocksAt H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hst := Trace.upTo_state tr y (d := t) hi
  have hBU : B ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hst]; exact hBt.1⟩
  have h := held_origin_viable_before (hrun.upTo ht0) (hnc.upTo _) (b := t) hf
    (fun _ => Compose.originsBelowUpTo_iff.2 fun C j C' j' _ _ hC hC' =>
      compatible_upTo hrun hnc ht0 (originWithin_upTo_mem hrun hnc ht0 hC)
        (originWithin_upTo_mem hrun hnc ht0 hC')
        (hP C j C' j' (originWithin_of_upTo hrun hC) (originWithin_of_upTo hrun hC')))
    hy i hi
    (fun C s hC => by
      have hCw := hC.within (b := t) hi
      exact compatible_upTo hrun hnc ht0 hBU (originWithin_upTo_mem hrun hnc ht0 hCw)
        (hBc C s (originBefore_of_upTo hrun hC)))
    (by rw [hst]; exact hBt)
  rwa [hst] at h

/-- **The Sleepy record invariant up to `b` under growing faults** (S1–S3), from the finite
service and the count shapes through `b`. -/
theorem sleepy_invariant_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) : SleepyInvariantUpTo tr H b := by
  have hF := frontier_at hrun hnc hb hsync hB
  have hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocksAt H) C C' := fun C s C' s' h h' =>
    originsBelowUpTo_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  refine ⟨hcomp, fun C s hC y i e he hib hs => ?_,
    fun y i t ht0 hi htb hy => record_origin_at_stub hrun hnc ht0 hi htb hy,
    fun y i t ht0 hi htb hy => caches_on_chain_at_stub hrun hnc ht0 hi htb hy (hB.two t ht0 htb),
    fun y i t ht0 hi htb hy l hl => ?_,
    fun y i hy hi ℓ C h => source_on_chain_at_stub hrun hnc hy hi h,
    fun y i t ht0 hi htb hy C s hC hCt => held_origin_viable_read hrun hnc ht0 hi hy
      (hB.two t ht0 htb) (fun C₁ s₁ C₂ s₂ h₁ h₂ => hcomp C₁ s₁ C₂ s₂ (h₁.mono htb) (h₂.mono htb))
      (fun C' s' hC' => hcomp C s C' s' hC (hC'.within fun k hk => (hi k hk).trans htb)) hCt⟩
  · exact votesBelowUpTo_iff.1 (hF e.msg.slot).2 C s hC y i e he hib hs le_rfl
  · -- `lock_origin` on the prefix through `t`, for the validators honest at `t`
    have hst := Trace.upTo_state tr y (d := t) hi
    obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin (hrun.upTo ht0) (hnc.upTo _) hy i l
      (by rw [hst]; exact hl)
    rw [hst] at hL
    exact ⟨L, hL, hLr, onOriginChainWithin_iff.2 (Or.inr ⟨C, l.slot,
      (originBefore_of_upTo hrun hC).within fun k hk => (hi k hk).trans htb,
      hLC.mono (upTo_subset hrun ht0)⟩)⟩

end Consensus.Goldilocks.Compose.Growing

end
