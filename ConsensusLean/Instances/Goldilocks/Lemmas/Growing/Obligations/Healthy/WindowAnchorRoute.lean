module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorRoute
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalReplay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality

public section

/-! # The anchor route to window coverage, under growing faults

The growing form of the trace part of `Obligations/WindowAnchorRoute`; the store-level lemmas
(`Store.coverage_of_anchor_window` and its helpers) are reused unchanged.

* `anchor_window_advance_at`: three anchor steps give `σ[P₀].h + 3 ≤ σ[P₃].h` at every store
  holding the four anchors of a node honest at an observation time after the store's cuts;
* `cacheCoverage_of_anchor_window_upTo_at`: for such a holder of `P₃`, with the four anchors
  below `P₃` in the honest blocks, the block `F` of root `σ[P₃].F` is held and `P₀ ⪯ F` in the
  honest blocks;
* `reader_cache_covers_at`: a reader honest at a read time at or after that holder's cut has
  `P₀` below its finalized cache, once it accepts `P₃` before its read whenever its cache is below
  `P₃`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- **The anchor window advance** under growing faults. Three anchor steps `P i → P (i+1)` give
`σ[P₀].h + 3 ≤ σ[P₃].h` at every store holding the four anchors of a node honest at an
observation time `t` after the store's cuts. -/
private theorem anchor_window_advance_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {P : Fin 4 → AC.Blk sp.n (List (FG.Att sp.n))}
    (hmem : ∀ i, P i ∈ (tr.state y k).fg.tree)
    (hstep : ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ)) :
    ((tr.state y k).fg.σ (P 0).root).h + 3 ≤ ((tr.state y k).fg.σ (P 3).root).h := by
  have key : ∀ i : Fin 3, ((tr.state y k).fg.σ (P i.castSucc).root).h + 1 ≤
      ((tr.state y k).fg.σ (P i.succ).root).h := by
    intro i
    obtain ⟨z, j, j', hz, hz', hA, hX, hl⟩ := anchorStepAt_iff.mp (hstep i)
    rw [Healing.Growing.σ_eq_honest_at hrun hnc ht hle hy (hrun.time_nonneg j)
        (fun _ hq => hrun.time_mono hq.le) hz (hmem _) hA,
      Healing.Growing.σ_eq_honest_at hrun hnc ht hle hy (hrun.time_nonneg j')
        (fun _ hq => hrun.time_mono hq.le) hz' (hmem _) hX]
    exact hl
  have h0 : ((tr.state y k).fg.σ (P 0).root).h + 1 ≤ ((tr.state y k).fg.σ (P 1).root).h :=
    key 0
  have h1 : ((tr.state y k).fg.σ (P 1).root).h + 1 ≤ ((tr.state y k).fg.σ (P 2).root).h :=
    key 1
  have h2 : ((tr.state y k).fg.σ (P 2).root).h + 1 ≤ ((tr.state y k).fg.σ (P 3).root).h :=
    key 2
  omega

/-- **Window coverage from an anchor window** under growing faults. Four anchors `P i` below
`P 3` in the honest blocks, three anchor steps, and `(P 3).slot ≤ (P 0).slot + δt`. For a holder
`y` of `P 3` at cut `k`, honest at an observation time `t` after its earlier cuts, the block `F` of
root `σ[P₃].F` is held by `y` and `P₀ ⪯ F` in the honest blocks. -/
theorem cacheCoverage_of_anchor_window_upTo_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {P : Fin 4 → AC.Blk sp.n (List (FG.Att sp.n))}
    (hch : ∀ i, Anc (tr.HonestBlocksAt H) (P i) (P 3))
    (hstep : ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ))
    (hsl : (P 3).slot ≤ (P 0).slot + sp.toParams.fg.δt) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hB₃ : P 3 ∈ (tr.state y k).fg.tree) :
    ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocksAt H) (P 0) F := by
  have hmem : ∀ i, P i ∈ (tr.state y k).fg.tree := fun i =>
    Healing.Growing.mem_of_honest_anc_at hrun hnc ht hle hy (hch i) hB₃
  obtain ⟨F, hF, hAF⟩ := Store.coverage_of_anchor_window
    (Healing.Growing.fg_reachable_at hrun ht hle hy) hB₃
    (Healing.Growing.store_anc_of_honest_anc_at hrun hnc ht hle hy (hch 0) hB₃)
    (anchor_window_advance_at hrun hnc ht hle hy hmem hstep) hsl
  exact ⟨F, hF, Healing.Growing.honest_anc_of_store_anc_at ht hle hy hAF⟩

/-- **The reader's finalized cache covers a held window anchor** under growing faults. A holder
`x` of `B` at cut `c + 1`, honest at `time c`, caches the block `X` of root `σ[B].F` with
`A ⪯ X`. A reader `y` read at `j` and honest at `t ≥ time c`, with every cut before `j` at a time
`≤ t` and fewer than `2q − n` faults at `t`, has `A` below its finalized cache. Finalized safety,
charged at `t`, puts `X` below the reader's cache or the cache below `X ⪯ B`. In the second case
the reader accepts `B` before `j` (`hacc`), caches `X` there, and its cache grows on the run up to
`j`. -/
theorem reader_cache_covers_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {c : Nat}
    {A B X : AC.Blk sp.n (List (FG.Att sp.n))} (hx : x ∈ H (tr.time c))
    (hBx : B ∈ (tr.state x (c + 1)).fg.tree)
    (hX : (tr.state x (c + 1)).fg.blocks ((tr.state x (c + 1)).fg.σ B.root).F = some X)
    (hAX : Anc (tr.HonestBlocksAt H) A X) {y : Fin sp.n} {j : Nat} {t : Time}
    (hct : tr.time c ≤ t) (hle : ∀ q < j, tr.time q ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hacc : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B) :
    Anc (tr.HonestBlocksAt H) A (tr.state y j).fg.F := by
  have fg := Compose.Growing.fg_projection _ _ _ _ _ _ _
    (fun z => Compose.requirements_from _ (hrun.vstart z)) hrun.genesis_root_ok
    hrun.toLocalRun hnc
  have hstore : ∀ {z : Fin sp.n} {i : Nat} {u : Time}, 0 ≤ u → (∀ q < i, tr.time q ≤ u) →
      z ∈ H u → tr.projFG.store z i = (tr.state z i).fg := fun {_ i _} hu hl hz => by
    have h := Compose.projFG_state (hrun.toLocalRun.upTo hu) hz i
    rw [RunTrace.upTo_projFG, Trace.upTo_state tr.projFG _ hl, Trace.upTo_state tr _ hl] at h
    exact congrArg Prod.fst h
  have hmono := hrun.time_mono
  have hc0 := hrun.time_nonneg c
  have hlc : ∀ q < c + 1, tr.time q ≤ tr.time c := fun q hq => hmono (by omega)
  have ht0 : 0 ≤ t := hc0.trans hct
  -- the holder's covering block, below `B` in its store
  have hRx := Healing.Growing.fg_reachable_at hrun hc0 hlc hx
  have hXR := hRx.blocks_root hX
  have hXt : X ∈ (tr.state x (c + 1)).fg.tree := by
    change (tr.state x (c + 1)).fg.blocks X.root = some X
    rwa [hXR]
  have hancx : (tr.state x (c + 1)).fg.Anc X B := by
    obtain ⟨_, ⟨X', hX', hX'r, hanc⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hRx _ hBx
    have he : X' = X := (Store.accepted_tree _ _ _ _ hRx).2.1.1 hX' hXt (hX'r.trans hXR.symm)
    subst X'
    exact hanc
  have hXB : Anc (tr.HonestBlocksAt H) X B :=
    Healing.Growing.honest_anc_of_store_anc_at hc0 hlc hx hancx
  have hsx := hstore hc0 hlc hx
  -- finalized safety between the holder and the reader, charged at the read time
  have hf' : (H (max (tr.time c) t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    rw [max_eq_right hct]; exact hf
  have hsafe := fg.replay_finalized_safety_upTo_at hc0 hlc hx ht0 hle hy hf'
    (B := B) (X := X) (by rw [hsx]; exact hBx) (by rw [hsx]; exact hXt)
    (by rw [hsx]; exact hXR)
  rw [hstore ht0 hle hy] at hsafe
  rcases hsafe with hXF | hFX
  · exact hAX.trans hXF
  -- the reader's cache is below `X`: it accepts `B` before its read
  obtain ⟨k, hkj, hacc'⟩ := hacc (hFX.trans hXB)
  have hlk : ∀ q < k + 1, tr.time q ≤ t := fun q hq => hle q (by omega)
  have hlk' : ∀ q < k, tr.time q ≤ t := fun q hq => hle q (by omega)
  have hsk1 := hstore ht0 hlk hy
  have hsk := hstore ht0 hlk' hy
  -- the reader's acceptance, on the prefix through its read
  have fgt := fg.upTo ht0
  have hpre1 := Trace.upTo_state tr.projFG y hlk
  have hpre := Trace.upTo_state tr.projFG y hlk'
  have hac : FGTrace.AcceptAt (tr.projFG.upTo t) y k B :=
    (Trace.upTo_callAt tr.projFG).mpr ⟨hle k hkj, Compose.projFG_callAt.mpr hacc'⟩
  have hpostB : B ∈ (FGTrace.store (tr.projFG.upTo t) y (k + 1)).tree := by
    have h := Store.accept_onBlock fgt hy hac
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fgt hy k)).1 _ _ h]
    exact Set.mem_insert _ _
  have hpostB' : B ∈ (tr.projFG.store y (k + 1)).tree := by
    simpa only [FGTrace.store, hpre1] using hpostB
  have hBx' : B ∈ (tr.projFG.store x (c + 1)).tree := by rw [hsx]; exact hBx
  have hσ := Store.Growing.σ_eq_of_held fg hc0 ht0 hx hy hlc hlk hBx' hpostB'
  have hancy := Store.Growing.anc_transfer fg hc0 ht0 hx hy hlc hlk
    (show (tr.projFG.store x (c + 1)).Anc X B by rw [hsx]; exact hancx) hpostB'
  have hpostX : X ∈ (tr.projFG.store y (k + 1)).tree := by
    by_cases he : X = B
    · exact he ▸ hpostB'
    · exact (Anc.mem hancy he).1
  have hXr' : X.root = ((tr.projFG.store y (k + 1)).σ B.root).F := by
    rw [← hσ, hsx]; exact hXR
  -- the reader's cache before the acceptance is below `X`
  have hrt := hrun.upTo ht0
  have hgrow : ∀ {k₁ k₂}, k₁ ≤ k₂ → k₂ ≤ j →
      Anc (tr.HonestBlocksAt H) (tr.state y k₁).fg.F (tr.state y k₂).fg.F := by
    intro k₁ k₂ h12 h2
    have h := (Compose.fg_grows hrt hy h12).2
    have hl₂ : ∀ q < k₂, tr.time q ≤ t := fun q hq => hle q (by omega)
    have hl₁ : ∀ q < k₁, tr.time q ≤ t := fun q hq => hle q (by omega)
    rw [Trace.upTo_state tr y hl₁, Trace.upTo_state tr y hl₂] at h
    exact h.mono (RunTrace.honestBlocks_upTo_subset hmono ht0)
  have hFX' : Anc (tr.HonestBlocksAt H) (FGTrace.store (tr.projFG.upTo t) y k).F X := by
    rw [show FGTrace.store (tr.projFG.upTo t) y k = tr.projFG.store y k by
      simp only [FGTrace.store, hpre], hsk]
    exact (hgrow hkj.le le_rfl).trans hFX
  have hcache := Healing.accepted_replay_finalized_cached fgt hf hy hac
    (by simpa only [FGTrace.store, hpre1] using hpostX)
    (by simpa only [FGTrace.store, hpre1] using hXr') hFX'
  rw [show FGTrace.store (tr.projFG.upTo t) y (k + 1) = tr.projFG.store y (k + 1) by
    simp only [FGTrace.store, hpre1], hsk1] at hcache
  exact hAX.trans (hcache.trans (hgrow hkj le_rfl))

end Consensus.Goldilocks.Obligations.Growing

end
