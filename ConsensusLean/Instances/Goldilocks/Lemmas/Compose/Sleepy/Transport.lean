module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: what an origin carries to the next voters

workbench#11 §2.3 (transport) and S3's non-root case: for an origin `C` of label `s` and an honest
slot-`(s+1)` vote whose `Σ.F` is at or below `C`, the counted votes and heads reach the voter in
time (`SA.CarryAt`), and, for a result, every slot-`s` vote of the voter's merged view reaches the
writer (A1.8 (d)). Under `Sync[0, ∞)`: each counted vote was admitted by the writer (so forwarded)
and each counted head accepted by it (so relayed) before `t_s + 2Δ`; the voter is joined at its
vote, so awake since `t_s` with its pool kept, and processes them before `t_s + 3Δ`; the relay
applies since the voter's `Σ.F` is below `C`, below each head. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **A result's counted votes reach the next voters** (`Carry_y`), when the voter's `Σ.F` is at
or below the result. -/
theorem result_carry (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  sorry

/-- **An optimistic selection's counted votes reach the next voters** (`Carry_y`), when the
voter's `Σ.F` is at or below the selection. -/
theorem optimistic_carry (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC x i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  sorry

/-- **A1.8 (d) under `Sync`**: every slot-`s` vote of an honest slot-`(s+1)` voter's merged view is
in the pool of an honest writer of a slot-`s` result, or that pool holds two votes of its
validator. -/
theorem result_writer_pool (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
  sorry

end Consensus.Goldilocks.Compose

end
