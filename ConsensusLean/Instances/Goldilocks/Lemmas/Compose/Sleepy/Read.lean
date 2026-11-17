module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the ready read is the effective record

A node-local fact of the Sleepy invariant up to a horizon `b`:

* **The ready read is the effective record** (`ready_read_record_before`): at a read point `(j, t)`
  of an honest node ready at `t` (awake on `[t − 18Δ − 1, t]`, hence joined at `t`, F.4), the
  confirmed read `ac_confirmed` at `t` is the record's block when the frame holds it, and `Σ.F`
  otherwise. When the frame holds the record's block `R`, the head at `t` extends `R`
  (`read_head_support_before`, the served head of `Served` read at `t` instead of at a cut's own
  time, then `SA.anc_acHead`), so the deepest common ancestor of `R` and the head is `R`
  (`SA.acConfirmed_eq`); otherwise the lookup fails and it is `Σ.F` (`SA.acConfirmed_eq_F`).

It is for read points at times `≤ b` and cuts within `b`, from `SleepyInvariantUpTo`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The ready read up to `b` is the effective record.** Under the prefix premises up to `b`, at
a read point `(j, t)` with `t ≤ b` of an honest node `y` ready at `t`: when the frame holds the
block `R` named by the record, `readAfter y j t = R`; otherwise it is `Σ.F`. -/
theorem ready_read_record_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    (hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → tr.FaultBound H (sp.ts s + sp.Δ))
    {y : Fin sp.n} {j : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr j t) (_hb : Regimes.Boundary tr y j)
    (hready : Regimes.ReadyAt tr H (Regimes.catchUp sp) y t) (htb : t ≤ b) :
    (∃ R ∈ (Node.frame (tr.state y j)).tree,
        R.root = (tr.state y j).ac.latestConfirmed ∧ Regimes.readAfter tr y j t = R) ∨
      ((¬ ∃ R ∈ (Node.frame (tr.state y j)).tree,
          R.root = (tr.state y j).ac.latestConfirmed) ∧
        Regimes.readAfter tr y j t = (tr.state y j).fg.F) := by
  have hy : y ∈ H := hready.1
  have hΦ : FrameOK (Node.frame (tr.state y j)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy j)).1
  by_cases hin : ∃ R ∈ (Node.frame (tr.state y j)).tree,
      R.root = (tr.state y j).ac.latestConfirmed
  · obtain ⟨R, hR, hRr⟩ := hin
    have hwj : 0 ≤ t → tr.awake y t ∧ tr.JoinedAt y t := fun ht0 =>
      ready_implies_joined sp ro dg H tr proposer hrun y hy t (Regimes.catchUp sp) ht0
        (by simp only [Regimes.catchUp]; linarith [sp.toParams.hΔ]) hready.2
    obtain ⟨hc, hs⟩ := read_head_support_before hinv hrun hnc hsync hy htb
      (fun s hs => hfb s (hs.trans htb)) hrp.1 hrp.2 hwj ⟨hR, hRr⟩
    exact Or.inl ⟨R, hR, hRr, SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)⟩
  · exact Or.inr ⟨hin, SA.acConfirmed_eq_F hΦ fun ⟨R, hR, hr⟩ => hin ⟨R, hR, hr⟩⟩

end Consensus.Goldilocks.Compose

end
