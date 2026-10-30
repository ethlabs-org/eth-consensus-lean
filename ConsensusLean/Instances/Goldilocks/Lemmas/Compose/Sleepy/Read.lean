module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Reads
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks under `Sleepy`: the ready read and the effective record (R.1)

The two node-local facts R.1 (`Regimes.SleepySafe`) reads of the Sleepy invariant:

* **The ready read is the effective record** (`ready_read_record`): at a read point `(j, t)` of an
  honest node ready at `t` (awake on `[t − 18Δ − 1, t]`, hence joined at `t`, F.4), the confirmed
  read `ac_confirmed` at `t` is the record's block when the frame holds it, and `Σ.F` otherwise.
  When the frame holds the record's block `R`, the head at `t` extends `R` (`read_head_support`,
  the served head of `Served` read at `t` instead of at a cut's own time, then `SA.anc_acHead`),
  so the deepest common ancestor of `R` and the head is `R` (`SA.acConfirmed_eq`); otherwise the
  lookup fails and it is `Σ.F` (`SA.acConfirmed_eq_F`).
* **The effective record only extends** (`effective_record_mono`): the effective record (the
  record's block if the frame holds it, else `Σ.F`) is the later of the record's block and `Σ.F`,
  which are compatible (both on the origin chain), since a record's block at or above `Σ.F` is in
  the frame; both move to descendants at every cut (`record_step`, `fg_grows`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **The ready read is the effective record.** At a read point `(j, t)` between two events of an
honest node `y` ready at `t`: when the frame holds the block `R` named by the record,
`readAfter y j t = R`; otherwise it is `Σ.F`. (The proof does not use the boundary: the served
head holds at every cut, also inside an event.) -/
theorem ready_read_record (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} {j : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr j t) (_hb : Regimes.Boundary tr y j)
    (hready : Regimes.ReadyAt tr H (Regimes.catchUp sp) y t) :
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
      ready_implies_joined sp ro dg H tr hrun y hy t (Regimes.catchUp sp) ht0
        (by simp only [Regimes.catchUp]; linarith [sp.toParams.hΔ]) hready.2
    obtain ⟨hc, hs⟩ := read_head_support (sleepy_invariant hrun hnc hsl) hrun hnc hsl hy hrp.1
      hrp.2 hwj ⟨hR, hRr⟩
    exact Or.inl ⟨R, hR, hRr, SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)⟩
  · exact Or.inr ⟨hin, SA.acConfirmed_eq_F hΦ fun ⟨R, hR, hr⟩ => hin ⟨R, hR, hr⟩⟩

/-- The effective record at cut `m` is the later of the record's block `C` and `Σ.F`: it is `C`
with `Σ.F ⪯ C` (the frame holds `C`), or `Σ.F` with `C ⪯ Σ.F` (the frame does not hold `C`, which
is compatible with `Σ.F` on the origin chain and so below it). -/
private theorem effective_record_spec (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) :
    ∃ C ∈ tr.HonestBlocks H, C.root = (tr.state y m).ac.latestConfirmed ∧
      (((SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed).getD
          (Node.frame (tr.state y m)).F = C ∧ Anc (tr.HonestBlocks H) (tr.state y m).fg.F C) ∨
        ((SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed).getD
          (Node.frame (tr.state y m)).F = (tr.state y m).fg.F ∧
          Anc (tr.HonestBlocks H) C (tr.state y m).fg.F)) := by
  have hU := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
  have hΦ : FrameOK (Node.frame (tr.state y m)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy m)).1
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX.1⟩
  obtain ⟨C, hC, hCr, hgo⟩ := hinv.record y hy m
  have hCU : C ∈ tr.HonestBlocks H := ⟨y, hy, m, hC⟩
  refine ⟨C, hCU, hCr, ?_⟩
  rcases hl : SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed with _ | X
  · -- the frame does not hold `C`: then `Σ.F ⋠ C`, and `C ⪯ Σ.F` on the origin chain
    refine Or.inr ⟨rfl, ?_⟩
    have hFt : (tr.state y m).fg.F ∈ (tr.state y m).fg.tree := hΦ.rooted.1.1
    have hCc : OnOriginChain tr H C :=
      onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)
    refine (OnOriginChain.compatible hrun hnc hinv.origins_compatible hCU ⟨y, hy, m, hFt⟩ hCc
      (hinv.caches y hy m).1).resolve_right fun h => SA.lookup_eq_none hl ⟨C, ⟨hC, ?_⟩, hCr⟩
    obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree sp.toParams (Payload sp.n) _ _
      (fg_reachable hrun.toLocalRun hy m)
    have hΦg : FrameOK (⟨(tr.state y m).fg.tree, _, _, ∅⟩ :
        Frame sp.n (List (FG.Att sp.n)) (Payload sp.n)) :=
      { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
        F_anc_fcRoot := Relation.ReflTransGen.refl, viableHeads_subset := Set.empty_subset _
        fcRoot_anc_viableHeads := fun _ h => h.elim }
    exact SA.anc_tree_of_anc_U hU hΦg (fun X hX => ⟨y, hy, m, hX⟩) hFt h hC
  · obtain ⟨hX, hXr⟩ := SA.lookup_eq_some hl
    obtain rfl : X = C := hU.1 (hΦU hX) hCU (hXr.trans hCr.symm)
    exact Or.inl ⟨rfl, (hΦ.rooted.2 X hX).mono hΦU⟩

/-- **The effective record only extends**: the effective record of an honest node (the block of
its record when its frame holds it, else its `Σ.F`) at a later cut extends the one at an earlier
cut (inside the honest blocks). -/
theorem effective_record_mono (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j) :
    Anc (tr.HonestBlocks H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F)
      ((SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (Node.frame (tr.state y j)).F) := by
  have hinv := sleepy_invariant hrun hnc hsl
  have hU := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ m _ ih =>
    refine ih.trans ?_
    obtain ⟨C, hCU, hCr, hC⟩ := effective_record_spec hinv hrun hnc hy m
    obtain ⟨C', hC'U, hC'r, hC'⟩ := effective_record_spec hinv hrun hnc hy (m + 1)
    obtain ⟨E, hE, hEr, hCE⟩ := record_step hinv hrun hnc hy m C hCU hCr
    obtain rfl : E = C' := hU.1 hE hC'U (hEr.trans hC'r.symm)
    have hF := (fg_grows hrun hy (Nat.le_succ m)).2
    rcases hC with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
      rcases hC' with ⟨he', hFC⟩ | ⟨he', hCF⟩ <;> rw [he']
    · exact hCE
    · exact hCE.trans hCF
    · exact hF.trans hFC
    · exact hF

end Consensus.Goldilocks.Compose

end
