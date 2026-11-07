module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.ServedRead
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head

public section

/-! # Goldilocks under `Sleepy` with growing faults: confirmed reads and the effective record

The read facts of `Compose/Sleepy/Chain` and `Compose/Sleepy/Read` for a reader honest at the read
time `t`: the state of `y` before cut `i`, every earlier cut at a time `≤ t ≤ b`, `y ∈ H t`.

* `confirmed_read_on_chain_at`: a confirmed read is held while honest and is on the chain of the
  origins within `b` (an ancestor of the effective record, which is the record's block or `Σ.F`);
* `SleepyInvariantUpTo.read_compatible_at`: two such reads are compatible;
* `SleepyInvariantUpTo.effective_record_mono_at`: the effective record only extends;
* `ready_read_record_at`: the ready read is the effective record. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The FG state of a reader honest at `t ≥ 0`, before a cut whose earlier cuts are at or before
`t`, is reachable. -/
theorem fg_reachable_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i : Nat}
    {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    Store.Reachable (goldilocksNode sp ro).genesisPayload (tr.state y i).fg := by
  have h := fg_reachable (hrun.upTo ht0).toLocalRun hy i
  rwa [Trace.upTo_state tr y hi] at h

/-- The tree of such a reader is held while honest. -/
theorem tree_subset_at {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hX => ⟨y, i, t, ht0, hi, hy, hX⟩

/-- **A confirmed read is on the origin chain**: the confirmed output of a reader honest at `t`
(every earlier cut at or before `t ≤ b`), at any time `u`, is held while honest and on the chain of
the origins within `b`. -/
theorem confirmed_read_on_chain_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (u : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u ∈
        tr.HonestBlocksAt H ∧
      OnOriginChainWithin tr H
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u) b := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable_at hrun ht0 hi hy)).1
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => tree_subset_at ht0 hi hy hX.1
  have hanc : ∀ {A B}, A ∈ tr.HonestBlocksAt H → Anc (tr.HonestBlocksAt H) A B →
      OnOriginChainWithin tr H B b → OnOriginChainWithin tr H A b :=
    fun hA hAB h => OnOriginChainWithin.of_anc hrun hnc hA hAB h
  have hF := (hinv.caches y i t ht0 hi htb hy).1
  -- the effective record is on the chain
  have hCr : (SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F ∈ (Node.frame (tr.state y i)).tree ∧
      OnOriginChainWithin tr H ((SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (Node.frame (tr.state y i)).F) b := by
    rcases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
      _ | R
    · exact ⟨hΦ.rooted.1, hF⟩
    · obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
      obtain ⟨C, hC, hCr, hgo⟩ := hinv.record y i t ht0 hi htb hy
      obtain rfl : R = C :=
        hU.1 (hsub hR) (tree_subset_at ht0 hi hy hC) (hRr.trans hCr.symm)
      exact ⟨hR, onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨R, s, hs, .refl⟩)⟩
  -- the confirmed output is an ancestor of it in the frame
  have hX : ∀ X, X = (SA.deepest (Node.frame (tr.state y i))
      {X | X ∈ (Node.frame (tr.state y i)).tree ∧
        (Node.frame (tr.state y i)).Anc X ((SA.lookup (Node.frame (tr.state y i))
          (tr.state y i).ac.latestConfirmed).getD (Node.frame (tr.state y i)).F) ∧
        (Node.frame (tr.state y i)).Anc X (SA.acHead sp (tr.state y i).ac
          (Node.frame (tr.state y i)) u)}).getD (Node.frame (tr.state y i)).F →
      X ∈ (Node.frame (tr.state y i)).tree ∧ (Node.frame (tr.state y i)).Anc X
        ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
          (Node.frame (tr.state y i)).F) := by
    rintro X rfl
    rcases hd : SA.deepest (Node.frame (tr.state y i)) _ with _ | D
    · exact ⟨hΦ.rooted.1, hΦ.rooted.2 _ hCr.1⟩
    · obtain ⟨⟨hDt, hDC, -⟩, -⟩ := SA.deepest_mem hd
      exact ⟨hDt, hDC⟩
  replace hX := hX _ rfl
  exact ⟨hsub hX.1, hanc (hsub hX.1) (hX.2.mono hsub) hCr.2⟩

/-- **Confirmed reads are compatible**: the confirmed outputs of two readers, each honest at its
read time within `b` (every earlier cut at or before it), at any times, are compatible inside the
blocks held while honest. -/
theorem SleepyInvariantUpTo.read_compatible_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y y' : Fin sp.n}
    {i i' : Nat} {t t' : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (ht0' : 0 ≤ t') (hi' : ∀ k < i', tr.time k ≤ t') (htb' : t' ≤ b)
    (hy' : y' ∈ H t') (u u' : Time) :
    Compatible (tr.HonestBlocksAt H)
      ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u)
      ((goldilocksNode sp ro).confirmed (tr.state y' i').ac (Node.frame (tr.state y' i')) u') :=
  have ⟨hB, hc⟩ := confirmed_read_on_chain_at hinv hrun hnc ht0 hi htb hy u
  have ⟨hB', hc'⟩ := confirmed_read_on_chain_at hinv hrun hnc ht0' hi' htb' hy' u'
  OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

/-- The effective record of a reader honest at `t` is the later of the record's block `C` and
`Σ.F`. -/
private theorem effective_record_spec_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    {m : Nat} {t : Time} (ht0 : 0 ≤ t) (hm : ∀ k < m, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) :
    ∃ C ∈ tr.HonestBlocksAt H, C.root = (tr.state y m).ac.latestConfirmed ∧
      (((SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed).getD
          (Node.frame (tr.state y m)).F = C ∧ Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F C) ∨
        ((SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed).getD
          (Node.frame (tr.state y m)).F = (tr.state y m).fg.F ∧
          Anc (tr.HonestBlocksAt H) C (tr.state y m).fg.F)) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hR := fg_reachable_at hrun ht0 hm hy
  have hΦ : FrameOK (Node.frame (tr.state y m)) := (Store.frame_realization _ _ _ _ hR).1
  have hts := tree_subset_at ht0 hm hy
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocksAt H := fun X hX => hts hX.1
  obtain ⟨C, hC, hCr, hgo⟩ := hinv.record y m t ht0 hm htb hy
  have hCU : C ∈ tr.HonestBlocksAt H := hts hC
  refine ⟨C, hCU, hCr, ?_⟩
  rcases hl : SA.lookup (Node.frame (tr.state y m)) (tr.state y m).ac.latestConfirmed with _ | X
  · refine Or.inr ⟨rfl, ?_⟩
    have hFt : (tr.state y m).fg.F ∈ (tr.state y m).fg.tree := hΦ.rooted.1.1
    have hCc : OnOriginChainWithin tr H C b :=
      onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)
    refine (OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hCU (hts hFt)
      hCc (hinv.caches y m t ht0 hm htb hy).1).resolve_right fun h =>
        SA.lookup_eq_none hl ⟨C, ⟨hC, ?_⟩, hCr⟩
    obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree sp.toParams (Payload sp.n) _ _ hR
    have hΦg : FrameOK (⟨(tr.state y m).fg.tree, _, _, ∅⟩ :
        Frame sp.n (List (FG.Att sp.n)) (Payload sp.n)) :=
      { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
        F_anc_fcRoot := Relation.ReflTransGen.refl, viableHeads_subset := Set.empty_subset _
        fcRoot_anc_viableHeads := fun _ h => h.elim }
    exact SA.anc_tree_of_anc_U hU hΦg hts hFt h hC
  · obtain ⟨hX, hXr⟩ := SA.lookup_eq_some hl
    obtain rfl : X = C := hU.1 (hΦU hX) hCU (hXr.trans hCr.symm)
    exact Or.inl ⟨rfl, (hΦ.rooted.2 X hX).mono hΦU⟩

/-- **The effective record only extends**: for a reader honest at `t' ≤ b` with every cut before
`j` at or before `t'`, the effective record (the record's block if the frame holds it, else `Σ.F`)
before `j` extends the one before `i ≤ j`, inside the blocks held while honest. -/
theorem SleepyInvariantUpTo.effective_record_mono_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    {i j : Nat} {t' : Time} (hij : i ≤ j) (ht0 : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t')
    (ht'b : t' ≤ b) (hy : y ∈ H t') :
    Anc (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F)
      ((SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (Node.frame (tr.state y j)).F) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hsub := upTo_subset hrun ht0
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ m _ ih =>
    have hm : ∀ k ≤ m, tr.time k ≤ t' := fun k hk => hj k (by omega)
    refine (ih fun k hk => hm k hk.le).trans ?_
    obtain ⟨C, hCU, hCr, hC⟩ :=
      effective_record_spec_at hinv hrun hnc ht0 (fun k hk => hm k hk.le) ht'b hy
    obtain ⟨C', hC'U, hC'r, hC'⟩ := effective_record_spec_at hinv hrun hnc ht0 hj ht'b hy
    have hym : y ∈ H (tr.time m) := hrun.antitone (hm m le_rfl) hy
    obtain ⟨E, hE, hEr, hCE⟩ := record_step_at hinv hrun hnc hym
      (fun k hk => (hm k hk).trans ht'b) C hCU hCr
    obtain rfl : E = C' := hU.1 hE hC'U (hEr.trans hC'r.symm)
    have hF : Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F (tr.state y (m + 1)).fg.F := by
      have h := (fg_grows (hrun.upTo ht0) hy (Nat.le_succ m)).2
      rw [Trace.upTo_state tr y (fun k hk => hm k hk.le), Trace.upTo_state tr y hj] at h
      exact h.mono hsub
    rcases hC with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
      rcases hC' with ⟨he', hFC⟩ | ⟨he', hCF⟩ <;> rw [he']
    · exact hCE
    · exact hCE.trans hCF
    · exact hF.trans hFC
    · exact hF

/-- A node ready at `t ≥ 0` (catch-up `18Δ`, honest at `t`) is awake and joined at `t` (the static
`ready_implies_joined` on the prefix through `t`). -/
theorem ready_awake_joined_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {t : Time} (ht0 : 0 ≤ t) (hready : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  obtain ⟨hw, hj⟩ := ready_implies_joined sp ro dg (H t) (tr.upTo t) proposer (hrun.upTo ht0) y
    hready.1 t (Regimes.catchUp sp) ht0 (by simp only [Regimes.catchUp]; linarith [sp.toParams.hΔ])
    (fun u h1 h2 => ⟨hready.2 u h1 h2, h2⟩)
  exact ⟨hw.1, fun k hk hkt => hj k ((RunTrace.upTo_restartAt tr).mpr ⟨hkt, hk⟩) hkt⟩

/-- **The ready read is the effective record.** At a read point `(j, t)` with `0 ≤ t ≤ b` of a
node ready at `t` (honest at `t`): when the frame holds the block `R` named by the record,
`readAfter y j t = R`; otherwise it is `Σ.F`. The latest-view count is charged at `t`. -/
theorem ready_read_record_at {ΔF b : Time} (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b) {y : Fin sp.n} {j : Nat}
    {t : Time} (hrp : Regimes.ReadPoint tr j t) (ht0 : 0 ≤ t)
    (hready : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) (htb : t ≤ b) :
    (∃ R ∈ (Node.frame (tr.state y j)).tree,
        R.root = (tr.state y j).ac.latestConfirmed ∧ Regimes.readAfter tr y j t = R) ∨
      ((¬ ∃ R ∈ (Node.frame (tr.state y j)).tree,
          R.root = (tr.state y j).ac.latestConfirmed) ∧
        Regimes.readAfter tr y j t = (tr.state y j).fg.F) := by
  have hy : y ∈ H t := hready.1
  have hΦ : FrameOK (Node.frame (tr.state y j)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable_at hrun ht0 hrp.1 hy)).1
  by_cases hin : ∃ R ∈ (Node.frame (tr.state y j)).tree,
      R.root = (tr.state y j).ac.latestConfirmed
  · obtain ⟨R, hR, hRr⟩ := hin
    obtain ⟨hc, hs⟩ := read_head_support_at hinv hrun hnc hsync hy ht0 htb
      (fun s h1 h2 => hB.slot s t h1 htb h2.le) hrp.1 hrp.2 (ready_awake_joined_at hrun ht0 hready)
      ⟨hR, hRr⟩
    exact Or.inl ⟨R, hR, hRr, SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)⟩
  · exact Or.inr ⟨hin, SA.acConfirmed_eq_F hΦ fun ⟨R, hR, hr⟩ => hin ⟨R, hR, hr⟩⟩

end Consensus.Goldilocks.Compose.Growing

end
