module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks: the frame regime keeps a covered block (N1)

consensus-lean#135, plan N1 (fm-forward §3, step 3): the premise `FrameKeeps` of the lock keep
lemmas from the paper premises P1 (`fcRoot ⪯ B₀`) and P2 (the node holds `Y ⪰ B₀` at state height
at least the head height floor). `Y` is then a viable head (`Store.viableHead_of_cover`), and
the case split on `h_max = h_j + 1` and `Contest` gives the disjunct of `FrameKeeps`
(`frameKeeps_of_cover`). The R0 case `B₀ ⪯ fcRoot` is not a disjunct of `FrameKeeps`;
`viableAncestor_eq_self_of_keeps_or_root` adds it beside `viableAncestor_eq_self_run`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- **A cover block is a viable head.** An accepted `Y ⪰ B` with `B` in the frame's tree above
the fork-choice root and state height at least the head height floor is a viable head. -/
theorem viableHead_of_cover (st : Store P ACP) {B Y : NodeBlock P ACP} (hB : B ∈ st.toFrame.tree)
    (hY : Y ∈ st.tree) (hroot : st.Anc st.fcRoot B) (hBY : st.Anc B Y)
    (hh : st.headHeightFloor ≤ (st.σ Y.root).h) : Y ∈ st.toFrame.viableHeads :=
  ⟨hY, Relation.ReflTransGen.trans hB.2 hBY, Relation.ReflTransGen.trans hroot hBY, hh⟩

/-- **The frame-regime cases from a cover (fm-forward §3, step 3, store form).** With
`Σ.F ⪯ Σ.J`, a block `B` of the frame's tree with `fcRoot ⪯ B` (P1) and an accepted `Y ⪰ B` at
state height at least the head height floor (P2) satisfies one of the three cases of
`FrameKeeps`. -/
theorem frameKeeps_of_cover (st : Store P ACP) (hFJ : st.Anc st.F st.J)
    {B Y : NodeBlock P ACP} (hB : B ∈ st.toFrame.tree) (hY : Y ∈ st.tree)
    (hroot : st.Anc st.fcRoot B) (hBY : st.Anc B Y)
    (hh : st.headHeightFloor ≤ (st.σ Y.root).h) :
    (st.Contest ∧ ∃ Y ∈ st.tree, st.Anc st.F Y ∧ st.hmax ≤ (st.σ Y.root).h ∧
      st.toFrame.Anc B Y) ∨
    (st.hmax = st.hj + 1 ∧ ¬ st.Contest ∧ st.Anc st.F st.J ∧ st.Anc st.J B ∧
      ∃ Y ∈ st.tree, st.Anc st.J Y ∧ st.IsViable Y ∧ st.toFrame.Anc B Y) ∨
    (st.hmax ≠ st.hj + 1 ∧ ∃ Y ∈ st.toFrame.viableHeads, st.toFrame.Anc B Y) := by
  have hFBY : st.toFrame.Anc B Y := by
    change Goldilocks.Anc {X | X ∈ st.tree ∧ st.Anc st.F X} B Y
    exact Anc.restrict hB.2 hBY
  have hW := st.viableHead_of_cover hB hY hroot hBY hh
  by_cases hm : st.hmax = st.hj + 1
  · by_cases hc : st.Contest
    · refine Or.inl ⟨hc, Y, hY, hW.2.1, ?_, hFBY⟩
      rw [← st.headHeightFloor_of_contest hc]
      exact hh
    · rw [st.fcRoot_of_not_contest hm hc] at hroot
      exact Or.inr (Or.inl ⟨hm, hc, hFJ, hroot, Y, hY,
        Relation.ReflTransGen.trans hroot hBY, hh, hFBY⟩)
  · exact Or.inr (Or.inr ⟨hm, Y, hW, hFBY⟩)

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **`FrameKeeps` from a cover (N1, fm-forward §3, step 3).** At an honest node `x` and cut
`j`: a block `B₀` of the frame's tree with `fcRoot ⪯ B₀` (P1) and an accepted `Y ⪰ B₀` at state
height at least the head height floor (P2) give `FrameKeeps tr x j B₀`. `Σ.F ⪯ Σ.J` is the cache
invariant of the reachable store. -/
theorem frameKeeps_of_cover (hrun : GoldilocksRun proposer dg H tr) {x : Fin sp.n} (hx : x ∈ H)
    (j : Nat) {B₀ Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree) (hY : Y ∈ (tr.state x j).fg.tree)
    (hroot : (tr.state x j).fg.Anc (tr.state x j).fg.fcRoot B₀)
    (hBY : (tr.state x j).fg.Anc B₀ Y)
    (hh : (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ Y.root).h) :
    FrameKeeps tr x j B₀ :=
  Store.frameKeeps_of_cover _
    (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hx j)).2.2.1 hB hY hroot hBY hh

/-- `FrameKeeps` or the R0 case `B ⪯ fcRoot` in the frame: the premise of the lock keep lemmas
that need only `viableAncestor B = B` (`viableAncestor_eq_self_of_keeps_or_root`). -/
abbrev FrameKeepsOrRoot (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (j : Nat)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  FrameKeeps tr y j B ∨ (tr.state y j).fg.toFrame.Anc B (tr.state y j).fg.toFrame.fcRoot

/-- **`B` is its own viable ancestor, with the R0 case.** `viableAncestor_eq_self_run` with the
case `B ⪯ fcRoot` (`SA.viableAncestor_self`, right disjunct) added beside `FrameKeeps`. -/
theorem viableAncestor_eq_self_of_keeps_or_root (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (h : FrameKeepsOrRoot tr y i B) :
    (tr.state y i).fg.toFrame.viableAncestor B = B := by
  rcases h with h | h
  · exact viableAncestor_eq_self_run hrun hy i hB h
  · exact SA.viableAncestor_self (frameOK_state hrun.toLocalRun hy i) hB (Or.inr h)

end Consensus.Goldilocks.Compose

end
