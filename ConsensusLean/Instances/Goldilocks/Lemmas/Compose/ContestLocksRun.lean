module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.ContestLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Goldilocks: the contest-lock lemmas at an honest node of a run

The four `Store.viableAncestor_of_*` lemmas (`Compose.ContestLocks`) with the premise
`FrameOK st.toFrame` discharged by `frameOK_state`: the store of an honest node at every cut of a
run has a well-formed frame. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- `Store.viableAncestor_of_contest` at the store of an honest node `y` at cut `i`. -/
theorem viableAncestor_of_contest_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hc : (tr.state y i).fg.Contest)
    {B Y : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (hY : Y ∈ (tr.state y i).fg.tree) (hFY : (tr.state y i).fg.Anc (tr.state y i).fg.F Y)
    (hh : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ Y.root).h)
    (hBY : (tr.state y i).fg.toFrame.Anc B Y) :
    (tr.state y i).fg.toFrame.viableAncestor B = B :=
  Store.viableAncestor_of_contest (frameOK_state hrun.toLocalRun hy i) hc hB hY hFY hh hBY

/-- `Store.viableAncestor_of_not_contest` at the store of an honest node `y` at cut `i`. -/
theorem viableAncestor_of_not_contest_run (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hm : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1) (hc : ¬ (tr.state y i).fg.Contest)
    (hFJ : (tr.state y i).fg.Anc (tr.state y i).fg.F (tr.state y i).fg.J)
    {B Y : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (hJB : (tr.state y i).fg.Anc (tr.state y i).fg.J B) (hY : Y ∈ (tr.state y i).fg.tree)
    (hJY : (tr.state y i).fg.Anc (tr.state y i).fg.J Y) (hv : (tr.state y i).fg.IsViable Y)
    (hBY : (tr.state y i).fg.toFrame.Anc B Y) :
    (tr.state y i).fg.toFrame.viableAncestor B = B :=
  Store.viableAncestor_of_not_contest (frameOK_state hrun.toLocalRun hy i) hm hc hFJ hB hJB hY
    hJY hv hBY

/-- `Store.viableAncestor_of_F_advance` with the new store the store of an honest node `y` at
cut `i`; the old store `st` is arbitrary. -/
theorem viableAncestor_of_F_advance_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) {st : Store sp.toParams (Payload sp.n)}
    (htree : (tr.state y i).fg.tree = st.tree) (hσ : (tr.state y i).fg.σ = st.σ)
    (hJ : (tr.state y i).fg.J = st.J) (hhj : (tr.state y i).fg.hj = st.hj)
    (hhm : (tr.state y i).fg.hmax = st.hmax) (hFJ' : st.Anc (tr.state y i).fg.F st.J)
    (hm : st.hmax = st.hj + 1) {B Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.toFrame.tree) (hJB : st.Anc st.J B) (hY : Y ∈ st.tree)
    (hJY : st.Anc st.J Y) (hv : (tr.state y i).fg.IsViable Y) (hh : st.hmax ≤ (st.σ Y.root).h)
    (hBY : (tr.state y i).fg.toFrame.Anc B Y) :
    (tr.state y i).fg.toFrame.viableAncestor B = B :=
  Store.viableAncestor_of_F_advance htree hσ hJ hhj hhm hFJ' hm
    (frameOK_state hrun.toLocalRun hy i) hB hJB hY hJY hv hh hBY

/-- `Store.viableAncestor_of_hmax_ne` at the store of an honest node `y` at cut `i`. -/
theorem viableAncestor_of_hmax_ne_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hm : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1)
    {B Y : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (hW : Y ∈ (tr.state y i).fg.toFrame.viableHeads) (hBY : (tr.state y i).fg.toFrame.Anc B Y) :
    (tr.state y i).fg.toFrame.viableAncestor B = B :=
  Store.viableAncestor_of_hmax_ne (frameOK_state hrun.toLocalRun hy i) hm hB hW hBY

end Consensus.Goldilocks.Compose

end
