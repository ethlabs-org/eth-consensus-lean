module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.ContestLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep

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

/-- **The AC lock keep lemma at an honest node of a run.** A lock `l` that an honest node `y`
holds before cut `i` is held after it when, at the frame `fg_to_ac(Σ)` of `y` before cut `i` (the
frame of an AC call at cut `i`) and the time of cut `i`: `l` does not expire, its block `B` is
its own viable ancestor, and `unlock` does not move it (`SA.mem_step_locks_of_keep`). A cut that
is not an AC call keeps `𝒜`. -/
theorem lock_keep_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hk : sp.slot (tr.time i) ≤ l.slot + sp.k)
    (hB : B ∈ (Node.frame (tr.state y i)).tree) (hBr : B.root = l.block)
    (hva : (Node.frame (tr.state y i)).viableAncestor B = B)
    (hu : (sp.slot (tr.time i) : Int) - 1 ≤ l.slot ∨ ∀ V, SA.unlockTarget sp
      (Node.frame (tr.state y i)) V ((sp.slot (tr.time i) : Int) - 1) B = B) :
    l ∈ (tr.state y (i + 1)).ac.locks := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    rw [tr.state_succ_of_call hc]
    cases c with
    | ac ℓ =>
      obtain ⟨hfr, hstep, -, -⟩ := hlaw
      rw [hfr] at hstep
      have := SA.mem_step_locks_of_keep (ro := ro) y ℓ.call (frameOK_state hrun.toLocalRun hy i)
        (hrun.time_nonneg i) hl hk hB hBr hva hu
      rw [hstep] at this
      exact this
    | fg ℓ =>
      cases ℓ with
      | block C acc =>
        cases acc with
        | true => rw [hlaw.2.2.1]; exact hl
        | false => rw [hlaw.2]; exact hl
      | attestation a => rw [hlaw.2.1]; exact hl
      | attest C s =>
        cases s with
        | none => rw [hlaw.2]; exact hl
        | some a => rw [hlaw.2.2]; exact hl
  · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
    exact hl

end Consensus.Goldilocks.Compose

end
