module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.ContestLocksRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents

public section

/-! # Goldilocks: a lock kept over an interval of cuts

`lock_keep_interval`: the interval induction of `lock_keep_run` (consensus-lean#135, WI-15/16).
If an honest node `y` holds a lock `l` on `B` at cut `i`, and at every cut `j ∈ [i, k)` the
premises of `lock_keep_run` hold (no expiry, `B` in the frame's tree and its own viable ancestor,
`unlock` does not move it), then `y` holds `l` at cut `k`.

`viableAncestor_eq_self_run` discharges the viable-ancestor premise by one of three of the
contest-lock lemmas (contest; no contest with `hmax = hj + 1`; `hmax ≠ hj + 1`), and
`lock_keep_interval_cases` is the interval induction with that disjunction per cut.
`viableAncestor_of_F_advance_run` reads an earlier store and is not in the disjunction. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A lock kept over `[i, k]`.** -/
theorem lock_keep_interval (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i k : Nat} (hik : i ≤ k) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).viableAncestor B = B ∧
      ((sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨ ∀ V, SA.unlockTarget sp
        (Node.frame (tr.state y j)) V ((sp.slot (tr.time j) : Int) - 1) B = B)) :
    l ∈ (tr.state y k).ac.locks := by
  induction k, hik using Nat.le_induction with
  | base => exact hl
  | succ k hik ih =>
    obtain ⟨hk, hB, hva, hu⟩ := hstep k hik (Nat.lt_succ_self k)
    exact lock_keep_run hrun hy k (ih fun j h1 h2 => hstep j h1 (by omega)) hk hB hBr hva hu

/-- `B` is its own viable ancestor at the frame of an honest node `y` at cut `i` by one of
`viableAncestor_of_contest_run`, `viableAncestor_of_not_contest_run` and
`viableAncestor_of_hmax_ne_run`. -/
theorem viableAncestor_eq_self_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (hcases :
      ((tr.state y i).fg.Contest ∧ ∃ Y ∈ (tr.state y i).fg.tree,
        (tr.state y i).fg.Anc (tr.state y i).fg.F Y ∧
        (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ Y.root).h ∧
        (tr.state y i).fg.toFrame.Anc B Y) ∨
      ((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧ ¬ (tr.state y i).fg.Contest ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.F (tr.state y i).fg.J ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J B ∧ ∃ Y ∈ (tr.state y i).fg.tree,
        (tr.state y i).fg.Anc (tr.state y i).fg.J Y ∧ (tr.state y i).fg.IsViable Y ∧
        (tr.state y i).fg.toFrame.Anc B Y) ∨
      ((tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 ∧
        ∃ Y ∈ (tr.state y i).fg.toFrame.viableHeads, (tr.state y i).fg.toFrame.Anc B Y)) :
    (tr.state y i).fg.toFrame.viableAncestor B = B := by
  rcases hcases with ⟨hc, Y, hY, hFY, hh, hBY⟩ | ⟨hm, hc, hFJ, hJB, Y, hY, hJY, hv, hBY⟩ |
      ⟨hm, Y, hW, hBY⟩
  · exact viableAncestor_of_contest_run hrun hy i hc hB hY hFY hh hBY
  · exact viableAncestor_of_not_contest_run hrun hy i hm hc hFJ hB hJB hY hJY hv hBY
  · exact viableAncestor_of_hmax_ne_run hrun hy i hm hB hW hBY

/-- `lock_keep_interval` with the viable-ancestor premise at each cut given by the case
disjunction of `viableAncestor_eq_self_run`. -/
theorem lock_keep_interval_cases (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i k : Nat} (hik : i ≤ k) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (tr.state y j).fg.toFrame.tree ∧
      (((tr.state y j).fg.Contest ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.F Y ∧
        (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ Y.root).h ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.J ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.J B ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.J Y ∧ (tr.state y j).fg.IsViable Y ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 ∧
        ∃ Y ∈ (tr.state y j).fg.toFrame.viableHeads, (tr.state y j).fg.toFrame.Anc B Y)) ∧
      ((sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨ ∀ V, SA.unlockTarget sp
        (Node.frame (tr.state y j)) V ((sp.slot (tr.time j) : Int) - 1) B = B)) :
    l ∈ (tr.state y k).ac.locks :=
  lock_keep_interval hrun hy hik hl hBr fun j h1 h2 => by
    obtain ⟨hk, hB, hc, hu⟩ := hstep j h1 h2
    exact ⟨hk, hB, viableAncestor_eq_self_run hrun hy j hB hc, hu⟩

/-! ## With the view that `unlock` reads

`lock_keep_run_view`, `lock_keep_interval_view` and `lock_keep_interval_cases_view`: the lemmas
above with the unlock premise at the view of the AC call made at the cut
(`SA.unlockView`, `SA.mem_step_locks_of_keep_view`) instead of every view. -/

/-- `lock_keep_run` with the unlock premise at the view `SA.unlockView` of the AC call at cut
`i`. -/
theorem lock_keep_run_view (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hk : sp.slot (tr.time i) ≤ l.slot + sp.k)
    (hB : B ∈ (Node.frame (tr.state y i)).tree) (hBr : B.root = l.block)
    (hva : (Node.frame (tr.state y i)).viableAncestor B = B)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ l.slot ∨
      SA.unlockTarget sp (Node.frame (tr.state y i))
        (SA.unlockView (ro := ro) (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B = B) :
    l ∈ (tr.state y (i + 1)).ac.locks := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    rw [tr.state_succ_of_call hc]
    cases c with
    | ac ℓ =>
      obtain ⟨hfr, hstep, -, -⟩ := hlaw
      rw [hfr] at hstep
      have := SA.mem_step_locks_of_keep_view (ro := ro) y ℓ.call
        (frameOK_state hrun.toLocalRun hy i) (hrun.time_nonneg i) hl hk hB hBr hva (hu ℓ hc)
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

/-- `lock_keep_interval` with the unlock premise at the view of the AC call at each cut. -/
theorem lock_keep_interval_view (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i k : Nat} (hik : i ≤ k) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).viableAncestor B = B ∧
      ∀ ℓ, tr.CallAt y j (.ac ℓ) → (sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨
        SA.unlockTarget sp (Node.frame (tr.state y j))
          (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j)
            ℓ.call) ((sp.slot (tr.time j) : Int) - 1) B = B) :
    l ∈ (tr.state y k).ac.locks := by
  induction k, hik using Nat.le_induction with
  | base => exact hl
  | succ k hik ih =>
    obtain ⟨hk, hB, hva, hu⟩ := hstep k hik (Nat.lt_succ_self k)
    exact lock_keep_run_view hrun hy k (ih fun j h1 h2 => hstep j h1 (by omega)) hk hB hBr hva
      hu

/-- `lock_keep_interval_cases` with the unlock premise at the view of the AC call at each
cut. -/
theorem lock_keep_interval_cases_view (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i k : Nat} (hik : i ≤ k) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (tr.state y j).fg.toFrame.tree ∧
      (((tr.state y j).fg.Contest ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.F Y ∧
        (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ Y.root).h ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.J ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.J B ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.J Y ∧ (tr.state y j).fg.IsViable Y ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 ∧
        ∃ Y ∈ (tr.state y j).fg.toFrame.viableHeads, (tr.state y j).fg.toFrame.Anc B Y)) ∧
      ∀ ℓ, tr.CallAt y j (.ac ℓ) → (sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨
        SA.unlockTarget sp (Node.frame (tr.state y j))
          (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j)
            ℓ.call) ((sp.slot (tr.time j) : Int) - 1) B = B) :
    l ∈ (tr.state y k).ac.locks :=
  lock_keep_interval_view hrun hy hik hl hBr fun j h1 h2 => by
    obtain ⟨hk, hB, hc, hu⟩ := hstep j h1 h2
    exact ⟨hk, hB, viableAncestor_eq_self_run hrun hy j hB hc, hu⟩

/-! ## The O-form of the unlock premise

`lock_keep_interval_cases_held`: `lock_keep_interval_cases_view` with the unlock premise at each
cut `j` stated on the votes that `y` holds (`SA.heldVotes`: the pools of `y` at `j` and at
`j + 1` and the votes and support entries of the blocks of its frame's tree at `j`). The pools at
`j` matter only for a restart at `j` (no other call removes a vote from a pool). -/

/-- **A lock kept over `[i, k]`, O-form.** If at every cut `j ∈ [i, k)` the lock does not
expire, `B` is in the tree with one of the cases of `viableAncestor_eq_self_run`, and either the
lock's slot is at least `slot(t_j) − 1` or the opponents of `B` against the slot-
`(slot(t_j) − 1)` votes among the votes held by `y` across the cut lie in a set `O` with
`2 · |O| < n`, then `y` holds `l` at cut `k`. -/
theorem lock_keep_interval_cases_held (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i k : Nat} (hik : i ≤ k) {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block) {O : Set (Fin sp.n)}
    (hOn : 2 * O.ncard < sp.n)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (tr.state y j).fg.toFrame.tree ∧
      (((tr.state y j).fg.Contest ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.F Y ∧
        (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ Y.root).h ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.J ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.J B ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.J Y ∧ (tr.state y j).fg.IsViable Y ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 ∧
        ∃ Y ∈ (tr.state y j).fg.toFrame.viableHeads, (tr.state y j).fg.toFrame.Anc B Y)) ∧
      ((sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨
        SA.opponents sp (Node.frame (tr.state y j))
          ⟨SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)),
            SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j))⟩
          ((sp.slot (tr.time j) : Int) - 1) B ⊆ O)) :
    l ∈ (tr.state y k).ac.locks :=
  lock_keep_interval_cases_view hrun hy hik hl hBr fun j h1 h2 => by
    obtain ⟨hk, hB, hc, hu⟩ := hstep j h1 h2
    refine ⟨hk, hB, hc, fun ℓ hcall => hu.imp_right fun hO => ?_⟩
    obtain ⟨hfr, hst, -, -⟩ := hrun.cutLaw y hy j _ hcall
    rw [hfr] at hst
    have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
        (Node.frame (tr.state y j)) (tr.time j) ℓ.call).1 = (tr.state y (j + 1)).ac := by
      rw [tr.state_succ_of_call hcall, hst]
    exact SA.unlockTarget_unlockView_held y ℓ.call hA' (frameOK_state hrun.toLocalRun hy j) _
      hB hO hOn

end Consensus.Goldilocks.Compose

end
