module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks under `Sleepy`: the honest slot-`s` votes are the honest proposal

workbench#12 (`sleepy-proposal-adoption.md`, f42c0ad) §2–§3, over the Sleepy invariant: for the
honest proposal `P` of slot `s` by a joined proposer, every honest slot-`s` vote is `P`
(`honest_votes_eq_proposal`). The proposal walk (`ac_proposal`: the full viable tree, the
slot-`(s−1)` pool view `pay`, from the unlocked anchor) ends at `Q = P.parent`, and each voter's
walk (the viable voter block tree, the merged view, from its unlocked anchor) is compared with it:

* `proposal_data` (open): the run's proposal of `P` is `ac_proposal`'s, at `t_s`, on the duty
  head `Q`, with payload `pay`;
* `pivot` (open, §2.1, §2.2): a block `D` that the proposal walk passes and that every honest
  slot-`s` voter's walk passes (the deepest of genesis, the regular origins of labels at most
  `s − 2` and the optimistic origins of labels at most `s − 1`; the voters pass it by S2, the
  proposer by the honest batch; the voters' current-slot optimistic locks by the first vote not
  `P`);
* `suffix_agree` (open, §3): from `D` to `Q`, the proposer's winner is eligible for the voter (an
  ancestor of `P`, in the frozen domain) with at least its proposer score, and every other
  eligible child of the voter is the proposer's with at most its proposer score (a sandwich:
  competitor scores can differ between the frames);
* `stop_at_parent` (open, §3): at `Q` the voter's only eligible child is `P` (its slot is the
  current one; no old child is eligible), and the voter's walk stops at `P`.

The assembly (`honest_votes_eq_proposal`) joins them with the walk lemmas of `Steps/Walk`
(`ghost_visits`, `ghost_add`, `ghost_follow`, `ghost_stopped`, `ghost_fuel_stable`). The honest
slot-`s` batch then reaches the joined updater of slot `s`, resolved before `t_s + 2Δ` (§4,
`honest_batch_at_update` in `Service/Batch`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The duty head of a proposal is the walk of the full viable tree from its start, with the
payload's view of the previous slot's votes. -/
private theorem acProposal_head {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    d.head = SA.ghost sp (Φ.viableTree Φ.tree)
      (SA.goldfishScore sp Φ (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
      (SA.goldfishEligible sp Φ t (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
      Φ.tree.ncard d.start := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- **The run's proposal of `P` is `ac_proposal`'s** at `t_s`: on the duty head `Q = P.parent`,
with the payload `pay` (open: the tick's proposal step, `Node.proposeBlock`). -/
theorem proposal_data {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s)
    (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  sorry

/-- **The pivot** (workbench#12 §2.1, §2.2; open): a block `D` of the proposal walk, between its
start and `Q`, that every honest slot-`s` voter's walk passes. -/
theorem pivot {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
        ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∧
        ℓy.frame.Anc D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
          (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  sorry

/-- **The suffix** (workbench#12 §3; open): along the proposal walk from the pivot `D` to `Q`, the
proposer's best child is eligible for the voter with a score at least its proposer score (the
path's supporters are the same in both views), and every other eligible child of the voter is
eligible for the proposer with a voter score at most its proposer score. A sandwich, not equality:
competitor scores can differ between the two frames in reachable runs (A1.7 model sweep, d55d292:
543,903 differing counts, the vote still `P`). -/
theorem suffix_agree {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) :
    ∀ m < ℓp.frame.tree.ncard,
      let X := SA.ghost sp (ℓp.frame.viableTree ℓp.frame.tree)
        (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1)) m D
      X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        C ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
          B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} ∧
        SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) C ≤
          SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1) C ∧
        ∀ B ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B}, B ≠ C →
          B ∈ {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} ∧
          SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
              ((s : Int) - 1) B ≤
            SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B := by
  sorry

/-- **The stop at `P.parent`** (workbench#12 §3; open): at `Q` a voter's only eligible child is
`P`, and its walk has no best child at `P`. -/
theorem stop_at_parent {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    (P ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} ∧
      ∀ B ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
          B.parent = some d.head.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
        ((s : Int) - 1))
      {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  sorry

/-- **Every honest slot-`s` vote is the honest proposal `P` of slot `s`** (workbench#12 §2–§3):
each voter's walk reaches the pivot, then follows the proposal walk to `Q` and steps to `P`, where
it stops (`ghost_follow`); with its full fuel it has stopped (`ghost_stopped`), so it ends at
`P`. -/
theorem honest_votes_eq_proposal {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨i, ℓp, d, pay, hc, hcall, hd, hti, hPQ, -⟩ := proposal_data hrun hnc hp hP hPs hpj
  obtain ⟨D, hsD, hDQ, hvot⟩ := pivot hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
  intro y hy j e ⟨ℓy, hcy, hey⟩ hes
  have hcast : SA.CastAt tr.projAC y j ℓy e := ⟨hcy, hey⟩
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    have := (SA.slot_arithmetic sp s).1 0 (by omega)
    simpa using this
  -- the proposal walk: from its start, through `D`, to `Q`, where it stops
  have hΦp := (SA.frameIn_of_callAt hr hp hc).1
  set W₁ := SA.ghost sp (ℓp.frame.viableTree ℓp.frame.tree)
    (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1)) with hW₁
  have hTp : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have hQ : d.head = W₁ ℓp.frame.tree.ncard d.start := by
    rw [acProposal_head hd, hsl_i]
  have hstop₀ := SA.ghost_stopped hΦp.coherent hTp (hΦp.finite.subset hTp)
    (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
    (Set.ncard_le_ncard hTp hΦp.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  obtain ⟨kp, -, hkp⟩ := SA.ghost_visits hΦp.coherent hTp _ hsD (hQ ▸ hDQ)
  rw [← hW₁] at hkp
  have h₁ : W₁ ℓp.frame.tree.ncard D = d.head := by
    have hadd := SA.ghost_add (T := ℓp.frame.viableTree ℓp.frame.tree)
      (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      (el := SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
      kp ℓp.frame.tree.ncard d.start
    rw [← hW₁, hkp] at hadd
    rw [← hadd, hQ]
    exact SA.ghost_fuel_stable (by omega) hstop₀
  -- the voter's walk: from its anchor to `D`, then to `P`, where it stops
  obtain ⟨hstep₀, hP₀⟩ := stop_at_parent hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcast hes
  have hfollow := SA.ghost_follow _ D h₁ hstop₁
    (suffix_agree hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hy hcast hes) hstep₀ hP₀
  have hΦy := (SA.frameIn_of_callAt hr hy hcy).1
  obtain ⟨haD, hDend⟩ := hvot y hy j ℓy e hcast hes
  have hspec := (SA.castAt_spec hr hy hcast).2.2.2
  rw [hes] at hspec
  rw [hspec]
  congr 1
  set W₂ := SA.ghost sp (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓy.frame (tr.time j) (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1)) with hW₂
  have hTy : ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ⊆ ℓy.frame.tree :=
    fun B hB => hB.1.1
  change W₂ ℓy.frame.tree.ncard (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P
  obtain ⟨ky, -, hky⟩ := SA.ghost_visits hΦy.coherent hTy _ haD hDend
  have hP₂ : W₂ (ky + (ℓp.frame.tree.ncard + 1))
      (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P := by
    rw [hW₂, SA.ghost_add, ← hW₂]
    rw [← hW₂] at hky
    rw [hky]; exact hfollow
  have hstop₂ := SA.ghost_stopped hΦy.coherent hTy (hΦy.finite.subset hTy)
    (sc := SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (Set.ncard_le_ncard hTy hΦy.finite) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
  rw [← hW₂] at hstop₂
  have hmax₁ := SA.ghost_fuel_stable (le_max_left (ℓy.frame.tree.ncard)
    (ky + (ℓp.frame.tree.ncard + 1))) hstop₂
  have hmax₂ := SA.ghost_fuel_stable (le_max_right (ℓy.frame.tree.ncard)
    (ky + (ℓp.frame.tree.ncard + 1))) (hP₂ ▸ hP₀)
  rw [← hW₂] at hmax₁ hmax₂
  rw [← hmax₁, hmax₂, hP₂]

end Consensus.Goldilocks.Compose

end
