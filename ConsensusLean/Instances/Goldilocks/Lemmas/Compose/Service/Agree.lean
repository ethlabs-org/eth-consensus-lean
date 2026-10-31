module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain

public section

/-! # Goldilocks under `Sleepy`: the honest slot-`s` votes are the honest proposal

workbench#12 (`sleepy-proposal-adoption.md`, f42c0ad) §2–§3, over the Sleepy invariant: for the
honest proposal `P` of slot `s` by a joined proposer, every honest slot-`s` vote is `P`
(`honest_votes_eq_proposal`). The proposal walk (`ac_proposal`: the full viable tree, the
slot-`(s−1)` pool view `pay`, from the unlocked anchor) ends at `Q = P.parent`, and each voter's
walk (the viable voter block tree, the merged view, from its unlocked anchor) is compared with it:

* `proposal_data` (proved): the run's proposal of `P` is `ac_proposal`'s, at `t_s`, on the duty
  head `Q`, with payload `pay`;
* `pivot` (open, `Service/Pivot`, §2.1, §2.2): a block `D` on the proposal walk such that every
  honest slot-`s` voter's walk passes a block of the path from `D` through `Q` to `P` (a voter
  whose anchor is a current-slot optimistic lock starts on that path above `D`);
* `suffix_agree` (proved, `Service/Suffix`, §3): at every block from `D` below `Q` at or above
  the voter's anchor, the proposer's best child is the voter's best child;
* `stop_at_parent` (§3): at `Q` the voter's only eligible child is `P` (its slot is the current
  one; another slot-`s` block would be the honest proposer's second; no old child is eligible,
  `old_children_ineligible`, proved), and the voter's walk stops at `P` (`P ∈` the voter's viable
  voter block tree, `proposal_at_voter` in `Service/Suffix`).

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
with the payload `pay`. An own block is processed inside a tick (position `≠ 0`), so it is the
proposal step's (`blockCall_cases`), made by `Node.proposeBlock` from `ac_proposal`'s duty head and
payload at the cut after the tick's `ac_on_tick`. -/
theorem proposal_data {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun dg H tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, rfl, hg, hPr, d, pay, hr, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  set t := tr.time (j + 2)
  set st := tr.state p j
  set st1 := (Node.tickStep dg p st t x .acTick).1
  have hcuts : (Node.exec dg p st t (.tick x)).2 = (Node.tickStep dg p st t x .acTick).2 ++
      (Node.tickStep dg p st1 t x .proposal).2 ++
      (Node.tickStep dg p (Node.tickStep dg p st1 t x .proposal).1 t x .fgUpdate).2 := by
    simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, st1]
  have h0 : (Node.exec dg p st t (.tick x)).2[0]? = some (Node.acCall p st t .tick).2 := by
    rw [hcuts]; simp [Node.tickStep]
  have h1 : (Node.exec dg p st t (.tick x)).2[1]? = some (Node.acProposal st1 t).2.1 := by
    rw [hcuts]
    simp only [Node.tickStep, hPr, ↓reduceIte]
    split <;> simp [Node.acProposal, Node.acCall]
  obtain ⟨hk0, hc0⟩ := List.getElem?_eq_some_iff.1 h0
  obtain ⟨hk1, hc1⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hg.2.1 0 hk0
  obtain ⟨hn1, ht1, -, -, hl1⟩ := hg.2.1 1 hk1
  rw [hc0] at hl0
  rw [hc1] at hl1
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall0 : tr.CallAt p j (Node.acCall p st t .tick).2 := ⟨hn0, hl0⟩
  have hst1 : (tr.state p (j + 1)).ac = st1.ac := by
    rw [tr.state_succ_of_call hcall0]
    obtain ⟨-, hstep, -, -⟩ := hrun.cutLaw p hp j _ hcall0
    rw [ht0] at hstep
    exact (congrArg Prod.fst hstep).symm
  have hts : t = sp.ts s := by
    rw [htk, sp.slotTime_eq, hPs]; rfl
  refine ⟨j + 1, ⟨.proposal, Node.frame st1, []⟩, d, pay, projAC_callAt.2 ⟨hn1, hl1⟩, rfl, ?_,
    ht1.trans hts, by rw [hB]; rfl, by rw [hB]; rfl⟩
  rw [projAC_state h hp, hst1, show tr.time (j + 1) = t from ht1]
  exact hr

/-- **No old child of `Q` is eligible at the voter** (workbench#12 §3: at `Q` the proposal walk
stopped, so no old child of `Q` is eligible at the proposer, and its score and the majority
denominator agree at the voter; `old_child_ineligible` in `Service/Suffix`, from `pivot`). -/
theorem old_children_ineligible {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
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
    ∀ B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s),
      B.parent = some d.head.root → B.slot < s →
      ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B := by
  intro B hB hBQ hBs
  obtain ⟨D, -, hDQ, hviab, -⟩ := pivot hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
  exact old_child_ineligible hrun hnc hsl hp hP hPs hc hcall hd hti hPQ hDQ hviab hy hcy hes hB
    hBQ hBs

/-- **The stop at `P.parent`** (workbench#12 §3): at `Q` a voter's only eligible child is `P` (of
the current slot; another block of slot `s` would be a second block of the honest proposer, and
an old child is ineligible, `old_children_ineligible`), and its walk has no best child at `P` (no
block of the frame is of a later slot): `SA.stop_core` from the two leaves. -/
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
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hU := hrun'.localRun.coherent
  have hΦU := (SA.frameIn_of_callAt hrun'.localRun hy hcy.1).2
  have hng : ∀ B ∈ ℓy.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hg
    rw [honest_eq_genesis hrun hU (hΦU hB) hg] at hpar
    exact hpar (by simp [Params.genesisBlock])
  exact SA.stop_core hrun' hy hcy hes hPs hPQ (by rw [hP.2.1]; exact hp) hng
    (proposal_at_voter hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcy hes)
    (old_children_ineligible hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcy hes)


/-- **Every honest slot-`s` vote is the honest proposal `P` of slot `s`** (workbench#12 §2–§3), by
induction on the vote's cut (the first vote not `P`; `pivot` reads the earlier ones): each voter's
walk reaches a block `X` of the path from `D` to `P`; from `X` it is at `P`, or it
follows the proposal walk to `Q` and steps to `P`, where it stops (`ghost_follow`); with its full
fuel it has stopped (`ghost_stopped`), so it ends at `P`. -/
theorem honest_votes_eq_proposal {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨i, ℓp, d, pay, hc, hcall, hd, hti, hPQ, -⟩ := proposal_data hrun hp hP hPs
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := pivot hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
  suffices main : ∀ j, (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
      e'.msg.slot = s → e'.msg.head = P.root) →
      ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y j e → e.msg.slot = s → e.msg.head = P.root by
    intro x hx j
    induction j using Nat.strong_induction_on generalizing x with
    | _ j ih => exact main j (fun x' hx' j' hj' => ih j' hj' x' hx') x hx
  intro j hIH y hy e ⟨ℓy, hcy, hey⟩ hes
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
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := by rw [hW₁]; rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m) (by rw [h0]; exact hstop₁)).trans h0
  -- the proposal walk from a block `X` of its path from `D` ends at `Q`
  have hXQend : ∀ {X}, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      W₁ ℓp.frame.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, -, hkx⟩ := SA.ghost_visits hΦp.coherent hTp _ hDX (h₁ ▸ hXQ)
    rw [← hW₁] at hkx
    rw [← hkx, ← hW₁add, add_comm, hW₁add, h₁, hstopQ]
  -- the voter's walk passes a block `X` of the path from `D` through `Q` to `P`
  obtain ⟨hstep₀, hP₀⟩ := stop_at_parent hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcast hes
  have hsuf :=
    suffix_agree hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy hcast hes
  have hΦy := (SA.frameIn_of_callAt hr hy hcy).1
  have hΦyU := (SA.frameIn_of_callAt hr hy hcy).2
  have hΦpU := (SA.frameIn_of_callAt hr hp hc).2
  obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j ℓy e hcast hes hIH
  set W₂ := SA.ghost sp (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓy.frame (tr.time j) (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1)) with hW₂
  -- from `X`, the voter's walk ends at `P`
  have hXP : ∃ fX, W₂ fX X = P := by
    rcases hXc with rfl | ⟨hDX, hXQ⟩
    · exact ⟨0, rfl⟩
    refine ⟨ℓp.frame.tree.ncard + 1, SA.ghost_follow _ X ?_ hstop₁ ?_ hstep₀ hP₀⟩
    · -- the proposal walk from `X` (on its path from `D`) ends at `Q`
      exact hXQend hDX hXQ
    · intro m hm hne
      by_cases hXQ' : X = d.head
      · exact absurd (by rw [hXQ']; exact hstopQ m) hne
      have hXt : X ∈ ℓp.frame.tree := (Anc.mem hXQ hXQ').1
      -- the position `W₁ m X` is between `D` and `Q`
      have hXm : ℓp.frame.Anc X (W₁ m X) := by rw [hW₁]; exact SA.anc_ghost hTp m hXt
      have hQm : ℓp.frame.Anc (W₁ m X) d.head := by
        have hmem : W₁ m X ∈ ℓp.frame.tree := by
          rcases eq_or_ne (W₁ m X) X with h | h
          · rw [h]; exact hXt
          · exact (Anc.mem hXm (Ne.symm h)).2
        have hend : W₁ (ℓp.frame.tree.ncard - m) (W₁ m X) = d.head := by
          rw [← hW₁add, Nat.add_sub_cancel' hm.le]
          exact hXQend hDX hXQ
        rw [← hend, hW₁]
        exact SA.anc_ghost hTp _ hmem
      exact hsuf _ (hDX.trans hXm) hQm
        ((haX.mono hΦyU).trans (hXm.mono hΦpU)) hne
  obtain ⟨fX, hfX⟩ := hXP
  have hspec := (SA.castAt_spec hr hy hcast).2.2.2
  rw [hes] at hspec
  rw [hspec]
  congr 1
  have hTy : ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ⊆ ℓy.frame.tree :=
    fun B hB => hB.1.1
  change W₂ ℓy.frame.tree.ncard (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P
  obtain ⟨ky, -, hky⟩ := SA.ghost_visits hΦy.coherent hTy _ haX hXend
  have hP₂ : W₂ (ky + fX) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) = P := by
    rw [hW₂, SA.ghost_add, ← hW₂]
    rw [← hW₂] at hky
    rw [hky]; exact hfX
  have hstop₂ := SA.ghost_stopped hΦy.coherent hTy (hΦy.finite.subset hTy)
    (sc := SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (Set.ncard_le_ncard hTy hΦy.finite) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
  rw [← hW₂] at hstop₂
  have hmax₁ := SA.ghost_fuel_stable (le_max_left (ℓy.frame.tree.ncard) (ky + fX)) hstop₂
  have hmax₂ := SA.ghost_fuel_stable (le_max_right (ℓy.frame.tree.ncard) (ky + fX)) (hP₂ ▸ hP₀)
  rw [← hW₂] at hmax₁ hmax₂
  rw [← hmax₁, hmax₂, hP₂]

end Consensus.Goldilocks.Compose

end
