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
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.VoterWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.ProposalTick

public section

/-! # Goldilocks under `Sleepy`: the honest slot-`s` votes are the honest proposal

Over the Sleepy invariant: for the
honest proposal `P` of slot `s` by a joined proposer, every honest slot-`s` vote is `P`
(`honest_votes_eq_proposal_before`). The proposal walk (`ac_proposal`: the full viable tree, the
slot-`(s−1)` pool view `pay`, from the unlocked anchor) ends at `Q = P.parent`, and each voter's
walk (the viable voter block tree, the merged view, from its unlocked anchor) is compared with it:

* `proposal_data` (proved): the run's proposal of `P` is `ac_proposal`'s, at `t_s`, on the duty
  head `Q`, with payload `pay`;
* `pivot_before` (`Service/Pivot`): a block `D` on the proposal walk such that every
  honest slot-`s` voter's walk passes a block of the path from `D` through `Q` to `P` (a voter
  whose anchor is a current-slot optimistic lock starts on that path above `D`);
* `suffix_agree_before` (proved, `Service/Suffix`): at every block from `D` below `Q` at or
  above the voter's anchor, the proposer's best child is the voter's best child;
* `stop_at_parent_before`: at `Q` the voter's only eligible child is `P` (its slot is the
  current one; another slot-`s` block would be the honest proposer's second; no old child is
  eligible), and the voter's walk stops at `P` (`P ∈` the voter's viable
  voter block tree, `proposal_at_voter_before` in `Service/Suffix`).

The assembly (`honest_votes_eq_proposal_before`) joins them by the walk comparison
`voter_walk_eq_proposal` (`Service/VoterWalk`). The honest
slot-`s` batch then reaches the joined updater of slot `s`, resolved before `t_s + 2Δ`
(`honest_batch_at_update_before` in `Service/Batch`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- **The run's proposal of `P` is `ac_proposal`'s** at `t_s`: on the duty head `Q = P.parent`,
with the payload `pay`. An own block is processed inside a tick (position `≠ 0`), so it is the
proposal step's (`blockCall_cases`), made by `Node.proposeBlock` from `ac_proposal`'s duty head and
payload at the cut after the tick's `ac_on_tick`. -/
theorem proposal_data {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, rfl, hg, hPr, d, pay, hr, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  exact proposal_data_of_tick hg hPr hr hB (by rw [htk, sp.slotTime_eq, hPs]; rfl)
    (hrun.cutLaw p hp j) (projAC_state h hp (j + 1))

/-- **The stop at `P.parent`**: at `Q` a voter's only eligible child is `P` (of
the current slot; another block of slot `s` would be a second block of the honest proposer, and
an old child is ineligible), and its walk has no best child at `P` (no
block of the frame is of a later slot): `SA.stop_core` from the two leaves. -/
theorem stop_at_parent_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hstock : sp.committeeSize = sp.n) :
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
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hU := hrun'.localRun.coherent
  have hΦU := (SA.frameIn_of_callAt hrun'.localRun hy hcy.1).2
  have hng : ∀ B ∈ ℓy.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hg
    rw [honest_eq_genesis hrun hU (hΦU hB) hg] at hpar
    exact hpar (by simp [Params.genesisBlock])
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨D, -, hDQ, hviab, -⟩ := pivot_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj
    hc hcall hd hti hPQ hib hstock
  exact SA.stop_core hrun' hy hcy hes hPs hPQ (by rw [hP.2.1]; exact hp) hng
    (proposal_at_voter_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hc hcall hd hti hPQ
      hy hcy hes hib hjb hstock)
    (fun B hB hBQ hBs => old_child_ineligible_before hrun hnc hp hP hPs hc hcall hd hti hPQ
      hDQ hviab hy hcy hes hsync.ac hib hjb hf
      (proposal_walk_passes_old_before hrun hnc hb0 hsync hfb hinv hp hc hcall hd hti hib hstock)
      hB hBQ hBs hstock)


/-- **Every honest slot-`s` vote is the honest proposal `P` of slot `s`**, by
induction on the vote's cut (the first vote not `P`; `pivot_before` reads the earlier ones): each
voter's walk reaches a block `X` of the path from `D` to `P`; from `X` it is at `P`, or it
follows the proposal walk to `Q` and steps to `P`, where it stops (`ghost_follow`); with its full
fuel it has stopped (`ghost_stopped`), so it ends at `P`. -/
theorem honest_votes_eq_proposal_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time}
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) (hsb : sp.ts s ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → tr.time j ≤ b →
      e.msg.head = P.root := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨i, ℓp, d, pay, hc, hcall, hd, hti, hPQ, -⟩ := proposal_data hrun hp hP hPs
  have hib : tr.time i ≤ b := hti ▸ hsb
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := pivot_before hrun hnc hb0 hsync hfb hinv
    hp hP hPs hpj hc hcall hd hti hPQ hib hstock
  suffices main : ∀ j, (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
      e'.msg.slot = s → e'.msg.head = P.root) →
      ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y j e → e.msg.slot = s → tr.time j ≤ b →
        e.msg.head = P.root by
    intro x hx j
    induction j using Nat.strong_induction_on generalizing x with
    | _ j ih =>
      intro e hv hs hjb
      exact main j (fun x' hx' j' hj' e' hv' hs' =>
        ih j' hj' x' hx' e' hv' hs' ((hrun.time_mono hj'.le).trans hjb)) x hx e hv hs hjb
  intro j hIH y hy e ⟨ℓy, hcy, hey⟩ hes hjb
  have hcast : SA.CastAt tr.projAC y j ℓy e := ⟨hcy, hey⟩
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    have := (SA.slot_arithmetic sp s).1 0 (by omega)
    simpa using this
  -- the voter's walk passes a block `X` of the path from `D` through `Q` to `P`
  obtain ⟨hstep₀, hP₀⟩ := stop_at_parent_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj
    hc hcall hd hti hPQ hy hcast hes hib hjb hstock
  have hsuf :=
    suffix_agree_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hc hcall hd hti hPQ
      hsD hDQ hviab hy hcast hes hib hjb hstock
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy
  obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j ℓy e hcast hjb hes hIH
  -- the voter block tree has a viable block: `P` itself (`stop_at_parent_before`)
  have hne : (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)).Nonempty :=
    ⟨P, hstep₀.1.1⟩
  rw [SA.viableTree_voteDomain_eq_of_viable hne] at hXend
  have hspec := SA.castAt_head_of_viable hr hy hcast (hes ▸ hne)
  rw [hes] at hspec
  rw [hspec]
  congr 1
  -- from `X`, the voter's walk follows the proposal walk to `Q`, steps to `P` and stops
  exact voter_walk_eq_proposal hd hsl_i hΦp hΦpU hΦy hΦyU hsD hDQ (fun B hB => hB.1.1) hXc haX
    hXend hstep₀ hP₀ hsuf

end Consensus.Goldilocks.Compose

end
