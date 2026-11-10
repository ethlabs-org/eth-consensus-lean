module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Suffix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.VoterWalk

public section

/-! # Goldilocks under `Sleepy` with growing faults: the honest slot-`s` votes are the proposal

The growing-fault form of `Compose/Service/Agree`. For the proposal `P` of slot `s` by a proposer
still honest at `t_s + Δ` (the hold), every slot-`s` vote of a node honest at its vote is `P`
(`honest_votes_eq_proposal_at`). The hold is what the stop at `P.parent` consumes: a vote is cast
by `t_s + Δ`, so the proposer is honest at the vote, and a second slot-`s` block in the voter's
frame would be a second block of a proposer honest then (`SA.stop_core` on the prefix through the
vote).

* `proposal_data_at`: the run's proposal of `P` is `ac_proposal`'s at `t_s` (the static
  `proposal_data` on the prefix through the proposal);
* `stop_at_parent_at`: at `Q = P.parent` the voter's only eligible child is `P`, and its walk has
  no best child at `P`;
* `honest_votes_eq_proposal_at`: by induction on the vote's cut, with `pivot_at` and
  `suffix_agree_at`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The run's proposal of `P` is `ac_proposal`'s** at `t_s`, on the duty head `Q = P.parent`,
with the payload `pay`, for a proposer honest at its proposal (the static `proposal_data` on the
prefix through it). -/
theorem proposal_data_at (hrun : Growing.GoldilocksRun proposer dg H tr) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (tr.time k))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  have hd := hrun.time_nonneg k
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  obtain ⟨i, ℓp, d, pay, hc, hcall, hdp, hti, hPQ, hpay⟩ :=
    Compose.proposal_data (hrun.upTo hd) hp hP' hPs
  rw [RunTrace.upTo_projAC] at hc hdp
  obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).1 hc
  rw [projAC_upTo_state hrun hid] at hdp
  exact ⟨i, ℓp, d, pay, hc, hcall, hdp, hti, hPQ, hpay⟩

/-- **The stop at `P.parent`** under growing faults, from `P` in the voter's viable voter block
tree and no old child of `Q = P.parent` eligible there: at `Q` the voter's only eligible child is
`P`, and its walk has no best child at `P`. The proposer is honest at the vote (cast by
`t_s + Δ`), so `SA.stop_core` applies on the prefix through the vote. -/
theorem stop_at_parent_of (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hvt : P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hold : ∀ B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s),
      B.parent = some d.head.root → B.slot < s →
      ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B) :
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
  have hU := honestBlocksAt_coherent hrun hnc
  have hΦU := (frameIn_at hrun hnc hy hcy.1).2
  have hng : ∀ B ∈ ℓy.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hBt hpar hg
    rw [honestAt_eq_genesis hrun hU (hΦU hBt) hg] at hpar
    exact hpar (by simp [Params.genesisBlock])
  have htj : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hpj : P.proposer ∈ H (tr.time j) := by
    rw [hP.2.1]
    exact hrun.antitone htj hp
  exact SA.stop_core (acRun_upTo hrun hnc (hrun.time_nonneg j)) hy
    (sa_castAt_upTo.2 ⟨le_rfl, hcy⟩) hes hPs hPQ hpj hng hvt (fun X hX hXQ hXs => hold X hX hXQ hXs)

/-- **The stop at `P.parent`** under growing faults: at `Q` the voter's only eligible child is
`P`, and its walk has no best child at `P`. The proposer is honest at the vote (cast by
`t_s + Δ`), so `SA.stop_core` applies on the prefix through the vote. -/
theorem stop_at_parent_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) :
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
  obtain ⟨D, -, hDQ, hviab, -⟩ := pivot_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti
    hPQ hib
  exact stop_at_parent_of hrun hnc hp hP hPs hPQ hy hcy hes
    (proposal_at_voter_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti hPQ hy hcy hes hib hjb)
    (fun X hX hXQ hXs => old_child_ineligible_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd
      hti hPQ hDQ hviab hy hcy hes hib hjb hX hXQ hXs)

/-- **Every slot-`s` vote of a node honest at its vote is the proposal `P` of slot `s`**, from a
pivot `D` of the proposal walk (`hvot`, as in `pivot_of`), the suffix agreement from `D` at every
honest vote (`hsuf`), `P` in every honest voter's viable voter block tree (`hvt`) and no old child
of `Q` eligible there (`hold`): by induction on the vote's cut (the first vote not `P`), each
voter's walk reaches a block of the path from `D` through `Q` to `P`, follows the proposal walk to
`Q`, steps to `P` and stops there. -/
theorem honest_votes_eq_proposal_of (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hvot : ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b →
        e.msg.slot = s →
        (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)))
    (hsuf : ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
      tr.time j ≤ b →
      ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
        X ≠ d.head →
        ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
            {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
              SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
                ((s : Int) - 1) B} C →
          SA.IsBest sp
            (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
              ((s : Int) - 1))
            {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
              B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
                (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C)
    (hvt : ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
      tr.time j ≤ b →
      P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hold : ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
      tr.time j ≤ b →
      ∀ B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s),
        B.parent = some d.head.root → B.slot < s →
        ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → tr.time j ≤ b → e.msg.head = P.root := by
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hp
  suffices main : ∀ j, (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root) →
      ∀ y e, HVoteAt tr H y j e → e.msg.slot = s → tr.time j ≤ b → e.msg.head = P.root by
    intro x j
    induction j using Nat.strong_induction_on generalizing x with
    | _ j ih =>
      intro e hv hs hjb
      exact main j (fun x' j' e' hj' hv' hs' =>
        ih j' hj' x' e' hv' hs' ((hrun.time_mono hj'.le).trans hjb)) x e hv hs hjb
  intro j hIH y e hv hes hjb
  obtain ⟨hy, ℓy, hcy, hey⟩ := hVoteAt_iff.1 hv
  have hcast : SA.CastAt tr.projAC y j ℓy e := ⟨hcy, hey⟩
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    have := (SA.slot_arithmetic sp s).1 0 (by omega)
    simpa using this
  -- the voter's walk passes a block `X` of the path from `D` through `Q` to `P`
  obtain ⟨hstep₀, hP₀⟩ := stop_at_parent_of hrun hnc hp hP hPs hPQ hy hcast hes
    (hvt y j ℓy e hy hcast hes hjb) (hold y j ℓy e hy hcast hes hjb)
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  obtain ⟨hΦy, hΦyU⟩ := frameIn_at hrun hnc hy hcy
  obtain ⟨X, hXc, haX, hXend⟩ := hvot y j ℓy e hy hcast hjb hes hIH
  -- the voter block tree has a viable block: `P` itself
  have hne : (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)).Nonempty :=
    ⟨P, hstep₀.1.1⟩
  rw [SA.viableTree_voteDomain_eq_of_viable hne] at hXend
  have hspec := SA.castAt_head_of_viable (acRun_upTo hrun hnc (hrun.time_nonneg j)).localRun hy
    (sa_castAt_upTo.2 ⟨le_rfl, hcast⟩) (hes ▸ hne)
  rw [hes] at hspec
  rw [hspec]
  congr 1
  -- from `X`, the voter's walk follows the proposal walk to `Q`, steps to `P` and stops
  exact voter_walk_eq_proposal hd hsl_i hΦp hΦpU hΦy hΦyU hsD hDQ (fun B hB => hB.1.1) hXc haX
    hXend hstep₀ hP₀ (hsuf y j ℓy e hy hcast hes hjb)

/-- **Every slot-`s` vote of a node honest at its vote is the proposal `P` of slot `s`** by a
proposer still honest at `t_s + Δ`, through `b ≥ t_s`: by induction on the vote's cut (the first
vote not `P`; `pivot_at` reads the earlier ones), each voter's walk reaches a block of the path
from the pivot `D` to `P`, follows the proposal walk to `Q`, steps to `P` and stops there. -/
theorem honest_votes_eq_proposal_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s ≤ b) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → tr.time j ≤ b → e.msg.head = P.root := by
  have hk : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [hk]; linarith [sp.toParams.hΔ]) hp
  obtain ⟨i, ℓp, d, pay, hc, hcall, hd, hti, hPQ, -⟩ := proposal_data_at hrun hpk hP hPs
  have hib : tr.time i ≤ b := hti ▸ hsb
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := pivot_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti
    hPQ hib
  exact honest_votes_eq_proposal_of hrun hnc hp hP hPs hc hd hti hPQ hsD hDQ hvot
    (fun y j ℓy e hy hcy hes hjb => suffix_agree_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd
      hti hPQ hsD hDQ hviab hy hcy hes hib hjb)
    (fun y j ℓy e hy hcy hes hjb => proposal_at_voter_at hrun hnc hsync hB hinv hp hP hPs hc hcall
      hd hti hPQ hy hcy hes hib hjb)
    (fun y j ℓy e hy hcy hes hjb B => old_child_ineligible_at hrun hnc hsync hB hinv hp hP hPs hc
      hcall hd hti hPQ hDQ hviab hy hcy hes hib hjb (B := B))

end Consensus.Goldilocks.Compose.Growing

end
