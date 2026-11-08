module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Suffix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

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
  have hU := honestBlocksAt_coherent hrun hnc
  have hΦU := (frameIn_at hrun hnc hy hcy.1).2
  have hng : ∀ B ∈ ℓy.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hBt hpar hg
    rw [honestAt_eq_genesis hrun hU (hΦU hBt) hg] at hpar
    exact hpar (by simp [Params.genesisBlock])
  obtain ⟨D, -, hDQ, hviab, -⟩ := pivot_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti
    hPQ hib
  have htj : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hpj : P.proposer ∈ H (tr.time j) := by
    rw [hP.2.1]
    exact hrun.antitone htj hp
  exact SA.stop_core (acRun_upTo hrun hnc (hrun.time_nonneg j)) hy
    (sa_castAt_upTo.2 ⟨le_rfl, hcy⟩) hes hPs hPQ hpj hng
    (proposal_at_voter_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti hPQ hy hcy hes hib hjb)
    (fun X hX hXQ hXs => old_child_ineligible_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd
      hti hPQ hDQ hviab hy hcy hes hib hjb hX hXQ hXs)

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
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hp
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := pivot_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti
    hPQ hib
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
  -- the proposal walk: from its start, through `D`, to `Q`, where it stops
  have hΦp := (frameIn_at hrun hnc hpi hc).1
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
  obtain ⟨hstep₀, hP₀⟩ := stop_at_parent_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti hPQ
    hy hcast hes hib hjb
  have hsuf := suffix_agree_at hrun hnc hsync hB hinv hp hP hPs hc hcall hd hti hPQ hsD hDQ hviab
    hy hcast hes hib hjb
  have hΦy := (frameIn_at hrun hnc hy hcy).1
  have hΦyU := (frameIn_at hrun hnc hy hcy).2
  have hΦpU := (frameIn_at hrun hnc hpi hc).2
  obtain ⟨X, hXc, haX, hXend⟩ := hvot y j ℓy e hy hcast hjb hes hIH
  -- the voter block tree has a viable block: `P` itself
  have hne : (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)).Nonempty :=
    ⟨P, hstep₀.1.1⟩
  rw [SA.viableTree_voteDomain_eq_of_viable hne] at hXend
  set W₂ := SA.ghost sp (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1))
    (SA.goldfishEligible sp ℓy.frame (tr.time j) (SA.mergedVoteView sp e.readPoint ℓy.frame s)
      ((s : Int) - 1)) with hW₂
  -- from `X`, the voter's walk ends at `P`
  have hXP : ∃ fX, W₂ fX X = P := by
    rcases hXc with rfl | ⟨hDX, hXQ⟩
    · exact ⟨0, rfl⟩
    refine ⟨ℓp.frame.tree.ncard + 1, SA.ghost_follow _ X ?_ hstop₁ ?_ hstep₀ hP₀⟩
    · exact hXQend hDX hXQ
    · intro m hm hne
      by_cases hXQ' : X = d.head
      · exact absurd (by rw [hXQ']; exact hstopQ m) hne
      have hXt : X ∈ ℓp.frame.tree := (Anc.mem hXQ hXQ').1
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
  have hspec := SA.castAt_head_of_viable (acRun_upTo hrun hnc (hrun.time_nonneg j)).localRun hy
    (sa_castAt_upTo.2 ⟨le_rfl, hcast⟩) (hes ▸ hne)
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

end Consensus.Goldilocks.Compose.Growing

end
