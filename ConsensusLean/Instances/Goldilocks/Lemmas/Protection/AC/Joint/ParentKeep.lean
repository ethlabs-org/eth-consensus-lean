module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # Tier A protection, the joint invariant over AC traces: the parent's keep

The parent discharges the per-call lock retention `FloorKeepAC` on its own runs, read as runs
with the unlock given at the parent's mode and oracle (`ACRun.toU`: `WriteMode.parent sp`,
`parentOracle sp tr`). At a call of the cohort, the parent's given locks are its `unlock` of the
call's input (`parentUnlock`). The input keeps the floor (the optimistic check of a receipt is an
`add_locks`), and `unlock` keeps it (`SA.floor_unlock`) when the lock's slot is at least the
view's or the unlock target of `P` is `P`: the view holds only slot-`(slot(t_k) − 1)` votes, the
honest ones outside `W` were cast before `k` and extend `P` (the keep's vote input), no honest
validator has two of them (one vote per slot), and `2·|Hᶜ ∪ W| < n`
(`SA.unlockTarget_unlockView_held_of_honest_slot`; the composite `unlockKeeps_of_voteCompat` and
`floor_run_view`).

* `parent_floorKeepAC`: the parent's keep, for every package over a run at the parent's mode and
  oracle;
* `parent_outage_inv_AC`: the joint invariant on such a run from the step `OutageS5StepAC`. -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The view `unlock` reads at a call is the call's unlock view. -/
private theorem unlockView_eq_callView (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksSA sp FGP ro).Call) : unlockView A Φ t c = callView sp A Φ t c := by
  cases c with
  | tick => rw [unlockView_tick]
  | proposal => rw [unlockView_proposal]
  | toFG => rw [unlockView_toFG]
  | message v => rw [unlockView_message]
  | block C => rw [unlockView_block]
  | restart => rw [unlockView_restart]

/-- The input of a call's unlock keeps the floor. -/
private theorem floor_callInput {Φ : Frm sp.n FGP} {t : Time} {j m : Nat} {B₀ : Blk sp.n FGP}
    {A : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (callInput sp A Φ t c).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  cases c with
  | message v =>
    refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact h
  | block C =>
    refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [blockReceipt_locks]
    exact h
  | tick => exact h
  | proposal => exact h
  | toFG => exact h
  | restart => exact h

/-- **The parent's keep**: on a run at the parent's mode and oracle, the parent's `unlock` at
every call of the cohort keeps a floor of label `j₀ − 1` or `j₀` within its life, given the keep's
vote input and count. -/
theorem parent_floorKeepAC
    (D : OutagePremisesAC (WriteMode.parent sp) (parentOracle sp tr) proposer tr H U) :
    FloorKeepAC D := by
  refine floorKeepAC_iff.2 fun x hx k ℓ hc j hj hfl hk hext hcount => ?_
  have hxH := D.hA₀ hx
  have hr := D.hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hxH hc
  obtain ⟨hP, hA⟩ := D.floor_frameAC hxH hc hfl
  have hva0 := (D.trivial_viableAncestorAC hxH hc hP).2
  -- the parent's given locks are its unlock of the call's input
  have hpo : parentOracle sp tr k =
      parentUnlock sp (tr.state x k) ℓ.frame (tr.time k) ℓ.call := by
    unfold parentOracle
    rw [hc.2, hc.1]
  -- the call is the parent's step
  have hstep : ((goldilocksSA sp FGP ro).step x (tr.state x k) ℓ.frame (tr.time k) ℓ.call).1 =
      tr.state x (k + 1) := by
    have he := hr.exec k ℓ hc.2 (hc.1 ▸ hxH)
    rw [hc.1, stepWithM_parent, hpo] at he
    rw [step_eq_stepWith, he, Trace.state_succ_of_call tr hc]
  -- `unlock` keeps `P`
  have hu : (sp.slot (tr.time k) : Int) - 1 ≤ j ∨
      unlockTarget sp ℓ.frame (callView sp (tr.state x k) ℓ.frame (tr.time k) ℓ.call)
        ((sp.slot (tr.time k) : Int) - 1) D.P = D.P := by
    by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
    · exact Or.inl hs
    refine Or.inr ?_
    have hpool : ∀ i, ∀ τ, ∀ v ∈ (tr.state x i).pool τ, v.slot = τ := fun i τ v hv =>
      state_pool_slotU sp hr hxH i τ v hv
    have hHn : (H \ D.W)ᶜ = Hᶜ ∪ D.W := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, not_and, not_not]
      tauto
    rw [← unlockView_eq_callView]
    refine unlockTarget_unlockView_held_of_honest_slot (Hn := H \ D.W) x ℓ.call hstep hΦ _ hP
      (hpool k) (hpool (k + 1)) (frame_validPayloadU sp hr hxH hc)
      (fun v hv v' hv' hvH hval hsl => ?_) (fun v hv hvH hsl Hd hHd hHdr => ?_)
      (by rw [hHn]; exact hcount)
    · obtain ⟨i, e, hve, rfl⟩ := held_vote_castAC D.hrun hxH hc hv hvH.1
      obtain ⟨i', e', hve', rfl⟩ := held_vote_castAC D.hrun hxH hc hv' (hval ▸ hvH.1)
      rw [hval] at hve'
      exact congrArg (fun e : Em sp FGP => e.msg)
        (one_vote_per_slotU sp FGP ro H U tr hr _ hvH.1 i i' e e' hve hve' hsl).2
    · obtain ⟨i, e, hve, rfl⟩ := held_vote_castAC D.hrun hxH hc hv hvH.1
      have hik : i < k := by
        obtain ⟨ℓ', hc', he'⟩ := hve
        have hsi := (castAt_specU hr hvH.1 ⟨hc', he'⟩).2.1
        by_contra hki
        have := slot_mono sp (hr.time_nonneg k) (hr.time_mono (Nat.le_of_not_lt hki))
        omega
      obtain ⟨Hd', hHd', hHd'r, hPHd⟩ := hext _ hvH.1 hvH.2 i hik e hve hsl
      obtain rfl : Hd = Hd' := hU.1 (hΦU hHd) hHd' (hHdr.trans hHd'r.symm)
      exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hP hPHd hHd)
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ :=
    floor_unlock hΦ hP hva0 hk hu (floor_callInput ℓ.call hΦ hP hva0 hk hA)
  rw [hpo]
  exact ⟨l, hl, hlj, hle, B, hΦU hB, hBr, hPB.mono hΦU⟩

/-- **The joint invariant on the parent's runs**: on a run at the parent's mode and oracle (every
parent run, by `ACRun.toU`), the outage lock invariant holds at every cut, from the premise package
and the step `OutageS5StepAC`. -/
theorem parent_outage_inv_AC
    (D : OutagePremisesAC (WriteMode.parent sp) (parentOracle sp tr) proposer tr H U)
    (hS5 : OutageS5StepAC D) : ∀ i, OutageInvAC D i :=
  outage_inv_AC D (parent_floorKeepAC D) hS5

end Consensus.Goldilocks.Comparison

end
