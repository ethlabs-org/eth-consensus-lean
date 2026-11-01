module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Epoch
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepGateHistory -- shake: keep

public section

/-! WC plan §6.5; DC the ordered handler cases preserve and identify the output. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC a fresh accepted gate normalizes an already compatible output. -/
private theorem gate_output {j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j x s)
    (hB : gateResultAt p c E rho j = some (some B)) (hpass : gatePassedAt p c E rho j)
    (hcompat : Block.Compatible (S_at p c E rho j x) B) :
    S_at p c E rho (j + 1) x = GridCO.advance (S_at p c E rho j x) B ∧
      Block.Preceq (S_at p c E rho j x) (S_at p c E rho (j + 1) x) := by
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho (wc_gate_enabled_of_result hsch ht hB))
  have hraw := Option.some.inj (hrawAt.symm.trans hB)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.1.symm.trans ht))
  have hlabel : r = s := by
    have ht := hevent.2
    change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
    have hcast : (r : Int) = s := by nlinarith [p.deltaPos]
    exact Int.ofNat_inj.mp hcast
  have hxy := hevent.1
  subst y
  subst r
  have heq : G = B := Option.some.inj (hG.symm.trans hraw)
  subst G
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j x) s
  have hraw' : (fgsaAC E rho).raw j s x = some B := by
    rw [clockPre_fg] at hraw
    have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hview
    exact he.symm.trans hraw
  have hguard' : ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j x s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp hguard lease hm
    simpa only [Gen.AC.Lease.target, Block.Compatible, Bool.not_eq_true',
      Bool.not_eq_false] using hg
  have hc := hcompat
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  rcases (fgsaAC_gate_write E rho j s x
      (wc_gate_pre_joined (wc_gate_enabled_of_result hsch ht hB)) ht).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch ht
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw' hguard').1
    change S_at p c E rho (j + 1) x = Gen.AC.normalizeOutput (F_at p c E rho j x)
      (GridCO.advance (S_at p c E rho j x) B) at hw
    have hn : Block.preceq (F_at p c E rho j x)
        (GridCO.advance (S_at p c E rho j x) B) = true :=
      block_preceq_trans (nestOK_stateBefore E rho j x) hadv
    rw [Gen.AC.normalizeOutput_def, ite_eq_left hn] at hw
    exact ⟨hw, hw ▸ hadv⟩

/-- Each event keeps the output, writes its gate result, or exposes received finality. -/
theorem wc_outputStep {i : Nat} {w : HealingWitness}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (hfinal : ∀ x ∈ rho.honest,
      Block.Compatible (S_at p c E rho i x) (F_at p c E rho (i + 1) x))
    (hgate : ∀ x s, x ∈ rho.honest → enabledGateAt p c E rho i x s →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ gatePassedAt p c E rho i ∧
        w.u < s ∧ Block.Compatible (S_at p c E rho i x) B) :
    ∀ x ∈ rho.honest,
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        (∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) ∨
        S_at p c E rho (i + 1) x = F_at p c E rho (i + 1) x) := by
  intro x hx
  have keep (heq : S_at p c E rho (i + 1) x = S_at p c E rho i x) :
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        (∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) ∨
        S_at p c E rho (i + 1) x = F_at p c E rho (i + 1) x) :=
    ⟨heq ▸ block_preceq_refl _, Or.inl heq⟩
  rcases fgsaAC_output_step E rho i x with hsame | ⟨s, ht⟩ | hrc | ⟨t, hr, _⟩
  · exact keep hsame
  · change IsGateTick p c rho i x s at ht
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    by_cases hJ : joinedNow p pre = true
    · have hG : enabledGateAt p c E rho i x s := by
        refine ⟨ht, ?_⟩
        have hg : joinedAtTime p (storeAt p c E rho i x).restartTime
            (SA.gateTime p.toParams s) = true := by
          simpa only [pre, clockPre_joined] using hJ
        have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
          (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
            (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
        change (match (storeAt p c E rho i x).restartTime with
          | none => True | some w => w ≤ slotStartZ p (s : Int))
        cases hw : (storeAt p c E rho i x).restartTime with
        | none => trivial
        | some w =>
          rw [hw] at hg
          change decide (w ≤ 4 * p.Δ *
            ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) = true at hg
          change w ≤ 4 * p.Δ * (s : Int)
          simpa only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
            decide_eq_true_eq] using hg
      obtain ⟨B, hB, hp, hl, hc⟩ := hgate x s hx hG
      obtain ⟨heq, hm⟩ := gate_output hsch ht hB hp hc
      refine ⟨hm, ?_⟩
      unfold GridCO.advance at heq
      split at heq
      · exact Or.inl heq
      · exact Or.inr (Or.inl ⟨s, ht, hl, heq ▸ hB⟩)
    · have hj : joinedNow p pre = false := Bool.eq_false_iff.mpr hJ
      have hfresh : GridCO.savedGenuine pre.base s = none := by
        rw [GridCO.savedGenuine, clockPre_genuine]
        exact fgsa_gate_fresh E rho hsch ht
      have hn : NestOK pre := by
        change Block.Preceq (eraseFG pre.fg.F) pre.base.stableRecord
        dsimp only [pre]
        rw [clockPre_fg, clockPre_stable]
        exact nestOK_stateBefore E rho i x
      have hout := ((gateStep_unjoined p pre s hfresh hj).2.2 hn).2.2
      have hclock : clock p (storeAt p c E rho i x) (SA.gateTime p.toParams s) =
          gateStep p pre s := by
        have hl : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
          have hz : (4 * p.Δ : Int) ≠ 0 := by nlinarith [p.deltaPos]
          change ((4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ) / (4 * p.Δ)).toNat = s
          simp [hz]
        unfold clock
        rw [hl]
        dsimp only
        have h0 : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by
          change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ
          nlinarith [p.deltaPos, Int.natCast_nonneg s]
        simp only [h0, decide_true, beq_self_eq_true, Bool.true_and, ite_true]
        rfl
      apply keep
      change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
      rw [V2.D.Run.stateBefore_succ E rho ht]
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho i x) x _]
      change (clock p (storeAt p c E rho i x) _).base.stableRecord = _
      rw [hclock, hout, clockPre_stable]
      rfl
  · obtain ⟨o, t, B, _he, _hb, _hf, hout⟩ := hrc
    change S_at p c E rho (i + 1) x = Gen.AC.normalizeOutput
      (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hout
    by_cases hbelow : Block.preceq (F_at p c E rho (i + 1) x)
        (S_at p c E rho i x) = true
    · rw [Gen.AC.normalizeOutput_def, ite_eq_left hbelow] at hout
      exact keep hout
    · rw [Gen.AC.normalizeOutput_def, ite_eq_right hbelow] at hout
      refine ⟨hout ▸ ?_, Or.inr (Or.inr hout)⟩
      rcases Bool.or_eq_true_iff.mp (hfinal x hx) with h | h
      · exact h
      · exact (hbelow h).elim
  · apply keep
    change rho.events[i]? = some (.restart x t) at hr
    change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
    rw [V2.D.Run.stateBefore_succ E rho hr]
    simp only [V2.D.World.step, Function.update_self]
    change (acRestart p (storeAt p c E rho i x) t).base.stableRecord = _
    exact acRestart_stableRecord p _ t

end AvailableChain.FGSA.Run
end
