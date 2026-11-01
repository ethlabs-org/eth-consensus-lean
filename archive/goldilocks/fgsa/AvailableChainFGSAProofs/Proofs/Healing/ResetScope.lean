module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope -- shake: keep

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- The approved recovery start includes the six-delta update delay. -/
theorem healing_recovery_start_lower (E : Generic.Env V) :
    E.t_GST + 6 * p.Δ ≤ recoveryStart p E := by
  let a := max 0 E.t_GST + 4 * p.Δ - 1
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have ha : 0 ≤ a := by
    have hdelta : 1 ≤ p.Δ := by have := p.deltaPos; dsimp [Time] at *; omega
    dsimp [a]
    linarith [le_max_left 0 E.t_GST]
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  change E.t_GST + 6 * p.Δ ≤ 4 * p.Δ * ((a / (4 * p.Δ)).toNat : Int) + 6 * p.Δ
  rw [Int.toNat_of_nonneg hq]
  dsimp [a] at he hm
  dsimp [Time] at *
  nlinarith [le_max_right 0 E.t_GST]

omit [DecidableEq V] in
/-- For nonnegative integer GST, add the approved recovery delay exactly once. -/
theorem healing_recovery_delay_bounds (E : Generic.Env V) (hgst : 0 ≤ E.t_GST) :
    6 * p.Δ ≤ recoveryDelay p E ∧ recoveryDelay p E ≤ 10 * p.Δ - 1 := by
  have hlo := healing_recovery_start_lower (p := p) E
  let a := E.t_GST + 4 * p.Δ - 1
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have ha : 0 ≤ a := by
    have := p.deltaPos
    dsimp [a, Time] at *
    omega
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_nonneg a (ne_of_gt hd)
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  have ht : recoveryStart p E = 4 * p.Δ * (a / (4 * p.Δ)) + 6 * p.Δ := by
    change 4 * p.Δ * (((max 0 E.t_GST + 4 * p.Δ - 1) / (4 * p.Δ)).toNat : Int) +
      6 * p.Δ = _
    rw [max_eq_right hgst, Int.toNat_of_nonneg hq]
  change 6 * p.Δ ≤ recoveryStart p E - E.t_GST ∧
    recoveryStart p E - E.t_GST ≤ 10 * p.Δ - 1
  rw [ht] at hlo ⊢
  dsimp [a] at he
  constructor <;> nlinarith

omit [DecidableEq V] in
/-- The approved recovery start puts GST before this voter's previous slot start. -/
theorem healing_ready_vote_cutoff (E : Generic.Env V) {s : Slot}
    (hready : recoveryStart p E ≤ SA.voteTime p.toParams s) :
    E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
  have hlo := healing_recovery_start_lower (p := p) E
  change recoveryStart p E ≤ 4 * p.Δ * (s : Int) + p.Δ at hready
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  linarith [p.deltaPos]


omit [DecidableEq V] in
/-- Every bounded recovery read has the previous-slot GST cutoff. -/
theorem healing_ready_read_cutoff (E : Generic.Env V) {t : Time}
    (hready : recoveryStart p E ≤ t) :
    E.t_GST ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
  let d := 4 * p.Δ
  let a := max 0 E.t_GST + d - 1
  have hd : 0 < d := by dsimp [d]; linarith [p.deltaPos]
  have ha : 0 ≤ a := by
    have := p.deltaPos
    dsimp [a, d, Time] at *
    omega
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a d
  have hstart : recoveryStart p E = d * (a / d) + 6 * p.Δ := by
    change d * ((a / d).toNat : Int) + 6 * p.Δ = _
    rw [Int.toNat_of_nonneg hq]
  have hle : (a / d) + 1 ≤ t / d := by
    apply Int.le_ediv_of_mul_le hd
    rw [hstart] at hready
    dsimp [d] at *
    nlinarith [p.deltaPos]
  have ht : 0 ≤ t / d := by dsimp [Time] at *; omega
  change E.t_GST ≤ d * ((t / d).toNat - 1)
  rw [Int.toNat_of_nonneg ht]
  have hceil : E.t_GST ≤ d * (a / d) := by
    dsimp [a] at he hm
    nlinarith [le_max_right 0 E.t_GST]
  nlinarith

omit [DecidableEq V] in
/-- A proposal after recoveryStart also has the preceding HEAD batch cutoff. -/
theorem healing_ready_proposal_cutoff (E : Generic.Env V) {s : Slot}
    (hready : recoveryStart p E ≤ SA.proposalTime p.toParams s) :
    E.t_GST ≤ slotStartZ p ((s : Int) - 2) := by
  let d := 4 * p.Δ
  let a := max 0 E.t_GST + d - 1
  have hd : 0 < d := by dsimp [d]; linarith [p.deltaPos]
  have ha : 0 ≤ a := by
    have := p.deltaPos
    dsimp [a, d, Time] at *
    omega
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a d
  have hstart : recoveryStart p E = d * (a / d) + 6 * p.Δ := by
    change d * ((a / d).toNat : Int) + 6 * p.Δ = _
    rw [Int.toNat_of_nonneg hq]
  have hlabels : a / d + 2 ≤ (s : Int) := by
    have hr : d * (a / d) + 6 * p.Δ ≤ d * (s : Int) := by
      change recoveryStart p E ≤ d * (s : Int) at hready
      rw [hstart] at hready
      exact hready
    have hone : a / d + 1 < (s : Int) := by
      dsimp [d] at *
      nlinarith [p.deltaPos]
    dsimp [Time] at *
    omega
  change E.t_GST ≤ d * ((s : Int) - 2)
  have hceil : E.t_GST ≤ d * (a / d) := by
    dsimp [a] at he hm
    nlinarith [le_max_right 0 E.t_GST]
  nlinarith

variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The first reset row is after the inclusive frontier cut. -/
theorem healing_reset_action_after_cut {w : HealingWitness} (hreset : H0Reset p c E rho w) :
    w.u₀ < p.actionTime w.rStar := by
  obtain ⟨j, y, a, C, ha, hentry, _, _, _⟩ := hreset.fresh
  by_contra hn
  have hcap := hreset.rowCap j y w.rStar a (w.M + 1) (heightView p C).T_h.root
    (p.actionTime w.rStar) ha ha.2.1 (le_of_not_gt hn) hentry
  change w.M + 1 ≤ w.M at hcap
  omega

/-- The fresh reset row has a source vote after the single healing start. -/
theorem healing_reset_source_ready {w : HealingWitness}
    (hreset : H0Reset p c E rho w) :
    recoveryStart p E ≤ SA.voteTime p.toParams w.sStar := by
  have hafter := healing_reset_action_after_cut hreset
  have he : p.actionTime w.rStar = SA.voteTime p.toParams w.sStar + 5 * p.Δ := by
    rw [hreset.label]
    change 4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 6 * p.Δ =
      4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + p.Δ + 5 * p.Δ
    ring
  have hR : (2 : Int) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Int) * p.Δ
    nlinarith [p.deltaPos]
  rw [he] at hafter
  nlinarith [hreset.cut_lower, p.deltaPos]

/-- The shifted reset cut puts GST before the source slot start.
The synchronous vote bound alone does not prove this cutoff. -/
theorem healing_reset_slot_cutoff {w : HealingWitness} (hreset : H0Reset p c E rho w) :
    E.t_GST ≤ slotStartZ p (w.sStar : Int) := by
  have hafter := healing_reset_action_after_cut hreset
  have hlo := hreset.cut_lower
  have hstart := healing_recovery_start_lower (p := p) E
  have hP : 0 ≤ P p := by
    have := p.deltaPos
    change 0 ≤ 4 * (p.R : Time) * p.Δ
    positivity
  have he : p.actionTime w.rStar = slotStartZ p (w.sStar : Int) + 6 * p.Δ := by
    rw [hreset.label]
    rfl
  rw [he] at hafter
  linarith

/-- The reset suffix supplies the exact gate join cutoff at each later label. -/
theorem healing_reset_gate_cutoff {w : HealingWitness} (hreset : H0Reset p c E rho w)
    {s : Slot} (hs : w.sStar ≤ s) : E.t_GST ≤ slotStartZ p (s : Int) := by
  have hlo := healing_reset_slot_cutoff hreset
  have hi : (w.sStar : Int) ≤ (s : Int) := by exact_mod_cast hs
  change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) at hlo
  change E.t_GST ≤ 4 * p.Δ * (s : Int)
  nlinarith [p.deltaPos]

/-- Every later reset HEAD uses the exact previous-slot join cutoff. -/
theorem healing_reset_vote_cutoff {w : HealingWitness} (hreset : H0Reset p c E rho w)
    {s : Slot} (hs : w.sStar + 1 ≤ s) :
    E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
  have hlo := healing_reset_slot_cutoff hreset
  have hi : (w.sStar : Int) + 1 ≤ (s : Int) := by exact_mod_cast hs
  change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) at hlo
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  nlinarith [p.deltaPos]

/-- Recovery's closed awake interval supplies the exact post-clock vote join guard. -/
theorem healing_vote_joined_of_recovery [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) {j : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x (SA.voteTime p.toParams s)))
    (hh : SA.voteTime p.toParams s ≤ rho.horizon)
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1)) :
    joinedNow p (FGSA.clock p (storeAt p c E rho j x) (SA.voteTime p.toParams s)) = true := by
  have hslot : p.slotOf (SA.voteTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j x) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ s)
  apply fgsa_joinedNow_of_awakeClosed E rho hrec.base.valid.toScheduleWellFormed
    hrec.base.restartsAtWakes ht
  intro t hlo hhi
  apply hrec.awake x hx t _ (hhi.trans hh)
  rw [hslot] at hlo
  exact hcut.trans hlo

/-- The exact recovery gate cutoff enables its scheduled execution. -/
theorem healing_gate_enabled_of_recovery [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) {j : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho j x s) (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (hcut : E.t_GST ≤ slotStartZ p (s : Int)) : enabledGateAt p c E rho j x s := by
  have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  have hjoined : joinedNow p (FGSA.clock p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)) = true := by
    apply fgsa_joinedNow_of_awakeClosed E rho hrec.base.valid.toScheduleWellFormed
      hrec.base.restartsAtWakes ht
    intro t hlo hhi
    apply hrec.awake x hx t _ (hhi.trans hh)
    rw [hslot] at hlo
    have hcut' : E.t_GST ≤ 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) := by
      change E.t_GST ≤ 4 * p.Δ * (s : Int) at hcut
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hcut
    exact hcut'.trans hlo
  unfold joinedNow at hjoined
  rw [fgsa_clock_restartTime, (clock_vn _ _).2] at hjoined
  refine ⟨ht, ?_⟩
  unfold joinedAtTime at hjoined
  cases hr : (storeAt p c E rho j x).restartTime with
  | none => trivial
  | some w =>
    rw [hr, hslot] at hjoined
    change w ≤ 4 * p.Δ * (s : Int)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using of_decide_eq_true hjoined

end AvailableChain.FGSA.Run
end
