module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingStep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingHistory

public section

/-! Plan O-ARM §4 field 9, §6.2 step 8, §§6.3–6.4. The input of an actual
pending gate tick. Ticks precede deliveries at one time, so the store at the
gate tick is the store at the strict pending read. The stored batch gives the
F anchor and `D` strict majorities, so the raw result covers `D`. The fast
test counts the batch; the slow test reads saved Clean results, which every
step before the pending gate keeps. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; at its own tick a node has
the store of the strict read at the tick time. -/
theorem arming_tick_store {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho) {i : Nat} {y : V}
    {t : Time} (hi : rho.events[i]? = some (.tick y t)) :
    storeAt p c E rho i y = storeAt p c E rho (V2.D.Run.idxBefore rho t) y := by
  change (V2.D.Run.stateBefore E rho i y).st =
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho t) y).st
  rw [fgsa_preTick_eq_timeRead E rho hs hN hi, Gen.V2.Duty.stateBefore_idxBefore E rho t hs]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.3. Class (iii). DC: INTENTIONAL; `inclusion_head_seats` with
the exact count: the honest awake HEAD seats of a label are in bijection with
the honest awake nodes at its vote time. -/
theorem arming_head_seats {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true) ∧
      H.card = (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head r)) q) :=
    hC (.base (.head r)) trivial
  have himage : H.image (rho.seatOf (.base (.head r))) =
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r) := by
    ext y
    rw [Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  exact ⟨H, hH, (Finset.card_image_of_injective H hbij.1).symm.trans
    (congrArg Finset.card himage)⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.4. Class (iii). DC: INTENTIONAL; a saved result compatible
with the new F survives the reconcile filter of the saved results. -/
theorem arming_saved_map {n : Nat} {v w : GridCO.State n .root} {F C : Block} {u : Slot}
    (hg : w.genuine = v.genuine.map (fun row =>
      (row.1, row.2.filter (fun b => Block.compatible b F))))
    (hv : GridCO.savedGenuine v u = some (some C)) (hc : Block.compatible C F = true) :
    GridCO.savedGenuine w u = some (some C) := by
  change (w.genuine.find? (fun row => row.1 == u)).map Prod.snd = some (some C)
  change (v.genuine.find? (fun row => row.1 == u)).map Prod.snd = some (some C) at hv
  rw [hg, List.find?_map]
  have hp : ((fun row : Slot × Option Block => row.1 == u) ∘
      (fun row : Slot × Option Block =>
        (row.1, row.2.filter (fun b => Block.compatible b F)))) =
      (fun row : Slot × Option Block => row.1 == u) := rfl
  rw [hp]
  cases hf : v.genuine.find? (fun row => row.1 == u) with
  | none =>
    rw [hf] at hv
    cases hv
  | some row =>
    rw [hf] at hv
    obtain ⟨u', o⟩ := row
    cases hv
    simp only [Option.map_some, Option.filter_some, hc, ite_true]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.4. Class (iii). DC: INTENTIONAL; between the cut and the
pending gate a saved Clean result below `D` stays saved: off-gate ticks keep
the saved list, and a delivery keeps it or filters it by an F below `D`. -/
theorem arming_saved_interval_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V) (u : Slot) {Cu : Block} (hCuD : Block.Preceq Cu D)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (h₀ : GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) y).base u = some (some Cu))
    {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (hEpoch : V2.D.restartFree rho y (timeIdx rho b₀) i) :
    GridCO.savedGenuine (storeAt p c E rho i y).base u = some (some Cu) := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkd : k < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
      lt_of_lt_of_le (Nat.lt_succ_self k) hi
    have hprev := ih hkd.le (hEpoch.mono le_rfl (Nat.le_succ k))
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le hkd (arming_idxBefore_le_length rho _)
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    rcases arming_store_succ_on (E := E) he y
        (hEpoch.mono hk (Nat.le_refl (k + 1))) with heq | ⟨t, het, heq⟩ | ⟨o, t, het, heq⟩
    · rw [heq]
      exact hprev
    · obtain ⟨hb, hd⟩ := arming_event_window hs he hk hkd
      rw [het] at hb hd
      have hoff := arming_clock_offGate_fields p (storeAt p c E rho k y) t
        (arming_offGate p l hl hb hd)
      rw [heq, savedGenuine_congr hoff.2.2.1]
      exact hprev
    · rw [heq]
      rcases arming_process_lease p (storeAt p c E rho k y) (toWire p o) with h | h
      · rw [savedGenuine_congr h.2]
        exact hprev
      · apply arming_saved_map h.2 hprev
        have hFk := hF (k + 1) hi
        change Block.Preceq (eraseFG (storeAt p c E rho (k + 1) y).fg.F) D at hFk
        rw [heq] at hFk
        exact block_compatible_of_common hCuD hFk

/-- The old no-restart helper follows from the exact receiver epoch helper. -/
theorem arming_saved_interval {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V) (u : Slot) {Cu : Block} (hCuD : Block.Preceq Cu D)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (h₀ : GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) y).base u = some (some Cu))
    {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))) :
    GridCO.savedGenuine (storeAt p c E rho i y).base u = some (some Cu) :=
  arming_saved_interval_on hs hl y u hCuD hF h₀ hi₀ hi
    (hnr.restartFree y (timeIdx rho b₀) i)

/-- Only the current receiver's saved rows are read by the pending slow test.
P-Cl1 supplies each row at the cut. No row from a prior epoch is used. -/
theorem arming_slow_saved_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {B D : Block}
    (hl : SA.gateTime p.toParams l ≤ b₀) {y : V} {i : Nat}
    (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (hEpoch : V2.D.restartFree rho y (timeIdx rho b₀) i)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (hrows : ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) y).base
        (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca ∧ Block.Preceq Ca D) :
    ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca := by
  intro a ha
  obtain ⟨Ca, hCa, hBCa, hCaD⟩ := hrows a ha
  refine ⟨Ca, ?_, hBCa⟩
  rw [savedGenuine_congr (clockPre_genuine p _ _)]
  exact arming_saved_interval_on hs hl y _ hCaD hF hCa hi₀ hi hEpoch

/-- The current epoch's k-1 rows make the pending slow test pass. -/
theorem arming_slow_eligible_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {B D : Block}
    (hl : SA.gateTime p.toParams l ≤ b₀) {y : V} {i : Nat}
    (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (hEpoch : V2.D.restartFree rho y (timeIdx rho b₀) i) (hk : p.k ≤ l + 2)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (hrows : ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) y).base
        (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca ∧ Block.Preceq Ca D) :
    GridCO.slowEligible p.toParams.engine
      (FGSA.actView (FGSA.clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1)))) (l + 1) B = true := by
  have hwin := arming_slow_saved_on hs hl hi₀ hi hEpoch hF hrows
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hk, List.all_eq_true.mpr ?_⟩
  intro a ha
  obtain ⟨Ca, hCa, hBCa⟩ := hwin a (List.mem_range.mp ha)
  change GridCO.savedGenuine (FGSA.actView (FGSA.clockPre p (storeAt p c E rho i y)
    (SA.gateTime p.toParams (l + 1)))) (l + 1 - (a + 1)) = some (some Ca) at hCa
  rw [hCa]
  exact hBCa

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §4 field 9 (slow clause), §6.4. Class (iii). DC: INTENTIONAL;
the slow window of the pending gate: every label strictly between the origin
and the pending label has a saved Clean result that covers B. -/
theorem arming_slow_saved {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho) {b₀ : Time}
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hsavedKeep : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') → Block.Preceq C' C)
    {l : Slot} {B D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D)
    {u₀ : V} {s : Slot} {C₀ : Block} {iₛ : Nat} (hu₀ : u₀ ∈ rho.honest) (hs1 : 1 ≤ s)
    (hts : IsGateTick p c rho iₛ u₀ s) (hres : gateResultAt p c E rho iₛ = some (some C₀))
    (hBC : Block.Preceq B C₀) (hgap : s + p.k ≤ l + 1)
    (hF : ∀ k y, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho k y) D) :
    ∀ i y, IsGateTick p c rho i y (l + 1) → y ∈ rho.honest →
      p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
        GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i y)
          (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
        Block.Preceq B Ca := by
  intro i y hi hy
  refine ⟨by simp only [Slot] at hs1 hgap ⊢; omega, ?_⟩
  intro a ha
  obtain ⟨hsu, hul, _⟩ := arming_slow_window_label p s l a hs1 hgap ha
  have hub : SA.gateTime p.toParams (l + 1 - (a + 1)) ≤ b₀ :=
    ((arming_gate_le_iff p _ _).mpr hul).trans hl
  have hsb : SA.gateTime p.toParams s ≤ b₀ :=
    ((arming_gate_le_iff p _ _).mpr (by simp only [Slot] at hsu ⊢; omega)).trans hub
  obtain ⟨Cu, hCu, ⟨q, hq, hpass⟩, _, _⟩ := hcleanGate _ y hub hy
  have hqI : q < timeIdx rho b₀ := (arming_lt_timeIdx_iff hs b₀ hq).mpr hub
  have hresq : gateResultAt p c E rho q = some (some Cu) :=
    (gateResultAt_eq_gateResult p c E rho hs hq).trans hCu
  have hC₀ : gateResult p c E rho u₀ s = some (some C₀) :=
    (gateResultAt_eq_gateResult p c E rho hs hts).symm.trans hres
  have hBCu : Block.Preceq B Cu :=
    block_preceq_trans hBC ((hordered u₀ y s _ C₀ Cu hu₀ hy hsb hub hC₀ hCu).1
      (by simp only [Slot] at hsu ⊢; omega))
  have hCuD : Block.Preceq Cu D :=
    hmax _ Cu ⟨q, hqI, y, hq, (arming_enabled_of_pass hq hpass).2, hresq⟩ hul
  have hkeep := hsavedKeep (timeIdx rho b₀) y le_rfl hy q _ Cu hqI hq hresq
  have hsaved := arming_saved_interval hs hnr hl y _ hCuD (fun k hk => hF k y hk hy) hkeep
    (arming_timeIdx_le_idxBefore rho hcut) le_rfl
  refine ⟨Cu, ?_, hBCu⟩
  rw [arming_tick_store hs hnr hi, savedGenuine_congr (clockPre_genuine p _ _)]
  exact hsaved

end AvailableChain.FGSA.Run
end
