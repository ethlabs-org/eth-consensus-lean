module
public import AvailableChainFGCompose.Proofs.Healing.ResetCut
public import AvailableChainFGCompose.Statements.FrontierSearch

public section

/-! Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1–R3. Reset witness assembly.
The inclusive cut and the first honest height-(M+1) row give all 13 fields of the reset
history `H0Reset` from one first row and its original source. The repair allowance is a
parameter with its budget equation. The search result is the start-family companion
statement, which a canonical-budget producer can supply. No proposal-first field and no
service seed is read. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the two HG.5 charges, with all subtraction in integer time. -/
theorem healing_reset_budget_sum (T : FGTiming) (G ΔF ρbar : Time) :
    B_resetF T ΔF G ρbar = 3 * FGCompose.P T +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar) +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar) := by
  unfold B_resetF
  ring

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the strict cut bound gives the strict reset deadline. The allowance and its
budget equation are inputs; the protocol chooses the allowance. -/
theorem healing_reset_budget_lt (T : FGTiming) (G ΔF Jst u₀ ρbar budget : Time)
    (hbudget : budget = 3 * FGCompose.P T +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar) +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar))
    (hcut : u₀ < Jst + 3 * FGCompose.P T) :
    u₀ + (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar) +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar) < Jst + budget := by
  rw [hbudget]
  linarith only [hcut]

variable (T : FGTiming) (L : FGTimingLaws T) (Jst : Time)
variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (O : FGObservationReads R)
variable (I : V2.D.Interface Prot) (pair : Wire → NamedHeightPair)
variable (Ef : Electorate (Fin n)) (HL : FGHeightLaws Ef O.height)
variable (CL : FGCoreLaws R) (K : FGTreeKeepLaws R)
variable (storeInv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (V2.D.Run.stateBefore E rho i x)).fg)

section Source

variable (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : Wire} {e : Height × BlockId},
  HonestRowAt S E rho T j x r a → namedEntry (pair a) = some e →
  ∃ C, actionSourceFG R E rho T x r = some (some C) ∧
    e = ((O.height C).h, (O.height C).T_h.root))

include CL K storeInv emittedName in
/-- Blueprint 21 H.11:1755–1756; S5 J8 R1 rowCap.
DC: SAME the closed cap at the inclusive cut. -/
theorem healing_reset_rowCap (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime T L Jst →
      namedEntry (pair a) = some (h, e) → h ≤ resetCutFrontier R E rho T L Jst := by
  intro j y r a h e t ha hj ht he
  rw [reset_frontier]
  exact reset_row_cap T R S E rho O (fun a => namedEntry (pair a)) CL K storeInv hs
    (fun ha he => by
      obtain ⟨C, hC, hh⟩ := emittedName ha he
      exact ⟨C, hC, congrArg Prod.fst hh⟩) ha hj ht he

include HL CL K storeInv emittedName in
/-- Blueprint 21 H.11:1754–1756,1772–1777; S5 J8 R1 mu_le.
DC: SAME an actual height row supplies a nonempty honest set. -/
theorem healing_reset_mu_le (hs : V2.D.ScheduleWellFormed E rho) {r h : Nat}
    (hrow : HeightRow S E rho T (fun a => namedEntry (pair a)) r h) :
    muOf S E rho T (fun a => namedEntry (pair a)) Jst ≤ resetCutFrontier R E rho T L Jst := by
  refine (reset_mu_le_iff (T := T) (L := L) (Jst := Jst) (R := R) (S := S) (E := E)
    (rho := rho) (O := O) (entry := fun a => namedEntry (pair a)) Ef HL CL K storeInv hs
    (fun ha he => by
      obtain ⟨C, hC, hh⟩ := emittedName ha he
      exact ⟨C, hC, congrArg Prod.fst hh⟩)).mpr ?_
  obtain ⟨j, y, a, e, ha, _⟩ := hrow
  exact ⟨y, ha.1⟩

include emittedName in
/-- Blueprint 21 H.11:1757–1759,1799–1800; S5 J8 R1 fresh.
DC: SAME select the erased actual source of the row, with the row's exact root. -/
theorem healing_reset_fresh {r M : Nat}
    (hrow : HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1)) :
    ∃ CStar, ∃ j y, ∃ (a : Wire) (C : FGBlock (Fin n)),
      HonestRowAt S E rho T j y r a ∧
      namedEntry (pair a) = some (M + 1, (O.height C).T_h.root) ∧
      actionSourceFG R E rho T y r = some (some C) ∧
      R.erase C = CStar ∧ (O.height C).h = M + 1 := by
  obtain ⟨j, y, a, e, ha, he⟩ := hrow
  obtain ⟨C, hC, hh⟩ := emittedName ha he
  have hheight : M + 1 = (O.height C).h := congrArg Prod.fst hh
  have hroot : e = (O.height C).T_h.root := congrArg Prod.snd hh
  exact ⟨R.erase C, j, y, a, C, ha, hroot ▸ he, hC, rfl, hheight.symm⟩

end Source

/-- Blueprint 21 H.11:1778–1780; S5 J8 R1 synchronous.
DC: SAME a height-(M+1) row is strictly after the inclusive cut, so its source vote is
after the old cutoff. -/
theorem healing_reset_synchronous (hJst : E.t_GST ≤ Jst) {r : Nat}
    (rowCap : ∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime T L Jst →
      namedEntry (pair a) = some (h, e) → h ≤ resetCutFrontier R E rho T L Jst)
    (hrow : HeightRow S E rho T (fun a => namedEntry (pair a)) r
      (resetCutFrontier R E rho T L Jst + 1)) :
    E.t_GST ≤ T.vote (r * T.roundSlots) := by
  obtain ⟨j, y, a, e, ha, he⟩ := hrow
  have hafter : resetCutTime T L Jst < T.action r := by
    by_contra hn
    have hc := rowCap j y r a (resetCutFrontier R E rho T L Jst + 1) e
      (T.action r) ha ha.2.1 (le_of_not_gt hn) he
    exact Nat.not_succ_le_self _ hc
  have ht : T.action r = T.vote (r * T.roundSlots) + 5 * T.delta := by
    rw [L.action_eq, L.gate_eq, L.vote_eq]
    ring
  have hc := reset_cut_lower T L Jst
  have hp := reset_period_lower T L
  rw [ht] at hafter
  linarith [L.delta_pos]

/-- Blueprint 21 H.11:1757–1758; S5 J8 R1 reset_first support.
DC: SAME the first-row contract supplies the exact minimality field. -/
theorem healing_reset_reset_first {M : Nat} {deadline : Time}
    (firstRow : FirstHeightRowBy S E rho T pair (M + 1) deadline) :
    ∃ rStar, HeightRow S E rho T (fun a => namedEntry (pair a)) rStar (M + 1) ∧
      (∀ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1) → rStar ≤ r) ∧
      T.action rStar ≤ deadline :=
  (FirstHeightRowBy_def S E rho T pair (M + 1) deadline).mp firstRow

section Source

variable (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : Wire} {e : Height × BlockId},
  HonestRowAt S E rho T j x r a → namedEntry (pair a) = some e →
  ∃ C, actionSourceFG R E rho T x r = some (some C) ∧
    e = ((O.height C).h, (O.height C).T_h.root))

include HL CL K storeInv emittedName in
/-- Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1 field support.
DC: INTENTIONAL reset-only history: all 13 fields from the cut and one first row with
its source. No service seed and no proposal-first field. -/
theorem healing_reset_fields (hs : V2.D.ScheduleWellFormed E rho) (hstart : 0 ≤ Jst)
    (hJst : E.t_GST ≤ Jst) {deadline : Time}
    (firstRow : FirstHeightRowBy S E rho T pair (resetCutFrontier R E rho T L Jst + 1)
      deadline) :
    ∃ w : FGResetHistory, H0Reset R S E rho O T (fun a => namedEntry (pair a)) Jst w ∧
      w.rG = resetFirstRound T L Jst ∧ w.u0 = resetCutTime T L Jst ∧
      w.M = resetCutFrontier R E rho T L Jst ∧ T.action w.rStar ≤ deadline := by
  have hcap := healing_reset_rowCap (T := T) (L := L) (Jst := Jst) (R := R) (S := S) (E := E)
    (rho := rho) (O := O) (pair := pair) (CL := CL) (K := K) (storeInv := storeInv)
    (emittedName := emittedName) hs
  obtain ⟨rStar, hrow, hfirst, htime⟩ := healing_reset_reset_first (T := T) (S := S)
    (E := E) (rho := rho) (pair := pair) firstRow
  obtain ⟨CStar, hfresh⟩ := healing_reset_fresh (T := T) (R := R) (S := S) (E := E)
    (rho := rho) (O := O) (pair := pair) (emittedName := emittedName) hrow
  refine ⟨⟨resetFirstRound T L Jst, resetCutTime T L Jst, resetCutFrontier R E rho T L Jst,
    rStar, rStar * T.roundSlots, CStar⟩, ?_, rfl, rfl, rfl, htime⟩
  exact
    { rG_after := reset_rG_after T L Jst
      rG_first := reset_rG_first T L Jst
      cut := reset_cut T L Jst
      frontier := reset_frontier T L Jst R E rho
      rowCap := hcap
      mu_le := healing_reset_mu_le (T := T) (L := L) (Jst := Jst) (R := R) (S := S) (E := E)
        (rho := rho) (O := O) (pair := pair) (Ef := Ef) (HL := HL) (CL := CL) (K := K)
        (storeInv := storeInv) (emittedName := emittedName) hs hrow
      cut_lower := reset_cut_lower T L Jst
      cut_upper := reset_cut_upper T L Jst hstart
      reset_row := hrow
      reset_first := hfirst
      label := rfl
      fresh := hfresh
      synchronous := healing_reset_synchronous (T := T) (L := L) (Jst := Jst) (R := R) (S := S)
        (E := E) (rho := rho) (pair := pair) hJst hcap hrow }

variable (leaseSlots deltaT : Nat)

include HL CL K storeInv emittedName in
/-- Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1.
DC: INTENTIONAL reset-only history with the strict reset deadline `Jst + budget`.
`hsearch` is the start-family search result for the chosen allowance; its premises are
nonnegativity and the allowance at every actual phase start. The budget equation and
the complete horizon guard are inputs. -/
theorem healing_resetWitness (hs : V2.D.ScheduleWellFormed E rho) (hstart : 0 ≤ Jst)
    (hJst : E.t_GST ≤ Jst) {G ΔF ρbar budget : Time}
    (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF) (hρ : 0 ≤ ρbar)
    (hfamily : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
      Jst + 2 * FGCompose.P T ≤ ev.time →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta))
    (hsearch : FrontierSearchFamilyStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF
      ρbar)
    (hbudget : budget = 3 * FGCompose.P T +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar) +
      (E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar))
    (hhor : Jst + budget ≤ rho.horizon) :
    ∃ w : FGResetHistory, H0Reset R S E rho O T (fun a => namedEntry (pair a)) Jst w ∧
      w.rG = resetFirstRound T L Jst ∧ w.u0 = resetCutTime T L Jst ∧
      w.M = resetCutFrontier R E rho T L Jst ∧ T.action w.rStar < Jst + budget := by
  have hcap := healing_reset_rowCap (T := T) (L := L) (Jst := Jst) (R := R) (S := S) (E := E)
    (rho := rho) (O := O) (pair := pair) (CL := CL) (K := K) (storeInv := storeInv)
    (emittedName := emittedName) hs
  have hlt := healing_reset_budget_lt T G ΔF Jst (resetCutTime T L Jst) ρbar budget hbudget
    (reset_cut_upper T L Jst hstart)
  rw [← frontierSearchRiseBudget_def, ← frontierSearchRowBudget_def] at hlt
  have hguard : resetCutTime T L Jst + frontierSearchRiseBudget T G ΔF ρbar +
      frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon := by linarith
  have hfs := (FrontierSearchFamilyStatement_def R S E rho O T I pair Jst leaseSlots deltaT G
    ΔF ρbar).mp hsearch hδ hbound hρ hfamily (resetFirstRound T L Jst) (resetCutTime T L Jst)
    (resetCutFrontier R E rho T L Jst) (reset_rG_after T L Jst) (reset_rG_first T L Jst)
    (reset_cut T L Jst) (reset_cut_lower T L Jst) (reset_frontier T L Jst R E rho) hcap
  obtain ⟨rStar, hrow, hfirst, j, ev, _, _, hevt, _, _, hrt⟩ := hfs.2 hguard
  have firstRow : FirstHeightRowBy S E rho T pair (resetCutFrontier R E rho T L Jst + 1)
      (resetCutTime T L Jst + frontierSearchRiseBudget T G ΔF ρbar +
        frontierSearchRowBudget T G ΔF ρbar) :=
    (FirstHeightRowBy_def S E rho T pair _ _).mpr ⟨rStar, hrow, hfirst, by linarith⟩
  obtain ⟨w, hw, h1, h2, h3, htime⟩ := healing_reset_fields
    (T := T) (L := L) (Jst := Jst) (R := R) (S := S) (E := E)
    (rho := rho) (O := O) (pair := pair) (Ef := Ef) (HL := HL) (CL := CL) (K := K)
    (storeInv := storeInv) (emittedName := emittedName) hs hstart hJst firstRow
  exact ⟨w, hw, h1, h2, h3, lt_of_le_of_lt htime hlt⟩

end Source

end AvailableChain.FGCompose
end
