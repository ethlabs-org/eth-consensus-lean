module
public import AvailableChainFGSAClaims.Statements.Healed

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- H.11 μ (21:1579–1582), P3 §4.6 L6. The height set is bounded;
its supremum is attained if nonempty, and μ is at least one and every member. -/
theorem muOf_spec : BddAbove (oldRowHeights p c E rho) ∧
    ((oldRowHeights p c E rho).Nonempty →
      sSup (oldRowHeights p c E rho) ∈ oldRowHeights p c E rho) ∧
    1 ≤ muOf p c E rho ∧
    (∀ h ∈ oldRowHeights p c E rho, h ≤ muOf p c E rho) ∧
    (∀ n, 1 ≤ n → (∀ h ∈ oldRowHeights p c E rho, h ≤ n) → muOf p c E rho ≤ n) := by
  classical
  let emitted := (List.range rho.events.length).flatMap (V2.D.Run.emitsAt E rho)
  let ht : Obj p → Nat := fun o => match o.payload with
    | .row a => ((namedEntry a.height_pair).map Prod.fst).getD 0
    | _ => 0
  have hsub : oldRowHeights p c E rho ⊆ ((emitted.map ht).toFinset : Set Nat) := by
    intro h hh
    obtain ⟨j, y, r, a, e, ha, hp, _⟩ := hh
    obtain ⟨hj, he⟩ := ha.2
    have hlt : j < rho.events.length := by
      by_contra hn
      have hz := List.getElem?_eq_none (l := rho.events) (by omega : rho.events.length ≤ j)
      rw [hz] at hj
      cases hj
    have hem : ofRow p a ∈ emitted :=
      List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hlt, he⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨ofRow p a, hem, ?_⟩
    change ((namedEntry a.payload.height_pair).map Prod.fst).getD 0 = h
    rw [hp]
    rfl
  have hfin := (emitted.map ht).toFinset.finite_toSet.subset hsub
  have hb := hfin.bddAbove
  rw [muOf_def]
  refine ⟨hb, fun hn => hn.csSup_mem hfin, le_max_left _ _, ?_, ?_⟩
  · intro h hh
    exact (le_csSup hb hh).trans (le_max_right _ _)
  · intro n hn hu
    exact max_le hn (csSup_le' hu)

/-- H0 has one reset round and one first honest proposal slot
(21 H.11:1572–1595; H.18:2868–2876). Consumer: H0.tstar_eq. -/
theorem H0.time_unique {w w' : HealingWitness}
    (h : H0 p c E rho w) (h' : H0 p c E rho w') : tstar p w = tstar p w' := by
  have hrG : w.rG = w'.rG := Nat.le_antisymm (h.rG_first _ h'.rG_after) (h'.rG_first _ h.rG_after)
  have hcut : w.u₀ = w'.u₀ := by rw [h.cut, h'.cut, hrG]
  have hM : w.M = w'.M := by rw [h.frontier, h'.frontier, hcut]
  have hr : w.rStar = w'.rStar := Nat.le_antisymm
    (h.reset_first _ (hM.symm ▸ h'.reset_row)) (h'.reset_first _ (hM ▸ h.reset_row))
  have hs : w.sStar = w'.sStar := by rw [h.label, h'.label, hr]
  have hu : w.u = w'.u := Nat.le_antisymm
    (h.proposal_first _ _ (hs.symm ▸ h'.proposal_lower) h'.proposal)
    (h'.proposal_first _ _ (hs ▸ h.proposal_lower) h.proposal)
  rw [tstar_def, tstar_def]
  exact congrArg (SA.gateTime p.toParams) hu

/-- P3 D44: the joined kernel reads the full H0 time (21:2868–2876).
Full H0 comes from ResetArrivalFullStatement at the H.18 horizon. -/
theorem H0.tstar_eq {w : HealingWitness} (h : H0 p c E rho w) :
    tstarOf p c E rho = some (tstar p w) := by
  classical
  have hex : ∃ w, H0 p c E rho w := ⟨w, h⟩
  change (if h : ∃ w, H0 p c E rho w then some (tstar p (Classical.choose h)) else none) = _
  rw [dite_eq_left hex]
  exact congrArg some (H0.time_unique p c E rho (Classical.choose_spec hex) h)

/-- T-SMONO is the H4 projection (01:141–142; 21:3116–3123), P3 A.7.
Consumers: F6, F8, FF5 and FF6. -/
theorem HealAC.tsMono {w : HealingWitness} (h : HealAC p c E rho w) :
    ScopedMono (confirmedReaderIdx p c E rho)
      (S_at p c E rho) (HealSuffix p c rho (tstar p w)) :=
  h.h4.2.2.1

/-- T-EXACT is the H3 projection (01:143–149; 21:3109–3114), P3 A.7.
Consumers: FF1, F1, F3 and F6. The gate is within the finite horizon. -/
theorem HealAC.tExact {w : HealingWitness} (h : HealAC p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hs : w.sStar + 2 ≤ v) (hh : SA.gateTime p.toParams v ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest)
    (hreader : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams v)) (SA.gateTime p.toParams v)) :
    (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
      (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)) :=
  ((h.h3 v Q hp hs).2 hh x hx hreader).2.2.2

end AvailableChain.FGSA.Run
end
