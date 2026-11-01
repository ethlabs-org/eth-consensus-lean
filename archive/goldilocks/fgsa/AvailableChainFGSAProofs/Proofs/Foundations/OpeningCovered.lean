module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- SO-COV at an exact-service frontier gate, blueprint 21 H.7 / H.9 and
HG.1. This is the q = r * R, height(Qfg) = m case of TCommon and TFrontier.
ExactService supplies the actual source; the selector supplies its domain.
The phase cap and source height supply the live-floor bound. IF.3(b) and
send-once history then supply an earlier-or-current complete matching row.
No client permission or fresh-emission premise is used.
DC: INTENTIONAL, fixedRootWindowRows_of_source has a fixed-root source;
this proof uses the actual W source and the existing exact-service contract.
The height premise is bridge-equal to the consumer's hOf premise. -/
theorem openingCovered_frontier_gate (G ΔF : Time) (h : HealingPrem p c G ΔF E rho ())
    (u : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (r : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n))
    (hGST : E.t_GST ≤ u) (hQ : eraseFG Qfg = Q)
    (hh : (heightView p Qfg).h = m)
    (hservice : ExactService p c E rho (r * p.R) Q)
    (hu : u ≤ SA.proposalTime p.toParams (r * p.R))
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    OpeningCovered p c E rho r Q := by
  have hut : u < p.actionTime r := by
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) at hu
    change u < 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    have := p.deltaPos
    linarith
  intro x hx
  have hreader := rowPermission_confirmedReader_gate h.set x hx (r * p.R)
    (hGST.trans hu) hphase.2.1
  have hs := (hservice.2 hphase.2.1 x hx hreader).2.2.2.2 r rfl
  change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = some (some Q) at hs
  obtain ⟨src, hsrc, he⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨K, hKsrc, hKe⟩ := Option.map_eq_some_iff.mp he
  subst src
  have hKQ : K = Qfg := eraseFG_injective (hKe.trans hQ.symm)
  subst K
  rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hsrc; contradiction
  | some i =>
    have ht := V2.D.Run.tickIdx?_spec hi
    let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
    have hnd : postClock E rho x (p.actionTime r) = some nd := by
      rw [postClock_def, preTick_def, hi]; rfl
    have hsel : FGSA.fgSource p nd.st = some Qfg := by
      simpa only [hi, Option.map_some, Option.some.injEq] using hsrc
    have hread : actionSourceFG p c E rho x r = some (some Qfg) := by
      rw [actionSourceFG_def, hnd]; exact congrArg some hsel
    have hd : Qfg ∈ FGSA.fullTree p nd.st := by
      rw [fgSource_eq_jointSource] at hsel
      have hm := (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsel).1).1
      exact hm
    have hil : timeIdx rho u ≤ i := by
      apply Nat.le_of_not_gt
      intro hil
      have hb := (V2.D.Engine.index_lt_read_length_iff
        h.set.base.valid.toScheduleWellFormed u ht).mp hil
      exact (not_le_of_gt hut) hb
    have hih : i ≤ timeIdx rho (p.actionTime r) :=
      Nat.le_of_lt ((V2.D.Engine.index_lt_read_length_iff
        h.set.base.valid.toScheduleWellFormed (p.actionTime r) ht).mpr le_rfl)
    have hil' : V2.D.Run.idxBefore rho u ≤ i := (idxBefore_le_timeIdx rho u).trans hil
    have hH := (hphase.2.2.2 i x hil' hih hx).1
    have hH' : (FGSA.controls p nd.st).H = m := by
      change (FGSA.clock p _ _).fg.h_max = m
      rw [FGSA.clock_fg]
      exact hH
    have hlo : (FGSA.controls p nd.st).lo ≤ (heightView p Qfg).h := by
      rw [hh]
      exact (KitFG.Controls.lo_le_H _).trans_eq hH'
    obtain ⟨j, rSent, a, hr, ha, hn⟩ := rowPermission_covered E rho h.set.base h.set.fault
      x hx r nd hnd Qfg hread hd hlo (h.set.awake x hx _ (hGST.trans hut.le) hphase.2.1)
    exact ⟨Qfg, nd, j, rSent, a, hnd, hread, hd, hQ ▸ Gen.Pure.block_preceq_refl _, hr, ha, hn⟩
end AvailableChain.FGSA.Run
