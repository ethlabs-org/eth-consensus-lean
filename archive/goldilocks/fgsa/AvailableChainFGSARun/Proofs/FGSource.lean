module
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def source_read (p : Params) (st : State p.n) : Option (SimplexFG.FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

private theorem source_read_eq : @FGSA.fgSource = @source_read := rfl

theorem fgsa_clock_restartTime (st : State p.n) (t : Time) :
    (FGSA.clock p st t).restartTime = st.restartTime := by
  have hp : (clockPre p st t).restartTime = st.restartTime := by
    unfold clockPre
    dsimp only
    split_ifs <;> rfl
  have hg (st : State p.n) (s : Slot) :
      (gateStep p st s).restartTime = st.restartTime := by
    unfold gateStep
    rw [normalizeS_fields]
    dsimp only
    split_ifs <;> rfl
  unfold FGSA.clock
  dsimp only
  split
  · rw [hg, hp]
  · exact hp

private theorem source_gate_eq (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.gateTime p.toParams s) =
      gateStep p (clockPre p st (SA.gateTime p.toParams s)) s := by
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  have ht : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hs : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    rw [ht, Int.mul_ediv_cancel_left _ (by positivity), Int.toNat_natCast]
  unfold FGSA.clock
  dsimp only
  rw [hs]
  have hnonneg : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by rw [ht]; positivity
  simp only [hnonneg, decide_true, beq_self_eq_true, Bool.true_and, ite_true]

/-- A scheduled unjoined FG action reads the empty fast set written by its gate. -/
theorem fgsa_fgAction_unjoined_source_none
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hvalid : V2.D.ExecutionValid E rho) {i r : Nat} {v : V}
    (hi : rho.events[i]? = some (.tick v (p.actionTime r)))
    (hj : joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v)
      (p.actionTime r)).st = false) :
    fgSource p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v)
      (p.actionTime r)).st = none := by
  let st := (V2.D.Run.stateBefore E rho i v).st
  let pre := clockPre p st (p.actionTime r)
  have hn : GridCO.savedGenuine st.base (r * p.R) = none :=
    fgsa_gate_fresh E rho hvalid.toScheduleWellFormed hi
  have hnp : GridCO.savedGenuine pre.base (r * p.R) = none := by
    unfold GridCO.savedGenuine
    rw [clockPre_genuine]
    exact hn
  have hnow : (FGSA.clock p st (p.actionTime r)).base.now = p.actionTime r :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i v) _).1
  have hrt := fgsa_clock_restartTime st (p.actionTime r)
  change joinedNow p (FGSA.clock p st (p.actionTime r)) = false at hj
  have hjoin : joinedNow p pre = false := by
    rw [clockPre_joined]
    simpa only [joinedNow, hrt, hnow] using hj
  have hf := (gateStep_unjoined p pre (r * p.R) hnp hjoin).2.1
  have hnone : st.fastWrite.find? (fun row => row.1 == r * p.R) = none := by
    apply List.find?_eq_none.mpr
    intro row hr he
    have hd := (cstoreInv_stateBefore E rho i v).fastDom.2 row.1 (List.mem_map_of_mem hr)
    rw [beq_iff_eq.mp he, hn] at hd
    exact Bool.noConfusion hd
  have hfw : fastWriteAt (FGSA.clock p st (p.actionTime r)) (r * p.R) = some [] := by
    have hgate : FGSA.clock p st (p.actionTime r) = gateStep p pre (r * p.R) :=
      source_gate_eq st (r * p.R)
    rw [hgate]
    change ((gateStep p pre (r * p.R)).fastWrite.find? (fun row => row.1 == r * p.R)).map
      Prod.snd = some []
    rw [hf]
    dsimp only [pre]
    rw [clockPre_fastWrite, List.find?_append, hnone]
    simp
  have hround := (fgsa_action_slot_round (p := p) (c := c)
    (V2.D.Run.stateBefore E rho i v) r).2
  change p.round ((FGSA.clock p st (p.actionTime r)).slot p) = r at hround
  change fgSource p (FGSA.clock p st (p.actionTime r)) = none
  rw [source_read_eq]
  unfold source_read
  dsimp only
  rw [hround]
  rw [hfw]
  simp only [Option.getD_some, List.not_mem_nil, decide_false, Bool.false_and,
    Bool.false_eq_true, Finset.filter_false]
  change SimplexFG.pickPair (∅ : Finset (SimplexFG.FGBlock (Fin p.n))) _ = none
  exact KitFG.pickPair_empty _

end AvailableChain.FGSA.Run
end
