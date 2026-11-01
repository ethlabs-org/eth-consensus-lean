module
public import AvailableChainPCSAProofs.Proofs.Clean.GateCounts
public import AvailableChainPCSAClaims.Statements.LaneReads

public section

/-! C6 GateReads: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private def CountData {n : Nat} (st : State n) :=
  (st.fg.F, st.base.blocks, st.base.votes, st.base.blockStamp,
    st.base.voteStamp, st.base.headDomain, st.base.now)
private theorem countData_normalize {n : Nat} (st : State n) :
    CountData (normalizeS st) = CountData st := by
  delta normalizeS
  split <;> rfl
private theorem countData_gate {n : Nat} (p : Params) (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    CountData (gateFrom p a cs rank st s) = CountData st := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => CountData acc = CountData st)
      · rfl
      · intro acc ha B _
        apply List.foldlRecOn (motive := fun acc : State n => CountData acc = CountData st)
        · exact ha
        · intro acc' ha' g _
          exact ha'
private theorem countData_clock (p : Params) (st : State p.n) (t : Time) :
    CountData (clock p st t) = CountData (clockPre p st t) := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def, countData_normalize]
    split
    · rfl
    · exact countData_gate p _ _ _ _ _
  · rfl
private theorem grid_confirmation_fields {n : Nat} (q : GridCO.Params)
    (v w : GridCO.State n .root) (a : Block) (s : Slot)
    (hb : v.blocks = w.blocks) (hv : v.votes = w.votes)
    (hbs : v.blockStamp = w.blockStamp) (hvs : v.voteStamp = w.voteStamp)
    (hd : v.headDomain = w.headDomain) (hn : v.now = w.now) :
    GridCO.confirmationFrom q a v s = GridCO.confirmationFrom q a w s := by
  have htree : GridCO.resolutionTree v = GridCO.resolutionTree w := by
    change v.headDomain.getD v.blocks = w.headDomain.getD w.blocks
    rw [hd, hb]
  have hhead (o : GridCO.Wire n .root) :
      GridCO.resolvedHead? v o = GridCO.resolvedHead? w o := by
    delta GridCO.resolvedHead?
    rw [htree, hb]
  have hsv (o : GridCO.Wire n .root) : GridCO.stampVote v o = GridCO.stampVote w o := by
    delta GridCO.stampVote
    rw [hvs, hn]
  have hsb (B : Block) : GridCO.stampBlock v B = GridCO.stampBlock w B := by
    delta GridCO.stampBlock
    rw [hbs, hn]
  have hbefore (o : GridCO.Wire n .root) (t : Time) :
      GridCO.resolvedBefore v o t = GridCO.resolvedBefore w o t := by
    delta GridCO.resolvedBefore
    rw [hhead]
    cases GridCO.resolvedHead? w o with
    | none => rfl
    | some B =>
      change (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
        decide (GridCO.stampVote v o < t) && decide (GridCO.stampBlock v B < t)) =
        (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
          decide (GridCO.stampVote w o < t) && decide (GridCO.stampBlock w B < t))
      rw [hsv, hsb]
  have hearly : GridCO.earlyVotes q v s = GridCO.earlyVotes q w s := by
    delta GridCO.earlyVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    exact hbefore o _
  have hlate : GridCO.lateVotes q v s = GridCO.lateVotes q w s := by
    delta GridCO.lateVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    rw [hsv]
  have hclean : GridCO.cleanSupport q v s = GridCO.cleanSupport q w s := by
    delta GridCO.cleanSupport
    rw [hearly, hlate]
  delta GridCO.confirmationFrom
  rw [hclean, hlate, htree, hb]
private theorem confirmation_of_countData {n : Nat} (p : Params) (st st' : State n)
    (s : Slot) (h : CountData st = CountData st') :
    SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s =
      SA.Root.confirmationFrom p.toParams (eraseFG st'.fg.F) (actView st') s := by
  change (_, _, _, _, _, _, _) = (_, _, _, _, _, _, _) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hF, hblocks, hvotes, hbstamps, hvstamps, hdomain, hnow⟩ := h
  rw [hF]
  apply grid_confirmation_fields
  · change st.base.blocks.filter (activeCompatible st) =
      st'.base.blocks.filter (activeCompatible st')
    delta activeCompatible
    rw [hblocks, hF]
  · exact hvotes
  · exact hbstamps
  · exact hvstamps
  · change some (st.base.headDomain.getD st.base.blocks) =
      some (st'.base.headDomain.getD st'.base.blocks)
    rw [hdomain, hblocks]
  · exact hnow
/-- The post-clock gate has the same raw confirmation as its pre-gate input. -/
theorem pcsa_clock_confirmation_eq_pre (p : Params) (st : State p.n) (t : Time) (s : Slot) :
    SA.Root.confirmationFrom p.toParams (eraseFG (clock p st t).fg.F) (actView (clock p st t)) s =
      SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F) (actView (clockPre p
        st t)) s :=
  confirmation_of_countData p _ _ s (countData_clock p st t)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A claim-level gate result has an exact indexed post-clock source. -/
theorem pcsa_gateResultAt_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (X : Block)
    (h : gateResultAt p c E rho x s = some (some X)) :
    ∃ k, rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      SA.Root.confirmationFrom p.toParams
        (eraseFG (clock p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).fg.F)
        (actView (clock p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s))) s =
          some X := by
  rw [pcsa_gateResultAt_def] at h
  obtain ⟨st, hst, hr⟩ := Option.map_eq_some_iff.mp h
  rw [pcsa_gateInAt_def] at hst
  obtain ⟨nd, hnd, he⟩ := Option.map_eq_some_iff.mp hst
  rw [pcsa_preTick_def] at hnd
  obtain ⟨k, hk, hnd⟩ := Option.map_eq_some_iff.mp hnd
  subst nd
  subst st
  refine ⟨k, V2.D.Run.tickIdx?_spec hk, ?_⟩
  rw [pcsa_clock_confirmation_eq_pre]
  exact hr
/-- Same-label results need a floor at the freeze time of label `s`. -/
theorem pcsa_clean_same_label_results_from_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X Y : Block) (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams
        s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hY : gateResultAt p c E rho y s = some (some Y)) : Block.Compatible X Y := by
  obtain ⟨a, ha, hX⟩ := pcsa_gateResultAt_source E rho x s X hX
  obtain ⟨b, hb, hY⟩ := pcsa_gateResultAt_source E rho y s Y hY
  exact pcsa_same_label_gate_results_win E rho h hF hD (hT := hT) a b x y hx hy s
    X Y hc ha hb hX hY
/-- In the delivery window: Same-label compatibility holds for the exact gate reader in the Clean
claim. -/
theorem pcsa_clean_same_label_results_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X Y : Block) (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams
        s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hY : gateResultAt p c E rho y s = some (some Y)) : Block.Compatible X Y :=
  pcsa_clean_same_label_results_from_freeze E rho h hF hD x y hx hy s X Y
    (pcsa_floor_freeze hT) hc hX hY
/-- Same-label compatibility holds for the exact gate reader in the Clean claim. -/
theorem pcsa_clean_same_label_results (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X Y : Block) (hc : SA.gateTime p.toParams s ≤ cut)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hY : gateResultAt p c E rho y s = some (some Y)) : Block.Compatible X Y := by
  obtain ⟨a, ha, hX⟩ := pcsa_gateResultAt_source E rho x s X hX
  obtain ⟨b, hb, hY⟩ := pcsa_gateResultAt_source E rho y s Y hY
  exact pcsa_same_label_gate_results E rho h hF hD a b x y hx hy s X Y hc ha hb hX hY
end AvailableChain.PCSA.Run

end
