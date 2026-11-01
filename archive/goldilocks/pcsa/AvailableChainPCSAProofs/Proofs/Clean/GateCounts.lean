module
public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport
public import AvailableChainPCSAProofs.Proofs.Clean.CommonResolution

public section

/-! C6 GateCounts: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private theorem gate_score_seats (p : Params) (tree : List Block)
    (v : GridCO.State p.n .root) (s : Slot) (X : Block) :
    GridCO.goldfishScore tree (GridCO.cleanSupport p.toParams.engine v s)
      (GridCO.cleanSupport p.toParams.engine v s) X =
    ((GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
      (fun i => Gen.AC.Root.poolSupports tree (GridCO.cleanSupport p.toParams.engine v s) i X =
        true)).card := by
  rw [Gen.AC.Root.vote_pool_score_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  rw [FGSA.fgsa_cleanSupport_no_equivocation]
  rfl
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: Every early input seat appears in the late denominator of every honest
gate. -/
theorem pcsa_early_input_gate_relay_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (o : GridCO.Wire p.n .root) (i : Fin p.n) (v : Time)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (ho : o ∈ GridCO.earlyVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s)
    (hi : GridCO.headSeat? o = some i) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true := by
  obtain ⟨hm, hr⟩ := List.mem_filter.mp ho
  have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp hm).2
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
  have hstamp : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ < SA.earlyTime p.toParams s := by
    delta GridCO.resolvedBefore at hr
    cases hd : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v))
        ⟨.seat s i, .head r⟩ with
    | none => rw [hd] at hr; cases hr
    | some B =>
      rw [hd] at hr
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).2
  have hfreeze : SA.earlyTime p.toParams s ≤ SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    linarith
  have hgate : SA.freezeTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s + E.Δ) ≤ k := by
    apply Nat.le_of_not_gt
    intro hh
    exact not_lt_of_ge hgate
      ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hh)
  exact pcsa_frozen_input_relay_late_win E rho h hD (hT := hT) a k x y hx hy s i r v _ hc hidx
    (List.mem_filter.mp hm).1 (lt_of_lt_of_le hstamp hfreeze)
/-- Every early input seat appears in the late denominator of every honest gate. -/
theorem pcsa_early_input_gate_relay (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (o : GridCO.Wire p.n .root) (i : Fin p.n) (v : Time)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (ho : o ∈ GridCO.earlyVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s)
    (hi : GridCO.headSeat? o = some i) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true :=
  pcsa_early_input_gate_relay_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy s
    o i v (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hk ho hi
/-- In the delivery window: Actual same-label honest gate results are compatible by their receipt
counts. -/
theorem pcsa_same_label_gate_results_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a b : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X Y : Block) (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams
        s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hb : rho.events[b]? = some (.tick y (SA.gateTime p.toParams s)))
    (hX : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hY : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s))) s = some
        Y) :
    Block.Compatible X Y := by
  let stx := clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)
  let sty := clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s)
  let Px := GridCO.cleanSupport p.toParams.engine (actView stx) s
  let Py := GridCO.cleanSupport p.toParams.engine (actView sty) s
  let Lx := GridCO.lateVotes p.toParams.engine (actView stx) s
  let Ly := GridCO.lateVotes p.toParams.engine (actView sty) s
  let SX := (GridCO.seats p.n Px).toFinset.filter
    (fun i => Gen.AC.Root.poolSupports stx.base.blocks Px i X = true)
  let SY := (GridCO.seats p.n Py).toFinset.filter
    (fun i => Gen.AC.Root.poolSupports sty.base.blocks Py i Y = true)
  have score (k : Nat) (z : V) (hz : z ∈ rho.honest) (B : Block) :
      SA.Root.prefixSupport p.toParams
        (actView (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s))) s B =
      ((GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s)))
          s)).toFinset.filter
        (fun i => Gen.AC.Root.poolSupports
          (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s)).base.blocks
          (GridCO.cleanSupport p.toParams.engine
            (actView (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s))) s)
              i B = true)).card := by
    have hf : (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s)).fg.F =
      .genesis := by
      rw [pcsa_body_clock_fg]
      exact (hF z hz k).1
    have hd : (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams
      s)).base.headDomain = none := by
      rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
    rw [pcsa_gate_score_of_genesis p _ s B hf hd, gate_score_seats]
  have hmajX := pcsa_gate_result_majority p (actView stx) _ X s hX
  have hmajY := pcsa_gate_result_majority p (actView sty) _ Y s hY
  rw [score a x hx X, Gen.AC.Root.vote_pool_voterCount_card] at hmajX
  rw [score b y hy Y, Gen.AC.Root.vote_pool_voterCount_card] at hmajY
  have transport (k l : Nat) (z w : V) (hz : z ∈ rho.honest) (hw : w ∈ rho.honest)
      (hl : rho.events[l]? = some (.tick w (SA.gateTime p.toParams s))) :
      (GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k z).st (SA.gateTime p.toParams s)))
          s)).toFinset ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho l w).st (SA.gateTime p.toParams s)))
          s)).toFinset := by
    apply Gen.AC.Root.vote_pool_seats_backward
    intro o ho i hi
    exact pcsa_early_input_gate_relay_win E rho h hD (hT := hT) k l z w hz hw s o i _ hc hl
        (List.mem_filter.mp
      ho).1 hi
  have hleft : SX ∪ SY ⊆ (GridCO.seats p.n Lx).toFinset :=
    Finset.union_subset ((Finset.filter_subset _ _).trans (transport a a x x hx hx ha))
      ((Finset.filter_subset _ _).trans (transport b a y x hy hx ha))
  have hright : SX ∪ SY ⊆ (GridCO.seats p.n Ly).toFinset :=
    Finset.union_subset ((Finset.filter_subset _ _).trans (transport a b x y hx hy hb))
      ((Finset.filter_subset _ _).trans (transport b b y y hy hy hb))
  obtain ⟨i, hi⟩ := Gen.Pure.two_majorities_intersect hleft hright hmajX hmajY
  obtain ⟨hix, hiy⟩ := Finset.mem_inter.mp hi
  obtain ⟨ox, hox, hoxi, hoxX⟩ := (Gen.AC.Root.vote_pool_support_witness stx.base.blocks Px i X).mp
    (Finset.mem_filter.mp hix).2
  obtain ⟨oy, hoy, hoyi, hoyY⟩ := (Gen.AC.Root.vote_pool_support_witness sty.base.blocks Py i Y).mp
    (Finset.mem_filter.mp hiy).2
  have heq : ox = oy := by
    rcases pcsa_early_input_gate_relay_win E rho h hD (hT := hT) a b x y hx hy s ox i _ hc hb
      (List.mem_filter.mp hox).1 hoxi with hm | hcap
    · exact pcsa_clean_input_unique_late p (actView sty) s oy i hoy hoyi ox hm hoxi
    · have hf := pcsa_clean_input_not_capped p (actView sty) s oy i hoy hoyi
      rw [hcap] at hf
      cases hf
  subst oy
  obtain ⟨Hx, hrx, hpx⟩ := pcsa_read_vote_support_body E rho hF a x hx _ ox X hoxX
  obtain ⟨Hy, hry, hpy⟩ := pcsa_read_vote_support_body E rho hF b y hy _ ox Y hoyY
  have hsame := pcsa_run_common_head_resolution E rho h a b x y hx hy _ _ ox Hx Hy hrx hry
  subst Hy
  exact Gen.Pure.block_compatible_of_common hpx hpy
/-- Actual same-label honest gate results are compatible by their receipt counts. -/
theorem pcsa_same_label_gate_results (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a b : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X Y : Block) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hb : rho.events[b]? = some (.tick y (SA.gateTime p.toParams s)))
    (hX : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hY : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho b y).st (SA.gateTime p.toParams s))) s = some
        Y) :
    Block.Compatible X Y :=
  pcsa_same_label_gate_results_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a b x y hx
    hy s X Y (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc ha hb hX hY
end AvailableChain.PCSA.Run

end
