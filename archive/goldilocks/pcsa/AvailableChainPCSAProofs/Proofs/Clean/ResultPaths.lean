module
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths
public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport

public section

/-! C6 ResultPaths: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A genuine result has an early resolved HEAD whose body extends the result. -/
theorem pcsa_result_early_support (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (a : Nat) (x : V) (hx : x ∈ rho.honest) (v : Time) (s : Slot) (X : Block)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st v).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s = some X) :
    ∃ i H, (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.earlyVotes p.toParams.engine (actView (clock p (V2.D.Run.stateBefore E rho a x).st
        v)) s ∧
      GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v))
        ⟨.seat s i, .head H.root⟩ = some H ∧ Block.Preceq X H := by
  let st := clock p (V2.D.Run.stateBefore E rho a x).st v
  let P := GridCO.cleanSupport p.toParams.engine (actView st) s
  have hf : st.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF x hx a).1
  have hd : st.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hmaj := pcsa_gate_result_majority p (actView st) _ X s hresult
  rw [pcsa_gate_score_of_genesis p st s X hf hd] at hmaj
  have hpos : 0 < GridCO.goldfishScore st.base.blocks P P X := by
    change GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView st) s) <
      2 * GridCO.goldfishScore st.base.blocks P P X at hmaj
    omega
  rw [Gen.AC.Root.vote_pool_score_card] at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hp := (Finset.mem_filter.mp hi).2
  have hcap : GridCO.equivocates P i = false :=
    FGSA.fgsa_cleanSupport_no_equivocation p (actView st) s i
  rw [hcap, Bool.false_or] at hp
  obtain ⟨o, ho, hoi, hsup⟩ := (Gen.AC.Root.vote_pool_support_witness st.base.blocks P i X).mp hp
  obtain ⟨H, hr, hXH⟩ := pcsa_read_vote_support_body E rho hF a x hx v o X hsup
  have hl : GridCO.headLabel? o = some s :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
  have he := FGSA.Run.resolvedHead_root _ _ hr
  change some r = some H.root at he
  have heq := Option.some.inj he
  subst r
  exact ⟨i, H, (List.mem_filter.mp ho).1, hr, hXH⟩
/-- In the delivery window: Every prefix of a result is retained in both later proposer and voter
trees. -/
theorem pcsa_result_prefixes_retained_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v u : Time) (s : Slot) (X : Block)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st v).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s = some X) :
    ∀ C, Block.Preceq C X →
      C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k y).st u)
        (fullTree p (clock p (V2.D.Run.stateBefore E rho k y).st u)) ∧
      C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k y).st u)
        (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho k y).st u).fg
          (voterBlocks p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))) := by
  obtain ⟨i, H, ho, hr, hXH⟩ := pcsa_result_early_support E rho hF a x hx v s X hresult
  have hm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  have ht : GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho a x).st v))
      ⟨.seat s i, .head H.root⟩ (SA.earlyTime p.toParams s) = true := (List.mem_filter.mp ho).2
  delta GridCO.resolvedBefore at ht
  rw [hr] at ht
  have hstamp : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base H <
      SA.earlyTime p.toParams s := of_decide_eq_true (Bool.and_eq_true_iff.mp ht).2
  have hrelay := pcsa_early_body_relay_frozen_win E rho h hF hD (hT := hT) a
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) x y hx hy s H v u hc (le_refl _) hm hstamp
  have hearly := hrelay.1
  rw [pcsa_clock_blocks] at hearly
  have hlate := pcsa_body_stateBefore_mono E rho h.noRestart y hk hearly
  have hclock : H ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.blocks := by
    rw [pcsa_clock_blocks]
    exact hlate
  intro C hCX
  have hCH := Gen.Pure.block_preceq_trans hCX hXH
  exact ⟨pcsa_full_read_prefix_mem E rho hF k y hy u H C hclock hCH,
    pcsa_frozen_read_prefix_mem E rho h hF _ k y hy s u H C (le_refl _) hk hearly hCH⟩
/-- Every prefix of a result is retained in both later proposer and voter trees. -/
theorem pcsa_result_prefixes_retained (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v u : Time) (s : Slot) (X : Block)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st v).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s = some X) :
    ∀ C, Block.Preceq C X →
      C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k y).st u)
        (fullTree p (clock p (V2.D.Run.stateBefore E rho k y).st u)) ∧
      C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k y).st u)
        (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho k y).st u).fg
          (voterBlocks p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))) :=
  pcsa_result_prefixes_retained_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy v u s X (pcsa_floor_early (pcsa_zero_le_proposal s)) hc hk hresult
end AvailableChain.PCSA.Run

end
