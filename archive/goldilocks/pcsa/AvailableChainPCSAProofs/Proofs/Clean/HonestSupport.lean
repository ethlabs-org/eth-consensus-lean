module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadBody
public import AvailableChainPCSAProofs.Proofs.Clean.HonestReceipt

public section

/-! C6 HonestSupport: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private theorem support_head_label_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot)
    (hl : GridCO.headLabel? o = some s) : ∃ i r, o = ⟨.seat s i, .head r⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> (delta GridCO.headLabel? at hl; cases hl)
  exact ⟨_, _, rfl⟩
/-- An uncapped early HEAD survives the clean-support filter. -/
theorem pcsa_early_uncapped_clean (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.earlyVotes p.toParams.engine v s)
    (hc : GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) i = false) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.cleanSupport p.toParams.engine v s := by
  apply List.mem_filter.mpr
  refine ⟨hm, ?_⟩
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro o ho hbad
  obtain ⟨hsame, hne⟩ := Bool.and_eq_true_iff.mp hbad
  have hl : GridCO.headLabel? o = some s :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  obtain ⟨j, r', rfl⟩ := support_head_label_shape o s hl
  have hji : j = i := by
    change (s == s && j == i) = true at hsame
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hsame).2
  subst j
  have he := Gen.AC.Root.vote_pool_clean_unique _ i hc _ _ ho
    (FGSA.fgsa_early_subset_late p v s hm) rfl rfl
  exact (bne_iff_ne.mp hne) he
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A late denominator has no cap on an honest seat. -/
theorem pcsa_honest_late_not_capped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (u : Time) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = false := by
  apply Gen.AC.Root.vote_pool_clean_subset _
    (GridCO.votesAt (V2.D.Run.stateBefore E rho k y).st.base s) i
    ?_ (pcsa_honest_head_pool_not_capped E rho hv k y s i hi)
  intro o ho
  have hm := (List.mem_filter.mp ho).1
  change o ∈ GridCO.votesAt (clock p (V2.D.Run.stateBefore E rho k y).st u).base s at hm
  delta GridCO.votesAt at hm
  rw [pcsa_clock_heads] at hm
  exact hm
/-- In the delivery window: Exact HEAD and body receipt put every honest HEAD into clean early
support. -/
theorem pcsa_honest_head_clean_support_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H)
    (hT : T₀ ≤ SA.voteTime p.toParams s) (hc : SA.earlyTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) (u : Time) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∧
    GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st u))
      ⟨.seat s i, .head H.root⟩ = some H := by
  obtain ⟨hh, ht⟩ := pcsa_honest_head_before_early_win E rho h hD (hT := hT) x y hy
      s i H hi hH hc k hk
  obtain ⟨hb, hbt⟩ := pcsa_honest_head_body_before_early_win E rho h hF hD (hT := hT) x y hy s H hH
      hc k hk
  have hr := pcsa_resolved_head_of_held_body E rho h hF k y hy s i H u hb
  have hslot := pcsa_honest_head_slot_le E rho h hF x s H hH
  obtain ⟨headRow, hheadRow⟩ := pcsa_head_stamp_lookup E rho k y ⟨.seat s i, .head H.root⟩ hh
  obtain ⟨bodyRow, hbodyRow⟩ := pcsa_body_stamp_lookup E rho k y H hb
  have hheads : (V2.D.Run.stateBefore E rho k y).st.base.voteStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)).voteStamp := by
    change _ <+: (clock p _ u).base.voteStamp
    rw [pcsa_clock_headStamps]
  have hbodies : (V2.D.Run.stateBefore E rho k y).st.base.blockStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)).blockStamp := by
    change _ <+: (clock p _ u).base.blockStamp
    rw [pcsa_clock_bodyStamps]
  have ht' := pcsa_stampVote_eq_of_prefix _ _ ⟨.seat s i, .head H.root⟩ headRow hheads hheadRow
  have hbt' := pcsa_stampBlock_eq_of_prefix _ _ H bodyRow hbodies hbodyRow
  refine ⟨?_, hr⟩
  apply pcsa_early_uncapped_clean
  · apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · change _ ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes
      rw [pcsa_clock_heads]
      exact hh
    · change (some s == some s) = true
      exact beq_self_eq_true _
    · delta GridCO.resolvedBefore
      rw [hr]
      apply Bool.and_eq_true_iff.mpr
      refine ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hslot, ?_⟩, ?_⟩
      · apply decide_eq_true
        rw [ht']
        exact ht
      · apply decide_eq_true
        rw [hbt']
        exact hbt
  · apply pcsa_honest_late_not_capped E rho h.valid k y u s i
    rw [hi]
    exact hH.1
/-- Exact HEAD and body receipt put every honest HEAD into clean early support. -/
theorem pcsa_honest_head_clean_support (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hy : y ∈ rho.honest) (s : Slot) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H)
    (hc : SA.earlyTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) (u : Time) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∧
    GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st u))
      ⟨.seat s i, .head H.root⟩ = some H :=
  pcsa_honest_head_clean_support_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) x y hy s i
    H hi hH (pcsa_floor_vote (pcsa_zero_le_proposal s)) hc k hk u
end AvailableChain.PCSA.Run

end
