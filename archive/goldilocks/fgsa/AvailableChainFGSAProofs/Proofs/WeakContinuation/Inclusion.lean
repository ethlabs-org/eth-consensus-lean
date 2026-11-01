module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.ExactProposal
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.InclusionGate
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepService
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

/-! WC J3, plan §6.11; DC persistent proposal inclusion.
Earlier labels use retrospective transfer. Gates at one time use event induction. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.11; DC pending result: exact HEAD bounds label s−1. -/
theorem wc_prior_below_proposal
    (hs : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar rho.events.length) (pt : PtSP) (D : Block)
    (hpivot : WCProposalPivot p c E rho w iStar pt D)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s) →
      headAtLabel p c E rho y pt.s = some pt.P)
    (y : V) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s)) :
    Block.Preceq w.QStar pt.P ∧
      ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
        r < pt.s → Block.Preceq B pt.P := by
  have hDP := hpivot.headWalk y hy hJ pt.P (hhead y hy hJ)
  refine ⟨block_preceq_trans hpivot.greatestSeed hDP, ?_⟩
  intro j x r B hB hr
  by_cases hprev : r + 1 = pt.s
  · obtain ⟨k, _, hk⟩ := hi.retrospective j x r B hB y hy (hprev ▸ hJ)
    have he : headAtIdx p c E rho k (r + 1) = pt.P := by
      have hh := hhead y hy hJ
      rw [← hprev] at hh
      change (postClock E rho y (SA.voteTime p.toParams (r + 1))).map _ = _ at hh
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk.event] at hh
      dsimp only [headAtIdx]
      rw [hk.event]
      exact Option.some.inj hh
    exact he ▸ hk.covers
  · have hle : r ≤ pt.s - 2 := by simp only [Slot] at hr hprev ⊢; omega
    exact block_preceq_trans (hpivot.greatest j x r B hB hle) hDP

/-- WC J3, plan §6.11; DC cut order: every later gate input is after the seed. -/
private theorem wc_gate_after_cut (hs : V2.D.ScheduleWellFormed E rho)
    (hseed : WCSeed p c E rho w iStar) {i : Nat} {x : V} {s : Slot}
    (he : IsGateTick p c rho i x s) (hstart : w.u < s) : iStar ≤ i := by
  have ht : SA.gateTime p.toParams w.u < SA.gateTime p.toParams s := by
    have hc : (w.u : Time) < s := Nat.cast_lt.mpr hstart
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ < 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  rw [hseed.cut]
  refine (preIdx_le_afterTicksIdx E rho hs _).2.trans ?_
  have hm := V2.D.Engine.read_length_mono (rho := rho)
    (SA.gateTime p.toParams w.u) (SA.gateTime p.toParams s - 1) (by
      simp only [Time] at ht ⊢; omega)
  exact hm.trans (Nat.le_of_not_lt
    ((V2.D.Engine.index_lt_read_length_iff hs (SA.gateTime p.toParams s - 1) he).not.mpr (by
      change ¬ SA.gateTime p.toParams s ≤ SA.gateTime p.toParams s - 1
      exact not_le_of_gt (sub_lt_self _ (by decide : (0 : Time) < 1)))))

/-- WC J3, plan §6.11; DC gate event induction: earlier same-time results are exact.
Only the reviewed frame conclusion is supplied to this local construction. -/
theorem wc_proposal_gates [Fintype V]
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.RestartsAtWakes E rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho) (hmono : RMonoAll p c E rho)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (pt : PtSP) (hstart : w.u + 2 ≤ pt.s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s) →
      headAtLabel p c E rho y pt.s = some pt.P)
    (hQP : Block.Preceq w.QStar pt.P)
    (hprior : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r < pt.s → Block.Preceq B pt.P)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams pt.s)
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E rho (SA.voteTime p.toParams pt.s)).card) :
    ∀ i x, x ∈ rho.honest → enabledGateAt p c E rho i x pt.s →
      gateResultAt p c E rho i = some (some pt.P) ∧
        Block.Preceq pt.P (S_at p c E rho (i + 1) x) := by
  have hs := hvalid.toScheduleWellFormed
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro x hx hG
    have ht := hG.1
    have hiN := (List.getElem?_eq_some_iff.mp ht).1
    have hcut := wc_gate_after_cut hs hseed ht (by simp only [Slot] at hstart ⊢; omega)
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams pt.s)
    have hhistory : ∀ j y r B, WCResult p c E rho w iStar i j y r B →
        Block.Preceq B pt.P := by
      intro j y r B hB
      have hBN : WCResult p c E rho w iStar rho.events.length j y r B :=
        { hB with completed := hB.completed.trans hiN }
      have htime : SA.gateTime p.toParams r ≤ SA.gateTime p.toParams pt.s := by
        by_contra hn
        have hj := V2.D.Engine.eventIndex_lt_of_time_lt hs ht hB.event (lt_of_not_ge hn)
        exact (Nat.not_lt_of_ge hB.completed.le hj).elim
      have hle : r ≤ pt.s := by
        change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
          4 * p.Δ * (pt.s : Time) + 6 * p.Δ at htime
        have hc : (r : Time) ≤ pt.s := by nlinarith [p.deltaPos]
        exact_mod_cast hc
      rcases lt_or_eq_of_le hle with hr | rfl
      · exact hprior j y r B hBN hr
      · have heq := (ih j hB.completed y hB.honest (hB.enabled hs)).1
        have hBP := Option.some.inj (Option.some.inj (hB.value.symm.trans heq))
        exact hBP ▸ block_preceq_refl B
    have hF : Block.Preceq (F_at p c E rho i x) pt.P := by
      rcases (wc_finalHistoryAt hseed hi hcut hiN.le hx).origin with hQ |
        ⟨j, y, r, B, hB, hFB⟩
      · exact block_preceq_trans hQ hQP
      · exact block_preceq_trans hFB (hhistory j y r B hB)
    have head_eq (k : Nat) (y : V)
        (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams pt.s)))
        (hJ : joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s)) :
        headAtIdx p c E rho k pt.s = pt.P := by
      have hh := hhead y (hs.honest_only _ (List.mem_of_getElem? hk)) hJ
      change (postClock E rho y (SA.voteTime p.toParams pt.s)).map _ = _ at hh
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk] at hh
      dsimp only [headAtIdx]
      rw [hk]
      exact Option.some.inj hh
    have hreceipts := wc_gate_active_heads hvalid hnr hdelta hcstar hroots hsync hcumul
      hG hGST (by
        intro k y hk hJ j hji
        rw [head_eq k y hk hJ]
        exact block_preceq_trans (eraseFG_preceq (hmono j i x hx hji).1) hF)
      pt.P (by intro k y hk hJ; rw [head_eq k y hk hJ]; exact block_preceq_refl _)
    obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho hcstar pt.s ⟨hpart⟩
    have hraw := (wc_exact_gate_raw hvalid hcstar H hH hbatch (by
      intro q hq
      obtain ⟨K, t, hy, he, hv, hK, hslot, hvs, hbs, hFK, _⟩ :=
        hreceipts q ((hH q).mp hq).1 ((hH q).mp hq).2
      have hm : K ∈ (storeAt p c E rho i x).base.blocks := by
        have hm := (List.mem_filter.mp hK).1
        rwa [(clockPre_fields p _ _).2.1] at hm
      have heq := exactService_emitted_head_joined E rho hvalid pt.s pt.P hhead q hy K t
        (headTargetAtEmission_of_stored E rho (hroots.toNamedRootCollisionFree E rho)
          he rfl i x hm)
      subst K
      exact ⟨t, he, hv, hK, hslot, hvs, hbs, hFK⟩)).1
    have hvalue : gateResultAt p c E rho i = some (some pt.P) := by
      rw [wc_gate_raw_enabled hs hG, ← clockPre_fg]
      exact congrArg some hraw
    have hr : WCResult p c E rho w iStar rho.events.length i x pt.s pt.P :=
      ⟨hx, hcut, hiN, by simp only [Slot] at hstart ⊢; omega, ht, hvalue⟩
    exact ⟨hvalue, wc_gate_result_served hs hi hr⟩

/-- WC J3, plan §6.11; DC persistence: compose the finite suffix transitions. -/
theorem wc_suffix_mono (hs : V2.D.ScheduleWellFormed E rho)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    {i j : Nat} {x : V} (hcut : iStar ≤ i) (hij : i ≤ j)
    (hjN : j ≤ rho.events.length) (hx : x ∈ rho.honest) :
    Block.Preceq (S_at p c E rho i x) (S_at p c E rho j x) :=
  wc_output_mono_of_inv hs hseed hi i j x ⟨hcut, hij.trans hjN⟩
    ⟨hcut.trans hij, hjN⟩ hij hx

/-- WC J3, plan §6.11; DC six-Delta inclusion: serve both getters at every later read.
The sole producer premise is the reviewed live-frame Statement. -/
theorem wc_inclusion6_result [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCInclusion6ResultStatement p c E rho ΔF w iStar := by
  classical
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have hs := hvalid.toScheduleWellFormed
  have hi := hinv rho.events.length ⟨hseed.within, le_rfl⟩
  obtain ⟨D, hpivot⟩ := wc_proposalPivot ΔF w iStar hframeLive
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have had := wc_proposalAdmission ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot
  have hhead := wc_exactProposal ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot had
  have hGST : E.t_GST ≤ SA.voteTime p.toParams pt.s := by
    refine hseed.firstVoteAfterGST.trans ?_
    have hc : (w.u : Time) + 2 ≤ pt.s := by exact_mod_cast hstart
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (pt.s : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have hvg : SA.voteTime p.toParams pt.s + E.Δ ≤ SA.gateTime p.toParams pt.s := by
    rw [hdelta]
    change 4 * p.Δ * (pt.s : Time) + p.Δ + p.Δ ≤
      4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hpartS := hpart (SA.voteTime p.toParams pt.s) (by
    have hc : ((w.u + 1 : Nat) : Int) ≤ pt.s := Int.ofNat_le.mpr (by
      simp only [Slot] at hstart ⊢; omega)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (pt.s : Int) + p.Δ
    nlinarith [p.deltaPos]) ((le_add_of_nonneg_right (hdelta ▸ p.deltaPos.le)).trans
      (hvg.trans hgate))
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hpartS)
  obtain ⟨hy, hJ⟩ := Finset.mem_filter.mp hy
  have hslot : slotAt p (SA.voteTime p.toParams pt.s) = pt.s := by
    exact slotOf_offset p pt.s p.Δ p.deltaPos.le (by linarith [p.deltaPos])
  rw [hslot] at hJ
  obtain ⟨hQP, hprior⟩ := wc_prior_below_proposal hs hi pt D hpivot hhead y hy hJ
  have hgates := wc_proposal_gates hvalid hnr hdelta hcstar hroots ΔF hsync hcumul hmono
    hseed hi pt hstart hhead hQP hprior hGST hpartS
  have hpartG := hpart (SA.gateTime p.toParams pt.s) (by
    have hc : ((w.u + 1 : Nat) : Int) ≤ pt.s := Int.ofNat_le.mpr (by
      simp only [Slot] at hstart ⊢; omega)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]) hgate
  obtain ⟨z, j, hz, hGz, _⟩ := wc_joined_gate_witness hvalid hdelta pt.s hpartG hgate
  have hlabel : w.u < pt.s := by simp only [Slot] at hstart ⊢; omega
  have hresult : WCResult p c E rho w iStar rho.events.length j z pt.s pt.P :=
    ⟨hz, (wc_gate_cut_iff hs hseed hGz.1).mpr hlabel, (List.getElem?_eq_some_iff.mp hGz.1).1,
      hlabel, hGz.1, (hgates j z hz hGz).1⟩
  refine ⟨⟨j, z, hresult⟩, ?_⟩
  intro g hg t x ht hx
  have hN : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  have hW : WakesAppliedAtIdx E rho x (timeIdx rho t) t := by
    intro wake hw0 hwt hw
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hvalid.wake_restart x hx.1 wake hw0
      (hwt.trans ht.2) hw)
    exact ⟨k, (V2.D.Engine.index_lt_read_length_iff hs t hk).mpr hwt, hk⟩
  have hcut : afterTicksIdx rho (SA.gateTime p.toParams pt.s) ≤ timeIdx rho t := by
    exact (preIdx_le_afterTicksIdx E rho hs _).2.trans
      (V2.D.Engine.read_length_mono _ _ ht.1)
  have finish (k r : Nat) (C : Block)
      (hr : WCResult p c E rho w iStar rho.events.length k x r C)
      (hki : k < timeIdx rho t) (hPC : Block.Preceq pt.P C) :
      Block.Preceq pt.P (V2.D.outputAt E rho g x t) := by
    rw [fgsa_outputAt_eq_S_at E rho hs g hg x t]
    exact block_preceq_trans hPC (block_preceq_trans (wc_gate_result_served hs hi hr)
      (wc_suffix_mono hs hseed hi (hr.afterCut.trans (Nat.le_succ k))
        (Nat.succ_le_of_lt hki) hN hx.1))
  by_cases hmarker : ∀ wake, (storeAt p c E rho (timeIdx rho t) x).restartTime = some wake →
      wake ≤ slotStartZ p (pt.s : Int)
  · obtain ⟨k, hki, hG⟩ := wc_confirmedReader_public_gate hvalid hdelta hx hW hgate
      ht.1 hcut hmarker
    exact finish k pt.s pt.P ⟨hx.1, (wc_gate_cut_iff hs hseed hG.1).mpr hlabel,
      hki.trans_le hN, hlabel, hG.1, (hgates k x hx.1 hG).1⟩ hki (block_preceq_refl _)
  · push Not at hmarker
    obtain ⟨wake, hw, hlate⟩ := hmarker
    have hc := hx.2.2
    rw [hw] at hc
    obtain ⟨r, k, hwr, _, hki, hG, _, _⟩ := hc
    have hsr : pt.s < r := by
      change 4 * p.Δ * (pt.s : Int) < wake at hlate
      change wake ≤ 4 * p.Δ * (r : Int) at hwr
      have hh : (pt.s : Int) < r := by nlinarith [p.deltaPos]
      exact_mod_cast hh
    have hk := (wc_gate_cut_iff hs hseed hG.1).mpr (hlabel.trans hsr)
    obtain ⟨C, hC, _, _⟩ := hi.nonempty k x r hk (hki.trans_le hN) hx.1 hG (hlabel.trans hsr)
    have hr : WCResult p c E rho w iStar rho.events.length k x r C :=
      ⟨hx.1, hk, hki.trans_le hN, hlabel.trans hsr, hG.1, hC⟩
    exact finish k r C hr hki (hi.ordered j k z x pt.s r pt.P C hresult hr hsr)

/-- The public output service is the reader-scoped result projection. -/
theorem wc_inclusion6 [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCInclusion6Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  exact (wc_inclusion6_result ΔF w iStar hframeLive
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate).2

end AvailableChain.FGSA.Run
end
