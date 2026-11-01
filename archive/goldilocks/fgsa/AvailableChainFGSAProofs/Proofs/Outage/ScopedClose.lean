module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedEarly
public import AvailableChainFGSAClaims.Statements.Packages.Outage
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Every scoped confirmed reader before restoration is covered. -/
theorem outage_confirmed_reader_before_restore {fast : Bool} {b₀ b₁ t : Time} {x : V}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t) (ht : t < b₁) :
    x ∈ coveredNodes p E rho fast b₀ := by
  rcases hReader.2 with hG | ⟨s, j, hEnd, hst, _⟩
  · exact hG
  · have hr := outage_first_restored_label p b₁
    have hEndR : SA.voteTime p.toParams (restoredLabel p b₁) ≤
        OutageEnd p (restoredLabel p b₁) := by
      change 4 * p.Δ * (restoredLabel p b₁ : Int) + p.Δ ≤
        4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ
      push_cast; nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) p.k]
    exact (not_lt_of_ge (((hr _).mpr le_rfl).trans (hEndR.trans (hEnd.trans hst))) ht).elim

/-- P-Cl1 supplies joined provenance at each actual duty, with a local prior proposal tick. -/
theorem outage_joined_provenance (hV : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ) :
    ArmingJoinedProvenance (c := c) E rho := by
  intro s i y hy hi hJ
  have hs := hV.toScheduleWellFormed
  have hw := arming_joined_window (c := c) hy hJ
  have ht : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    rw [arming_proposal_eq, arming_vote_eq]; push_cast; linarith [p.deltaPos]
  obtain ⟨it, hit⟩ := arming_tick_exists hs hdelta hy (4 * s) (arming_proposal_nat p s)
    (ht.trans (hs.in_horizon _ (List.mem_of_getElem? hi)).2)
    (hw.awake _ (by rw [arming_proposal_eq]; have := p.deltaPos; positivity) le_rfl ht)
  exact inclusion_relay_headVotes_provenance E rho hV i y s hi hJ hit

/-- A protected initial read selects an FG lift from its actual Clean origin. -/
theorem outage_protected_initial_lift {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hV : V2.D.ExecutionValid E rho)
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) :
    ∃ β : FGBlock (Fin p.n), eraseFG β = B := by
  obtain ⟨r, C, _, hOrigin, _, hBC⟩ := hc.origin
  obtain ⟨j, _, x, ht, hJ, hres⟩ := hOrigin
  have hraw := (arming_gateResult_tick hV.toScheduleWellFormed ⟨ht, hJ⟩).symm.trans
    ((gateResultAt_eq_gateResult p c E rho hV.toScheduleWellFormed ht).symm.trans hres)
  have he := Option.some.inj hraw
  let st := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams r)
  have hinv := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x)
    (SA.gateTime p.toParams r)
  obtain ⟨β, _, hβ⟩ := arming_lift_mem hinv (compat_of_confirmation p st hinv he).2 hBC
  exact ⟨β, hβ⟩

/-- If G is empty, the certificate's receiver obligations are empty. The actual last
Clean comparison and joined in-flight HEADs still bound the global source history. -/
theorem outage_empty_covered_certificate [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) (hEmpty : coveredNodes p E rho fast b₀ = ∅) :
    ∃ D Dh, ArmingSleepGateCert p c E rho fast T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  classical
  let l := (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat)
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨r, C, hr, hOrigin, hTime, hBC⟩ :=
    arming_protected_origin_on hs h.order.2.1 hState hHist hread hne
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg.trans (hTime.trans h.order.2.1)
  have hl := (arming_label p b₀ h6).1
  have hcut := (arming_label p b₀ h6).2
  have hcover : coverLabel p b₀ = l + 1 := rfl
  have hgap : r < l := by
    cases fast with
    | true => have hg := arming_fast_gap p r T b₀ hTime h.lag
              dsimp only [l, Slot] at *; omega
    | false => have hg := arming_slow_gap p r T b₀ hTime h.lag
               have := p.kLarge; dsimp only [l, Slot] at *; omega
  have hlpos : 1 ≤ l := by dsimp only [Slot] at *; omega
  obtain ⟨q, D, hql, hDq, hmax, hheads⟩ :
      ∃ q D, q ≤ l ∧ (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
        (∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
          Block.Preceq C D) ∧
        (∀ z, z ∈ rho.honest → joinedAt p E rho z (l + 1)
          (SA.voteTime p.toParams (l + 1)) → ∀ k,
          rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
          Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
            (SA.voteTime p.toParams (l + 1))) (l + 1))) := by
    by_cases hLast : ∃ C, (l, C) ∈ cleanResults p c E rho (timeIdx rho b₀)
    · obtain ⟨C, hC⟩ := hLast
      obtain ⟨D, hD, hmax⟩ := arming_last_max_on hHist hC
      exact ⟨l, D, le_rfl, hD, hmax,
        fun z hz hJ k hk => arming_head_ge_on hs htransfer hD hz hJ hk⟩
    · have hq : l - 1 + 1 = l := Nat.sub_add_cancel hlpos
      have hqcut : SA.gateTime p.toParams (l - 1) < b₀ :=
        ((arming_gate_lt_iff p _ l).mpr (by dsimp only [Slot] at *; omega)).trans_le hl
      obtain ⟨z, i, hG⟩ := arming_joined_gate_before h.sleepPre (l - 1) hqcut
      have hiCut := arming_lt_of_tick hs hG.1 hqcut.le
      obtain ⟨D₀, hD₀, _⟩ := hHist.nonempty i z (l - 1) hiCut hG
      have hD₀mem : (l - 1, D₀) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
        ⟨i, hiCut, z, hG.1, hG.2, hD₀⟩
      obtain ⟨D, hD, hmax⟩ := arming_last_max_on hHist hD₀mem
      obtain ⟨Dh, hDh⟩ := arming_sleep_comparison_lift hs hD
      have hBD : Block.Preceq B D := block_preceq_trans hBC
        (hmax r C hOrigin (by dsimp only [Slot] at *; omega))
      have hDne : D ≠ .genesis := fun hg =>
        hne (block_preceq_antisymm (hg ▸ hBD) (block_genesis_preceq B))
      refine ⟨l - 1, D, Nat.sub_le _ _, hD, ?_, ?_⟩
      · intro r C hC hrl
        have hrne : r ≠ l := fun he => hLast ⟨C, he ▸ hC⟩
        exact hmax r C hC (by dsimp only [Slot] at *; omega)
      · intro z hz hJ k hk
        have hHeads := arming_joined_head_from_previous (i := k) h hf hsrc hState htransfer
          hprov hDh hD hDne (by rw [hq]; exact hl) hmax hz
        have heq : l - 1 + 2 = l + 1 := by dsimp only [Slot] at *; omega
        rw [heq] at hHeads
        exact hHeads hk hJ
  obtain ⟨Dh, hDh⟩ := arming_sleep_comparison_lift hs hDq
  have hBD := block_preceq_trans hBC (hmax r C hOrigin hgap.le)
  have hentry := arming_sleep_entry_below hs (hState _ le_rfl) hDh hl hmax
  have hF : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D := by
    intro i y hi hy
    exact (arming_frame_below (hroots := h.pre.base.idealization) (hstrat := hf.strat)
      (hScope := hDh.symm ▸ rootScope_result h.pre.base.valid hDq)
      hs hf.store hf.frame.1 hsrc hDh hentry hi hy).1
  refine ⟨D, Dh, ⟨⟨r, C, hr, hOrigin, hTime, hBC⟩, hDh, hBD, ⟨q, hql, hDq⟩,
    hmax, hl, hcut, hcover, arming_source_below hs htsrc hl hmax, hheads, hF, ?_⟩⟩
  intro i y hi hyG
  rw [hEmpty] at hyG
  exact (Finset.notMem_empty y hyG).elim

section Protected

variable [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (hO : OutagePrem p c fast E rho ⟨T, b₀, b₁⟩ ΔF)
    (hf : FGFoundation p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)

include hO hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- O11-OUTAGE is proved in Close's OutagePrem context. G supplies protection;
source history supplies every honest F. No post-outage service is requested. -/
theorem outage_protected_scoped
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y)) :
    (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ y t, b₀ ≤ t → t < b₁ → outageConfirmedReader p c E rho fast b₀ b₁ y t →
        Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
      DutiesExtendScoped p c E rho fast B b₀ b₁ ∧
      (∀ t x, 0 ≤ t → t < b₁ → x ∈ rho.honest →
        Block.Compatible B (V2.D.outputAt E rho finalizedOut x t)) ∧
      (∀ t x, SA.gateTime p.toParams (coverLabel p b₀) ≤ t → t < b₁ →
        x ∈ coveredNodes p E rho fast b₀ →
        let st := storeAt p c E rho (timeIdx rho t) x
        Block.Preceq B (eraseFG st.fg.F) ∨
          ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
            SA.gateTime p.toParams (coverLabel p b₀) + L p ≤ dl ∧
            ((∃ X ∈ fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (controls p st).Z))) := by
  classical
  have hs := hO.set.pre.base.valid.toScheduleWellFormed
  have read {t : Time} (hdt : SA.gateTime p.toParams (l + 1) ≤ t) (htb : t < b₁) :=
    outage_armed_read_scoped hO.set hf hsrc htsrc hnamed hState hprov hne hc hβ
      (hdt.trans (htb.le.trans hO.set.order.2.2.2)) hdt htb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg y t hb ht hReader
    rw [fgsa_outputAt_eq_S_at E rho hs g hg]
    have hyG := outage_confirmed_reader_before_restore hReader ht
    by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
    · exact (read hdt ht).2 y hyG |>.1
    · exact arming_cover_sleep hO.set hState hHist hOutput hc y t hyG hReader.1
        (hc.gate_le_cut.trans hb) (lt_of_not_ge hdt) (ht.le.trans hO.set.order.2.2.2)
  · intro x t o hReader hb ht hem
    have hxG := outage_early_head_reader_covered hReader
      (ht.trans_le ((outage_first_restored_label p b₁ _).mpr (Nat.le_succ _)))
    by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
    · obtain ⟨i, hi, ho⟩ := hem
      by_cases heq : t = SA.gateTime p.toParams (l + 1)
      · constructor
        · intro H hH
          obtain ⟨s, _, _, _, he, _, _⟩ := arming_emit_head hO.set.pre.base.valid
            hReader.1.1 ⟨i, hi, ho⟩ hH
          exact (arming_gate_ne_vote p (l + 1) s (heq.symm.trans he)).elim
        · intro N hN
          obtain ⟨s, _, _, he, _, _⟩ := arming_emit_proposal hO.set.pre.base.valid
            hReader.1.1 ⟨i, hi, ho⟩ hN
          exact (arming_gate_ne_proposal p (l + 1) s (heq.symm.trans he)).elim
      have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i := by
        apply le_of_not_gt
        intro hn
        exact heq (le_antisymm (arming_tick_le hs hi
          (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)) hdt)
      obtain ⟨_, hDuty, _, _⟩ := outage_armed_induction_scoped hO.set hf hsrc htsrc hnamed
        hState hprov hne hc hβ (hdt.trans (hs.in_horizon _ (List.mem_of_getElem? hi)).2)
        (i + 1) (hI.trans (Nat.le_succ i))
        (Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr ht))
      exact hDuty.history i x t o (Nat.lt_succ_self i) hxG hdt hi ho
    · exact arming_pending_duties_sleep hO.set hf hsrc hState hprov hc hne
        x o t hReader.1.1 (hc.gate_le_cut.trans hb) (lt_of_not_ge hdt) hem
  · intro t x h0 ht hx
    have hFinal : V2.D.outputAt E rho finalizedOut x t =
        F_at p c E rho (timeIdx rho t) x := by
      change eraseFG (V2.D.Run.readAt E rho t x).st.fg.F = _
      rw [V2.D.Engine.readAt_eq_stateBefore hs t]; rfl
    rw [hFinal]
    by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
    · exact Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp ((read hdt ht).1 x hx)))
    · exact arming_compat hc.max_read hc.f_below x t hx h0 (lt_of_not_ge hdt)
        (ht.le.trans hO.set.order.2.2.2)
  · intro t x hdt ht hxG
    rw [hc.cover_label] at hdt ⊢
    exact (read hdt ht).2 x hxG |>.2

end Protected

end AvailableChain.FGSA.Run
end
