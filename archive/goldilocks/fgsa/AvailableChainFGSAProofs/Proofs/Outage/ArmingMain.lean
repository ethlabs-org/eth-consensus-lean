module
public import AvailableChainFGSAProofs.Proofs.Outage.Arming
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingInput
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingOutput

public section

/-! Plan O-ARM §5: `fast_arming` and `slow_arming`. Both build the common
arming certificate at the cut label `l` of `b₀`; the mode enters only through
the label distance and the admission input of the pending gate. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem arming_comparison_lift {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {r : Slot} {D : Block} (hD : (r, D) ∈ cleanResults p c E rho i) :
    ∃ Dh : FGBlock (Fin p.n), eraseFG Dh = D := by
  obtain ⟨j, _, x, ht, hJ, hres⟩ := hD
  have hG : enabledGateAt p c E rho j x r := ⟨ht, hJ⟩
  have hraw := (arming_gateResult_tick hs hG).symm.trans
    ((gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres)
  have hc := Option.some.inj hraw
  let st := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams r)
  have hinv := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) (SA.gateTime p.toParams r)
  obtain ⟨Dh, _, he⟩ := (hinv.baseTree D).mp (compat_of_confirmation p st hinv hc).2
  exact ⟨Dh, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §4, §6. Class (iii). DC: INTENTIONAL; the arming certificate at
an arbitrary label `l` with d(l) ≤ b₀ < d(l + 1). The mode label distance and
the fast count are inputs; the slow window is proved here. -/
theorem arming_cert [Fintype V] {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (fast : Bool) (T b₀ b₁ ΔF : Time)
    (hvalid : V2.D.ExecutionValid E rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ)
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hpart : ∀ t : Time, 0 ≤ t → t < b₀ →
      (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card)
    (hTb : T ≤ b₀)
    (hbudget : b₁ - b₀ ≤ min p.η (L p))
    (x : V) (B : Block) (hx : x ∈ rho.honest)
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : fast = false → ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)
    (l : Slot) (hl : SA.gateTime p.toParams l ≤ b₀)
    (hcutl : b₀ < SA.gateTime p.toParams (l + 1))
    (hgap : ∀ s : Slot, SA.gateTime p.toParams s ≤ T →
      if fast then s + 2 ≤ l + 1 else s + p.k ≤ l + 1)
    (hfast : fast = true → SA.releaseThreshold p.toParams ≤
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card)
    (hroots : NamedRootCollisionFree p c E rho)
    (hReceipt : NamedReceiptRootCollisionFree p c E rho) (hstrat : RStrat p c E rho) :
    ∃ u s C iₛ D Dh, ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨u, s, C, iₛ, hu, hs1, hts, hpass, hres, hsT, hBC⟩ :=
    arming_origin hs hTb hnonempty hbelow hsOrigin hcleanGate hx hread hne
  have hgs := hgap s hsT
  have hsl : s < l := by
    have hk := p.kLarge
    cases fast with
    | true =>
      simp only [ite_true] at hgs
      simp only [Slot] at hgs ⊢
      omega
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hgs
      simp only [Slot] at hgs ⊢
      omega
  have hsb : SA.gateTime p.toParams s ≤ b₀ := hsT.trans hTb
  obtain ⟨Cl, hCl, ⟨k, hk, _⟩, _, _⟩ := hcleanGate l x hl hx
  obtain ⟨D, hDmem, hmax⟩ := arming_max_label hs hordered
    (fgsa_enabledGate_noRestart E rho hnr hk) hl hCl
  obtain ⟨Dh, hDh⟩ := arming_comparison_lift hs hDmem
  have hsI : iₛ < timeIdx rho b₀ := (arming_lt_timeIdx_iff hs b₀ hts).mpr hsb
  have hCD : Block.Preceq C D := hmax s C ⟨iₛ, hsI, u, hts,
    (fgsa_enabledGate_noRestart E rho hnr hts).2, hres⟩ hsl.le
  have hBD : Block.Preceq B D := block_preceq_trans hBC hCD
  have hDne : D ≠ .genesis := by
    rintro rfl
    exact hne (block_preceq_antisymm hBD (block_genesis_preceq B))
  have hentry := arming_entry_below hs hnamed hcleanGate hDh hl hmax
  have hprefix : ArmingPrefixState p c E rho l D Dh :=
    arming_prefix_state (hroots := hroots) (hstrat := hstrat)
      (hScope := hDh.symm ▸ rootScope_result hvalid hDmem) hs hnr hstore hframe hsrc hDh hl hcutl
        hentry hleaseOrigin hmax
  have hF : ∀ k y, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho k y) D := fun k y hk hy =>
    (hprefix k y hk (hk.trans (arming_idxBefore_le_length rho _)) hy).1
  have hev : SA.voteTime p.toParams (l + 1) < SA.earlyTime p.toParams (l + 1) :=
    (arming_vote_lt_early p (l + 1)).1
  have he : SA.earlyTime p.toParams (l + 1) ≤ b₀ := (arming_early_next p l).trans_le hl
  have hpartv : Gen.Pure.Batch
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card :=
    ⟨hpart _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity) (hev.trans_le he)⟩
  have hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1)) :=
    Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) b₀ _ _
      hhealthy (fgsaDelay_nonrow E.Δ ΔF)
      (by rw [hdelta, arming_vote_add]) he hcut.2
  have hbatchF : ArmingBatchState p c E rho l D := by
    intro y q hy hq haw
    obtain ⟨Cy, hCy, ⟨j, hj, _⟩, _⟩ := hcleanGate l y hl hy
    have hAw : E.awake y (SA.earlyTime p.toParams (l + 1)) = true := by
      rw [arming_early_next]
      exact hvalid.tick_awake y _ (List.mem_of_getElem? hj)
    obtain ⟨k, hk⟩ := arming_tick_exists hs hdelta hy (4 * (l + 1) + 2)
      (arming_early_nat p (l + 1)) (he.trans hcut.2) hAw
    obtain ⟨kk, hkk⟩ := arming_tick_exists hs hdelta hq (4 * (l + 1) + 1)
      (arming_vote_nat p (l + 1)) (hev.le.trans (he.trans hcut.2)) haw
    let K := headVote p ((fgsa p c).clock
      (rho.stateBefore E kk (rho.seatOf (.base (.head (l + 1))) q))
        (SA.voteTime p.toParams (l + 1))).st (l + 1)
    have hDK : Block.Preceq D K := arming_head_ge hs htransfer hDmem hq hkk
    have hkI : k ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) :=
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr
        ((arming_early_next p l).trans_lt
          ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)))).le
    obtain ⟨hem, hv, hvs, hK, hbs, hslot⟩ := inclusion_head_receipt_early
      E rho hvalid hnr hdelta hcstar (l + 1) hSync hk q hq haw hkk K rfl
      (block_preceq_trans (hF k y hkI hy) hDK) hReceipt
    exact ⟨K, k, hk, hem, hDK, hslot, hv, hK, hvs, hbs⟩
  have hC' : gateResult p c E rho u s = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hs hts).symm.trans hres
  have hS₀ : ∀ y, y ∈ rho.honest → Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D :=
    fun y hy => arming_S_cut hs hcutl hsOrigin hmax hy (fun q hq =>
      hF q y (hq.trans (arming_timeIdx_le_idxBefore rho hcutl)) hy)
  have hslowIn : fast = false → ∀ i y, IsGateTick p c rho i y (l + 1) → y ∈ rho.honest →
      p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
        GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i y)
          (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
        Block.Preceq B Ca := by
    intro hf
    subst hf
    simp only [Bool.false_eq_true, ite_false] at hgs
    exact arming_slow_saved hs hnr hordered (hsavedKeep rfl) hcleanGate hl hcutl hmax hu hs1
      hts hres hBC hgs hF
  refine ⟨u, s, C, iₛ, D, Dh, ?_⟩
  exact {
    origin_honest := hu
    origin_pos := hs1
    origin_tick := hts
    origin_passed := hpass
    origin_result := hres
    origin_time := hsT
    origin_cover := hBC
    max_lift := hDh
    max_read := hBD
    max_mem := hDmem
    max_le := hmax
    gate_le_cut := hl
    cut_lt_pending := hcutl
    early_eq_gate := arming_early_next p l
    end_lt_deadline := arming_end_lt_deadline p l b₀ b₁ hcutl hbudget
    mode_gap := hgs
    source_below := arming_source_below hs htsrc hl hmax
    entry_below := hentry
    prefix_state := hprefix
    healthy_batch := hbatchF
    pending_cover := arming_cover hs hnr hordered hmono hcleanGate hl hu hsl hC' hBC hF hS₀
    pending_duties := by
      intro y o t hy hlt htd hem
      constructor
      · intro H hH
        obtain ⟨r, _, i, _, rfl, hi, rfl⟩ := arming_emit_head hvalid hy hem hH
        obtain rfl := arming_vote_window p l r hlt htd
        exact block_preceq_trans hBD (arming_head_covers (hroots := hroots)
          (hReceipt := hReceipt) hvalid hnr hdelta
          hcstar hDh hDne
          hSync hpartv hprefix hbatchF hy hi)
      · intro N hX
        obtain ⟨r, i, _, rfl, hi, hpar⟩ := arming_emit_proposal hvalid hy hem hX
        obtain rfl := arming_proposal_window p l r hlt htd
        rw [hpar]
        exact block_preceq_trans hBD (arming_proposal_covers hvalid hnr hcstar hDh hpartv
          hprefix hbatchF hy hi)
    pending_compat := arming_compat hBD hF
    inflight_label := fun r h₁ h₂ => arming_inflight p (l + 1) r h₁ h₂
    inflight_heads := by
      intro y o t q H hy hem hauth hH
      obtain ⟨r, q', i, hauth', rfl, hi, rfl⟩ := arming_emit_head hvalid hy hem hH
      rw [hauth] at hauth'
      injection hauth' with hlab
      injection hlab with hlab
      injection hlab with hlab
      subst hlab
      exact block_preceq_trans hBD (arming_head_covers (hroots := hroots)
          (hReceipt := hReceipt) hvalid hnr hdelta hcstar
        hDh hDne
        hSync hpartv hprefix hbatchF hy hi)
    pending_input := arming_pending_input hvalid hnr hcstar hBD hpartv hprefix hbatchF fast
      hfast hslowIn }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §§6–8; plan O-ARM §5 `fast_arming`. Class (iii).
DC: INTENTIONAL; the fast arming certificate of a protected stable read. The
lag T + 4Δ ≤ b₀ puts the pending label at least two labels after the origin.
High participation before b₀ gives the fast count at the pending gate. -/
theorem fast_arming [Fintype V] {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (T b₀ b₁ ΔF : Time)
    (hvalid : V2.D.ExecutionValid E rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ)
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hpart : ∀ t : Time, 0 ≤ t → t < b₀ →
      (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card)
    (horder : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon)
    (hbudget : b₁ - b₀ ≤ min p.η (L p))
    (x : V) (B : Block) (hx : x ∈ rho.honest)
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)
    (hlag : T + 4 * p.Δ ≤ b₀)
    (hfastPart : ∀ t : Time, 0 ≤ t → t < b₀ →
      (p.n + 1) / 2 ≤ (Gen.V2.Duty.awakeHonest E rho t).card)
    (hroots : NamedRootCollisionFree p c E rho)
    (hReceipt : NamedReceiptRootCollisionFree p c E rho) (hstrat : RStrat p c E rho) :
    ArmingData p c E rho true T b₀ b₁ B := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨_, s, _, _, _, _, _, _, _, hsT, _⟩ :=
    arming_origin hs horder.2.1 hnonempty hbelow hsOrigin hcleanGate hx hread hne
  have h6 : 6 * p.Δ ≤ b₀ := by
    have h := hsT.trans horder.2.1
    rw [arming_gate_eq] at h
    have hd := p.deltaPos
    have : (0 : Time) ≤ 4 * p.Δ * (s : Time) := by positivity
    linarith
  obtain ⟨hl, hcutl⟩ := arming_label p b₀ h6
  rw [ArmingData_def]
  exact arming_cert (hroots := hroots) (hReceipt := hReceipt) (hstrat := hstrat)
    true T b₀ b₁ ΔF hvalid hcstar hnr hdelta hcut hhealthy hpart horder.2.1
    hbudget x B hx hread hne hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow
    hleaseOrigin (fun h => nomatch h) hsOrigin hmono hcleanGate _ hl hcutl
    (fun s hs => arming_fast_gap p s T b₀ hs hlag)
    (fun _ => hfastPart _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p _).trans_le hl)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §§6–8; plan O-ARM §5 `slow_arming`. Class (iii).
DC: INTENTIONAL; the slow arming certificate of a protected stable read. The
lag T + (L − 3Δ) ≤ b₀ puts the pending label at least k labels after the
origin. The saved Clean results give the slow window; no participation
threshold is used. -/
theorem slow_arming [Fintype V] {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (T b₀ b₁ ΔF : Time)
    (hvalid : V2.D.ExecutionValid E rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ)
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hpart : ∀ t : Time, 0 ≤ t → t < b₀ →
      (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card)
    (horder : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon)
    (hbudget : b₁ - b₀ ≤ min p.η (L p))
    (x : V) (B : Block) (hx : x ∈ rho.honest)
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)
    (hlag : T + (L p - 3 * p.Δ) ≤ b₀)
    (hroots : NamedRootCollisionFree p c E rho)
    (hReceipt : NamedReceiptRootCollisionFree p c E rho) (hstrat : RStrat p c E rho) :
    ArmingData p c E rho false T b₀ b₁ B := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨_, s, _, _, _, _, _, _, _, hsT, _⟩ :=
    arming_origin hs horder.2.1 hnonempty hbelow hsOrigin hcleanGate hx hread hne
  have h6 : 6 * p.Δ ≤ b₀ := by
    have h := hsT.trans horder.2.1
    rw [arming_gate_eq] at h
    have hd := p.deltaPos
    have : (0 : Time) ≤ 4 * p.Δ * (s : Time) := by positivity
    linarith
  obtain ⟨hl, hcutl⟩ := arming_label p b₀ h6
  rw [ArmingData_def]
  exact arming_cert (hroots := hroots) (hReceipt := hReceipt) (hstrat := hstrat)
    false T b₀ b₁ ΔF hvalid hcstar hnr hdelta hcut hhealthy hpart horder.2.1
    hbudget x B hx hread hne hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow
    hleaseOrigin (fun _ => hsavedKeep) hsOrigin hmono hcleanGate _ hl hcutl
    (fun s hs => arming_slow_gap p s T b₀ hs hlag) (fun h => nomatch h)

end AvailableChain.FGSA.Run
end
