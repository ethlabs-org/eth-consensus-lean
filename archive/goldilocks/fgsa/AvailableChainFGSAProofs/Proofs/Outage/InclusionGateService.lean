module
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBounds
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:438–441 (h_s honest supporters vs ≤ a others); plan I-GATE, G4. Class (iii).
DC: INTENTIONAL; the fresh HEAD seat bijection transfers the awake count.
Strict-before participation gives Batch without a fast threshold. -/
theorem inclusion_awake_seat_batch [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF) (s : Slot)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s)) ∧
      H.card = (joinedHonest p E rho (SA.voteTime p.toParams s)).card ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head s)) q) :=
    hset.pre.base.cstar (.base (.head s)) trivial
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  have himage : H.image (rho.seatOf (.base (.head s))) =
      joinedHonest p E rho (SA.voteTime p.toParams s) := by
    ext y
    change y ∈ H.image (rho.seatOf (.base (.head s))) ↔
      y ∈ rho.honest.filter (fun v => joinedAt p E rho v
        (slotAt p (SA.voteTime p.toParams s)) (SA.voteTime p.toParams s))
    rw [hslot, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (joinedHonest p E rho (SA.voteTime p.toParams s)).card :=
    (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  have hnonneg : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  exact ⟨H, hH, hc, ⟨hc ▸ hset.sleepPre.sleepPre.joinedPartBefore _ hnonneg
    ((fgsa_vote_lt_gate p s).trans_le hhor)⟩⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:418–458; plan I-GATE, G5. Class (iii).
DC: INTENTIONAL; a strict majority gives the exact raw result. Compatible
leases let the gate advance S to P. No lease admission test is needed. -/
theorem inclusion_gate_exact [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x pt.s)
    (hstrat : RStrat p c E rho) :
    gateResult p c E rho x pt.s = some (some pt.P) ∧
      (fgsaAC E rho).raw i pt.s x = some pt.P ∧ gatePassedAt p c E rho i ∧
      S_at p c E rho (i + 1) x = pt.P := by
  have ht := hG.1
  let st := storeAt p c E rho i x
  let pre := clockPre p st (SA.gateTime p.toParams pt.s)
  let v := actView pre
  have hE := hset.pre.base.valid
  have hs := hE.toScheduleWellFormed
  have hhead := inclusion_headAtLabel (hstrat := hstrat) E rho ΔF hset hInputs
    hstore hframe hsrc hordered
    hnonempty
    htransfer hleases hrows pt hprop hhor
  obtain ⟨hF, _, hS, hleasesP, _, _⟩ := inclusion_preGate_bounds (hstrat := hstrat)
    E rho ΔF hset hInputs hHistory
    hstore hframe
    hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hx hG
  have hgeom : GateReceiptGeometry E rho pre pt.s pt.P := by
    constructor
    · intro q hy _ K he
      rw [exactService_emitted_head_joined E rho hset.pre.base.valid pt.s pt.P hhead q hy K _ he]
      exact hF
    · intro q hy _ K he
      rw [exactService_emitted_head_joined E rho hset.pre.base.valid pt.s pt.P hhead q hy K _ he]
      exact block_preceq_refl _
  have hScope := inclusion_gate_services hset.pre.base (inclusion_clean_synchrony hset)
    hx hG (inclusion_clean_vote_gst hset pt.s) (by
      intro q K hy hK
      have hTarget := hK
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hK
      have hAw := hE.tick_awake _ _ (List.mem_of_getElem? hk)
      change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) K
      simpa only [pre, clockPre_fg] using hgeom.target_floor q hy hAw K
        hTarget)
  have hvd : SA.voteTime p.toParams pt.s + E.Δ ≤ SA.gateTime p.toParams pt.s := by
    rw [hset.pre.base.delta]
    change 4 * p.Δ * (pt.s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o)
    rho.horizon _ _ hset.pre.healthy (fgsaDelay_nonrow E.Δ ΔF) hvd hhor le_rfl
  obtain ⟨H, hH, _, hbatch⟩ := inclusion_awake_seat_batch E rho ΔF hset pt.s hhor
  obtain ⟨hr, _, _, _⟩ := exactService_gate_raw_of_head_on
    (hroots := hset.pre.base.receiptIdealization)
    E rho hE hset.pre.base.delta hset.pre.base.cstar pt.s pt.P hhead hsync ht hgeom
    hScope H hH hbatch
  have hv : { v with early := st.base.early } = (fgsaAC E rho).gateView i x pt.s :=
    fgsa_clockPre_gateView p st pt.s
  have hrawEq : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v pt.s =
      (fgsaAC E rho).raw i pt.s x := by
    rw [clockPre_fg]
    have he := congrArg (fun u =>
      SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) u pt.s) hv
    exact he
  have hraw := hrawEq.symm.trans hr
  have hguard : ∀ lease ∈ ((fgsaAC E rho).gateView i x pt.s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) pt.P := by
    intro lease hl
    have hobl := congrArg GridCO.State.obligations hv
    rw [← hobl] at hl
    exact Bool.or_eq_true_iff.mpr (Or.inl (hleasesP lease hl))
  have hanchor : Block.Preceq ((fgsaAC E rho).anchor i x) pt.P := by
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) pt.P
    simpa only [clockPre_fg] using hF
  have hout := (fgsa_S_eq_of_exact E rho hs i pt.s x pt.P hx ht hG hraw hguard
    (fun hPS => block_preceq_antisymm hS hPS) hanchor).1
  refine ⟨?_, hraw, ?_, hout⟩
  · exact (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans
      ((inclusion_gate_raw_at_tick E rho hs hG).trans (congrArg some hr))
  · refine ⟨x, pt.s, hG, ?_, pt.P, hr, ?_⟩
    · unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact fgsa_gate_fresh E rho hs ht
    · apply List.any_eq_false.mpr
      intro row hrow
      have hc : Block.compatible row.1 pt.P = true :=
        Bool.or_eq_true_iff.mpr (Or.inl (hleasesP row hrow))
      simp only [hc, Bool.not_true, Bool.false_eq_true, not_false_eq_true]

end AvailableChain.FGSA.Run
end
