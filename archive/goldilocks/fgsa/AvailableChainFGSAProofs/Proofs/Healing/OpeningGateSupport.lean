module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportGate
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAProofs.Proofs.Shared.Count

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.2 S1, 02 §5.4:531–541; plan H-GATE §3C (support count).
DC: INTENTIONAL if every honest HEAD of label w covers B and the gate F is at or below B,
the honest HEAD seats are clean early supporters of B at an honest gate of w. Their number
reaches the release threshold under RecoverySleep₂ after the previous-slot cutoff.
The honest receiver uses an enabled gate, fresh HEAD services, target services and
an exact read epoch. Awake at the vote alone does not supply these facts. -/
theorem opening_gate_support [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {w : Slot} {B : Block} (hcut : E.t_GST ≤ slotStartZ p ((w : Int) - 1))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams w)
    (hhor : SA.gateTime p.toParams w ≤ rho.horizon)
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {j : Nat} {y : V} (_hy : y ∈ rho.honest) (ht : IsGateTick p c rho j y w)
    (hScope : GateReceiptScope E rho j y w)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho j y).fg.F) B) :
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w B := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hC := hrec.base.cstar
  have hvg : SA.voteTime p.toParams w ≤ SA.gateTime p.toParams w := by
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams w + E.Δ ≤ SA.gateTime p.toParams w := by
    rw [hDelta]
    change 4 * p.Δ * (w : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorv : SA.voteTime p.toParams w ≤ rho.horizon := hvg.trans hhor
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  have hcovK (q : Fin p.n) (hq : rho.seatOf (.base (.head w)) q ∈ rho.honest) (K : Block)
      (t : Time) (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head w)) q)
        (ofHead p ⟨.seat (.head w) q, K.root⟩) t K) : Block.Preceq B K :=
    hcov _ hq K (healing_support_emitted_head (c := c) E rho hS w q K t he)
  have hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B := by
    refine ⟨fun q hq _ K he => ?_, fun q hq _ K he => hcovK q hq K _ he⟩
    rw [clockPre_fg]
    exact block_preceq_trans hFB (hcovK q hq K _ he)
  let H : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head w)) k ∈ rho.honest)
  have hHmem (k : Fin p.n) : k ∈ H ↔ rho.seatOf (.base (.head w)) k ∈ rho.honest := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head w)) k) :=
    hC (.base (.head w)) trivial
  have hHcard : H.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective H hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hHmem k).mp hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr hz, rfl⟩
  have hJoined := healing_recovery_joinedHonest E rho hrec w hcut hgst hhorv
  obtain ⟨hfast, hbatchJoined⟩ :=
    healing_recovery_joined_counts E rho hrec w hcut hgst hhorv
  have hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
    rw [hJoined, ← hHcard] at hbatchJoined
    exact hbatchJoined
  have hreceipts := fgsa_gateReceipt_on E rho hE hDelta hC w hSync ht B hgeom hScope
    hrec.base.receiptIdealization
  let vw := actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))
  have hsupp (k : Fin p.n) (hk : k ∈ H) :
      Gen.AC.Root.poolSupports vw.blocks (GridCO.cleanSupport p.toParams.engine vw w) k B = true
          := by
    have hq := (hHmem k).mp hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _, hBK⟩ :=
      hreceipts.2.2 k hq (healing_recovery_joined E rho hrec hq hcut hgst hhorv)
    exact fgsa_active_support_of_receipt E rho hE j y w k K B t hh he hv hK hslot hvs hbs hBK
  have hc := Gen.AC.Root.batch_counts vw.blocks (GridCO.lateVotes p.toParams.engine vw w)
    (GridCO.cleanSupport p.toParams.engine vw w) (GridCO.cleanSupport p.toParams.engine vw w)
    H H.card (Gen.V2.Duty.faulty rho).card B
    (fun _ ho => fgsa_early_subset_late p vw w (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p vw w k)
    hsupp (fgsa_late_rest_bound_joined E rho hC hE j y w H
      (fun k hk _ => (hHmem k).mpr hk)) hbatch
  have hcount : H.card ≤ SA.Root.prefixSupport p.toParams vw w B := by
    have heq : SA.Root.prefixSupport p.toParams vw w B =
        GridCO.goldfishScore vw.blocks (GridCO.cleanSupport p.toParams.engine vw w)
          (GridCO.cleanSupport p.toParams.engine vw w) B :=
      actView_score p (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j y) _)
        (by rw [clockPre_headDomain];
            exact base_headDomain_none p (reachable_stateBefore E rho j y)) _ _ B
    rw [heq]
    exact (hc.2.2.1 B (block_preceq_refl B)).1
  rw [hJoined, ← hHcard] at hfast
  exact hfast.trans hcount

/-- The reset supplies the selected-voter cutoff and the receiver gate epoch.
Fresh HEAD and target services remain tied to their actual emitted objects. -/
theorem opening_gate_support_of_reset [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (hreset : H0Reset p c E rho w) {s : Slot}
    (hs : w.sStar + 1 ≤ s) (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    {B : Block}
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq B K)
    {j : Nat} {y : V} (hy : y ∈ rho.honest) (ht : IsGateTick p c rho j y s)
    (hServices : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) y) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams s) y)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho j y).fg.F) B) :
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams s))) s B := by
  have hcut := healing_reset_vote_cutoff hreset hs
  have hgate := healing_reset_gate_cutoff hreset ((Nat.le_add_right w.sStar 1).trans hs)
  have hgst : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hgate.trans
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hScope := healing_recovery_gate_scope E rho hrec hy ht hgate hgst hhor hServices
  exact opening_gate_support E rho hrec hcut hgst hhor hcov hy ht hScope hFB

end AvailableChain.FGSA.Run
end
