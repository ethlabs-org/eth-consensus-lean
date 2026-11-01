module
public import AvailableChainFGSAProofs.Proofs.Healing.FrameRelay -- shake: keep (relay API)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt

public import AvailableChainFGSAProofs.Proofs.Healing.ReceiptProducers

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:2646–2649 (H.12); B13, B17.
DC: SAME the action of label u−1 follows both slot-u duty reads. -/
theorem healing_source_label_bound (p : Params) {s u : Slot}
    (hread : SA.gateTime p.toParams s ≤ SA.voteTime p.toParams u) :
    s + 2 ≤ u := by
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (u : Int) + p.Δ at hread
  have hd := p.deltaPos
  have hsu : (s : Int) + 1 < (u : Int) := by nlinarith
  have hsu' : (s : Int) + 2 ≤ (u : Int) := by omega
  exact_mod_cast hsu'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:2646–2649 (H.12); B17, B26.
DC: SAME the source early deadline is before the required freeze. -/
theorem healing_source_relay_deadline (p : Params) {s u : Slot} (hsu : s + 2 ≤ u) :
    SA.earlyTime p.toParams s ≤ SA.proposalTime p.toParams u - 6 * p.Δ ∧
      SA.proposalTime p.toParams u - 6 * p.Δ < SA.freezeTime p.toParams (u - 1) := by
  have hs : (s : Int) + 2 ≤ (u : Int) := by exact_mod_cast hsu
  have hu : (1 : Nat) ≤ u := by omega
  have hm : ((u - 1 : Nat) : Int) = (u : Int) - 1 := by omega
  change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (u : Int) - 6 * p.Δ ∧
    4 * p.Δ * (u : Int) - 6 * p.Δ < 4 * p.Δ * ((u - 1 : Nat) : Int) + 3 * p.Δ
  rw [hm]
  constructor <;> nlinarith [p.deltaPos]

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:2646–2649 (H.12); B13, B17.
DC: SAME event order bounds every earlier honest row, including controlling rows. -/
theorem healing_source_row_label (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x y : V} {r : Nat}
    {a : RowWire p.n} {u : Slot} {t : Time}
    (hi : rho.events[i]? = some (.tick x t))
    (ha : HonestRowBefore p c E rho i y r a)
    (ht : t = SA.proposalTime p.toParams u ∨ t = SA.voteTime p.toParams u) :
    r * p.R + 2 ≤ u := by
  obtain ⟨j, hji, hrow⟩ := ha
  have hj := hrow.2.1
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  rw [hie, hje] at hk
  have hb : p.actionTime r ≤ t := V2.D.Engine.time_le_of_key_le _ _ hk
  apply healing_source_label_bound p
  have hact : p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl
  rw [hact] at hb
  rcases ht with rfl | rfl
  · exact hb.trans (by
      change 4 * p.Δ * (u : Int) ≤ 4 * p.Δ * (u : Int) + p.Δ
      linarith [p.deltaPos])
  · exact hb

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:563–567 (IF.5), 2649–2652 (H.12); B13, B17.
DC: INTENTIONAL FG-SA TF is cumulative; finality changes the live window only.
`fgsa_store_cumulative` uses `clock_cumulative` and `process_cumulative`, including
the WindowStore admission and finalization steps. Thus the retention arm suffices. -/
theorem healing_tf_retention (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V)
    {B : FGBlock (Fin p.n)} (hB : B ∈ (storeAt p c E rho i x).fg.TF) :
    B ∈ (storeAt p c E rho j x).fg.TF ∨
      FGBlock.Preceq B (storeAt p c E rho j x).fg.F := by
  exact Or.inl ((fgsa_store_cumulative p c E rho hnr hij x).1 hB)

theorem healing_tf_retention_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i j : Nat} (hij : i ≤ j) (x : V)
    {B : FGBlock (Fin p.n)} (hB : B ∈ (storeAt p c E rho i x).fg.TF) :
    B ∈ (storeAt p c E rho j x).fg.TF ∨
      FGBlock.Preceq B (storeAt p c E rho j x).fg.F := by
  exact Or.inl ((fgsa_store_durable p c E rho hij x).1 hB)

omit [DecidableEq V] in
private theorem source_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le hab))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:563–567, 2649–2652; B17, B26.
DC: SAME retention at the strict-before read, including a changed receiver F. -/
theorem healing_source_path_retained (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {a b : Time} (hab : a ≤ b) (x : V) (K : FGBlock (Fin p.n))
    (hpath : Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) a x) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) b x := by
  rw [Gen.V2.Duty.HoldsBefore_def] at hpath ⊢
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hs] at hpath
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho b hs]
  intro B hBK
  exact (fgsa_store_cumulative p c E rho hnr (source_idx_mono rho hab) x).1 (hpath B hBK)

theorem healing_source_path_retained_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {a b : Time} (hab : a ≤ b) (x : V) (K : FGBlock (Fin p.n))
    (hpath : Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) a x) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) b x := by
  rw [Gen.V2.Duty.HoldsBefore_def] at hpath ⊢
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hs] at hpath
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho b hs]
  intro B hBK
  exact (fgsa_store_durable p c E rho (source_idx_mono rho hab) x).1 (hpath B hBK)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:620–631 (IF.6), 2649–2651 (H.12); B13, B17.
DC: SAME a fast source has an honest supporting HEAD at its source vote.
Assembly supplies `sourceDiscipline_tSrc` as `source`; no Foundations import. -/
theorem healing_source_supporter_head [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) {y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hK : actionSourceFG p c E rho y r = some (some K)) :
    ∃ j z W, z ∈ rho.honest ∧
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) ∧
      W ∈ (storeAt p c E rho j z).fg.TF ∧ FGBlock.Preceq K W := by
  have he : actionSource p c E rho y r = some (some (eraseFG K)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hK]
    rfl
  obtain ⟨X, _, _, hmem, _, _, hfast, _⟩ := source y r (eraseFG K) hy he
  obtain ⟨st, hst, hτ⟩ := hfast _ hmem
  rw [gateIn_def, preTick_def] at hst
  cases hi : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams (r * p.R)) with
  | none => simp only [hi, Option.map_none] at hst; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hst
    subst st
    obtain ⟨k, o, hh, ho, hk, hsup⟩ := healing_support_honest_seat rho
      hrec.base.cstar hrec.fault _ (r * p.R) (eraseFG K) hτ
    obtain ⟨H, hH, hHm, _, _, hm, hl⟩ := healing_support_clean_target E rho o ho
    obtain ⟨j, hj, hhead⟩ := healing_support_honest_head E rho hrec.base.valid hm hl hk hh
    let z : V := rho.seatOf (.base (.head (r * p.R))) k
    have heq : H = headVote p (clock p (storeAt p c E rho j z)
        (SA.voteTime p.toParams (r * p.R))) (r * p.R) :=
      stored_eq_headVote E rho hrec.base.idealization i y hHm j z
        (SA.voteTime p.toParams (r * p.R)) (r * p.R)
        (Option.some.inj ((resolvedHead_root _ o hH).symm.trans hhead))
    have hstored := headVote_stored p _ (storeBundle_postClock E rho j z
      (SA.voteTime p.toParams (r * p.R))).cstore
      (r * p.R)
    change headVote p (clock p (storeAt p c E rho j z)
      (SA.voteTime p.toParams (r * p.R))) (r * p.R) ∈
      (clock p (storeAt p c E rho j z) (SA.voteTime p.toParams (r * p.R))).base.blocks
      at hstored
    rw [← heq] at hstored
    change H ∈ (clock p (storeAt p c E rho j z) _).base.blocks at hstored
    rw [(clock_cumulative p _ _).2.1] at hstored
    obtain ⟨W, hW, hWH⟩ :=
      ((storeBundle_stateBefore E rho j z).cstore.baseTree H).mp hstored
    have hKW : Block.Preceq (eraseFG K) (eraseFG W) := by
      change Gen.AC.Root.voteSupports
        (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho i y)
          (SA.gateTime p.toParams (r * p.R))))) (eraseFG K) o = true at hsup
      rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hH] at hsup
      have hb := (Bool.and_eq_true_iff.mp hsup).2
      simpa only [hWH, decide_eq_true_eq, Block.Preceq] using hb
    refine ⟨j, z, W, hh, hj, hW, ?_⟩
    exact eraseFG_preceq_iff.mp hKW

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:2649–2652 (H.12), 563–567 (IF.5); B13, B17, B26.
DC: SAME relay before e_s and retain the full source path at the target freeze.
Assembly supplies `sourceDiscipline_tSrc` and `fgsa_rMono` as the named inputs.
Finality is compared at the target read, so it can change during transport. -/
theorem healing_source_body_relay [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    {y x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (_hgst : E.t_GST ≤ SA.voteTime p.toParams (r * p.R))
    {D : Time} (heD : SA.earlyTime p.toParams (r * p.R) ≤ D) (_hhor : D ≤ rho.horizon)
    (hF : FGBlock.Preceq (V2.D.Run.stateBeforeTime E rho D x).st.fg.F K)
    (hServices : ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      FGBlock.Preceq K W →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) D x := by
  obtain ⟨j, z, W, hz, hj, hW, hKW⟩ := healing_source_supporter_head E rho hrec source hy hK
  have hs := hrec.base.valid.toScheduleWellFormed
  have hFloor : FGBlock.Preceq
      (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W := by
    have hm := (mono (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (r * p.R)))
      (V2.D.Run.idxBefore rho D) x hx (source_idx_mono rho heD)).1
    change FGBlock.Preceq (rho.stateBefore E _ x).st.fg.F
      (rho.stateBefore E _ x).st.fg.F at hm
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hs,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hm
    exact KitFG.preceq_trans hm (KitFG.preceq_trans hF hKW)
  have hreceipt := healing_held_block_receipt_on p c E rho hrec.base.valid
    hrec.base.receiptIdealization W (SA.earlyTime p.toParams (r * p.R)) x hx
    (hServices j z W hz hj hW hKW hFloor)
  have hpath : Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF)
      (SA.earlyTime p.toParams (r * p.R)) x := by
    rw [Gen.V2.Duty.HoldsBefore_def]
    intro B hBK
    exact KitFG.ancestor_closed_of_parent_closed _
      (storeBundle_stateBeforeTime E rho _ x).cstore.fg.closed W hreceipt B
      (KitFG.preceq_trans hBK hKW)
  exact healing_source_path_retained_on E rho hs heD x K hpath

private theorem source_stamp_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {D : Time} (hD : 0 < D) (x : V) (b : Block)
    (hb : b ∈ (V2.D.Run.stateBeforeTime E rho D x).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho D x).st.base b < D :=
  fgsa_block_stamp_before_read E rho hs x D hD b hb

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:2649–2652 (H.12); B13, B17, B26.
DC: SAME the strict read excludes receipts at the freeze itself.
The named source and monotonicity inputs are `sourceDiscipline_tSrc` and `fgsa_rMono`. -/
theorem healing_source_body_stamps [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    {y x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams (r * p.R))
    {D : Time} (heD : SA.earlyTime p.toParams (r * p.R) ≤ D) (hhor : D ≤ rho.horizon)
    (hF : FGBlock.Preceq (V2.D.Run.stateBeforeTime E rho D x).st.fg.F K)
    (hServices : ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      FGBlock.Preceq K W →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd => ∀ B, FGBlock.Preceq B K →
      B ∈ nd.st.fg.TF ∧ GridCO.stampBlock nd.st.base (eraseFG B) < D) D x := by
  have hp := healing_source_body_relay E rho hrec source mono hy hx hK hgst heD hhor hF hServices
  rw [Gen.V2.Duty.HoldsBefore_def] at hp ⊢
  intro B hBK
  have hb := hp B hBK
  refine ⟨hb, source_stamp_before E rho hrec.base.valid.toScheduleWellFormed ?_ x
    (eraseFG B) (((storeBundle_stateBeforeTime E rho D x).cstore.baseTree _).mpr
      ⟨B, hb, rfl⟩)⟩
  have hpos : 0 < SA.earlyTime p.toParams (r * p.R) := by
    change 0 < 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  exact hpos.trans_le heD

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:2651–2652 (H.12 old bodies), 563–567 (IF.5); B13, B17, B26.
DC: SAME honest acceptance before GST relays by GST+Δ.
Assembly supplies `fgsa_rMono` as `mono`. The acceptance is an actual proposal
handler call, as supplied by `fgsa_block_stamp_source`, not an assumed receipt. -/
theorem healing_source_old_body [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (_mono : RMonoAll p c E rho)
    {j : Nat} {y x : V} {t D : Time} {s : Slot} {N : NamedProposal p.n} {K : FGBlock (Fin p.n)}
    (_hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (_ha : V2.D.Run.acceptsAt E rho j y (ofWire p ⟨.proposer s, .proposal N⟩) t)
    (_ht : t < E.t_GST) (hKb : eraseFG K = N.erase)
    (_hd : E.t_GST + p.Δ ≤ D) (_hhor : D ≤ rho.horizon)
    (_hF : FGBlock.Preceq (V2.D.Run.stateBeforeTime E rho D x).st.fg.F K)
    (hService : Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      t D x)) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) D x := by
  obtain ⟨hService⟩ := hService
  obtain ⟨Y, hY, hYb⟩ := hService.proposal hrec.base.valid.toScheduleWellFormed hx
    hrec.base.receiptIdealization
  have hYK : Y = K := eraseFG_injective (hYb.trans hKb.symm)
  subst Y
  rw [Gen.V2.Duty.HoldsBefore_def]
  intro B hBK
  exact KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D x).cstore.fg.closed K hY B hBK

/-- Recovery produces delivery for the selected source body at its actual vote tick. -/
theorem healing_source_delivery_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {j : Nat} {z x : V} {s : Slot}
    {W : FGBlock (Fin p.n)} (hz : z ∈ rho.honest) (hx : x ∈ rho.honest)
    (hj : rho.events[j]? = some (.tick z (SA.voteTime p.toParams s)))
    (hW : W ∈ (storeAt p c E rho j z).fg.TF)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.earlyTime p.toParams s ≤ rho.horizon)
    (hFloor : FGBlock.Preceq (rho.stateBeforeTime E
      (SA.earlyTime p.toParams s) x).st.fg.F W) :
    TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams s) x := by
  have he : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  rw [← he] at hhor hFloor ⊢
  exact healing_target_service_of_tick E rho hrec hz hx hj
    (((storeBundle_stateBefore E rho j z).cstore.baseTree _).mpr ⟨W, hW, rfl⟩)
    hpub hSync hhor (Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq hFloor)))

end AvailableChain.FGSA.Run
end
