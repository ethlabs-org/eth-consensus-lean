module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6 -- shake: keep H6 port
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConeHeads

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3.
DC: SAME common height pivot across the proposer and all honest HEAD reads. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3.
DC: SAME maximum live H across the proposer and every honest HEAD read. -/
def maxLiveH (s : Slot) (ip : Nat) (x : V) : Nat :=
  (insert (ip, x) (((Finset.range rho.events.length).product rho.honest).filter
    (fun q => rho.events[q.1]? = some (.tick q.2 (SA.voteTime p.toParams s))))).sup
      (fun q => (storeAt p c E rho q.1 q.2).fg.h_max)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3.
DC: SAME maximum equation for the actual read indices. -/
theorem maxLiveH_def (s : Slot) (ip : Nat) (x : V) :
    maxLiveH p c E rho s ip x =
      (insert (ip, x) (((Finset.range rho.events.length).product rho.honest).filter
        (fun q => rho.events[q.1]? = some (.tick q.2 (SA.voteTime p.toParams s))))).sup
          (fun q => (storeAt p c E rho q.1 q.2).fg.h_max) := by rfl

private theorem cone_cross_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin
    p c E rho) {i : Nat} {x : V}
    {W : FGBlock (Fin p.n)} {m : Nat} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hm : 1 ≤ m)
    (hmW : m < (heightView p W).h) :
    ∃ Y, FGBlock.Preceq Y W ∧ (heightView p Y).h = m ∧
      ∃ K s, SourceBefore p c E rho i K s ∧ (heightView p K).h = m ∧
        (heightView p K).T_h = Y := by
  classical
  obtain ⟨Y, hYW, hYm, Q, hQ, hrows⟩ :=
    (fgCertificateLaws p).height.height_crossing W m hm hmW
  let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) := fun k =>
    if hk : k ∈ Q then
      (Classical.choose (hrows k hk), Classical.choose (Classical.choose_spec (hrows k hk)))
    else (.genesis, ⟨k, .empty, none⟩)
  have hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧
      (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
      (rows k).2.height_pair.matchesEntry m Y.root = true := fun k hk => by
    simpa only [rows, hk, ↓reduceDIte] using
      Classical.choose_spec (Classical.choose_spec (hrows k hk))
  obtain ⟨h1, -, -⟩ := origin i x W hx hW
  obtain ⟨k, hk, y, r, wire, ⟨j, hj, hrow⟩, -, -, K, G, hK, hn, -⟩ :=
    h1 m Y Q rows hm hmW hYW hYm hQ hr
  obtain ⟨-, -, -, hmatch⟩ := hr k hk
  refine ⟨Y, hYW, hYm, K, r * p.R, ⟨j, y, r, wire, hj, hrow, hK, rfl⟩, ?_⟩
  cases hp : (rows k).2.height_pair with
  | empty =>
    rw [hp] at hmatch
    exact absurd hmatch Bool.false_ne_true
  | vote h e t =>
    rw [hp] at hmatch hn
    obtain ⟨rfl, rfl⟩ : h = m ∧ e = Y.root := of_decide_eq_true hmatch
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hn)
    exact ⟨h1.symm, rootScope_eq hroots (rootScope_entry (rootScope_source hrow.1 hK))
      (rootScope_ancestor (rootScope_store hx hW) hYW) h2.symm⟩

section Frame
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

variable (mono : RMonoAll p c E rho) (xing : RXing p c E rho)
    (origin : RQCOrigin p c E rho)
include hrec cap source rowCovered h0r mono xing origin

omit rowCovered origin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3.
DC: SAME reset copy in each later honest read, from healing_resetTransferCore. -/
theorem postReset_cone_reset_held {s : Slot} (hs : w.sStar + 2 ≤ s)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x t)) (hlo : SA.proposalTime p.toParams s ≤ t) :
    ∃ C ∈ (storeAt p c E rho j x).fg.TF, eraseFG C = w.CStar := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hqt : SA.releaseTime p.toParams w.sStar < t := by
    have h := postReset_release_before_proposal p w hs
    linarith [p.deltaPos]
  have hhor : SA.releaseTime p.toParams w.sStar ≤ rho.horizon :=
    hqt.le.trans (hS.in_horizon _ (List.mem_of_getElem? ht)).2
  have heq : SA.voteTime p.toParams (w.sStar + 1) =
      SA.releaseTime p.toParams w.sStar := by
    change 4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ =
      4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    push_cast
    ring
  have hawake := hrec.awake x hx (SA.voteTime p.toParams (w.sStar + 1)) (by
    apply h0r.synchronous.trans
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤
      4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]) (heq ▸ hhor)
  obtain ⟨jq, hjq⟩ := healing_support_vote_tick E rho hS hrec.base.delta hx (w.sStar + 1)
    (heq ▸ hhor) hawake
  rw [heq] at hjq
  have hjqj : jq ≤ j := (repair_idx_lt E rho hS hjq ht hqt).le
  have htransfer := healing_resetTransferCore_recovery p c E rho hrec mono xing cap source w h0r
  rw [ResetTransferCore_def] at htransfer
  obtain ⟨C, hC, he⟩ := (htransfer hhor jq x hx hjq).1
  exact ⟨C, (fgsa_store_durable p c E rho hjqj x).1 hC, he⟩

omit mono in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3/C4.
DC: SAME each active root below the preceding honest HEADs.
postReset_keep_roots supplies the reset or high-source alternative. -/
theorem postReset_root_heads_at_cut (i : Nat)
    (hraw : PostResetRawTransfer p c E rho w i)
    {s : Slot} {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x t)) (hji : j ≤ i)
    (htype : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    {C : FGBlock (Fin p.n)} (hC : C ∈ (storeAt p c E rho j x).fg.TF)
    (he : eraseFG C = w.CStar)
    (hCHeads : ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
      Block.Preceq w.CStar H)
    (hcut : timeIdx rho (SA.voteTime p.toParams (s - 1)) ≤ i) :
    ∀ B ∈ [(R_at p c E rho j x).Z, (storeAt p c E rho j x).fg.F],
      ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
        Block.Preceq (eraseFG B) H := by
  intro B hB y hy H hH
  rcases postReset_keep_roots (hroots := hrec.base.idealization) p c E rho
    hrec.base.valid.toScheduleWellFormed xing origin
      h0r hx hC he B hB with hBC | ⟨K, u, hK, hhK, hBK⟩
  · exact block_preceq_trans (he ▸ eraseFG_preceq hBC) (hCHeads y hy H hH)
  · obtain ⟨k, z, r, a, hkj, ha, hsrc, hu⟩ := hK
    have hgap := healing_source_row_label E rho hrec.base.valid.toScheduleWellFormed ht
      ⟨k, hkj, ha⟩ htype
    have hselected : SelectedBefore p c E rho i K u :=
      selectedBefore_of_sourceBefore p c E rho ⟨k, z, r, a, hkj.trans_le hji, ha, hsrc, hu⟩
    exact block_preceq_trans (eraseFG_preceq hBK)
      (postReset_source_heads_at_cut p c E rho hrec cap source rowCovered h0r i hraw
        hselected hhK (by rw [hu]; simp only [Slot] at *; omega) hcut y hy H hH)

end Frame
section Pivot
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
include hrec mono emittedNonempty emittedName writes xing origin h0r

private theorem cone_source_held (source : TSrc p c E rho)
    {K : FGBlock (Fin p.n)} {u : Slot} {l j : Nat} {x : V} {t : Time}
    (hK : SourceBefore p c E rho l K u) (hhK : high p w K)
    (_hlower : w.sStar ≤ u) (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x t))
    (hdeadline : SA.freezeTime p.toParams u ≤ t) :
    K ∈ (storeAt p c E rho j x).fg.TF := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hLoss := healing_loss_service_scope_recovery E rho hrec mono source
    emittedNonempty emittedName
  have highCompat := postReset_high_compatible_all p c E rho hrec hLoss mono
    emittedNonempty emittedName writes xing origin h0r
  have resetCompat := postReset_reset_compatible_all p c E rho hrec hLoss mono
    emittedNonempty emittedName writes xing origin h0r
  have lowFinality : ∀ {a : Nat} {y : V} {D : FGBlock (Fin p.n)}, y ∈ rho.honest →
      afterTicksIdx rho (p.actionTime w.rStar) ≤ a →
      D ∈ (storeAt p c E rho a y).fg.TF →
      (finalityView p D).F = (storeAt p c E rho a y).fg.F →
      (finalityView p D).h_F ≤ w.M → Block.Preceq (F_at p c E rho a y) w.CStar :=
    healing_low_finality_after_reset_on E rho hS xing w h0r
  obtain ⟨k, y, r, a, hk, ha, hsrc, hu⟩ := hK
  have hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon :=
    (hu ▸ hdeadline).trans (hS.in_horizon _ (List.mem_of_getElem? ht)).2
  have hdel := postReset_tDel p c E rho mono origin lowFinality
    highCompat resetCompat hrec.toRecovery₂ source
    (fun y r K hy hK hready hhor x hx _ j z W hz hj hW _ hFloor => by
      apply healing_source_delivery_service E rho hrec hz hx hj hW
      · have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos]
      · apply le_trans _ hhor
        change 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ ≤
          4 * p.Δ * ((r * p.R : Nat) : Int) + 3 * p.Δ
        linarith [p.deltaPos]
      · exact hFloor) emittedNonempty emittedName h0r ha.1 hsrc
    ⟨k, y, r, a, hk, ha, hsrc, rfl⟩ hhK hhor hx
  rw [Gen.V2.Duty.HoldsBefore_def,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hdel
  have hheld : K ∈ (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams (r * p.R))) x).fg.TF := by
    rcases hdel with hpath | hF
    · exact hpath K (KitFG.preceq_refl K)
    · exact KitFG.ancestor_closed_of_parent_closed _
        (cstoreInv_stateBefore E rho _ x).fg.closed _
        (cstoreInv_stateBefore E rho _ x).fg.Fmem K hF
  exact (fgsa_store_durable p c E rho
    (healing_support_idxBefore_le p c E rho hS ht (hu ▸ hdeadline)) x).1 hheld

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C3.
DC: SAME common pivot chosen after the maximum over all actual reads.
The high and reset compatibility facts have the base J2 producers.
The ports have producers fgsa_rMono, sourceDiscipline_emittedNonempty,
emittedName_window, fgsa_leaseOrigins_lastWrite, fgsa_rXing,
sourceDiscipline_qcOrigin, fgsa_rCap_channel, sourceDiscipline_tSrc,
and rowPermission_covered. -/
theorem postReset_commonPivot_at_cut
    (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (i : Nat) (hraw : PostResetRawTransfer p c E rho w i)
    {s : Slot} (hs : w.sStar + 2 ≤ s)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i) :
    ∃ D m, m = maxLiveH p c E rho s ip x ∧
      (heightView p D).h = max (w.M + 1) (m - 1) ∧
      (D ∈ (storeAt p c E rho ip x).fg.TF ∧
        Kept p c E rho ip x (storeAt p c E rho ip x).fg.TF D ∧
        (R_at p c E rho ip x).lo ≤ (heightView p D).h) ∧
      (∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
        D ∈ (storeAt p c E rho ih y).fg.TF ∧
          Kept p c E rho ih y (storeAt p c E rho ih y).fg.TF D ∧
          (R_at p c E rho ih y).lo ≤ (heightView p D).h) ∧
      (∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
        Block.Preceq (eraseFG D) H) := by
  classical
  have hS := hrec.base.valid.toScheduleWellFormed
  let reads := insert (ip, x) (((Finset.range rho.events.length).product rho.honest).filter
    (fun q => rho.events[q.1]? = some (.tick q.2 (SA.voteTime p.toParams s))))
  let m := maxLiveH p c E rho s ip x
  have hmax : m = reads.sup (fun q => (storeAt p c E rho q.1 q.2).fg.h_max) := by
    change maxLiveH p c E rho s ip x = _
    rw [maxLiveH_def]
  have hpv : SA.proposalTime p.toParams s < SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have read_spec (q : Nat × V) (hq : q ∈ reads) :
      q.2 ∈ rho.honest ∧ ∃ t, rho.events[q.1]? = some (.tick q.2 t) ∧
        SA.proposalTime p.toParams s ≤ t ∧ t ≤ SA.voteTime p.toParams s ∧
        (t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) := by
    rcases Finset.mem_insert.mp hq with he | hq
    · subst q
      exact ⟨hx, _, hip, le_rfl, hpv.le, Or.inl rfl⟩
    · obtain ⟨hq, ht⟩ := Finset.mem_filter.mp hq
      exact ⟨(Finset.mem_product.mp hq).2, _, ht, hpv.le, le_rfl, Or.inr rfl⟩
  have hreader {ih : Nat} {y : V} (hy : y ∈ rho.honest)
      (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
      (ih, y) ∈ reads := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hih).1, hy⟩, hih⟩
  have hread_bound (q : Nat × V) (hq : q ∈ reads) :
      (storeAt p c E rho q.1 q.2).fg.h_max ≤ m := by
    rw [hmax]
    exact Finset.le_sup (f := fun q => (storeAt p c E rho q.1 q.2).fg.h_max) hq
  have hLoss := healing_loss_service_scope_recovery E rho hrec mono source
    emittedNonempty emittedName
  have highCompat := postReset_high_compatible_all p c E rho hrec hLoss mono
    emittedNonempty emittedName writes xing origin h0r
  have resetCompat := postReset_reset_compatible_all p c E rho hrec hLoss mono
    emittedNonempty emittedName writes xing origin h0r
  obtain ⟨q, hq, hsup⟩ := Finset.exists_mem_eq_sup reads
    (Finset.insert_nonempty _ _) (fun q => (storeAt p c E rho q.1 q.2).fg.h_max)
  obtain ⟨hqhonest, t, hqt, hqlo, hqhi, hqtype⟩ := read_spec q hq
  have hqm : (storeAt p c E rho q.1 q.2).fg.h_max = m := by rw [hmax, hsup]
  have hpCut : ip < i :=
    ((V2.D.Engine.index_lt_read_length_iff hS _ hip).mpr hpv.le).trans_le hcut
  have pivot_source : ∃ D u, SourceBefore p c E rho ip D u ∧ high p w D ∧
      (heightView p D).h = max (w.M + 1) (m - 1) ∧ u + 2 ≤ s := by
    by_cases hl : m ≤ w.M + 1
    · obtain ⟨k, z, a, C, ha, _, hsrc, _he, hh⟩ := h0r.fresh
      have hgate : IsGateTick p c rho k z w.sStar := by rw [h0r.label]; exact ha.2.1
      have htime : SA.gateTime p.toParams w.sStar < SA.proposalTime p.toParams s := by
        have hI : (w.sStar : Int) + 2 ≤ (s : Int) := by exact_mod_cast hs
        change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int)
        nlinarith [p.deltaPos]
      have hkip := repair_idx_lt E rho hS hgate hip htime
      exact ⟨C, w.sStar, ⟨k, z, w.rStar, a, hkip, ha, hsrc, h0r.label⟩,
        (by rw [high_def, hh]), (by rw [max_eq_left ((Nat.sub_le m 1).trans hl)]; exact hh), hs⟩
    · have hI := (cstoreInv_stateBefore E rho q.1 q.2).fg
      obtain ⟨W, hW, hWsup⟩ := Finset.exists_mem_eq_sup _ ⟨_, hI.gen⟩
        (fun W => (heightView p W).h)
      have hWm : (heightView p W).h = m := by
        have hH := hI.hmax
        change (storeAt p c E rho q.1 q.2).fg.h_max =
          ((storeAt p c E rho q.1 q.2).fg.TF.sup (fun B => (heightView p B).h)) ⊔ 1 at hH
        change ((storeAt p c E rho q.1 q.2).fg.TF.sup (fun B => (heightView p B).h)) =
          (heightView p W).h at hWsup
        rw [hWsup, hqm] at hH
        change m = max (heightView p W).h 1 at hH
        simp only [Height] at *
        omega
      obtain ⟨_, _, _, K, u, hK, hhK, _⟩ :=
        cone_cross_source (hroots := hrec.base.idealization) p c E rho origin hqhonest hW (m := m
          - 1)
          (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
      obtain ⟨k, z, r, a, hkq, ha, hsrc, hu⟩ := hK
      have hgap := healing_source_row_label E rho hS hqt ⟨k, hkq, ha⟩ hqtype
      have htime : SA.gateTime p.toParams (r * p.R) < SA.proposalTime p.toParams s := by
        have hI : ((r * p.R : Nat) : Int) + 2 ≤ (s : Int) := by exact_mod_cast hgap
        change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int)
        nlinarith [p.deltaPos]
      refine ⟨K, u, ⟨k, z, r, a, repair_idx_lt E rho hS ha.2.1 hip htime,
        ha, hsrc, hu⟩, ?_, ?_, ?_⟩
      · rw [high_def, hhK]
        simp only [Height] at *; omega
      · rw [max_eq_right (by simp only [Height] at *; omega), hhK]
      · rwa [hu]
  obtain ⟨D, u, hD, hhD, hheight, hgap⟩ := pivot_source
  have hDSource := hD
  obtain ⟨k, z, r, a, hkp, ha, hsrc, hu⟩ := hD
  have hlower :=
    postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap h0r ha.1 hsrc hhD
  have hdeadline : SA.freezeTime p.toParams u ≤ SA.proposalTime p.toParams s := by
    have hI : (u : Int) + 2 ≤ (s : Int) := by exact_mod_cast hgap
    change 4 * p.Δ * (u : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int)
    nlinarith [p.deltaPos]
  have each_read (q : Nat × V) (hq : q ∈ reads) :
      D ∈ (storeAt p c E rho q.1 q.2).fg.TF ∧
        Kept p c E rho q.1 q.2 (storeAt p c E rho q.1 q.2).fg.TF D ∧
        (R_at p c E rho q.1 q.2).lo ≤ (heightView p D).h := by
    obtain ⟨hz, t, ht, hlo, _hhi, htype⟩ := read_spec q hq
    have hDh := cone_source_held p c E rho hrec mono emittedNonempty emittedName writes
      xing origin h0r source hDSource hhD (hu ▸ hlower) hz ht (hdeadline.trans hlo)
    have hDCut : SourceBefore p c E rho q.1 D u := by
      have htime : SA.gateTime p.toParams (r * p.R) < t := by
        have hI : ((r * p.R : Nat) : Int) + 2 ≤ (s : Int) := by exact_mod_cast hu ▸ hgap
        have htp : SA.gateTime p.toParams (r * p.R) < SA.proposalTime p.toParams s := by
          change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int)
          nlinarith [p.deltaPos]
        exact htp.trans_le hlo
      exact ⟨k, z, r, a, repair_idx_lt E rho hS ha.2.1 ht htime, ha, hsrc, hu⟩
    have hkept := postReset_descent_kept_of_compat (hroots := hrec.base.idealization) p c E rho
      xing origin
      (highCompat q.1) (resetCompat q.1) hz (Finset.Subset.refl _) hDh hhD
      (Or.inl ⟨u, hDCut⟩) (by
        intro K v hK _ _ hlt
        have hhK : high p w K := by rw [high_def] at hhD ⊢; exact hhD.trans hlt.le
        obtain ⟨kk, zz, rr, aa, hkk, hrow, hsource, hv⟩ := hK
        have hgapK := healing_source_row_label E rho hS ht ⟨kk, hkk, hrow⟩ htype
        have hlowerK := postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap h0r
          hrow.1 hsource hhK
        have hdK : SA.freezeTime p.toParams v ≤ t := by
          have hI : ((rr * p.R : Nat) : Int) + 2 ≤ (s : Int) := by exact_mod_cast hgapK
          have hh : SA.freezeTime p.toParams v ≤ SA.proposalTime p.toParams s := by
            rw [hv]
            change 4 * p.Δ * ((rr * p.R : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int)
            nlinarith [p.deltaPos]
          exact hh.trans hlo
        exact Or.inl (cone_source_held p c E rho hrec mono emittedNonempty emittedName
          writes xing origin h0r source ⟨kk, zz, rr, aa, hkk, hrow, hsource, hv⟩ hhK
          (hv ▸ hlowerK) hz ht hdK))
    obtain ⟨C, hC, heC⟩ := postReset_cone_reset_held p c E rho hrec cap source h0r
      mono xing hs hz ht hlo
    have hH := postReset_keep_height p c E rho h0r hC heC
    have hcontest := postReset_keep_contest (hroots := hrec.base.idealization) p c E rho hS origin
      (highCompat q.1) hH hz
    have hfloor := postReset_keep_floor p c E rho hcontest
    have hbound := hread_bound q hq
    refine ⟨hDh, hkept, ?_⟩
    rw [hheight]
    exact hfloor.trans (max_le_max le_rfl (Nat.sub_le_sub_right hbound 1))
  have hprev : timeIdx rho (SA.voteTime p.toParams (s - 1)) ≤ i := by
    apply le_trans _ hcut
    change (rho.events.filter (fun e => decide (e.time ≤
      SA.voteTime p.toParams (s - 1)))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ SA.voteTime p.toParams s))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    apply decide_eq_true
    apply (of_decide_eq_true he).trans
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hm : ((s - 1 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast Nat.sub_le s 1
    nlinarith [p.deltaPos]
  refine ⟨D, m, rfl, hheight, each_read (ip, x) (Finset.mem_insert_self _ _), ?_, ?_⟩
  · intro y hy ih hih
    exact each_read (ih, y) (hreader hy hih)
  · exact postReset_source_heads_at_cut p c E rho hrec cap source rowCovered h0r i hraw
      (selectedBefore_of_sourceBefore p c E rho
        ⟨k, z, r, a, hkp.trans hpCut, ha, hsrc, hu⟩) hhD
      (by simp only [Slot] at *; omega) hprev

end Pivot
end AvailableChain.FGSA.Run
end
