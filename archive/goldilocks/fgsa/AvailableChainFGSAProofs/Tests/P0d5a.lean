module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGCompose.Statements.FrontierSearch
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Counts
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public import AvailableChainFGSAProofs.Proofs.Shared.HealingFixture -- shake: keep (fixture)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aAuditCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }


private theorem p0d5aAuditCoreEq (p : Params) {In : Type} (c : AppCodec In) :
    p0d5aAuditCore p c = fgsaCoreReads p c := by
  rw [fgsaCoreReads_def]
  rfl

private def p0d5aAuditTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5aAuditTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5aAuditTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5aAuditObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5aAuditCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5aAuditSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- The frozen exact-service producer supplies the semantic projection.
-- No post-reset service envelope or generic StrongServed premise is used.
private theorem p0d5aAuditStrong (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (frontier : TFrontier p c E rho) {m : Nat} {t : Time}
    (served : StrongServed p c E rho m t) :
    FGCompose.StrongServed (p0d5aAuditCore p c) (p0d5aAuditSafety p c) E rho
      (p0d5aAuditObs p c) (p0d5aAuditTiming p) (fgsaInterface p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) p.k m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hu, hp, he, hh, hs, hseed, hq, hphase,
    hg, hhor, hcap⟩ := (strongServed_iff p c E rho m t).mp served
  have hseed0 := (frontierSeedQualification_iff p E u q).mp hseed
  obtain ⟨htransfer, hrepair, hopen⟩ :=
    frontier u t m J contested q Q Qfg hu hp he hh hs hseed0 hq hphase hg hhor hcap
  refine ⟨u, J, contested, q, Q, Qfg, hu, hp, he, hh, hs.1, hseed0, hq,
    ?_, hg, hhor, hcap, ?_⟩
  · cases J <;> simpa only [FGCompose.PhaseInterval, PhaseInterval, R_at, frameR_def,
      p0d5aAuditObs, p0d5aAuditTiming, storeAt, FGCompose.timeIdx_def, timeIdx] using hphase
  · refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
    · intro s B hqs hgate hprop
      exact (hrepair s B hqs hgate hprop).1
    · intro r hqr hrt
      obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
      refine ⟨?_, hent, hheight, htime⟩
      intro x hx
      obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := hcov x hx
      have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
      exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

-- Exercise the adapter and retain the same selected non-genesis proposal.
private theorem p0d5aAuditAdapterUse (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (frontier : TFrontier p c E rho)
    {m : Nat} {t : Time} (served : StrongServed p c E rho m t)
    (positive : 1 ≤ m) :
    ∃ q Q Qfg, HonestProposal E rho (fgsaInterface p c) q Q ∧ eraseFG Qfg = Q ∧
      (heightView p Qfg).h = m ∧
      FGCompose.FrontierProposalService (p0d5aAuditCore p c) E rho
        (p0d5aAuditTiming p) q Q ∧
      FGCompose.FrontierLocalService (p0d5aAuditCore p c) (p0d5aAuditSafety p c)
        E rho (p0d5aAuditObs p c) (p0d5aAuditTiming p) (fgsaInterface p c)
        (fun a => a.payload.height_pair) q Q Qfg m t ∧ 1 ≤ m := by
  obtain ⟨_, _, _, q, Q, Qfg, _, hp, he, hh, hs, _, _, _, _, _, _, hl⟩ :=
    p0d5aAuditStrong E rho frontier served
  exact ⟨q, Q, Qfg, hp, he, hh, hs, hl, positive⟩


/-! Terminal-promotion correspondence (lead rulings 5-7): every premise of the frozen
`TerminalPromotionFact` yields the generic premise by a private one-way lemma. -/

private def p0d5aAuditSigner (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5aAuditDecodeRow {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

private def p0d5aAuditWire : FGCompose.FGHistoryWireReads (p0d5aAuditSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5aAuditSigner
  decode_height a u ha := by
    delta p0d5aAuditSafety at ha
    rw [p0d5aAuditDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5aAuditSafety at ha
    rw [p0d5aAuditDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5aAuditSafety at ha
    rw [p0d5aAuditDecodeRow ha]
    rfl

private def p0d5aAuditDecode (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5aAuditDecode_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5aAuditDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5aAuditDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5aAuditPayload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5aAuditCarrier (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5aAuditDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5aAuditPayload o s N ((p0d5aAuditDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

private theorem p0d5aAuditSigner_iff (a : RowWire p.n) (i : Fin p.n) :
    p0d5aAuditSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5aAuditSigner; simp
  | proposer s => delta p0d5aAuditSigner; simp
  | seat label j => cases label <;> delta p0d5aAuditSigner <;> simp

private abbrev p0d5aAuditBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5aAuditCore p c) (p0d5aAuditSafety p c) (p0d5aAuditObs p c)
    (p0d5aAuditTiming p) E rho (fgsaInterface p c) (p0d5aAuditWire (c := c)) p.E
    p0d5aAuditDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((FGSA.parentFoldState p s H).h, (FGSA.parentFoldState p s H).T_h.root))
    (fun _ s H => FGSA.Window.rowValidW (FGSA.parentFoldState p s H)) ΔF .progress q y U X

-- The generic progress batch is the frozen batch at the same reads.
private theorem p0d5aAuditBatchFrom [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5aAuditBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5aAuditCarrier E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5aAuditSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

-- Ruling 5: frozen progress coverage is the generic progress coverage.
private theorem p0d5aAuditCovered_iff (X U : FGBlock (Fin p.n)) (y : Nat) :
    CoveredByChild p .progress X U y ↔
      FGCompose.ProgressCoveredByChild p.E (heightView p) X U y := Iff.rfl

-- Ruling 5: the frozen progress fold yields the generic fold advance.
private theorem p0d5aAuditFold (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => (p0d5aAuditCovered_iff X U y).mpr (hc hy))
    (fun _ => hm)).1

-- G0 control: the proved fold producer (read-only) yields the generic fold advance.
private theorem p0d5aAuditFoldProduced (p : Params) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt :=
  p0d5aAuditFold (fgsa_foldTrichotomy_progress p)

private theorem p0d5aAuditPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5aAuditCore p c) E rho (p0d5aAuditObs p c) u v m J
      contested ↔ PhaseInterval p c E rho u v m J contested := by
  cases J <;> simp only [FGCompose.PhaseInterval, PhaseInterval, R_at, frameR_def,
    p0d5aAuditObs, storeAt, FGCompose.timeIdx_def, timeIdx]

-- Ruling 6: frozen transfers are the generic phase transfers.
private theorem p0d5aAuditTransfers (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {B : Block} {v : Time} (h : Transfers p c E rho s B v) :
    FGCompose.PhaseTransfers (p0d5aAuditCore p c) E rho (p0d5aAuditTiming p)
      (fgsaInterface p c) s B v := h

-- Ruling 6: frozen TPerm yields generic permanence with the FG-SA phase body.
private theorem p0d5aAuditPerm (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : TPerm p c E rho) :
    FGCompose.PhasePermanence (p0d5aAuditCore p c) E rho (p0d5aAuditObs p c)
      (p0d5aAuditTiming p) (fgsaInterface p c) (recoveryStart p E) (PhaseBody p c E rho) := by
  intro u v m J contested s B hu hp hs hg hb
  exact p0d5aAuditTransfers E rho (h u v m J contested s B hu
    ((p0d5aAuditPhase_iff E rho).mp hp) hs hg hb)

-- Ruling 7(c): the frozen per-object delay is the generic family delay.
private theorem p0d5aAuditDelay (Δ ΔF : Time) :
    (fun o : Obj p => @ite _ (¬ isRowObject o) (Classical.propDecidable _) Δ ΔF) =
      fgsaDelay Δ ΔF := by
  funext o
  rcases o with ⟨a, m⟩
  cases m <;> simp [fgsaDelay, isRowObject]

-- Ruling 7(b): Base₂.receiptIdealization yields the used receipt hold.
private theorem p0d5aAuditReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (o : Obj p) (s : Slot) (N : NamedProposal p.n) (send freeze : Time) (x : V)
    (hx : x ∈ rho.honest) (hd : p0d5aAuditDecode o = some (s, N))
    (h : FGCompose.ReceiverService (fun o => ¬ isRowObject o) (fgsaTimely p) E rho o
      send freeze x) :
    ∃ Y ∈ ((p0d5aAuditCore p c).core (V2.D.Run.stateBeforeTime E rho freeze x)).fg.TF,
      (p0d5aAuditCore p c).erase Y = N.erase := by
  have ho := p0d5aAuditPayload o s N ((p0d5aAuditDecode_iff o s N).mp hd)
  subst ho
  exact ReceiverService.proposal ⟨h.dl, h.cut, h.anchor, h.within, h.ready, h.send_le,
    h.nonneg, h.later, h.cut_le, h.horizon, h.freeze_le, h.history, h.epoch, h.handlers,
    h.not_excluded⟩ hs hx hRoots

-- The frozen contract follows from the generic one: each frozen premise yields its
-- generic premise, and the generic conclusion is the frozen conclusion. The frozen
-- definition body is not exposed; the result type is its verbatim text
-- (FrontierSearchDefs.lean:209-229).
private theorem p0d5aAuditTerminal [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (h : FGCompose.TerminalPromotionFact (R := p0d5aAuditCore p c)
      (S := p0d5aAuditSafety p c) (E := E) (rho := rho) (O := p0d5aAuditObs p c)
      (T := p0d5aAuditTiming p) (I := fgsaInterface p c)
      (pair := fun a => a.payload.height_pair) (Jst := recoveryStart p E) (deltaT := p.δt)
      (D := p0d5aAuditWire (c := c)) (Ef := p.E) (family := fun o => ¬ isRowObject o)
      (timely := fgsaTimely p) (decodeProposal := p0d5aAuditDecode)
      (bodyErase := NamedProposal.erase) (bodyRows := NamedProposal.rows)
      (blockWireRows := fun nd => FGSA.blockWireRows nd.st)
      (parentFG := fun nd => FGSA.fgBlockOf nd.st)
      (parentHeight := fun _ s H =>
        ((FGSA.parentFoldState p s H).h, (FGSA.parentFoldState p s H).T_h.root))
      (validFor := fun _ s H => FGSA.Window.rowValidW (FGSA.parentFoldState p s H))
      (PhaseBody p c E rho) G ΔF) :
    Recovery₂ p c E rho G ΔF → p.δt = 2 * p.R → LivenessBoundW p ΔF →
    RMono p c E rho → RXing p c E rho → TPerm p c E rho →
    (∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF)) →
    (∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height) →
    foldTrichotomy p .progress →
    Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
    p.E.q ≤ p.E.weightOf (honestSeats p c rho) →
    ∀ r, p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon →
      ∀ u m J contested l q Q height,
        recoveryStart p E ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
        u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
        SA.proposalTime p.toParams l < SA.proposalTime p.toParams q →
        HonestProposal E rho (fgsaInterface p c) q Q → ExactService p c E rho q Q →
        OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
        (∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) →
        (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
          rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
          ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
        (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
          SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y)) := by
  intro hrec hδ hbound mono crossing perm rowsReceipt coverage hfold faultQ honestQuorum
    r hhor u m J contested l q Q height hready hp hu hq hl hQ hs hentry hcovered hrepair
  have hsync := hrec.sync
  rw [← p0d5aAuditDelay] at hsync
  exact h hsync hrec.deltaF hrec.gap hrec.base.valid hrec.base.delta hrec.fault hrec.awake
    hrec.gapPos
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
    (fun o s N send freeze x hx hd hsvc => p0d5aAuditReceipt E rho
      hrec.base.valid.toScheduleWellFormed hrec.base.receiptIdealization o s N send freeze
      x hx hd hsvc)
    hδ ⟨hbound.kappa_le_R⟩ (fun hnr => ⟨fun i j x hx hij => mono hnr i j x hx hij⟩)
    crossing (p0d5aAuditPerm E rho perm) rowsReceipt
    (fun r' y U X hb hy => (p0d5aAuditCovered_iff X U y).mp
      (coverage r' y U X (p0d5aAuditBatchFrom E rho ΔF hrec.base faultQ r' y U X hb) hy))
    (p0d5aAuditFold hfold) faultQ
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    r hhor u m J contested l q Q height hready ((p0d5aAuditPhase_iff E rho).mpr hp) hu hq hl
    hQ hs.1 hentry
    (by
      intro x hx
      obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQK, hr, ha, hn⟩ := hcovered x hx
      have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
      exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQK, hr, ha, hn⟩)
    (fun v hv s Q' hls hg hQ' =>
      (hrepair v ((p0d5aAuditPhase_iff E rho).mp hv) s Q' hls hg hQ').1)


-- Ruling 8(b): the proved TFrontier route from the recovery regime alone.
private theorem p0d5aAuditFrontierRoute [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    TFrontier p c E rho :=
  frontier_service E rho hrec (fgsa_rMonoAll p c E rho)
    (fgsa_rXing (hroots := hrec.base.idealization) p c E rho hrec.base.linked
      (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures)
    (fun q v _ _ _ => healing_frontier_service_scopes_recovery E rho hrec
      (fgsa_rMonoAll p c E rho) q v)
    (fun i x row hr => fgsa_leaseOrigins_lastWrite p c E rho
      hrec.base.valid.toScheduleWellFormed i x row hr)
    (rowPermission_covered E rho hrec.base hrec.fault)

/-- The run of Tests.NonVacuity.HealingRun.run, written out: the same params, env, gap,
deltaF and the same 311-batch events (ticks 0..310), with horizon 310 (HealingRun.horizon).
HealingRun.nvRecovery and nvPerm are stated for exactly this run; HealingFixture.mkRun alone keeps
horizon 304, which no schedule with tick 310 satisfies. -/
private abbrev p0d5aFixtureRun : V2.D.Run (Fin 1) (fgsa HealingFixture.params unitCodec) :=
  { HealingFixture.mkRun (HealingFixture.runPrefix 311).1 with horizon := 310 }

-- Guard: the horizon is 310, and the last batch index of the 311-prefix (tick time 310) is
-- within it; the 304-horizon pairing fails the same check.
private theorem p0d5aFixtureRunHorizon :
    p0d5aFixtureRun.horizon = 310 ∧ (List.range 311).getLast? = some 310 ∧
      ((310 : Nat) : Time) ≤ p0d5aFixtureRun.horizon ∧ ¬ ((310 : Nat) : Time) ≤
        HealingFixture.horizon :=
  ⟨rfl, by decide, by decide, by decide⟩

-- Ruling 8(b), strongest proved partial: on the fixture run, the recovery regime
-- (proved there as Tests.NonVacuity.HealingRun.nvRecovery; a Tests module cannot be
-- imported, TEST-USE) gives TFrontier by the proved route, and the one-way adapter maps
-- any saved seed above genesis height to the generic StrongServed with its actual
-- selected proposal and local service. StrongServed itself has no proved producer on an
-- inhabited run: it needs PhaseInterval over a seed-qualified window and ExactService q Q.
private theorem p0d5aAuditFixtureFrontier
    (hrec : RecoverySleep₂ HealingFixture.params unitCodec HealingFixture.env
      p0d5aFixtureRun HealingFixture.gap HealingFixture.deltaF)
    {m : Nat} {t : Time}
    (served : StrongServed HealingFixture.params unitCodec HealingFixture.env
      p0d5aFixtureRun m t) (above : 2 ≤ m) :
    TFrontier HealingFixture.params unitCodec HealingFixture.env p0d5aFixtureRun ∧
    ∃ q Q Qfg, HonestProposal HealingFixture.env p0d5aFixtureRun
        (fgsaInterface HealingFixture.params unitCodec) q Q ∧ eraseFG Qfg = Q ∧
      (heightView HealingFixture.params Qfg).h = m ∧ Qfg ≠ .genesis := by
  have frontier := p0d5aAuditFrontierRoute HealingFixture.env p0d5aFixtureRun hrec
  obtain ⟨q, Q, Qfg, hp, he, hh, _, _, _⟩ :=
    p0d5aAuditAdapterUse HealingFixture.env p0d5aFixtureRun frontier served
      (le_trans (by decide) above)
  refine ⟨frontier, q, Q, Qfg, hp, he, hh, ?_⟩
  intro hg
  subst hg
  rw [← hh] at above
  revert above
  decide

#print axioms p0d5aAuditCoreEq
#print axioms p0d5aAuditStrong
#print axioms p0d5aAuditAdapterUse
#print axioms p0d5aAuditBatchFrom
#print axioms p0d5aAuditFold
#print axioms p0d5aAuditFoldProduced
#print axioms p0d5aAuditPerm
#print axioms p0d5aAuditReceipt
#print axioms p0d5aAuditTerminal
#print axioms p0d5aAuditFrontierRoute
#print axioms p0d5aAuditFixtureFrontier
#print axioms p0d5aFixtureRunHorizon
end AvailableChain.FGSA.Run
end
