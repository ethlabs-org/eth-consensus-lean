module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic
-- shake: keep (arithmetic tests)
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion
-- shake: keep (promotion helper tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
-- shake: keep (actual proposal tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRenewed
-- shake: keep (expanded frozen promotion test)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAge
-- shake: keep (actual-entry HG.2 application)
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
-- shake: keep (Assembly RXing supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.Counts
-- shake: keep (Assembly fault suppliers)
public import AvailableChainFGSAProofs.Proofs.Finality.Height
-- shake: keep (Assembly progress-fold supplier)
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
-- shake: keep (Assembly honest-seat quorum supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (RMono supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases
-- shake: keep (last-write supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService
-- shake: keep (Assembly receipt supplier)

set_option linter.privateModule false

/-! H-PROMOTE tests include the expanded frozen renewed theorem.
Assembly supplies every INLINE fact by its named producer.
The same-time examples check event cuts, not a valid execution. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPromotion
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The common entry's bound is derived from the fixed sources, then used for maturity.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (hδ : p.δt = 2 * p.R)
    {r s : Nat} {height : Nat} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧ U.slot + p.δt ≤ s := by
  obtain ⟨U, hU, hslot, _⟩ := healing_promotion_bounded_rows
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF) (hrec := hrec)
    (r := r) (height := height) (Q := Q) (hentry := hentry) (hcovered := hcovered)
  exact ⟨U, hU, hslot, healing_promotion_maturity_of_action
    (p := p) (hδ := hδ) (r := r) (s := s) (U := U) (hU := hslot) (hs := hs)⟩

-- The original gap binders now produce the proposal and its ordered FG rows.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      ∃ rows, HonestCarrier p c E rho s (eraseFG X) rows ∧
        X.rows = rows.filterMap RowWire.toRow? := by
  obtain ⟨_, s, X, hp, hslot, hlo, hhi, _, hc⟩ := healing_promotion_gap_proposal
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF) (hrec := hrec)
    (r := r) (hgst := hgst) (hhor := hhor)
  exact ⟨s, X, hp, hslot, hlo, hhi, hc⟩

-- Source transfer supplies the path. Equal parent height is the local branch.
-- Every validity result refers to the same row selected at the starting action.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (perm : TPerm p c E rho)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hheight : (heightView p X.parent).h = height) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ x ∈ rho.honest, ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ValidForParent p c E rho X.slot (eraseFG X) a ∧
        HeightMatch p c E rho X.slot (eraseFG X) a := by
  obtain ⟨U, hU, hUslot, _, hrows⟩ := healing_promotion_same_rows
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF) (hrec := hrec)
    (perm := perm) (u := u) (m := m) (J := J) (contested := contested)
    (r := r) (height := height) (s := s) (Q := Q) (X := X)
    (hentry := hentry) (hcovered := hcovered) (hready := hready) (hphase := hphase)
    (hu := hu) (hgate := hgate) (hs := hs) (hnew := hnew) (hslot := hslot)
  refine ⟨U, hU, hUslot, ?_⟩
  intro x hx
  obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn, hv⟩ := hrows x hx
  exact ⟨j, rSent, a, hr, ha, hn, hv hheight⟩

-- Fixed action, with height one. Sources can differ and rows can be old.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) {r : Nat} {Q : Block}
    (hentry : OpeningEntry p c E rho r 1) (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U 1 := by
  obtain ⟨U, hU, _⟩ := healing_promotion_fixed_rows
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (height := 1) (Q := Q)
    (hentry := hentry) (hcovered := hcovered)
  exact ⟨U, hU⟩

example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s := by
  obtain ⟨_, s, hlo, hhi, hs, _⟩ := healing_promotion_gap
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (hgst := hgst) (hhor := hhor)
  exact ⟨s, hlo, hhi, hs⟩

-- Discharge the exact inline receipt binder with its main Assembly producer.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF) {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    r * p.R + 2 ≤ s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) :=
  healing_promotion_row_receipt (p := p) (c := c) (E := E) (rho := rho)
    (G := G) (ΔF := ΔF) (hrec := hrec) (hbound := hbound)
    (rowsReceipt := (fgsa_tRows_recovery p c E rho hrec).receipt)
    (r := r) (j := j) (rSent := rSent) (y := y) (a := a)
    (hr := hr) (ha := ha) (hgst := hgst) (s := s) (hs := hs) (hhor := hhor)

omit [Fintype V] in
example {x : V} {r : Nat} {K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    PhaseBody p c E rho (r * p.R) (eraseFG K) :=
  healing_promotion_source_body (p := p) (c := c) (E := E) (rho := rho)
    (x := x) (r := r) (K := K) (hx := hx) (hK := hK)

example {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {r : Nat} {s : Slot}
    {x : V} {K : FGBlock (Fin p.n)} {Q : Block} (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (perm : TPerm p c E rho)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s)
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K))
    (hs : r * p.R + 2 ≤ s) (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    Block.Preceq (eraseFG K) Q.parent := by
  exact healing_promotion_source_parent E rho perm hready hphase hu hgate hx hK hs hQ

omit [Fintype V] in
example {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {l s : Slot} {Q : Block}
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hafter : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
      ExactService p c E rho s Q :=
  healing_promotion_continuing_service (p := p) (c := c) (E := E) (rho := rho)
    (u := u) (m := m) (J := J) (contested := contested) (l := l) (s := s) (Q := Q)
    (hrepair := hrepair) (hafter := hafter) (hQ := hQ)

example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat) (q : Slot)
    (hgst : E.t_GST ≤ (r : Time) * P p)
    (hwin : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ)
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s := by
  obtain ⟨_, s, hlo, hhi, hs, _, _⟩ := healing_promotion_age_gap
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (q := q) (hgst := hgst) (hwin := hwin)
  exact ⟨s, hlo, hhi, hs⟩

-- q = rR uses the initial exact gate. No strict later-opening call is used.
omit [Fintype V] in
example (r : Nat) (Q : Block) (hservice : ExactService p c E rho (r * p.R) Q)
    (hhor : p.actionTime r ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hReader : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams (r * p.R)))
      (SA.gateTime p.toParams (r * p.R))) :
    actionSource p c E rho x r = some (some Q) := by
  have hg : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon := by
    rwa [← fgsa_grid_action_gate, fgsa_grid_action_time]
  exact (hservice.2 hg x hx hReader).2.2.2.2 r rfl

-- A receipt at time 10 is outside the strict cut at 10 and inside the inclusive cut.
-- A tick at that time is before the delivery in the post-tick cut.
omit [Fintype V] in
example (x : V) (o : Obj p) :
    let same := { rho with events := [.tick x 10, .deliver x o 10] }
    V2.D.Run.idxBefore same 10 = 0 ∧ timeIdx same 10 = 2 ∧ afterTicksIdx same 10 = 1 := by
  change 0 = 0 ∧ 2 = 2 ∧ 1 = 1
  decide

-- The final test uses the expanded frozen Claims proposition.
-- The pending public TPerm is an explicit conditional signature input here.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (perm : TPerm p c E rho)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (r : Nat)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
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
        (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
      (PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
        ExactService p c E rho s (eraseFG X) ∧
        SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ)) := by
  let mono := fgsa_rMonoAll p c E rho
  let crossing := fgsa_rXing (hroots := hrec.base.idealization) p c E rho hrec.base.linked
    (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures
  exact healing_renewedPromotion E rho hrec services hδ hbound mono crossing perm
    ((fgsa_tRows_recovery p c E rho hrec.toRecovery₂).receipt)
    (fgsa_batchCoverage p ΔF .progress c E rho)
    (fgsa_foldTrichotomy_progress p) (fgsa_faultQ_of_count p hrec.fault)
    (kmid_honest_quorum p c rho hrec.base.linked hrec.fault) r hhor

-- HG.2 uses the actual fixed entry slot in both trigger arms and deadlines.
-- Its phase and full-window premises include the finite horizon.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (perm : TPerm p c E rho)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {l : Slot} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hl : SA.proposalTime p.toParams l < (r : Time) * P p)
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ v, PhaseInterval p c E rho u v m J contested →
        max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon →
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ v →
        ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) := by
  let mono := fgsa_rMonoAll p c E rho
  let crossing := fgsa_rXing (hroots := hrec.base.idealization) p c E rho hrec.base.linked
    (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures
  obtain ⟨U, hU, hslot, hgo⟩ := healing_promotion_age_service E rho hrec services hδ hbound crossing
    perm ((fgsa_tRows_recovery p c E rho hrec.toRecovery₂).receipt)
    (fgsa_batchCoverage p ΔF .progress c E rho)
    (fgsa_foldTrichotomy_progress p) (fgsa_faultQ_of_count p hrec.fault)
    (kmid_honest_quorum p c rho hrec.base.linked hrec.fault)
    hentry hcovered hready hstart hu hl hrepair
  refine ⟨U, hU, hslot, ?_⟩
  intro v hp hwin hbudget
  obtain ⟨s, X, hnew, hXslot, _, _, hh, hreceipt, _⟩ := hgo v hp hwin hbudget
  exact ⟨s, X, hnew, hXslot, hh, hreceipt⟩

-- The event search contains an effective event exactly at D_event.
omit [Fintype V] in
example (hs : V2.D.ScheduleWellFormed E rho) {a d : Time} {i : Nat}
    {ev : V2.Event V (Obj p)} (hi : rho.events[i]? = some ev)
    (hlo : afterTicksIdx rho a ≤ i) (ht : ev.time = d)
    (heff : EffectiveEvent p c E rho i) :
    ∃ j ev', afterTicksIdx rho a ≤ j ∧ rho.events[j]? = some ev' ∧
      EffectiveEvent p c E rho j ∧ ev'.time ≤ d := by
  rcases healing_promotion_event_split p c E rho hs a d with
    ⟨j, ev', hj, hev, he, htime, _⟩ | hquiet
  · exact ⟨j, ev', hj, hev, he, htime⟩
  · exact (hquiet i hlo (healing_phase_lt_timeIdx p c E rho hs hi ht.le) heff).elim

-- A delivery exactly at d is excluded by the strict receipt cut.
omit [Fintype V] in
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {ev : V2.Event V (Obj p)}
    {d : Time} (hi : rho.events[i]? = some ev) (ht : ev.time = d) :
    ¬ i < V2.D.Run.idxBefore rho d := by
  intro hlt
  have := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp hlt
  exact (not_lt_of_ge ht.ge) this

-- Genesis top J uses the first-receipt proof at frontier one.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) {u : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (services : ∀ ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) 1
      (some .genesis) false) :
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y :=
  healing_promotion_first_receipt E rho hrec crossing services hnew hu hready hp

end AvailableChain.FGSA.Run.Tests.HealingPromotion
end

namespace AvailableChain.FGSA.Run.Tests.HealingPromotion
open AvailableChain.SimplexFG

private def promotionParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

example : LivenessBoundW promotionParams 6 := ⟨by decide⟩

-- ΔF = 6 > Δ = 1, κ = R = 3, and G = 10 has a nonzero grid remainder.
example : let p := promotionParams
    p.Δ < 6 ∧ betaF p 6 = 12 ∧ epsF p 6 = 4 ∧ Γ p 10 = 12 ∧
      p.actionTime 1 + 6 = carrierTimeW p 6 1 := by decide

example : 10 ≤ Γ (promotionParams) 10 ∧
    Γ (promotionParams) 10 < 10 + 4 * (promotionParams).Δ :=
  healing_promotion_gap_remainder (p := promotionParams) (G := 10)

-- Height-one entry and two-period maturity, with the same unequal row delay fixture.
example : EntryAt (promotionParams) (.genesis : FGBlock (Fin 4)) 1 := ⟨rfl, rfl⟩

example : (.genesis : FGBlock (Fin 4)).slot + (promotionParams).δt ≤ 9 :=
  healing_promotion_maturity_of_action (p := promotionParams) (hδ := rfl)
    (r := 1) (s := 9) (U := .genesis) (hU := by decide) (hs := by decide)

-- HG.2 can choose t_s = 36 when U_F = 32 and the old trigger is 48.
example : let p := promotionParams
    max ((2 : Time) * P p + betaF p 6 - 4 * p.Δ)
      (SA.proposalTime p.toParams 0 + 2 * P p - 4 * p.Δ) = 32 ∧
    32 < SA.proposalTime p.toParams 9 ∧ SA.proposalTime p.toParams 9 = 36 ∧
    carrierTimeW p 6 2 = SA.proposalTime p.toParams 9 ∧
    ¬ ((2 : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams 9) := by decide

example : (.genesis : FGBlock (Fin 4)).slot + promotionParams.δt ≤ 9 :=
  healing_promotion_maturity promotionParams rfl (s := 9) (U := .genesis) (by decide)

section
variable {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa promotionParams c))

-- The new deadline statement applies at equality with the carrier deadline.
example (hrec : Recovery₂ promotionParams c E rho 10 6)
    (hgst : E.t_GST ≤ promotionParams.actionTime 2) :
    max (promotionParams.actionTime 2) E.t_GST + 6 ≤
      SA.proposalTime promotionParams.toParams 9 ∧ promotionParams.R * 2 + 2 ≤ 9 := by
  obtain ⟨_, _, _, _, hd, hs⟩ := healing_promotion_row_deadline E rho hrec
    (show LivenessBoundW promotionParams 6 from ⟨by decide⟩)
    (r := 2) (rSent := 2) (s := 9) (by decide) hgst (by decide)
  exact ⟨hd, by simpa only [Nat.mul_comm] using hs⟩

-- Discharge the receipt port with its Assembly producer at the same trigger.
example (hrec : Recovery₂ promotionParams c E rho 10 6)
    {j : Nat} {y : V} {a : RowWire 4}
    (ha : HonestRowAt promotionParams c E rho j y 2 a)
    (hgst : E.t_GST ≤ promotionParams.actionTime 2) (hhor : 36 ≤ rho.horizon) :
    max (promotionParams.actionTime 2) E.t_GST + 6 ≤
      SA.proposalTime promotionParams.toParams 9 ∧
    max (promotionParams.actionTime 2) E.t_GST + 6 ≤
      SA.proposalTime promotionParams.toParams 9 ∧
    2 * promotionParams.R + 2 ≤ 9 ∧
    ∀ x ∈ rho.honest,
      HeldBefore promotionParams c E rho x a
        (max (promotionParams.actionTime 2) E.t_GST + 6) ∧
      HeldBefore promotionParams c E rho x a (promotionParams.actionTime 2 + 6) :=
  healing_promotion_row_receipt E rho hrec ⟨by decide⟩
    ((fgsa_tRows_recovery promotionParams c E rho hrec).receipt)
    (r := 2) (rSent := 2) (s := 9) (by decide) ha hgst (by decide) hhor

-- The age gap needs the full G window, which ends at 42 instead of the rounded gate budget 50.
example (hrec : Recovery₂ promotionParams c E rho 10 6)
    (hgst : E.t_GST ≤ (2 : Time) * P promotionParams) (hwin : 42 ≤ rho.horizon) :
    ∃ s, (32 : Time) < SA.proposalTime promotionParams.toParams s ∧
      SA.proposalTime promotionParams.toParams s ≤ 44 ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface promotionParams c) s := by
  obtain ⟨_, s, hlo, hhi, hs, _, _⟩ :=
    healing_promotion_age_gap E rho hrec 2 0 hgst hwin
  exact ⟨s, hlo, hhi, hs⟩

example (hrec : Recovery₂ promotionParams c E rho 10 6) {x : V} {a : RowWire 4}
    (ha : HeldBefore promotionParams c E rho x a 36) :
    HeldBefore promotionParams c E rho x a 40 :=
  healing_promotion_held_mono E rho hrec (by decide) ha
end

-- Each arm can set U_F. These values check both terminal and gate budgets.
example : let p := promotionParams
    max ((2 : Time) * P p + betaF p 6 - 4 * p.Δ)
      (SA.proposalTime p.toParams 0 + 2 * P p - 4 * p.Δ) = 32 ∧
    max ((1 : Time) * P p + betaF p 6 - 4 * p.Δ)
      (SA.proposalTime p.toParams 3 + 2 * P p - 4 * p.Δ) = 32 ∧
    max (p.actionTime 1 + Γ p 10 - p.Δ + epsF p 6)
      (SA.proposalTime p.toParams 3 + 2 * P p + Γ p 10 - 3 * p.Δ) = 45 ∧
    max (p.actionTime 1 + Γ p 10 + 4 * p.Δ + epsF p 6)
      (SA.proposalTime p.toParams 3 + 2 * P p + Γ p 10 + 2 * p.Δ) = 50 := by decide

end AvailableChain.FGSA.Run.Tests.HealingPromotion
