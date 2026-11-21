module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.VotingPolicyBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly

public section

/-! # Planning interfaces for independent FG signing and release rules

This is a proposal for review, not the installed node or a certified milestone.
-/

namespace Consensus.Goldilocks.VotingPolicyPlan

open SA (SAParams ReplayOrder)
open AsChainShape Shape Blocks

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {binding : VoteBinding}

inductive SourceChoice where
  | perReport
  | roundSnapshot
  deriving DecidableEq

inductive MissedSigning where
  | serveOverdue
  | nextAppointment
  deriving DecidableEq

/-- Signing and release calendars are independent. The two choices affect attempts only;
changing them neither edits an already signed row nor changes its release calendar. -/
structure Rules (n : Nat) where
  signAt : Fin n → Time → Time
  releaseAt : Fin n → Time → Time → Time
  /-- True: sign at the first leading poll, before the proposal and this tick's report. -/
  beforeProposal : Fin n → Bool := fun _ => false
  sourceChoice : SourceChoice := .perReport
  missedSigning : MissedSigning := .serveOverdue

def Rules.responsive (n : Nat) (_Δ : Time) : Rules n :=
  ⟨fun _ t => t, fun _ _ t => t, fun _ => false, .perReport, .serveOverdue⟩

/-- Fixed signing and independently scheduled release. For a fixed signing time with
immediate publication take `nextRelease y t = t`; to sign at release take `nextSign`
to be the release calendar and again publish immediately. -/
def Rules.scheduled {n : Nat} (nextSign nextRelease : Fin n → Time → Time) : Rules n :=
  ⟨nextSign, fun y _ t => nextRelease y t, fun _ => true, .perReport, .serveOverdue⟩

/-- First grid appointment at or after `t`, for positive period. -/
def nextAppointment (period offset t : Time) : Time :=
  t + (offset - t) % period

/-- `releaseOffset = none` means release in the signing poll. A stagger is a
validator-specific offset on the slot grid, not a refresh of the signed source. -/
def Rules.roundStart (n : Nat) (Δ : Time) (releaseOffset : Option (Fin n → Time)) : Rules n :=
  Rules.scheduled (fun _ => nextAppointment (4 * Δ) 0)
    (releaseOffset.elim (fun _ t => t) fun offset y => nextAppointment (4 * Δ) (offset y))

/-- Sign and release together at the next appointment, with no row held across polls. -/
def Rules.signAtRelease (n : Nat) (Δ : Time) (offset : Fin n → Time) : Rules n :=
  Rules.scheduled (fun y => nextAppointment (4 * Δ) (offset y)) (fun _ t => t)

structure Held (sp : SAParams) where
  source : Blk sp
  reportedAt : Time
  signedAt : Time
  eligibleAt : Time
  row : FG.Att sp.n

structure PolicyState (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (binding : VoteBinding) where
  base : State sp ro binding
  pending : List (Time × Time × Blk sp) := []
  held : List (Held sp) := []
  leading : Bool := false

def signingDue (p : Rules sp.n) (y : Fin sp.n) (t : Time) : Time :=
  let earliest := t + if p.beforeProposal y then 1 else 0
  max earliest (p.signAt y earliest)

/-- Under skip, an off-calendar wake does not run a missed signing duty. Work
stays pending until the next awake calendar appointment. -/
def SigningOpen {n : Nat} (p : Rules n) (y : Fin n) (t : Time) : Prop :=
  p.missedSigning = .serveOverdue ∨ p.signAt y t = t

/-- The snapshot alternative chooses the latest eligible report at the actual
appointment and consumes all eligible reports; it never rewrites future reports. -/
noncomputable def signingWork (p : Rules sp.n) (st : PolicyState sp ro binding) :
    List (Time × Time × Blk sp) × List (Time × Time × Blk sp) :=
  open Classical in
  if SigningOpen p st.base.self st.base.now then
    let due := st.pending.filter (fun q => q.1 ≤ st.base.now)
    let keep := st.pending.filter (fun q => st.base.now < q.1)
    (match p.sourceChoice with
      | .perReport => due
      | .roundSnapshot => due.getLast?.toList, keep)
  else ([], st.pending)

abbrev CutLog (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :=
  List (NodeState (goldilocksNode sp ro) × Cut (goldilocksNode sp ro) ×
    NodeState (goldilocksNode sp ro))

/-- Preserve each reported source at its own deadline, including across wake. This draft
does not permit a newer report to borrow an earlier report's signing appointment. -/
noncomputable def report (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding :=
  let r := Node.acToFG st.base.node st.base.now
  let pending := r.2.2.elim st.pending fun C =>
    st.pending ++ [(signingDue p st.base.self st.base.now, st.base.now, C)]
  { st with base := { st.base with node := r.1, fgDue := false }, pending }

/-- Charge the anti-slashing record at the real attempt. The immutable row is not admitted
to the proposal pool or outbox before its release gate. A refusal never overwrites a held row. -/
noncomputable def attempt (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × CutLog sp ro :=
  let (ready, later) := signingWork p st
  ready.foldl (fun (nd, logs) (_, r, C) =>
    match nd.base.node.fg.attest nd.base.node.record nd.base.self C with
      | none => (nd, logs ++ [(nd.base.node, .fg (.attest C none), nd.base.node)])
      | some (a, record) =>
        let u := max st.base.now (p.releaseAt st.base.self r st.base.now)
        let post := { nd.base.node with record }
        ({ nd with
          base := { nd.base with node := post }
          held := nd.held ++ [⟨C, r, st.base.now, u, a⟩] },
          logs ++ [(nd.base.node, .fg (.attest C (some a)), post)]))
    ({ st with pending := later }, [])

/-- Keep eligible items in append order and skip ineligible items without re-signing.
Clock and restart never call this handler. -/
noncomputable def flush (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × List (Held sp) :=
  let ready := st.held.filter (fun h => h.eligibleAt ≤ st.base.now)
  let node := ready.foldl (fun nd h => (Node.onAttestation nd h.row).1) st.base.node
  ({ st with
    base := { st.base with node := node }
    held := st.held.filter (fun h => st.base.now < h.eligibleAt) }, ready)

noncomputable def restore (self : Fin sp.n) (st : PolicyState sp ro binding) (t : Time) :
    PolicyState sp ro binding :=
  { st with base := AsChainShape.restore self st.base t, leading := false }

/-- Leading polls can flush held rows before a proposal. Respect the ordinary outbox
and forwarding order, then append due rows as separate guarded candidates. Do not put a
wake burst behind the one-body ordinary drain. -/
noncomputable def pollAttempts (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × CutLog sp ro :=
  if st.base.fgDue then
    let st' := report p st
    let r := if p.beforeProposal st.base.self then (st', []) else attempt p st'
    (r.1, (st.base.node, (Node.acToFG st.base.node st.base.now).2.1, st'.base.node) :: r.2)
  else if st.leading && p.beforeProposal st.base.self then attempt p st else (st, [])

noncomputable def preparePoll (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × List (Held sp) :=
  flush (pollAttempts p st).1

noncomputable def pollCutLog (p : Rules sp.n) (st : PolicyState sp ro binding) : CutLog sp ro :=
  let (mid, calls) := pollAttempts p st
  let (_, flushed) := flush mid
  calls ++ (flushed.foldl (fun (nd, logs) h =>
    let post := (Node.onAttestation nd h.row).1
    (post, logs ++ [(nd, .fg (.attestation h.row), post)])) (mid.base.node, [])).2

noncomputable def policyOps (p : Rules sp.n) :
    NodeAsChainShape.Ops sp.n binding.Kind Info Body Out (PolicyState sp ro binding) where
  init k q := ⟨(nodeOps sp ro binding).init k q, [], [], false⟩
  clock st t := { st with base := { st.base with now := t }, leading := true }
  propose st s := let r := AsChainShape.propose st.base s; ({ st with base := r.1 }, r.2)
  pollPropose st _ := ({ st with base := nodeTick st.base }, none)
  poll st t :=
    let r := AsChainShape.poll { st.base with fgDue := false } t
    ({ st with base := r.1 }, r.2)
  pollBatch st t :=
    let (st, ready) := preparePoll p st
    let r := AsChainShape.pollBatch st.base t
    ({ st with base := r.1, leading := false },
      r.2 ++ ready.map (fun h => (.att (encodeAtt h.row), [])))
  gossip st t := (nodeOps sp ro binding).gossip st.base t
  process st o hs := { st with base := AsChainShape.process st.base o hs }
  recordOwn st o hs := { st with base := AsChainShape.recordOwn st.base o hs }
  restore := restore
  out g st := outOf st.base.node st.base.now g

/-- Proposed family with the same wire format and duty selection, including `n = 0`. -/
noncomputable def delayedFamily (S : Setup) (p : (n : Nat) → Time → Rules n) :
    ChainShapeFamily schema Info :=
  fun pub =>
    NodeAsChainShape.shape (skeleton pub S.vote)
      (NodeAsChainShape.familyOps fun hn =>
        policyOps (sp := S.params pub hn) (ro := S.ro _) (binding := S.vote) (p pub.n pub.ΔAC))
      (S.vote.candidateRole pub.n) (dependencies pub.n (binding := S.vote))
      (conflicts (binding := S.vote)) (isFGAtt (binding := S.vote))

/-- The responsive branch uses the existing family verbatim, including its queue order. -/
noncomputable def family (S : Setup) (p : (n : Nat) → Time → Rules n) :
    ChainShapeFamily schema Info :=
  open Classical in
  if p = Rules.responsive then goldilocks S else delayedFamily S p

/-- Separate signing, outbox release and consumer receipt budgets; time is in units of ΔAC. -/
structure Budget where
  signSteps : Nat
  publishSteps : Nat
  relaySteps : Nat

def Budget.total (B : Budget) : Nat := B.signSteps + B.publishSteps + B.relaySteps

/-- Proposed numeric contract. The final heal reserve is an explicit review target, not a
proven coefficient. Window length must still satisfy the FG timeout and relay inequalities. -/
noncomputable def coefficients (S : Setup) (A : ContractAssumptions S) (B : Budget) :
    ContractCoefficients :=
  let old := contract_coefficients S A
  { old with
    heal := fun cap X => old.heal cap X + if cap = .final then 5 * B.total else 0
    latency := fun cap X => old.latency cap X + if cap = .final then B.total else 0 }

/-- Separate the original network range from the larger proposed four-anchor gap. -/
def TimingRoom {S : Setup} (A window : ContractAssumptions S) (B : Budget) : Prop :=
  6 + B.total + (A.fgDelay : Nat) ≤ 4 * window.fgSlots ∧
  7 + B.total ≤ 4 * window.fgSlots

/-- Smallest integer slot gap paying both budgets without reducing `fgDelay`. -/
def requiredGap {S : Setup} (A : ContractAssumptions S) (B : Budget) : Nat :=
  max 2 ((max (6 + B.total + (A.fgDelay : Nat)) (7 + B.total) + 3) / 4)

theorem timing_room_iff_timeout {S : Setup} (A : ContractAssumptions S) (B : Budget) :
    (∃ window : ContractAssumptions S, TimingRoom A window B) ↔
      3 * requiredGap A B ≤ S.δt := by
  sorry

noncomputable def windowContract (S : Setup) (A window : ContractAssumptions S) (B : Budget) :
    Contract ProgressReq :=
  let K := goldilocksContract window (coefficients S window B)
  { K with params := { K.params with fgDelay := A.fgDelay } }

/-- Public schedule bounds do not assert any node was awake or any row was released. -/
structure ScheduleBounds (p : (n : Nat) → Time → Rules n) (Δ : Time) (B : Budget) : Prop where
  sign : ∀ n y t, 0 ≤ t →
    let earliest := t + if (p n Δ).beforeProposal y then 1 else 0
    max earliest ((p n Δ).signAt y earliest) + Δ ≤ t + B.signSteps * Δ
  skip : ∀ n y g t, 0 ≤ t → (p n Δ).missedSigning = .nextAppointment →
    let earliest := t + if (p n Δ).beforeProposal y then 1 else 0
    let due := max earliest ((p n Δ).signAt y earliest)
    ∃ u, max g due ≤ u ∧ u ≤ max g t + B.signSteps * Δ ∧ Δ ∣ u ∧ (p n Δ).signAt y u = u
  release : ∀ n y r t, 0 ≤ r → r ≤ t →
    max t ((p n Δ).releaseAt y r t) + Δ ≤ t + B.publishSteps * Δ

section RunStatements

open SA (Payload gbar)
open Healing (cutZ)
open Healing.Growing

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}

/-- This is the projected cut-law bundle, not the old `LocalRun`: its old group law
requires immediate signing. The canonical adapter must construct these observations from
the same engine events, rather than postulate a second run. -/
structure CutObservations (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) : Prop where
  timeMono : Monotone tr.time
  honestMono : Antitone H
  treeKeeps : ∀ y i j, i ≤ j → y ∈ H (tr.time j) →
    (tr.state y i).fg.tree ⊆ (tr.state y j).fg.tree
  restartKeeps : ∀ y i, tr.RestartAt y i → y ∈ H (tr.time i) →
    (tr.state y (i + 1)).fg = (tr.state y i).fg ∧
      (tr.state y (i + 1)).record = (tr.state y i).record

/-- Cross-restart gate: the selected signing source still has to dominate the eligible
original report. A proof must rule out replacing a pending source with an incomparable or
lower source (or change the handler and prove a suitable supersession rule). -/
def Dominates (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (y : Fin sp.n) (i k : Nat) (R C : Blk sp) : Prop :=
  Anc (tr.HonestBlocksAt H) R C ∧
    ((tr.state y i).fg.σ R.root).h ≤ ((tr.state y k).fg.σ C.root).h

/-- Independent event-based hypotheses. `b` is the finite observation endpoint, `g` the
start of the service interval. No continuity and no restart restriction before or during
the interval; only bounded opportunities for the particular report/release clock. -/
structure SignDutyCoverage (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (p : Rules sp.n) (g b D : Time) : Prop where
  duty : ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R →
    max g (tr.time i) + D ≤ b → y ∈ H (max g (tr.time i) + D) →
    ∃ t, max g (signingDue p y (tr.time i)) ≤ t ∧
      t ≤ max g (tr.time i) + D ∧ sp.toParams.IsPublic t ∧ tr.awake y t ∧ SigningOpen p y t

def Attempts (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b D : Time) : Prop :=
  ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R →
    max g (tr.time i) + D ≤ b → y ∈ H (max g (tr.time i) + D) →
    ∃ j k ell' C s, i ≤ j ∧ j ≤ k ∧ tr.time k ≤ max g (tr.time i) + D ∧
      SA.ToFGAt tr.projAC y j ell' C ∧ tr.CallAt y k (.fg (.attest C s)) ∧
      Dominates tr H y i k R C

/-- Exact cut witness, including a refusal's earlier signature. An event mapper must
associate `released` with actual guarded publication in the very same engine run. -/
structure Publication (tr : GoldilocksTrace sp ro) where
  released : Fin sp.n → FG.Att sp.n → Time → Prop

def ReleasedBy (U : Publication tr) (H : Time → Set (Fin sp.n))
    (y : Fin sp.n) (a : FG.Att sp.n) (deadline : Time) : Prop :=
  ∃ t, t ≤ deadline ∧ y ∈ H t ∧ U.released y a t

/-- Supply is phrased for the actual anchor entry. The disjunction never substitutes
a signature above the entry for a matching row. -/
structure PublishedRows (U : Publication tr) (g b D R : Time) : Prop where
  supply : ∀ {T : Blk sp} {y : Fin sp.n} {m : Nat} {t : Time},
    0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
    ∀ {σT : FG.ChainState sp.n}, (tr.state y m).fg.σ T.root = σT → σT.Th = T.root →
    HZ tr H g + 1 ≤ σT.h → (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) →
    ∀ {d : Time}, gbar g ≤ d → d + D + R ≤ b →
    (∀ x r ell C, x ∈ H (tr.time r) → SA.ToFGAt tr.projAC x r ell C →
      tr.time r < d → ((tr.state x r).fg.σ C.root).h ≤ σT.h) →
    (∀ z, z ∈ H (max (cutZ sp.toParams g) d) → ∃ r ell C,
      SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ d ∧
        Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) (d + D + R)) ∧ ∃ a j,
        tr.SignAt z j a ∧ tr.time j ≤ d + D ∧ ReleasedBy U H z a (d + D + R) ∧
        a.val = z ∧ a.h = σT.h ∧ a.T = T.root ∧ a.timeout = false ∧
        (σT.previousHeightJustified → a.fin = some (σT.hj, σT.J))) ∨
    ∃ x r ell C, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r ell C ∧ d ≤ tr.time r ∧
      tr.time r ≤ d + D ∧ σT.h < ((tr.state x r).fg.σ C.root).h

theorem durable_held_and_pending (st : PolicyState sp ro binding) (t : Time) (y : Fin sp.n) :
    (restore y st t).held = st.held ∧ (restore y st t).pending = st.pending := by
  sorry

theorem frozen_flush_rank (st : PolicyState sp ro binding) (i : Nat) (h : Held sp)
    (hi : (st.held.filter (fun h' => h'.eligibleAt ≤ st.base.now))[i]? = some h) :
    ((flush st).2.map (fun q => Body.att (encodeAtt q.row)))[i]? =
      some (.att (encodeAtt h.row)) := by
  sorry

theorem flush_no_early_admission (st : PolicyState sp ro binding) (h : Held sp)
    (hm : h ∈ st.held) (ht : st.base.now < h.eligibleAt) :
    h ∈ (flush st).1.held ∧ h ∉ (flush st).2 := by
  sorry

def ExactService (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b D : Time) : Prop :=
  ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R →
    max g (tr.time i) + D ≤ b → y ∈ H (max g (tr.time i) + D) →
    ∃ k s, i ≤ k ∧ tr.time k ≤ max g (tr.time i) + D ∧ tr.CallAt y k (.fg (.attest R s))

def ReleaseService (U : Publication tr) (H : Time → Set (Fin sp.n)) (g b D : Time) : Prop :=
  ∀ y k a, tr.SignAt y k a → max g (tr.time k) + D ≤ b → y ∈ H (max g (tr.time k) + D) →
    ReleasedBy U H y a (max g (tr.time k) + D)

theorem attempts_of_exact_service (hcut : CutObservations tr H) {g b D : Time}
    (svc : ExactService tr H g b D)
    (hσ : ∀ y i ell R k s, i ≤ k → y ∈ H (tr.time k) →
      SA.ToFGAt tr.projAC y i ell R → tr.CallAt y k (.fg (.attest R s)) →
      Dominates tr H y i k R R) : Attempts tr H g b D := by
  sorry

theorem voteLatency_truncated_of_attempts {b D : Time}
    (ht : ∀ i, 0 ≤ tr.time i) (hcut : CutObservations tr H)
    (svc : Attempts tr H 0 b D) : Generic.VoteLatencyAt tr (Generic.truncH H b) D := by
  sorry

/-- The exact-bit target for a same-height attempt. A refusal must trace through the
durable record to a real earlier signature; a higher report cannot supply these bits. -/
def MatchingRows (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g b : Time) : Prop :=
  ∀ (T : Blk sp) (σT : FG.ChainState sp.n) y m t z r k ell C s,
      0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
      (tr.state y m).fg.σ T.root = σT → σT.Th = T.root → HZ tr H g + 1 ≤ σT.h →
      (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) → r ≤ k →
      z ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)) → tr.time k ≤ b →
      SA.ToFGAt tr.projAC z r ell C → tr.CallAt z k (.fg (.attest C s)) →
      Anc (tr.HonestBlocksAt H) T C → ((tr.state z r).fg.σ C.root).h = σT.h →
      ∃ j att, j ≤ k ∧ tr.SignAt z j att ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J))

theorem published_rows_of_attempts (U : Publication tr) {g b a D R : Time}
    (hreset : IsReset tr H g a) (hab : a ≤ b) (hcz : cutZ sp.toParams g ≤ b)
    (hquorum : ∀ t, gbar g ≤ t → t ≤ b → sp.toParams.fg.q ≤ (H t).ncard)
    (hcut : CutObservations tr H) (hmatching : MatchingRows tr H g b)
    (hattempt : Attempts tr H (gbar g) b D) (hrelease : ReleaseService U H (gbar g) b R)
    (hD : 0 ≤ D) (hR : 0 ≤ R) : PublishedRows (H := H) U g b D R := by
  sorry

theorem exact_report_dominates_across_restart
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (hcut : CutObservations tr H)
    (hnc : Compose.NoCollRun dg tr)
    (hheld : ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R → y ∈ H (tr.time i) →
      R ∈ (tr.state y i).fg.tree)
    (hstable : ∀ y i k R, i ≤ k → y ∈ H (tr.time k) → R ∈ (tr.state y i).fg.tree →
      R ∈ tr.HonestBlocksAt H ∧ (tr.state y i).fg.σ R.root = (tr.state y k).fg.σ R.root)
    {y i ell R k s} (hik : i ≤ k) (hy : y ∈ H (tr.time k))
    (hreport : SA.ToFGAt tr.projAC y i ell R) (ha : tr.CallAt y k (.fg (.attest R s))) :
    Dominates tr H y i k R R := by
  sorry

/-- The record is charged on signing, even if the row has not been released. -/
def RecordOrigins (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) : Prop :=
  ∀ y k c, y ∈ H (tr.time k) → c ∈ (tr.state y k).record.sent →
    ∃ j < k, ∃ a, tr.SignAt y j a ∧ a.content = c

/-- Report and attempt origins are statements about the same trace. A replaced
snapshot is not allowed to cite the original report as its signing source. -/
structure SourceFacts (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) : Prop where
  held : ∀ y i ell C, SA.ToFGAt tr.projAC y i ell C → y ∈ H (tr.time i) →
    C ∈ (tr.state y i).fg.tree
  stable : ∀ y i k C, i ≤ k → y ∈ H (tr.time k) → C ∈ (tr.state y i).fg.tree →
    C ∈ tr.HonestBlocksAt H ∧ (tr.state y i).fg.σ C.root = (tr.state y k).fg.σ C.root
  report_origin : ∀ y k C s, tr.CallAt y k (.fg (.attest C s)) →
    ∃ j ≤ k, ∃ ell, SA.ToFGAt tr.projAC y j ell C

/-- The high-chain argument must constrain the target, timeout and lock records at
the actual attempt cut (including records written by rows still held). -/
def HighRecordAgreement (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b : Time) : Prop :=
  ∀ y k h root, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.time k ≤ b →
    HZ tr H g + 1 ≤ h →
    ((tr.state y k).record.target h = some root ∨ root ∈ (tr.state y k).record.timeout h ∨
      (tr.state y k).record.lock h = some root) →
    ∀ x i j B T z m, HighOrigin tr H g x i j B → tr.time i ≤ b →
      z ∈ H (tr.time m) → T ∈ (tr.state z m).fg.tree → Anc (tr.HonestBlocksAt H) T B →
      ((tr.state z m).fg.σ T.root).h = h → ((tr.state z m).fg.σ T.root).Th = T.root →
      root = T.root

/-- The bounded high-origin lookup is independent of the mechanics of signing.
It has to be re-established on the delayed trace before the record proof. -/
def HighReportOrigins (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b : Time) : Prop :=
  ∀ y k ell C, SA.ToFGAt tr.projAC y k ell C →
    y ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.time k ≤ b →
    HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h →
    ∃ x i j B, HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧
      Anc (tr.HonestBlocksAt H) C B

theorem matching_rows_of_high_records {g b : Time}
    (hcut : CutObservations tr H) (hsrc : SourceFacts tr H) (horigin : RecordOrigins tr H)
    (hhigh : HighReportOrigins tr H g b) (hrecord : HighRecordAgreement tr H g b)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (hnc : Compose.NoCollRun dg tr)
    {acp₀ : Payload sp.n}
    (hreachable : ∀ y k, y ∈ H (tr.time k) → Store.Reachable acp₀ (tr.state y k).fg) :
    MatchingRows tr H g b := by
  sorry

end RunStatements

section EngineStatements

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {p : (n : Nat) → Time → Rules n}

/-- A canonical adapter must use this exact release relation: no hypothetical queue and no
replacement signature. Membership in the actual event's output includes the engine guard. -/
noncomputable def engineAttObj (_rho : Model.Run (compiled (delayedFamily S p)) E)
    (a : FG.Att (Fintype.card V)) : (Model.protoOf (compiled (delayedFamily S p)) E).Object :=
  attObj (binding := S.vote) a

def EngineRelease (rho : Model.Run (compiled (delayedFamily S p)) E)
    (v : V) (a : FG.Att (Fintype.card V)) (t : Time) : Prop :=
  rho.releases v (engineAttObj rho a) t

def EngineReleaseAt (rho : Model.Run (compiled (delayedFamily S p)) E)
    (i : Nat) (a : FG.Att (Fintype.card V)) : Prop :=
  engineAttObj rho a ∈ rho.releasesAt i

/-- Equality to the policy state at an actual event boundary. -/
def EngineBoundary (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (i : Nat) (v : V)
    (st : PolicyState (S.params (Model.pubOf E) hn) (S.ro _) S.vote) : Prop :=
  ((rho.stateBefore i v).st.1 hn) = st

/-- Interpret a compiled node's state at the positive-population component. -/
def policyStateAt (_rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (nd : Model.Node (Model.protoOf (compiled (delayedFamily S p)) E)) :
    PolicyState (S.params (Model.pubOf E) hn) (S.ro _) S.vote :=
  nd.st.1 hn

/-- State at an actual duty prefix of a tick, after clock and earlier releases. -/
noncomputable def tickPrefix (rho : Model.Run (compiled (delayedFamily S p)) E)
    (v : V) (i : Nat) (t : Time) (q : Nat) :=
  let nd := rho.stateBefore i v
  let P := Model.protoOf (compiled (delayedFamily S p)) E
  let clocked : Model.Node P := ⟨P.clock nd.st t (Model.mempool rho.inbox v t), nd.seen⟩
  rho.runDuties v clocked ((P.duties t).take q)

/-- Both queues survive a real restart event. No attest or release is inserted at wake. -/
theorem restart_retains_work (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    ∃ before after, EngineBoundary rho hn i v before ∧
    EngineBoundary rho hn (i + 1) v after ∧
    after.pending = before.pending ∧ after.held = before.held ∧
      after.base.node.fg = before.base.node.fg ∧ after.base.node.record = before.base.node.record ∧
      rho.releasesAt i = [] := by
  sorry

theorem prepared_rank (p : Rules sp.n) (st : PolicyState sp ro binding) (t : Time)
    (i : Nat) (h : Held sp) (hi : ((preparePoll p st).2)[i]? = some h) :
    let prior := (AsChainShape.pollBatch (preparePoll p st).1.base t).2
    ((policyOps (ro := ro) (binding := binding) p).pollBatch st t).2[prior.length + i]? =
      some (Body.att (encodeAtt h.row), []) := by
  sorry

/-- Transfer the real guard and timing, in both directions, in the same run. `key` and
`reindex` are the concrete enumeration bijections; they do not change attestation bits. -/
structure EngineProjection {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) where
  key : V ≃ Fin sp.n
  reindex : FG.Att sp.n → FG.Att (Fintype.card V)
  cutLaws : CutObservations tr H
  recordOrigins : RecordOrigins tr H
  sources : SourceFacts tr H
  timeNonneg : ∀ i, 0 ≤ tr.time i
  honest_iff : ∀ v t, key v ∈ H t ↔ v ∉ rho.faultyAt t
  awake_eq : ∀ v t, 0 ≤ t → t ≤ rho.horizon → (tr.awake (key v) t ↔ E.awake v t = true)
  signer_eq : ∀ a, (reindex a).val = rho.ownKey (key.symm a.val)
  bits_eq : ∀ a, (reindex a).h = a.h ∧ (reindex a).T = a.T ∧
    (reindex a).timeout = a.timeout ∧ (reindex a).fin = a.fin
  occurrence : ∀ i, (∃ y, tr.IsCall y i) → Nat × Nat
  ordered : ∀ i j hi hj, i < j →
    Prod.Lex (· < ·) (· < ·) (occurrence i hi) (occurrence j hj)
  event_owner_time : ∀ i y (hi : tr.IsCall y i),
    ∃ e, rho.events[(occurrence i ⟨y, hi⟩).1]? = some e ∧
      e.node = key.symm y ∧ e.time = tr.time i
  other_unchanged : ∀ i y z ℓ, tr.CallAt y i ℓ → z ≠ y → tr.state z (i + 1) = tr.state z i
  owner_post : ∀ i y ℓ, tr.CallAt y i ℓ → tr.state y (i + 1) = tr.post i
  cut_step : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i)
  cutLog : Nat → CutLog sp ro
  exactCut : ∀ i y ℓ (hi : tr.CallAt y i ℓ),
    let ij := occurrence i ⟨y, ℓ, hi⟩
    (cutLog ij.1)[ij.2]? = some (tr.state y i, ℓ, tr.post i)
  completeCut : ∀ (j q : Nat) before ℓ after, (cutLog j)[q]? = some (before, ℓ, after) →
    ∃ (i : Nat) (y : Fin sp.n) (hi : tr.CallAt y i ℓ), occurrence i ⟨y, ℓ, hi⟩ = (j, q)
  release_origin : ∀ y a j t,
    rho.SendsAt (key.symm y) j t → EngineReleaseAt rho j (reindex a) →
      ∃ (k : Nat) (hk : tr.IsCall y k), tr.SignAt y k a ∧ (occurrence k ⟨y, hk⟩).1 ≤ j
  own_receipt : ∀ y a j t,
    rho.SendsAt (key.symm y) j t → EngineReleaseAt rho j (reindex a) →
      ∃ (k : Nat) (hk : tr.IsCall y k), tr.ProcessAttAt y k a ∧ (occurrence k ⟨y, hk⟩).1 = j
  delivered_receipt : ∀ y a j t,
    rho.events[j]? = some (.deliver (key.symm y) (engineAttObj rho (reindex a)) t) →
      ∃ (k : Nat) (hk : tr.IsCall y k), tr.ProcessAttAt y k a ∧ (occurrence k ⟨y, hk⟩).1 = j
  release_iff : ∀ v a t, U.released (key v) a t ↔ EngineRelease rho v (reindex a) t

theorem canonical_bare_att_has_no_release_dependencies {n : Nat}
    (a : FG.Att n) (seen : List (Wire n S.vote)) :
    (dependencies n (binding := S.vote)).ready seen (attObj a) = true := by
  sorry

/-- At a positive slot start poll zero leads and poll four follows the proposal.
Otherwise the missing proposal shortens the latter index by one. -/
theorem tick_has_signing_phase (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (ht : 0 ≤ t)
    (hawake : E.awake v t = true) (hsel : rho.SelValid)
    (hpublic : (S.params (Model.pubOf E) hn).toParams.IsPublic t) :
    ∀ leading : Bool, ∃ q, ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? =
        some (ShapeDuty.poll t.toNat) ∧
      let before := policyStateAt rho hn (tickPrefix rho v i t q).1
      if leading then q = 0 ∧ before.leading = true ∧ before.base.fgDue = false
      else (q = 3 ∨ q = 4) ∧ before.leading = false ∧ before.base.fgDue = true := by
  sorry

/-- A popped row must be a real canonical candidate and an actual release in this
event. In particular the claim does not follow from the scheduler alone. -/
theorem popped_row_releases_at_tick (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i q : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hawake : E.awake v t = true)
    (hsel : rho.SelValid)
    (hpoll : ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? =
      some (.poll t.toNat))
    {h : Held (S.params (Model.pubOf E) hn)}
    (hown : h.row.val = rho.ownKey v)
    (hpop : h ∈ (preparePoll (p _ (Model.pubOf E).ΔAC)
      (policyStateAt rho hn (tickPrefix rho v i t q).1)).2) :
    EngineReleaseAt rho i h.row := by
  sorry

theorem poll_log_has_exact_attempt (p : Rules sp.n) (st : PolicyState sp ro binding)
    (due time : Time) (C : Blk sp)
    (hp : (due, time, C) ∈ (signingWork p st).1) :
    ∃ pre post result, (pre, .fg (.attest C result), post) ∈ (attempt p st).2 := by
  sorry

theorem snapshot_selects_last_eligible (p : Rules sp.n) (st : PolicyState sp ro binding)
    (hm : p.sourceChoice = .roundSnapshot) (ho : SigningOpen p st.base.self st.base.now) :
    (signingWork p st).1 =
      (st.pending.filter (fun q => q.1 ≤ st.base.now)).getLast?.toList := by
  sorry

theorem missed_signing_preserves_pending (p : Rules sp.n) (st : PolicyState sp ro binding)
    (hm : p.missedSigning = .nextAppointment)
    (ht : p.signAt st.base.self st.base.now ≠ st.base.now) :
    (signingWork p st).1 = [] ∧ (signingWork p st).2 = st.pending := by
  sorry

theorem poll_log_charges_record (p : Rules sp.n) (st : PolicyState sp ro binding)
    {pre post : NodeState (goldilocksNode sp ro)} {C : Blk sp} {a : FG.Att sp.n}
    (hs : (pre, .fg (.attest C (some a)), post) ∈ (pollCutLog p st)) :
    pre.fg.attest pre.record st.base.self C = some (a, post.record) ∧ post.fg = pre.fg := by
  sorry

/-- Every successful attempt appends its exact row, with immutable provenance. -/
theorem attempt_creates_held_row (p : Rules sp.n) (st : PolicyState sp ro binding)
    {pre post : NodeState (goldilocksNode sp ro)} {C : Blk sp} {a : FG.Att sp.n}
    (h : (pre, .fg (.attest C (some a)), post) ∈ (attempt p st).2) :
    ∃ item ∈ (attempt p st).1.held, item.source = C ∧ item.row = a ∧
      item.signedAt = st.base.now ∧
      item.eligibleAt = max item.signedAt
        (p.releaseAt st.base.self item.reportedAt item.signedAt) := by
  sorry

/-- A tick's poll log is a contiguous part of the actual event's cut sequence.
The state used to run the handler comes from the actual duty prefix. -/
def ProjectedTickPollLogs
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) : Prop :=
  ∀ (v : V) (i q : Nat) (t : Time),
    rho.events[i]? = some (.tick v t) → E.awake v t = true →
    ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? = some (.poll t.toNat) →
    let st := policyStateAt rho hn (tickPrefix rho v i t q).1
    let calls := pollCutLog (p _ (Model.pubOf E).ΔAC) st
    ∃ offset, ((M.cutLog i).drop offset).take calls.length = calls

/-- Every successful attempt either releases its exact row in that poll, or leaves
the same frozen item in the actual state at the end of the poll. -/
theorem poll_attempt_release_or_retain
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i q : Nat} {t : Time}
    (hv : rho.ExecutionValid) (he : rho.events[i]? = some (.tick v t))
    (hawake : E.awake v t = true)
    (hpoll : ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? =
      some (.poll t.toNat))
    (hpublic : (S.params (Model.pubOf E) hn).toParams.IsPublic t) :
    let st := policyStateAt rho hn (tickPrefix rho v i t q).1
    let rule := p _ (Model.pubOf E).ΔAC
    ∀ pre C a post, (pre, .fg (.attest C (some a)), post) ∈ (pollAttempts rule st).2 →
      ∃ h : Held (S.params (Model.pubOf E) hn), h.source = C ∧ h.row = a ∧ h.signedAt = t ∧
        h.eligibleAt = max t (rule.releaseAt st.base.self h.reportedAt t) ∧
        (EngineReleaseAt rho i a ∨
          h ∈ (policyStateAt rho hn (tickPrefix rho v i t (q + 1)).1).held) := by
  sorry

/-- Across any finite suffix (including arbitrary real restarts), a held item
survives unchanged unless its exact object really leaves the engine. -/
theorem held_retained_or_released
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {v : V} {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ rho.events.length)
    {h : Held (S.params (Model.pubOf E) hn)}
    (hh : h ∈ (policyStateAt rho hn (rho.stateBefore i v)).held)
    (hown : h.row.val = rho.ownKey v) :
    h ∈ (policyStateAt rho hn (rho.stateBefore j v)).held ∨
      ∃ l t, i ≤ l ∧ l < j ∧ h.eligibleAt ≤ t ∧
        rho.SendsAt v l t ∧ EngineReleaseAt rho l h.row := by
  sorry

/-- Each engine event occupies a half-open interval of cuts (possibly empty).
This links both boundaries for all validators, not just the event owner. -/
structure EventBoundaries
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) where
  first : Nat → Nat
  zero : first 0 = 0
  length : ∀ i < rho.events.length, first (i + 1) = first i + (M.cutLog i).length
  state_eq : ∀ i ≤ rho.events.length, ∀ v,
    tr.state (M.key v) (first i) = (policyStateAt rho hn (rho.stateBefore i v)).base.node
  index_eq : ∀ i h, i = first (M.occurrence i h).1 + (M.occurrence i h).2

def ProjectedRestarts
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M) : Prop :=
  ∀ v i t, rho.events[i]? = some (.restart v t) →
    B.first (i + 1) = B.first i + 1 ∧ tr.RestartAt (M.key v) (B.first i) ∧
      tr.time (B.first i) = t

/-- Open replay target: construct the projected cuts from the actual run. In particular
the new `.attest` cut must be separate from own receipt at `flush`. -/
theorem engine_projection (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hvalid : rho.ExecutionValid) (hn : 1 ≤ Fintype.card V) :
    ∃ (tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _))
      (H : Time → Set (Fin (Fintype.card V))) (U : Publication tr),
      ∃ (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M),
        ProjectedTickPollLogs rho hn M ∧ ProjectedRestarts rho hn M B := by
  sorry

theorem due_report_is_attempted
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid)
    (hmode : (p sp.n (Model.pubOf E).ΔAC).sourceChoice = .perReport)
    (hpublic : ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R → sp.toParams.IsPublic (tr.time i))
    {y i ell R t} (hreport : SA.ToFGAt tr.projAC y i ell R) (hit : tr.time i ≤ t)
    (hy : y ∈ H t) (hawake : tr.awake y t) (ht : sp.toParams.IsPublic t)
    (horizon : t ≤ rho.horizon)
    (hopen : SigningOpen (p sp.n (Model.pubOf E).ΔAC) y t)
    (hdue : signingDue (p sp.n (Model.pubOf E).ΔAC) y (tr.time i) ≤ t) :
    ∃ k s, i ≤ k ∧ tr.time k ≤ t ∧ tr.CallAt y k (.fg (.attest R s)) := by
  sorry

theorem exact_service_of_awake_duties
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    {g b D : Time} (coverage : SignDutyCoverage tr H (p sp.n (Model.pubOf E).ΔAC) g b D)
    (htrace : ∀ y i ell R t, SA.ToFGAt tr.projAC y i ell R → tr.time i ≤ t →
      y ∈ H t → tr.awake y t → sp.toParams.IsPublic t →
      SigningOpen (p sp.n (Model.pubOf E).ΔAC) y t →
      signingDue (p sp.n (Model.pubOf E).ΔAC) y (tr.time i) ≤ t →
      ∃ k s, i ≤ k ∧ tr.time k ≤ t ∧ tr.CallAt y k (.fg (.attest R s))) :
    ExactService tr H g b D := by
  sorry

/-- Snapshot-only seam. A discarded report needs a real dominating replacement;
latest-by-time order alone does not imply this across a restart. -/
theorem snapshot_attempts_of_duties
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {g b D : Time} (hb : b ≤ rho.horizon)
    (hm : (p sp.n (Model.pubOf E).ΔAC).sourceChoice = .roundSnapshot)
    (hduty : SignDutyCoverage tr H (p sp.n (Model.pubOf E).ΔAC) g b D)
    (hdominance : ∀ y i j k ell ell' C C' result, i ≤ j → j ≤ k → y ∈ H (tr.time k) →
      SA.ToFGAt tr.projAC y i ell C → SA.ToFGAt tr.projAC y j ell' C' →
      tr.CallAt y k (.fg (.attest C' result)) → Dominates tr H y i k C C') :
    Attempts tr H g b D := by
  sorry

/-- Preliminary opportunity only. An awake tick does not bound the queue rank. -/
structure RowPollOpportunity {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (g b R : Time) : Prop where
  due : ∀ v k a, tr.SignAt (M.key v) k a → max g (tr.time k) + R ≤ b →
    M.key v ∈ H (max g (tr.time k) + R) →
    ∃ (t : Time) (i : Nat), tr.time k ≤ t ∧ t ≤ max g (tr.time k) + R ∧
      rho.events[i]? = some (Model.Event.tick v t)

theorem release_of_poll_output
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    {g b R : Time}
    (hvalid : rho.ExecutionValid)
    (service : ∀ v k a, tr.SignAt (M.key v) k a → max g (tr.time k) + R ≤ b →
      M.key v ∈ H (max g (tr.time k) + R) →
      ∃ t i, t ≤ max g (tr.time k) + R ∧ rho.SendsAt v i t ∧
        EngineReleaseAt rho i (M.reindex a)) :
    ReleaseService U H g b R := by
  sorry

/-- An awake public duty in the next bounded interval, without asserting any release. -/
def PublicServiceWindow (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b slack : Time) : Prop :=
  ∀ y t, g ≤ t → t + slack ≤ b → y ∈ H (t + slack) →
    ∃ u, t ≤ u ∧ u ≤ t + slack ∧ sp.toParams.IsPublic u ∧ tr.awake y u

theorem bounded_publication_of_policy
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid) {g b R slack : Time}
    (horizon : b ≤ rho.horizon) (hslack : 0 ≤ slack) (hR : slack ≤ R)
    (hcal : ∀ y r t, 0 ≤ r → r ≤ t →
      (p sp.n (Model.pubOf E).ΔAC).releaseAt y r t ≤ t + (R - slack))
    (hwin : PublicServiceWindow tr H g b slack) : ReleaseService U H g b R := by
  sorry

theorem sign_duty_coverage_of_calendar
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (p : Rules sp.n)
    {g b D slack : Time} (hs : 0 ≤ slack) (hD : slack ≤ D)
    (hmode : p.missedSigning = .serveOverdue)
    (hcal : ∀ y t, signingDue p y t ≤ t + (D - slack))
    (hwin : PublicServiceWindow tr H g b slack) : SignDutyCoverage tr H p g b D := by
  sorry

/-- Skip needs an actual awake calendar point; an arbitrary awake public poll
cannot discharge the signing deadline. No such premise is needed for release. -/
theorem sign_duty_coverage_of_awake_appointments
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (p : Rules sp.n)
    {g b D slack : Time} (hs : 0 ≤ slack) (hD : slack ≤ D)
    (hcal : ∀ y t, signingDue p y t ≤ t + (D - slack))
    (happointments : ∀ y t, g ≤ t → t + slack ≤ b → y ∈ H (t + slack) →
      ∃ u, t ≤ u ∧ u ≤ t + slack ∧ sp.toParams.IsPublic u ∧
        tr.awake y u ∧ p.signAt y u = u) :
    SignDutyCoverage tr H p g b D := by
  sorry

/-- Establish the skip-mode coverage input under full participation. The next
appointment is rounded before the awake test, never rounded past the horizon. -/
theorem healthy_appointment_exists (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (p : Rules sp.n) {g b slack : Time} (hg : 0 ≤ g) (hc : CutObservations tr H)
    (hcalendar : ∀ y t, 0 ≤ t → t ≤ p.signAt y t ∧ p.signAt y t ≤ t + slack ∧
      sp.toParams.IsPublic (p.signAt y t) ∧ p.signAt y (p.signAt y t) = p.signAt y t)
    (hawake : ∀ y t, g ≤ t → t ≤ b → y ∈ H t → tr.awake y t) :
    ∀ y t, g ≤ t → t + slack ≤ b → y ∈ H (t + slack) →
      ∃ u, t ≤ u ∧ u ≤ t + slack ∧ sp.toParams.IsPublic u ∧
        tr.awake y u ∧ p.signAt y u = u := by
  sorry

theorem healthy_service_window (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    {g b : Time} (hg : 0 ≤ g)
    (hgrid : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + sp.Δ ∧ sp.toParams.IsPublic u)
    (hcut : CutObservations tr H)
    (hawake : ∀ y t, g ≤ t → t ≤ b → y ∈ H t → tr.awake y t) :
    PublicServiceWindow tr H g b sp.Δ := by
  sorry

theorem selected_tick_at_public_opportunity
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid) {v : V} {t : Time}
    (ht : 0 ≤ t) (hb : t ≤ rho.horizon) (hy : M.key v ∈ H t)
    (hp : sp.toParams.IsPublic t) (ha : tr.awake (M.key v) t) :
    ∃ i : Nat, rho.events[i]? = some (Model.Event.tick v t) := by
  sorry

/-- Sleepy and outage use individual awake opportunities, not the healthy full-population
service window. A ready reader supplies the opportunity only in its own awake interval. -/
theorem ready_public_opportunity (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    {g c t u : Time} {y : Fin sp.n}
    (hready : Regimes.Growing.ReadyAt tr H c y u)
    (hg : g ≤ t) (hl : max 0 (u - c - 1) ≤ t) (hu : t ≤ u)
    (hp : sp.toParams.IsPublic t) (hm : Antitone H) :
    y ∈ H t ∧ tr.awake y t := by
  sorry

/-- One service rule for sleepy and outage windows: do not run the deadline beyond a
ready validator's actual awake interval. Healthy coverage uses `healthy_service_window`. -/
theorem selected_tick_in_ready_interval
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid) {v : V} {g due deadline c t : Time}
    (hready : Regimes.Growing.ReadyAt tr H c (M.key v) deadline)
    (horizon : deadline ≤ rho.horizon) (hlo : max g due ≤ t)
    (hopen : max 0 (deadline - c - 1) ≤ t) (hclose : t ≤ deadline)
    (hpublic : sp.toParams.IsPublic t) :
    ∃ i : Nat, rho.events[i]? = some (Model.Event.tick v t) := by
  sorry

/-! The two non-Healthy interfaces deliberately claim a duty only when the actual
ready interval contains a whole rounding window. They do not claim this for every
owed row. For Outage before the fault gap use the synchronous leg (`g = 0`); for
recovery use `g = b₁`. The network service for the two legs is separate. -/

theorem selected_tick_after_clamp_in_ready_interval
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid) {v : V} {g due deadline c : Time}
    (hready : Regimes.Growing.ReadyAt tr H c (M.key v) deadline)
    (horizon : deadline ≤ rho.horizon)
    (hgrid : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + sp.Δ ∧ sp.toParams.IsPublic u)
    (hroom : max (max g due) (max 0 (deadline - c - 1)) + sp.Δ ≤ deadline) :
    ∃ (t : Time) (i : Nat), max g due ≤ t ∧ t ≤ deadline ∧ sp.toParams.IsPublic t ∧
      rho.events[i]? = some (Model.Event.tick v t) := by
  sorry

/-- Sleepy readers use `g = 0`; outage recovery readers use `g = b₁`.
The timing premise charges the calendar point inside that reader's ready interval. -/
theorem selected_calendar_tick_in_ready_interval
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {v : V} {g due deadline c : Time}
    (hready : Regimes.Growing.ReadyAt tr H c (M.key v) deadline)
    (horizon : deadline ≤ rho.horizon)
    (t : Time) (hlo : max (max g due) (max 0 (deadline - c - 1)) ≤ t)
    (hhi : t ≤ deadline) (hpub : sp.toParams.IsPublic t)
    (hcalendar : (p sp.n (Model.pubOf E).ΔAC).signAt (M.key v) t = t) :
    SigningOpen (p sp.n (Model.pubOf E).ΔAC) (M.key v) t ∧
      ∃ i : Nat, rho.events[i]? = some (Model.Event.tick v t) := by
  sorry

theorem release_at_awake_tick
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {v : V} {k : Nat} {a : FG.Att sp.n} {t : Time}
    (hs : tr.SignAt (M.key v) k a) (ht : tr.time k < t)
    (hawake : tr.awake (M.key v) t) (hhonest : M.key v ∈ H t)
    (hpublic : sp.toParams.IsPublic t)
    (hhorizon : t ≤ rho.horizon)
    (hdue : ∀ r, 0 ≤ r → r ≤ tr.time k →
      (p sp.n (Model.pubOf E).ΔAC).releaseAt (M.key v) r (tr.time k) ≤ t) :
    ReleasedBy U H (M.key v) a t := by
  sorry

/-- Same-run consumer seam. Proposal inclusion also needs parent-specific validity
and no earlier inclusion; a release timestamp alone cannot supply these. -/
theorem matching_row_carried_at_proposal
    (tr : GoldilocksTrace sp ro) (U : Publication tr) (H : Time → Set (Fin sp.n))
    {z y : Fin sp.n} {a : FG.Att sp.n} {j : Nat} {P C : Blk sp}
    (hreleased : ReleasedBy U H z a (tr.time j))
    (hown : tr.OwnBlockAt y j P) (hparent : P.parent = some C.root)
    (hvalid : (tr.state y j).fg.σ C.root |>.validAtt a)
    (hpool : a ∈ (tr.state y j).fg.atts)
    (hfresh : ¬ (tr.state y j).fg.OnChain C a)
    (hbuild : P.fgPayload = (tr.state y j).fg.proposalAttestations C) : a ∈ P.fgPayload := by
  sorry

end EngineStatements

section ResetStatements

open SA (Payload gbar)
open Healing (cutZ)
open Healing.Growing

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}

/-- The network clock starts at actual release, not at signing. The consumer must
budget delivery before the proposal's payload is read. -/
def ReleasedDelivery (U : Publication tr) (H : Time → Set (Fin sp.n)) (g ΔF b : Time) : Prop :=
  ∀ x a u, x ∈ H u → U.released x a u →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max u g) ΔF ≤ tr.time j →
      (∀ t, max u g ≤ t → t ≤ tr.time j → tr.awake y t) →
      ∃ k < j, tr.ProcessAttAt y k a ∧ tr.time k < tr.deadline y j (max u g) ΔF

/-- The non-row fields of the old service contract. They have no signing clock. -/
structure BaseService (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g : Time) : Prop where
  message : ∀ x i m,
    x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i P, x ∈ H (tr.time i) → tr.AcceptAt x i P ∨ tr.OwnBlockAt x i P →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) P
  relay : ∀ x i P, x ∈ H (tr.time i) → tr.AcceptAt x i P → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P →
      tr.BlockAcceptedBy y j (max (tr.time i) g) P

theorem received_row_survives_to_parent {y : Fin sp.n} {k j : Nat}
    {a : FG.Att sp.n} {C : Blk sp}
    (hk : k < j) (ha : tr.ProcessAttAt y k a) (hy : y ∈ H (tr.time j))
    (hC : C ∈ (tr.state y j).fg.tree)
    (hv : ((tr.state y j).fg.σ C.root).validAtt a)
    (hkeep : a ∈ (tr.state y (k + 1)).fg.atts → a ∈ (tr.state y j).fg.atts)
    (hreceipt : a ∈ (tr.state y (k + 1)).fg.atts ∨ (tr.state y j).fg.OnChain C a) :
    a ∈ (tr.state y j).fg.atts ∨ (tr.state y j).fg.OnChain C a := by
  sorry

/-- The pool is maintained by honest cuts and is part of the persistent FG store.
This is the producer needed by the parent-specific receipt consumer. -/
theorem received_row_retained_across_cuts
    (hcut : CutObservations tr H)
    (hpost : ∀ i y ℓ, tr.CallAt y i ℓ → tr.state y (i + 1) = tr.post i)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    (hunchanged : ∀ i y, ¬ tr.IsCall y i → tr.state y (i + 1) = tr.state y i)
    {y : Fin sp.n} {k j : Nat} {a : FG.Att sp.n}
    (hk : k < j) (ha : tr.ProcessAttAt y k a) (hy : y ∈ H (tr.time j)) :
    a ∈ (tr.state y j).fg.atts := by
  sorry

theorem row_service_of_publication (U : Publication tr) {g ΔF b R : Time}
    (hR : 0 ≤ R) (hrel : ReleaseService U H g b R) (hnet : ReleasedDelivery U H g ΔF b)
    {x y : Fin sp.n} {i j : Nat} {att : FG.Att sp.n}
    (hsign : tr.SignAt x i att) (hx : x ∈ H (max g (tr.time i) + R))
    (hxb : max g (tr.time i) + R ≤ b)
    (hy : y ∈ H (tr.time j)) (hcall : tr.IsCall y j) (hjb : tr.time j ≤ b)
    (hdeadline : tr.deadline y j (max g (tr.time i) + R) ΔF ≤ tr.time j)
    (hawake : ∀ u ≤ max g (tr.time i) + R,
      ReleasedBy U H x att u → ∀ t, max u g ≤ t → t ≤ tr.time j → tr.awake y t)
    (hmono : ∀ u ≤ max g (tr.time i) + R,
      tr.deadline y j (max u g) ΔF ≤ tr.deadline y j (max g (tr.time i) + R) ΔF) :
    ∃ k < j, tr.ProcessAttAt y k att := by
  sorry

end ResetStatements

section NetworkStatements

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {p : (n : Nat) → Time → Rules n}

/-- The exact release starts the network clock. Moving this start to the receiver's
wake is legal re-service; the sender need only be honest when it actually released. -/
theorem release_network_held
    (rho : Model.Run (compiled (delayedFamily S p)) E) {g : Time}
    (hnet : rho.log.PSync rho.point g) {v w : V}
    {o : (Model.protoOf (compiled (delayedFamily S p)) E).Object} {u start : Time}
    (hrelease : rho.releases v o u)
    (hfg : (Model.protoOf (compiled (delayedFamily S p)) E).isFGAtt o)
    (hv : rho.point.HonestAt v u)
    (hstart : u ≤ start) (horizon : max start g + E.ΔFG - 1 ≤ rho.horizon)
    (hw : rho.point.HonestAt w (max start g + E.ΔFG - 1))
    (hawake : rho.point.AwakeOnClosed w start (max start g + E.ΔFG - 1)) :
    rho.log.Held rho.point w o (max start g + E.ΔFG - 1) := by
  sorry

theorem release_network_held_before_outage
    (rho : Model.Run (compiled (delayedFamily S p)) E) {b₀ : Time}
    (hnet : rho.log.SyncUntil rho.point b₀) {v w : V}
    {o : (Model.protoOf (compiled (delayedFamily S p)) E).Object} {u start : Time}
    (hrelease : rho.releases v o u)
    (hfg : (Model.protoOf (compiled (delayedFamily S p)) E).isFGAtt o)
    (hv : rho.point.HonestAt v u) (hstart : u ≤ start)
    (hcut : start + E.ΔFG - 1 ≤ b₀) (hhorizon : start + E.ΔFG - 1 ≤ rho.horizon)
    (hw : rho.point.HonestAt w (start + E.ΔFG - 1))
    (hawake : rho.point.AwakeOnClosed w start (start + E.ΔFG - 1)) :
    rho.log.Held rho.point w o (start + E.ΔFG - 1) := by
  sorry

/-- A network witness alone is not a receipt cut. Reconcile the raw held object
with replay, allowing the reader's own release as well as delivery. -/
theorem held_row_processed_before_cut
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    {tr : GoldilocksTrace sp ro} {H U} (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {v : V} {a : FG.Att sp.n} {j : Nat} {d : Time}
    (hy : M.key v ∈ H (tr.time j)) (hj : tr.IsCall (M.key v) j) (hd : d < tr.time j)
    (hheld : rho.log.Held rho.point v (engineAttObj rho (M.reindex a)) d) :
    ∃ k < j, tr.ProcessAttAt (M.key v) k a ∧ tr.time k ≤ d := by
  sorry

end NetworkStatements

section ResetStatements

open SA (Payload gbar)
open Healing (cutZ)
open Healing.Growing

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}

/-- The first high signature is an internal-record boundary, not an engine-release
boundary. A separate invariant must bound the age and height of work held there. -/
def NoHighSignBefore (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g t : Time) : Prop :=
  ∀ y i a, y ∈ H (max (cutZ sp.toParams g) (tr.time i)) → tr.SignAt y i a →
    tr.time i < t → a.h ≤ HZ tr H g

/-- Before the first high sign, even rows still held locally are below the frontier.
The provenance hypothesis is about the current queue, not a publication fact. -/
theorem held_below_reset_frontier {g t : Time} {y : Fin sp.n} (h : Held sp)
    (hbefore : NoHighSignBefore tr H g t)
    (horigin : ∃ k, tr.SignAt y k h.row ∧ tr.time k = h.signedAt ∧
      y ∈ H (max (cutZ sp.toParams g) (tr.time k))) (ht : h.signedAt < t) :
    h.row.h ≤ HZ tr H g := by
  sorry

/-- A warm round consumes a carrier only after release and processing. The finite
induction must establish this without assuming old `LocalRun` group laws. -/
def WarmRoundRise (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (g b D R : Time) : Prop :=
  ∀ (s₀ N floor : Nat) (kindJ : Prop) (J : Blk sp),
    FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → sp.ts N + 2 * sp.Δ ≤ b →
    ∀ (u x : Nat) (i j : Nat) (P X : Blk sp),
    s₀ + 2 * sp.k ≤ u → x ≤ N →
    let z := proposer u
    let y := proposer x
    u + sp.toParams.fg.δt ≤ x → tr.time j ≤ b →
    z ∈ H (sp.ts u + sp.Δ) → y ∈ H (tr.time j) →
    tr.ProposesAt z i P → P.slot = u → tr.ProposesAt y j X → X.slot = x →
    NoHighSignBefore tr H g (sp.ts (u + 1) + 2 * sp.Δ + D + R + 1) →
    P ∈ (tr.state y (j + 1)).fg.tree ∧ X ∈ (tr.state y (j + 1)).fg.tree ∧
      ((tr.state y (j + 1)).fg.σ P.root).h + 1 ≤ ((tr.state y (j + 1)).fg.σ X.root).h

/-- The post-drain consumer must work on the actual proposal cuts. Either receipt
plus parent validity or the higher-report head route must supply the height step. -/
def PublishedAnchorSteps (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (g a b : Time) (c : Nat) : Prop :=
  ∀ (s₀ : Nat) (P : Fin 4 → Blk sp),
    (∀ i, HonestProposalRun tr H proposer (s₀ + ![0, c, 2 * c, 3 * c] i) (P i)) →
    Healing.drainTime sp a ≤ sp.ts s₀ → sp.ts (s₀ + 3 * c) ≤ b →
    (∃ y k, y ∈ H (tr.time k) ∧ P 0 ∈ (tr.state y k).fg.tree ∧
      HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h) →
    ∀ i : Fin 3, Obligations.Growing.AnchorStepAt tr H (P i.castSucc) (P i.succ)

/-- A pre-reset round's timeout quorum is tied to its later proposal, not merely
to published timeouts at the right height. This is the input to the store rise. -/
def WarmTimeoutRows (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (U : Publication tr) (proposer : Nat → Fin sp.n) (g b D R : Time) : Prop :=
  ∀ (s₀ N floor : Nat) (kindJ : Prop) (J : Blk sp),
    FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → sp.ts N + 2 * sp.Δ ≤ b →
    ∀ {u x : Nat} {i j : Nat} {P X C : Blk sp},
    s₀ + 2 * sp.k ≤ u → u + sp.toParams.fg.δt ≤ x → x ≤ N →
    let z := proposer u
    let y := proposer x
    z ∈ H (sp.ts u + sp.Δ) → y ∈ H (tr.time j) → X.slot = x →
    P.slot = u → tr.ProposesAt z i P → tr.ProposesAt y j X → X.parent = some C.root →
    C ∈ (tr.state y j).fg.tree → tr.time j ≤ b →
    NoHighSignBefore tr H g (sp.ts (u + 1) + 2 * sp.Δ + D + R + 1) →
    (((tr.state y j).fg.σ P.root).h < ((tr.state y j).fg.σ C.root).h) ∨
    ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ v ∈ ids, ∃ a k, tr.SignAt v k a ∧ a.val = v ∧
        a.h = ((tr.state y j).fg.σ P.root).h ∧
        a.h = ((tr.state y j).fg.σ C.root).h ∧ a.T = ((tr.state y j).fg.σ C.root).Th ∧
        ((tr.state y j).fg.σ C.root).validAtt a ∧ ReleasedBy U H v a (tr.time j) ∧
        (a ∈ X.fgPayload ∨ (tr.state y j).fg.OnChain C a)

/-- Store-transition step after the pre-reset row producer supplies rows of the
actual consuming parent. Timeout and target rows both contribute to `prog`.
The progress bits must be at the parent's own entry;
`validAtt` alone also admits older finality rows and is not enough. -/
theorem warm_timeout_parent_rises {y : Fin sp.n} {j : Nat} {P X C : Blk sp}
    {acp₀ : Payload sp.n}
    (hpre : Store.Reachable acp₀ (tr.state y j).fg)
    (hpost : Store.Reachable acp₀ (tr.state y (j + 1)).fg)
    (hP : P ∈ (tr.state y j).fg.tree) (hC : C ∈ (tr.state y j).fg.tree)
    (hX : X ∈ (tr.state y (j + 1)).fg.tree) (hparent : X.parent = some C.root)
    (hstore : (tr.state y j).fg.onBlock X = some (tr.state y (j + 1)).fg)
    (hheight : ((tr.state y j).fg.σ P.root).h = ((tr.state y j).fg.σ C.root).h)
    (hwait : ((tr.state y j).fg.σ C.root).ThSlot + sp.toParams.fg.δt ≤ X.slot)
    (hrows : ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ v ∈ ids, ∃ a : FG.Att sp.n, a.val = v ∧
        a.h = ((tr.state y j).fg.σ C.root).h ∧ a.T = ((tr.state y j).fg.σ C.root).Th ∧
        (a ∈ X.fgPayload ∨ (tr.state y j).fg.OnChain C a)) :
    ((tr.state y (j + 1)).fg.σ P.root).h + 1 ≤ ((tr.state y (j + 1)).fg.σ X.root).h := by
  sorry

/-- Evidence a pre-reset report window owes the warm-round argument. This is
not a schedule assumption: the drain proof must supply it for the actual
proposals. The named report window also bounds signing and publication. -/
def WarmReportWindow (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (g b D R : Time) : Prop :=
  ∀ (s₀ N floor : Nat) (kindJ : Prop) (J : Blk sp),
    FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → sp.ts N + 2 * sp.Δ ≤ b →
    ∀ {u x i j : Nat} {P X C : Blk sp},
    s₀ + 2 * sp.k ≤ u → u + sp.toParams.fg.δt ≤ x → x ≤ N →
    proposer u ∈ H (sp.ts u + sp.Δ) → proposer x ∈ H (tr.time j) →
    P.slot = u → X.slot = x → tr.ProposesAt (proposer u) i P →
    tr.ProposesAt (proposer x) j X → X.parent = some C.root →
    C ∈ (tr.state (proposer x) j).fg.tree → tr.time j ≤ b →
    let d := sp.ts (u + 1) + 2 * sp.Δ
    let h := ((tr.state (proposer x) j).fg.σ P.root).h
    NoHighSignBefore tr H g (d + D + R + 1) →
    h < ((tr.state (proposer x) j).fg.σ C.root).h ∨
      (gbar g ≤ d ∧ d + D + R ≤ tr.time j ∧
        ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
          ∀ v ∈ ids, v ∈ H (max (cutZ sp.toParams g) (d + D + R)) ∧
            ∃ l ell C', SA.ToFGAt tr.projAC v l ell C' ∧ tr.time l ≤ d ∧
              Anc (tr.HonestBlocksAt H) P C' ∧ h ≤ ((tr.state v l).fg.σ C'.root).h)

/-- Pre-reset assembly. The report window is upstream of signing, and the
local bridge is downstream of signing and actual receipt. The bridge must
discharge the low-floor refusal and parent-entry comparison, not assume that
the earlier report signed the timeout row. -/
theorem warm_timeout_rows_of_report_window {g b D R : Time}
    {proposer : Nat → Fin sp.n} (U : Publication tr)
    (hwindow : WarmReportWindow tr H proposer g b D R)
    (hlocal : ∀ (v y : Fin sp.n) (l j : Nat) (C' P X C : Blk sp) (d : Time),
      d + D + R ≤ tr.time j → v ∈ H (max (cutZ sp.toParams g) (d + D + R)) →
      (∃ ell, SA.ToFGAt tr.projAC v l ell C') → tr.time l ≤ d →
      Anc (tr.HonestBlocksAt H) P C' →
      ((tr.state y j).fg.σ P.root).h ≤ ((tr.state v l).fg.σ C'.root).h →
      tr.ProposesAt y j X → X.parent = some C.root → C ∈ (tr.state y j).fg.tree →
      NoHighSignBefore tr H g (d + D + R + 1) →
      ((tr.state y j).fg.σ P.root).h < ((tr.state y j).fg.σ C.root).h ∨
        ∃ a k, tr.SignAt v k a ∧ a.val = v ∧
          a.h = ((tr.state y j).fg.σ P.root).h ∧
          a.h = ((tr.state y j).fg.σ C.root).h ∧ a.T = ((tr.state y j).fg.σ C.root).Th ∧
          ((tr.state y j).fg.σ C.root).validAtt a ∧ ReleasedBy U H v a (tr.time j) ∧
          (a ∈ X.fgPayload ∨ (tr.state y j).fg.OnChain C a)) :
    WarmTimeoutRows tr H U proposer g b D R := by
  sorry

/-- The signed records and high-origin comparison are needed before using a
refusal as evidence of a suitable historical row. -/
theorem high_records_of_high_source_agreement {g b : Time}
    (hcut : CutObservations tr H) (hsrc : SourceFacts tr H) (horigin : RecordOrigins tr H)
    (hhigh : HighReportOrigins tr H g b)
    (hentry : ∀ x i j B z k l C, HighOrigin tr H g x i j B →
      HighOrigin tr H g z k l C → tr.time i ≤ b → tr.time k ≤ b →
      Compatible (tr.HonestBlocksAt H) B C)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (hnc : Compose.NoCollRun dg tr)
    {acp₀ : Payload sp.n}
    (hreachable : ∀ y k, y ∈ H (tr.time k) → Store.Reachable acp₀ (tr.state y k).fg)
    (hbounded : ∀ y k h root, y ∈ H (tr.time k) → tr.time k ≤ b →
      HZ tr H g + 1 ≤ h →
      ((tr.state y k).record.target h = some root ∨ root ∈ (tr.state y k).record.timeout h ∨
        (tr.state y k).record.lock h = some root) →
      ∃ x i j B T, HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧
        T ∈ tr.HonestBlocksAt H ∧ Anc (tr.HonestBlocksAt H) T B ∧ T.root = root) :
    HighRecordAgreement tr H g b := by
  sorry

/-- Unlike the landed reset kernel, this target does not assume `NoRestartUpTo`.
Its service is for a GST-clamped deadline and is indexed by actual release. -/
theorem reset_of_policy_service {g ΔF b r D R : Time} {G Ld : Nat}
    {K : SA.CommitteeDict sp.n} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (U : Publication tr)
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hawake : ∀ y t, gbar g ≤ t → t ≤ b → y ∈ H t → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hbase : BaseService tr H g)
    (hsvc : ReleasedDelivery U H g ΔF b) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hattempt : Attempts tr H (gbar g) b D) (hrel : ReleaseService U H (gbar g) b R)
    (hrise : WarmRoundRise tr H proposer g b D R)
    (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hΔF : 6 * sp.Δ + D + R + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * (D + R) ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ → sp.ts N + 2 * sp.Δ <
      Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * (D + R) →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld + 5 * (D + R) := by
  sorry

/-- Collector and FG forwarding are distinct obligations at the same anchor gap.
This is the window consumer interface; reset/high-origin facts must be ported to
the policy trace rather than assuming a legacy run. -/
theorem published_anchor_steps {g a b ΔF D R : Time} {c : Nat}
    {proposer : Nat → Fin sp.n} (U : Publication tr)
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hreset : IsReset tr H g a) (hbase : BaseService tr H g)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hsupply : PublishedRows (H := H) U g b D R)
    (hdelivery : ReleasedDelivery U H g ΔF b)
    (hawake : ∀ y t, gbar g ≤ t → t ≤ b → y ∈ H t → tr.awake y t)
    (hc : 2 ≤ c) (hspan : 3 * c ≤ sp.toParams.fg.δt) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hforward : 6 * sp.Δ + D + R + ΔF ≤ 4 * sp.Δ * c)
    (hcollector : 7 * sp.Δ + D + R ≤ 4 * sp.Δ * c) :
    PublishedAnchorSteps tr H proposer g a b c := by
  sorry

end ResetStatements

section EndpointStatements

variable (S : Setup) (A window : ContractAssumptions S)
  (p : (n : Nat) → Time → Rules n) (B : Budget)

/-- Timing only. A separate placement proof must show that these budgets pay for the
actual selected window, actual relay, and the reset induction. -/
theorem forwarding_and_collector_room (h : TimingRoom A window B) {Δ ΔF : Time}
    (hΔ : 0 ≤ Δ) (hnet : ΔF ≤ ((windowContract S A window B).params.fgDelay : Time) * Δ) :
    6 * Δ + (B.total : Time) * Δ + ΔF ≤ 4 * Δ * (window.fgSlots : Time) ∧
      7 * Δ + (B.total : Time) * Δ ≤ 4 * Δ * (window.fgSlots : Time) := by
  sorry

theorem calendar_appointments_fit {period offset t : Time} (hp : 0 < period) :
    t ≤ nextAppointment period offset t ∧ nextAppointment period offset t < t + period ∧
      period ∣ (nextAppointment period offset t - offset) := by
  sorry

/-- An aligned stagger remains on the public grid and is a fixed point when
started at its own appointment. This is the premise needed by skip mode. -/
theorem aligned_appointment {Δ offset t : Time} (hΔ : 0 < Δ) (hoff : Δ ∣ offset) :
    Δ ∣ nextAppointment (4 * Δ) offset t ∧
      nextAppointment (4 * Δ) offset (nextAppointment (4 * Δ) offset t) =
        nextAppointment (4 * Δ) offset t := by
  sorry

/-- The grid constructions pay the actual appointment after the GST clamp,
including when the original due point preceded GST. The source choice has no
effect on this calendar bound. -/
theorem round_start_schedule_bounds {Δ : Time} (hΔ : 1 ≤ Δ)
    (offsets : (n : Nat) → Option (Fin n → Time))
    (aligned : ∀ n (f : Fin n → Time), offsets n = some f → ∀ y, Δ ∣ f y)
    (source : SourceChoice) (missed : MissedSigning) :
    ScheduleBounds (fun n tick =>
      { Rules.roundStart n tick (offsets n) with sourceChoice := source, missedSigning := missed })
      Δ ⟨5, 4, 0⟩ := by
  sorry

theorem sign_at_release_schedule_bounds {Δ : Time} (hΔ : 1 ≤ Δ)
    (offsets : (n : Nat) → Fin n → Time) (aligned : ∀ n y, Δ ∣ offsets n y)
    (source : SourceChoice) (missed : MissedSigning) :
    ScheduleBounds (fun n tick =>
      { Rules.signAtRelease n tick (offsets n) with
        sourceChoice := source, missedSigning := missed }) Δ ⟨5, 1, 0⟩ := by
  sorry

theorem responsive_family : family S Rules.responsive = goldilocks S := by
  sorry

theorem same_network_range : (windowContract S A window B).params.fgDelay = A.fgDelay := by
  sorry

theorem zero_contract (hB : B.total = 0) :
    windowContract S A A B = goldilocksContract A (contract_coefficients S A) := by
  sorry

theorem final_heal_reserve (X : ℕ+) :
    (contract_catchUp S A : Nat) + healMargin S X + 5 * B.total ≤
      (coefficients S A B).heal .final X := by
  sorry

/-- Healthy liveness for one capability, on the actual policy family. -/
def HealthyLiveSupply (cap : Capability) : Prop :=
  let K := windowContract S A window B
  ∀ (V : Type) [Fintype V] [DecidableEq V] g,
    schema.output cap = some g → ∀ (i : K.Idx) (gst : Time),
    (Sys (family S p) V).Holds
      (fun r => (Sys (family S p) V).Healthy (shapeProgress (family S p) V).toExternal
          K gst r ∧
        (Sys (family S p) V).prog (shapeProgress (family S p) V) K cap i
          ((Sys (family S p) V).ready K gst r) ((Sys (family S p) V).pt r).horizon r)
      (fun r => ProposalLiveReady r.2 ((Sys (family S p) V).cDur K r) g
        ((Sys (family S p) V).heal K cap i gst r) (K.params.latency cap i))

/-- Independent endpoint suppliers. Field types are the existing claim contracts;
no final liveness conclusion is hidden among the non-final inputs. -/
structure OtherClaims (F : ChainShapeFamily schema Info) (K : Contract ProgressReq)
    (V : Type) [Fintype V] [DecidableEq V] : Prop where
  outputValid : (Sys F V).HoldsAlways fun r => ∀ c g, schema.output c = some g → OutputValid r.2 g
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → schema.output c₁ = some g₁ →
    schema.output c₂ = some g₂ → (Sys F V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂
  finalMonotone : ∀ g, schema.output .final = some g →
    (Sys F V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0
  finalAccountable : ∀ g, schema.output .final = some g → (Sys F V).Holds (fun _ => True)
    fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → schema.output cap = some g →
    (Sys F V).Holds ((Sys F V).Sleepy (shapeProgress F V).toExternal K) fun r =>
      (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → schema.output cap = some g →
    ∀ i : K.Idx, (Sys F V).Holds
      (fun r => (Sys F V).Sleepy (shapeProgress F V).toExternal K r ∧
        (Sys F V).prog (shapeProgress F V) K cap i 0 ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap i)
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → schema.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => (Sys F V).Healthy (shapeProgress F V).toExternal K gst r ∧
        (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K gst r)
          ((Sys F V).heal K cap i gst r) r)
      fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g ((Sys F V).heal K cap i gst r)
  persists : ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys F V).Holds ((Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁) fun r =>
      (chainTrace r.2).ProtectedReadyFrom ((Sys F V).cDur K r) g (resilienceTarget schema g) T
        ((Sys F V).recoveryAt K b₁ r)

def PolicySchedule : Prop := p = Rules.responsive ∨ ∀ Δ : Time, 1 ≤ Δ → ScheduleBounds p Δ B

noncomputable def policyIndex (X : ℕ+) : (windowContract S A window B).Idx := X

/-- One query of the actual compiled policy. The legacy `FinalQueryAt` cannot
serve as the input here because its run is typed over a different family. -/
structure PolicyFinalQuery (V : Type) [Fintype V] [DecidableEq V] where
  run : (Sys (family S p) V).Run
  positive : 1 ≤ Fintype.card V
  gst : Time
  query : Time
  index : ℕ+
  valid : (Sys (family S p) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (family S p) V).Healthy (shapeProgress (family S p) V).toExternal
    (windowContract S A window B) gst run
  progress : (Sys (family S p) V).prog (shapeProgress (family S p) V)
    (windowContract S A window B) .final (policyIndex S A window B index)
    ((Sys (family S p) V).ready (windowContract S A window B) gst run) run.2.horizon run
  mature : (Sys (family S p) V).heal (windowContract S A window B) .final
    (policyIndex S A window B index) gst run ≤ query
  bounded : query + ((windowContract S A window B).params.latency .final
    (policyIndex S A window B index) : Time) * run.1.ΔAC ≤ run.2.horizon

theorem policy_final_query_slot_room
    {V : Type} [Fintype V] [DecidableEq V] (Q : PolicyFinalQuery S A window p B V) :
    Q.query + 4 * ((Q.index : Nat) + 3 * window.fgSlots) * Q.run.1.ΔAC + Q.run.1.ΔAC ≤
      Q.query + ((windowContract S A window B).params.latency .final
        (policyIndex S A window B Q.index) : Time) * Q.run.1.ΔAC := by
  sorry

/-- Recurrence must be read from the delayed family's real progress premise,
not from a run of the legacy family with the same parameters. -/
theorem policy_final_window_slots
    {V : Type} [Fintype V] [DecidableEq V] (Q : PolicyFinalQuery S A window p B V)
    (a : Time)
    (hplace : let sp := S.params (Model.pubOf Q.run.1) Q.positive
      max (max ((Sys (family S p) V).ready (windowContract S A window B) Q.gst Q.run) 0)
        (sp.ts (sp.slot a + 2 * sp.k + 5) - 1) +
        ((Q.index : Nat) + S.δt : Nat) * (4 * sp.Δ) ≤ Q.query + 4 * sp.Δ) :
    let sp := S.params (Model.pubOf Q.run.1) Q.positive
    let c := window.fgSlots
    let deadline := Q.query + ((windowContract S A window B).params.latency .final
      (policyIndex S A window B Q.index) : Time) * Q.run.1.ΔAC
    ∃ u s₀ : Nat, 0 < u ∧ u + sp.toParams.fg.δt ≤ s₀ ∧
      Healing.drainTime sp a ≤ sp.ts u ∧ SA.gbar Q.gst + 4 * sp.Δ ≤ sp.ts u ∧
      HonestReadyIn Q.run.2.point Q.run.2.key (fun s => Q.run.2.sel (.proposer s)) u
        ((Sys (family S p) V).cDur (windowContract S A window B) Q.run) (sp.ts u) sp.Δ ∧
      Q.query < sp.ts s₀ ∧ sp.ts (s₀ + 3 * c) + sp.Δ ≤ deadline ∧
      ∀ i : Fin 4,
        let s := s₀ + ![0, c, 2 * c, 3 * c] i
        sp.ts s ≤ Q.run.2.horizon ∧
        HonestReadyIn Q.run.2.point Q.run.2.key (fun s => Q.run.2.sel (.proposer s)) s
          ((Sys (family S p) V).cDur (windowContract S A window B) Q.run) (sp.ts s) sp.Δ := by
  sorry

theorem obligations_of_policy_suppliers
    (hhealthy : ∀ cap, HealthyLiveSupply S A window p B cap)
    (hguard : GuardIdleAlways (family S p))
    (hother : ∀ (V : Type) [Fintype V] [DecidableEq V],
      OtherClaims (family S p) (windowContract S A window B) V)
    (hadmissible : (windowContract S A window B).params.Admissible)
    (hfits : ProgressFits (windowContract S A window B) (family S p))
    (htolerant : ProgressTolerant schema (windowContract S A window B)) :
    ShapeObligationsAs .ebbAndFlow (family S p) (windowContract S A window B) := by
  sorry

/-- End-to-end target under the existing healthy regime, with no per-run
signing/publication premise. If the bounded-queue or reset targets fail, this statement
requires a handler or contract revision before proof work. -/
theorem final_live_of_policy
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B) :
    HealthyLiveSupply S A window p B .final := by
  sorry

theorem policy_other_claims
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B)
    (V : Type) [Fintype V] [DecidableEq V] :
    OtherClaims (family S p) (windowContract S A window B) V := by
  sorry

theorem policy_nonfinal_healthy_live
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B)
    {cap : Capability} (hc : cap = .stable ∨ cap = .available) :
    HealthyLiveSupply S A window p B cap := by
  sorry

theorem policy_guard_idle : GuardIdleAlways (family S p) := by
  sorry

theorem policy_contract_side_conditions (htiming : TimingRoom A window B) :
    (windowContract S A window B).params.Admissible ∧
      ProgressFits (windowContract S A window B) (family S p) ∧
      ProgressTolerant schema (windowContract S A window B) := by
  sorry

theorem headline_of_policy_obligations
    (h : ShapeObligationsAs .ebbAndFlow (family S p) (windowContract S A window B))
    (V : Type) [Fintype V] [DecidableEq V] :
    CorrectProtocol (Model.sysOf schema (compiled (family S p)) V)
      (shapeProgress (family S p) V) (windowContract S A window B) ∧
      (windowContract S A window B).params.OptimalFaultTolerance := by
  sorry

theorem headline_with_excuses
    (h : ShapeObligationsAs .ebbAndFlow (family S p) (windowContract S A window B))
    (V : Type) [Fintype V] [DecidableEq V] :
    CorrectProtocolWithExcuses (Model.sysOf schema (compiled (family S p)) V)
      (shapeProgress (family S p) V) (windowContract S A window B)
      (fun r => r.2.StructuralValid) (fun r => r.2.BindingFailure) := by
  sorry

end EndpointStatements

end Consensus.Goldilocks.VotingPolicyPlan
