module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.VotingPolicyBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients

public section

/-! # Planning interfaces for independent FG signing and release rules

This is a proposal for review, not the installed node or a certified milestone.
-/

-- Keep the statement review in one leaf until the approved work-package split.
set_option linter.style.longFile 2600

namespace Consensus.Goldilocks.VotingPolicyPlan

open SA (SAParams ReplayOrder)
open AsChainShape Shape Blocks
open Obligations (healthyResetCoeff)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {binding : VoteBinding}

/-- Signing and release calendars are independent. Missed signing appointments
neither edit an already signed row nor change its release calendar. -/
structure Rules (n : Nat) where
  signAt : Fin n → Time → Time
  releaseAt : Fin n → Time → Time
  /-- True: snapshot at the leading poll, before the proposal. -/
  beforeProposal : Fin n → Bool := fun _ => false

def Rules.responsive (n : Nat) (_Δ : Time) : Rules n :=
  ⟨fun _ t => t, fun _ t => t, fun _ => false⟩

/-- Fixed signing and independently scheduled release. For a fixed signing time with
immediate publication take `nextRelease y t = t`; to sign at release take `nextSign`
to be the release calendar and again publish immediately. -/
def Rules.scheduled {n : Nat} (nextSign nextRelease : Fin n → Time → Time) : Rules n :=
  ⟨nextSign, nextRelease, fun _ => true⟩

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
  signedAt : Time
  eligibleAt : Time
  row : FG.Att sp.n

structure PolicyState (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (binding : VoteBinding) where
  base : State sp ro binding
  held : List (Held sp) := []
  lastSnapshot : Option Time := none
  leading : Bool := false

def signingDue (p : Rules sp.n) (y : Fin sp.n) (t : Time) : Time :=
  let earliest := t + if p.beforeProposal y then 1 else 0
  max earliest (p.signAt y earliest)

/-- Missed signing appointments are skipped. The cursor only prevents a repeat
snapshot at the same time, including across restart. -/
def SigningOpen (p : Rules sp.n) (st : PolicyState sp ro binding) : Prop :=
  p.signAt st.base.self st.base.now = st.base.now ∧ st.lastSnapshot ≠ some st.base.now

abbrev CutLog (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :=
  List (NodeState (goldilocksNode sp ro) × Cut (goldilocksNode sp ro) ×
    NodeState (goldilocksNode sp ro))

/-- Read `ac_to_fg` exactly once from this poll's current view. Only its actual
output can be attempted. A refusal leaves all earlier frozen rows untouched. -/
noncomputable def snapshot (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × CutLog sp ro :=
  let t := st.base.now
  let (nd, lbl, src) := Node.acToFG st.base.node t
  let read := (st.base.node, lbl, nd)
  let st' := { st with base := { st.base with node := nd }, lastSnapshot := some t }
  match src with
  | none => (st', [read])
  | some C =>
    match nd.fg.attest nd.record st.base.self C with
    | none => (st', [read, (nd, .fg (.attest C none), nd)])
    | some (a, record) =>
      let u := max t (p.releaseAt st.base.self t)
      let post := { nd with record }
      ({ st' with base := { st'.base with node := post }, held := st.held ++ [⟨C, t, u, a⟩] },
        [read, (nd, .fg (.attest C (some a)), post)])

/-- Keep eligible items in append order and skip ineligible items without re-signing.
Every executed poll can flush overdue rows, even when signing is off-calendar.
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
  open Classical in
  let phase := if p.beforeProposal st.base.self then st.leading else st.base.fgDue
  let r := if phase = true ∧ sp.toParams.IsPublic st.base.now ∧ SigningOpen p st then
    snapshot p st else (st, [])
  ({ r.1 with base := { r.1.base with fgDue := false } }, r.2)

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
  init k q := ⟨(nodeOps sp ro binding).init k q, [], none, false⟩
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
  appointment : ∀ n y g t, 0 ≤ t →
    let earliest := t + if (p n Δ).beforeProposal y then 1 else 0
    let due := max earliest ((p n Δ).signAt y earliest)
    ∃ u, max g due ≤ u ∧ u ≤ max g t + B.signSteps * Δ ∧ Δ ∣ u ∧ (p n Δ).signAt y u = u
  /-- A row is frozen at a public signing poll, never between grid points. -/
  release : ∀ n y t, 0 ≤ t → Δ ∣ t →
    max t ((p n Δ).releaseAt y t) + Δ ≤ t + B.publishSteps * Δ

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

/-- Compare the historical source with the source of the current attempt. An
appointment by itself does not imply this relation. -/
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
      t ≤ max g (tr.time i) + D ∧ sp.toParams.IsPublic t ∧ tr.awake y t ∧ p.signAt y t = t

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

/-- A joined appointment at its actual snapshot cut. It need not emit a report. -/
def AppointmentCohort (_tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (appointment : Fin sp.n → Nat → Time → Prop) (d deadline b : Time) : Prop :=
  ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
    ∀ z ∈ ids, z ∈ H b ∧ ∃ k t, appointment z k t ∧ d ≤ t ∧ t ≤ deadline

/-- The entry is selected from the earlier anchor as held at the actual
consuming proposal, not from an arbitrary later tree. -/
structure AnchorRowDemand (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g a b D R : Time) (z y : Fin sp.n) (i m : Nat) (P Q C T : Blk sp) : Prop where
  drained : Healing.drainTime sp a ≤ sp.ts P.slot
  origin : tr.ProposesAt z i P
  originHonest : z ∈ H (sp.ts P.slot + sp.Δ)
  consuming : tr.ProposesAt y m Q
  consumingHonest : y ∈ H (tr.time m)
  bounded : tr.time m ≤ b
  parent : Q.parent = some C.root
  held : C ∈ (tr.state y m).fg.tree ∧ P ∈ (tr.state y m).fg.tree ∧ T ∈ (tr.state y m).fg.tree
  branch : (tr.state y m).fg.Anc P C
  entry : Healing.EntryOf (tr.state y m).fg P T ((tr.state y m).fg.σ P.root).h
  notHigher : ((tr.state y m).fg.σ C.root).h ≤ ((tr.state y m).fg.σ P.root).h
  high : HZ tr H g + 2 ≤ ((tr.state y m).fg.σ P.root).h
  afterGST : gbar g ≤ sp.ts (P.slot + 1) + 2 * sp.Δ
  beforeConsumer : sp.ts (P.slot + 1) + 2 * sp.Δ + D + R < tr.time m
  noEarlierHigher : ∀ x r ell B, x ∈ H (tr.time r) → SA.ToFGAt tr.projAC x r ell B →
    Anc (tr.HonestBlocksAt H) P B → tr.time r < sp.ts (P.slot + 1) + 2 * sp.Δ →
    ((tr.state x r).fg.σ B.root).h ≤ ((tr.state y m).fg.σ T.root).h

/-- Supply only the entry demanded by the consuming edge. Joined polls through
`d + D` are opportunities; they do not themselves supply sources. -/
structure PublishedRows (U : Publication tr) (appointment : Fin sp.n → Nat → Time → Prop)
    (g a b D R : Time) : Prop where
  supply : ∀ {z y i m P Q C T}, AnchorRowDemand tr H g a b D R z y i m P Q C T →
    let σT := (tr.state y m).fg.σ T.root
    let d := sp.ts (P.slot + 1) + 2 * sp.Δ
    AppointmentCohort tr H appointment d (d + D) b →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) (d + D + R)) ∧ ∃ a j,
        tr.SignAt z j a ∧ tr.time j ≤ d + D ∧ ReleasedBy U H z a (d + D + R) ∧
        a.val = z ∧ a.h = σT.h ∧ a.T = T.root ∧ a.timeout = false ∧
        (σT.previousHeightJustified → a.fin = some (σT.hj, σT.J))) ∨
    ∃ x r ell B, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r ell B ∧
      Anc (tr.HonestBlocksAt H) P B ∧ d ≤ tr.time r ∧ tr.time r ≤ d + D ∧
      σT.h < ((tr.state x r).fg.σ B.root).h

/-- An update's lock need not survive in the same form. Check viability,
fastness, expiry and freshness in the state that actually runs the poll. -/
theorem candidate_at_anchor_poll {z k u} {P L : Blk sp}
    (hviable : L ∈ (Node.frame (tr.state z k)).viableTree (Node.frame (tr.state z k)).tree)
    (hbranch : (tr.state z k).fg.Anc P L)
    {lock : SA.Lock}
    (hlive : lock ∈ SA.liveLocks sp (tr.state z k).ac.locks (Node.frame (tr.state z k)) u)
    (hroot : lock.block = L.root) (hfast : lock.fast = true) (hage : sp.slot u ≤ lock.slot + 2) :
    L ∈ SA.toFGCandidates sp (tr.state z k).ac (Node.frame (tr.state z k)) u ∧
      (tr.state z k).fg.Anc P L := by
  sorry

/-- Calendar arithmetic only: the slot of the write supplying the candidate
must still fit at the selected poll. This does not show the lock is retained. -/
theorem anchor_poll_age_room {s : Nat} {u : Time}
    (hu : 0 ≤ u) (hbefore : u < sp.ts (s + 3 : Nat)) : sp.slot u ≤ s + 2 := by
  sorry

/-- Replay the update's actual fast-lock write to the selected poll. The
retention proof must track its viable move-back, not equality of lock sets. -/
theorem update_candidate_at_anchor_poll {z j k s u} {P L : Blk sp} {CV}
    (hwrite : Compose.StoredFastLockAt tr z j s L CV) (hjk : j < k)
    (hretained : let st := tr.state z k
      ∃ lock ∈ st.ac.locks, ∃ L' ∈ (Node.frame st).tree,
        lock.slot = s ∧ lock.fast = true ∧ lock.block = L'.root ∧ sp.slot u ≤ lock.expiry ∧
        st.fg.Anc L' L ∧ st.fg.Anc P ((Node.frame st).viableAncestor L'))
    (hage : sp.slot u ≤ s + 2) :
    ∃ B ∈ SA.toFGCandidates sp (tr.state z k).ac (Node.frame (tr.state z k)) u,
      (tr.state z k).fg.Anc P B := by
  sorry

/-- The valid-run producer must select a quorum with this evidence. In the
empty case a historical attempt is required even if restart reset the cursor. -/
def AnchorPollAvailable (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (P : Blk sp) (z : Fin sp.n) (k : Nat) (u : Time) : Prop :=
  let st := tr.state z k
  (∃ L ∈ SA.toFGCandidates sp st.ac (Node.frame st) u, st.fg.Anc P L) ∨
  (SA.toFGCandidates sp st.ac (Node.frame st) u = ∅ ∧
    ∃ r ell B s, r + 1 < k ∧ tr.time (r + 1) ≤ u ∧ SA.ToFGAt tr.projAC z r ell B ∧
      tr.CallAt z (r + 1) (.fg (.attest B s)) ∧ Anc (tr.HonestBlocksAt H) P B)

theorem durable_held_and_snapshot_cursor (st : PolicyState sp ro binding)
    (t : Time) (y : Fin sp.n) :
    (restore y st t).held = st.held ∧
      (restore y st t).lastSnapshot = st.lastSnapshot := by
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

theorem published_rows_of_appointments (U : Publication tr) {g b a D R : Time}
    {appointment : Fin sp.n → Nat → Time → Prop}
    (hreset : IsReset tr H g a) (hab : a ≤ b) (hcz : cutZ sp.toParams g ≤ b)
    (hcut : CutObservations tr H) (hmatching : MatchingRows tr H g b)
    (hsource : ∀ {w y i m P Q C T}, AnchorRowDemand tr H g a b D R w y i m P Q C T →
      let d := sp.ts (P.slot + 1) + 2 * sp.Δ
      AppointmentCohort tr H appointment d (d + D) b →
      (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H b ∧ ∃ k u r ell B s,
        appointment z k u ∧ d ≤ u ∧ u ≤ d + D ∧ r + 1 < m ∧
        AnchorPollAvailable tr H P z k u ∧
        let st := tr.state z k
        let picked := (Node.acToFG st u).2.2
        SA.ToFGAt tr.projAC z r ell B ∧ tr.CallAt z (r + 1) (.fg (.attest B s)) ∧
        tr.time (r + 1) ≤ u ∧ Anc (tr.HonestBlocksAt H) P B ∧
        ((r = k ∧ tr.time k = u ∧ picked = some B ∧ st.fg.Anc P B) ∨
          (r + 1 < k ∧ picked = none ∧
            ((∃ L, SA.IsDeepest (Node.frame st) (SA.toFGCandidates sp st.ac (Node.frame st) u) L ∧
                st.fg.Anc P L ∧ B.root = st.ac.fgReported ∧ SA.AncR (Node.frame st) L B.root) ∨
              SA.toFGCandidates sp st.ac (Node.frame st) u = ∅))) ∧
        ((tr.state y m).fg.σ T.root).h = ((tr.state z r).fg.σ B.root).h) ∨
      ∃ x r ell B, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r ell B ∧
        Anc (tr.HonestBlocksAt H) P B ∧ d ≤ tr.time r ∧ tr.time r ≤ d + D ∧
        ((tr.state y m).fg.σ T.root).h < ((tr.state x r).fg.σ B.root).h)
    (hrelease : ReleaseService U H (gbar g) b R)
    (hD : 0 ≤ D) (hR : 0 ≤ R) : PublishedRows (H := H) U appointment g a b D R := by
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
    ∃ i < k, ∃ j B, HighOrigin tr H g y i j B ∧ tr.time i ≤ b ∧
      Anc (tr.HonestBlocksAt H) C B

/-- Replay must track the write of the actual lock used by a high report,
including writes before the last restart and moves to viable ancestors. -/
theorem high_report_origins_of_fast_lock_lookup {g b : Time}
    (hcut : CutObservations tr H)
    (hlookup : ∀ y k ell C, SA.ToFGAt tr.projAC y k ell C →
      y ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.time k ≤ b →
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h →
      ∃ i < k, ∃ j B CV, tr.JoinedAt y (tr.time i) ∧
        Compose.StoredFastLockAt tr y i j B CV ∧
        HZ tr H g + 1 ≤ ((tr.state y i).fg.σ B.root).h ∧
        Anc (tr.HonestBlocksAt H) C B) : HighReportOrigins tr H g b := by
  sorry

theorem matching_rows_of_high_records {g b : Time}
    (hcut : CutObservations tr H) (hsrc : SourceFacts tr H) (horigin : RecordOrigins tr H)
    (hhigh : HighReportOrigins tr H g b) (hrecord : HighRecordAgreement tr H g b)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (hnc : Compose.NoCollRun dg tr)
    {acp₀ : Payload sp.n}
    (hreachable : ∀ y k, y ∈ H (tr.time k) → Store.Reachable acp₀ (tr.state y k).fg) :
    MatchingRows tr H g b := by
  sorry

/-- At an aligned height pair, duplicate refusal is a lookup of the original
signed bits, not permission to recompute finality using the current record. -/
theorem refused_height_pair_origin (horigin : RecordOrigins tr H)
    {y : Fin sp.n} {k : Nat} {C : Blk sp} {h T : Nat} {timeout : Bool}
    (hy : y ∈ H (tr.time k)) (ha : tr.CallAt y k (.fg (.attest C none)))
    (hstep : Node.CutStep y (tr.time k) (tr.state y k) (.fg (.attest C none)) (tr.post k))
    (hpair : let st := tr.state y k
      let entry := st.fg.σ (st.fg.σ C.root).Th
      st.record.heightPair entry.h entry.Th = some (h, T, timeout)) :
    ∃ j < k, ∃ a, tr.SignAt y j a ∧ a.h = h ∧ (timeout = true → a.T = T) := by
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

/-- The guarded output of one actual awake tick poll, not the union of outputs
of the tick's duties or the unguarded candidates of the poll. -/
def TickDutyRelease (rho : Model.Run (compiled (delayedFamily S p)) E)
    (v : V) (i q : Nat) (t : Time) (a : FG.Att (Fintype.card V)) : Prop :=
  rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
    ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? = some (.poll t.toNat) ∧
    engineAttObj rho a ∈ (rho.dutyStep v (tickPrefix rho v i t q).1 (.poll t.toNat)).2

noncomputable def deliveryPrefix (rho : Model.Run (compiled (delayedFamily S p)) E)
    (v : V) (i : Nat) (t : Time)
    (o : (Model.protoOf (compiled (delayedFamily S p)) E).Object) (q : Nat) :=
  let nd := rho.stateBefore i v
  let P := Model.protoOf (compiled (delayedFamily S p)) E
  let processed : Model.Node P := ⟨P.process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
  rho.runDuties v processed ((P.deliverDuties t).take q)

def DeliveryDutyRelease (rho : Model.Run (compiled (delayedFamily S p)) E)
    (v : V) (i q : Nat) (t : Time) (a : FG.Att (Fintype.card V)) : Prop :=
  ∃ o, rho.events[i]? = some (.deliver v o t) ∧
    ((Model.protoOf (compiled (delayedFamily S p)) E).deliverDuties t)[q]? =
      some (.poll t.toNat) ∧
    engineAttObj rho a ∈ (rho.dutyStep v (deliveryPrefix rho v i t o q).1 (.poll t.toNat)).2

theorem delivery_duty_release_in_event (rho : Model.Run (compiled (delayedFamily S p)) E)
    {v : V} {i q : Nat} {t : Time} {a : FG.Att (Fintype.card V)}
    (hr : DeliveryDutyRelease rho v i q t a) : EngineReleaseAt rho i a := by
  sorry

theorem tick_duty_release_in_event (rho : Model.Run (compiled (delayedFamily S p)) E)
    {v : V} {i q : Nat} {t : Time} {a : FG.Att (Fintype.card V)}
    (hr : TickDutyRelease rho v i q t a) : EngineReleaseAt rho i a := by
  sorry

/-- Held rows and the last snapshot time survive restart. Restart does not attest or release. -/
theorem restart_retains_work (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    ∃ before after, EngineBoundary rho hn i v before ∧
    EngineBoundary rho hn (i + 1) v after ∧
    after.lastSnapshot = before.lastSnapshot ∧ after.held = before.held ∧
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
  key_eq : ∀ v, (key v).val = (rho.ownKey v).val
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

/-- A popped row must pass the guard in the very poll that removes it. This
does not require an open signing appointment. -/
theorem popped_row_releases_at_poll (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) {v : V} {i q : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hawake : E.awake v t = true)
    (hsel : rho.SelValid)
    (hpublic : (S.params (Model.pubOf E) hn).toParams.IsPublic t)
    (hpoll : ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? =
      some (.poll t.toNat))
    {h : Held (S.params (Model.pubOf E) hn)}
    (hown : h.row.val = rho.ownKey v)
    (hpop : h ∈ (preparePoll (p _ (Model.pubOf E).ΔAC)
      (policyStateAt rho hn (tickPrefix rho v i t q).1)).2) :
    TickDutyRelease rho v i q t h.row := by
  sorry

theorem snapshot_log_follows_current_view (p : Rules sp.n) (st : PolicyState sp ro binding) :
    let (pre, label, result) := Node.acToFG st.base.node st.base.now
    match result with
    | none => (snapshot p st).2 = [(st.base.node, label, pre)]
    | some C => ∃ post row, (snapshot p st).2 =
        [(st.base.node, label, pre), (pre, .fg (.attest C row), post)] := by
  sorry

theorem missed_signing_has_no_attempt (p : Rules sp.n) (st : PolicyState sp ro binding)
    (ht : p.signAt st.base.self st.base.now ≠ st.base.now) :
    (pollAttempts p st).2 = [] ∧ (pollAttempts p st).1.lastSnapshot = st.lastSnapshot := by
  sorry

/-- A skipped signing appointment cannot defer a frozen row that is already due. -/
theorem overdue_flush_at_skipped_signing (p : Rules sp.n) (st : PolicyState sp ro binding)
    (hclosed : ¬ SigningOpen p st) {h : Held sp}
    (hheld : h ∈ st.held) (hdue : h.eligibleAt ≤ st.base.now) :
    h ∈ (preparePoll p st).2 := by
  sorry

theorem poll_log_charges_record (p : Rules sp.n) (st : PolicyState sp ro binding)
    {pre post : NodeState (goldilocksNode sp ro)} {C : Blk sp} {a : FG.Att sp.n}
    (hs : (pre, .fg (.attest C (some a)), post) ∈ (pollCutLog p st)) :
    pre.fg.attest pre.record st.base.self C = some (a, post.record) ∧ post.fg = pre.fg := by
  sorry

/-- Every successful attempt appends its exact row, with immutable provenance. -/
theorem attempt_creates_held_row (p : Rules sp.n) (st : PolicyState sp ro binding)
    {pre post : NodeState (goldilocksNode sp ro)} {C : Blk sp} {a : FG.Att sp.n}
    (h : (pre, .fg (.attest C (some a)), post) ∈ (snapshot p st).2) :
    ∃ item ∈ (snapshot p st).1.held, item.source = C ∧ item.row = a ∧
      item.signedAt = st.base.now ∧
      item.eligibleAt = max item.signedAt (p.releaseAt st.base.self item.signedAt) := by
  sorry

/-- A successful attempt releases its exact row in the signing poll if due.
Otherwise that item stays frozen in the actual state at the end of the poll. -/
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
        h.eligibleAt = max t (rule.releaseAt st.base.self t) ∧
        (if h.eligibleAt ≤ t then TickDutyRelease rho v i q t a
        else h ∈ (policyStateAt rho hn (tickPrefix rho v i t (q + 1)).1).held) := by
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
      ∃ l q t, i ≤ l ∧ l < j ∧ h.eligibleAt ≤ t ∧
        (TickDutyRelease rho v l q t h.row ∨ DeliveryDutyRelease rho v l q t h.row) := by
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

/-- Reconcile proposal and non-poll duty cuts as well as the polls. Clock and
gossip do not change the projected node state; the tick boundaries identify
their projected states with the first and last duty prefixes. -/
structure ProjectedTickDutyBoundaries
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M) where
  offset : Nat → Nat → Nat
  spec : ∀ v i t, rho.events[i]? = some (.tick v t) → E.awake v t = true →
    let P := Model.protoOf (compiled (delayedFamily S p)) E
    let len := (P.duties t).length
    offset i 0 = 0 ∧ offset i len = (M.cutLog i).length ∧
      Monotone (offset i) ∧
      (∀ q ≤ len, tr.state (M.key v) (B.first i + offset i q) =
        (policyStateAt rho hn (tickPrefix rho v i t q).1).base.node) ∧
      ∀ q, (P.duties t)[q]? = some (.poll t.toNat) →
        let calls := pollCutLog (p _ (Model.pubOf E).ΔAC)
          (policyStateAt rho hn (tickPrefix rho v i t q).1)
        offset i (q + 1) = offset i q + calls.length ∧
          ((M.cutLog i).drop (offset i q)).take calls.length = calls

/-- Replay the actual delivery traversal, not the object's raw closure. In
particular, a refused block does not contribute cuts for its carried rows. -/
noncomputable def deliveryCutLog (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (v : V) (i : Nat) (t : Time)
    (o : (Model.protoOf (compiled (delayedFamily S p)) E).Object) :
    CutLog (S.params (Model.pubOf E) hn) (S.ro _) :=
  let st := (policyStateAt rho hn (rho.stateBefore i v)).base
  let hs := Model.digests rho.hash o
  let proposer := fun s => if h : (rho.sel (.proposer s)).Nonempty then
    (rho.sel (.proposer s)).min' h else ⟨0, hn⟩
  (delivered hs st o).foldl (fun (before, logs) obj =>
    match canonEvent _ _ hs obj with
    | none => (before, logs)
    | some e =>
      let dg := Simulation.dgOf rho.hash S.genesisRoot
      let (after, labels) := Node.exec proposer dg (rho.ownKey v) before t e
      let posts := Node.cutPosts (rho.ownKey v) t labels before
      (after, logs ++ ((before :: posts).zip (labels.zip posts)).map
        (fun (pre, lbl, post) => (pre, lbl, post)))) (st.node, []) |>.2

def ProjectedDeliveries
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) : Prop :=
  ∀ v i t o, rho.events[i]? = some (.deliver v o t) →
    let P := Model.protoOf (compiled (delayedFamily S p)) E
    let duties := P.deliverDuties t
    ∃ offset : Nat → Nat,
      offset 0 = (deliveryCutLog rho hn v i t o).length ∧
      offset duties.length = (M.cutLog i).length ∧ Monotone offset ∧
      (M.cutLog i).take (offset 0) = deliveryCutLog rho hn v i t o ∧
      ∀ q, duties[q]? = some (.poll t.toNat) →
        let calls := pollCutLog (p _ (Model.pubOf E).ΔAC)
          (policyStateAt rho hn (deliveryPrefix rho v i t o q).1)
        offset (q + 1) = offset q + calls.length ∧
          ((M.cutLog i).drop (offset q)).take calls.length = calls

def ProjectedRestarts
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M) : Prop :=
  ∀ v i t, rho.events[i]? = some (.restart v t) →
    B.first (i + 1) = B.first i + 1 ∧ tr.RestartAt (M.key v) (B.first i) ∧
      tr.time (B.first i) = t

/-- The actual sign and local receipt of a same-poll release appear in order
inside that poll's slice. Merely finding both somewhere in the tick is not enough. -/
theorem same_poll_release_cuts
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (hcuts : ProjectedTickDutyBoundaries rho hn M B) (hv : rho.ExecutionValid)
    {v : V} {i q : Nat} {t : Time} {a : FG.Att (Fintype.card V)}
    (hreleased : TickDutyRelease rho v i q t a)
    (hattempt : let st := policyStateAt rho hn (tickPrefix rho v i t q).1
      ∃ pre C post, (pre, .fg (.attest C (some a)), post) ∈
        (pollAttempts (p _ (Model.pubOf E).ΔAC) st).2) :
    ∃ k j : Nat,
      B.first i + hcuts.offset i q ≤ k ∧ k < j ∧ j < B.first i + hcuts.offset i (q + 1) ∧
      tr.SignAt (M.key v) k a ∧ tr.ProcessAttAt (M.key v) j a := by
  sorry

/-- Open replay target: construct the projected cuts from the actual run. In particular
the new `.attest` cut must be separate from own receipt at `flush`. -/
theorem engine_projection (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hvalid : rho.ExecutionValid) (hn : 1 ≤ Fintype.card V) :
    ∃ (tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _))
      (H : Time → Set (Fin (Fintype.card V))) (U : Publication tr),
      ∃ (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M),
        Nonempty (ProjectedTickDutyBoundaries rho hn M B) ∧
          ProjectedDeliveries rho hn M ∧ ProjectedRestarts rho hn M B := by
  sorry

/-- The actual open signing phase of an awake tick. -/
def SnapshotDuty (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (v : V) (i q : Nat) (t : Time) : Prop :=
  rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
    ((Model.protoOf (compiled (delayedFamily S p)) E).duties t)[q]? = some (.poll t.toNat) ∧
    let st := policyStateAt rho hn (tickPrefix rho v i t q).1
    let rule := p _ (Model.pubOf E).ΔAC
    st.base.now = t ∧ (S.params (Model.pubOf E) hn).toParams.IsPublic t ∧ SigningOpen rule st ∧
      (if rule.beforeProposal st.base.self then st.leading = true else st.base.fgDue = true)

theorem appointment_has_snapshot_duty
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {e : Nat} {t : Time}
    (he : rho.events[e]? = some (.tick v t)) (ha : E.awake v t = true)
    (hh : v ∉ rho.faultyAt t) (hp : (S.params (Model.pubOf E) hn).toParams.IsPublic t)
    (hc : (p _ (Model.pubOf E).ΔAC).signAt (rho.ownKey v) t = t) :
    ∃ q, SnapshotDuty rho hn v e q t := by
  sorry

/-- Actual nonempty reports already owe their own adjacent attempt. Candidate
availability before a report is a distinct service question. -/
theorem report_has_adjacent_attempt
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B) (hv : rho.ExecutionValid)
    {y i ell C} (hy : y ∈ H (tr.time i)) (hr : SA.ToFGAt tr.projAC y i ell C) :
    ∃ result, tr.CallAt y (i + 1) (.fg (.attest C result)) ∧ tr.time (i + 1) = tr.time i := by
  sorry

/-- Transport independently established ancestry at the actual read to the
adjacent attempt. Candidate membership alone gives no ancestry. -/
theorem snapshot_dominance_across_restart
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B) (hv : rho.ExecutionValid)
    {v : V} {e q i : Nat} {t : Time} {ell C}
    (hd : SnapshotDuty rho hn v e q t) (hh : M.key v ∈ H t)
    (hi : i ≤ B.first e + cuts.offset e q) (hr : SA.ToFGAt tr.projAC (M.key v) i ell C)
    (hm : let st := (policyStateAt rho hn (tickPrefix rho v e t q).1).base.node
      C ∈ SA.toFGCandidates (S.params (Model.pubOf E) hn) st.ac (Node.frame st) t)
    {C' : Blk (S.params (Model.pubOf E) hn)}
    (hresult : let st := (policyStateAt rho hn (tickPrefix rho v e t q).1).base.node
      (Node.acToFG st t).2.2 = some C')
    (hbranch : Anc (tr.HonestBlocksAt H) C C') :
    ∃ j k lbl result,
      j = B.first e + cuts.offset e q ∧ k = j + 1 ∧ tr.time k = t ∧
      SA.ToFGAt tr.projAC (M.key v) j lbl C' ∧
      tr.CallAt (M.key v) k (.fg (.attest C' result)) ∧ Dominates tr H (M.key v) i k C C' := by
  sorry

/-- Local availability at the actual poll. If the report cursor suppresses
the selected candidate, the proof owes historical discharge, not a new cut. -/
theorem snapshot_source_or_suppressed
    (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (hj : SA.joined sp st.ac t)
    (hc : ∃ C, SA.IsDeepest (Node.frame st) (SA.toFGCandidates sp st.ac (Node.frame st) t) C) :
    ∃ C ∈ SA.toFGCandidates sp st.ac (Node.frame st) t,
      (Node.acToFG st t).2.2 = some C ∨
        ((Node.acToFG st t).2.2 = none ∧ SA.AncR (Node.frame st) C st.ac.fgReported) := by
  sorry

/-- A suppression by a non-genesis cursor must have a same-run origin. This
does not by itself say that the earlier row fits the later consuming parent. -/
theorem snapshot_cursor_report_origin
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B) (hv : rho.ExecutionValid)
    {v : V} {e q : Nat} {t : Time} (hd : SnapshotDuty rho hn v e q t)
    (hh : M.key v ∈ H t)
    (hcursor : (tr.state (M.key v) (B.first e + cuts.offset e q)).ac.fgReported ≠ S.genesisRoot) :
    ∃ j k ell C result, j < B.first e + cuts.offset e q ∧ k = j + 1 ∧
      SA.ToFGAt tr.projAC (M.key v) j ell C ∧ tr.CallAt (M.key v) k (.fg (.attest C result)) ∧
      C.root = (tr.state (M.key v) (B.first e + cuts.offset e q)).ac.fgReported := by
  sorry

/-- A historical report can discharge a snapshot demand only after the original
attempt is found and its source compared to the demanded block. Released rows
must separately pass the matching and consuming-parent tests. -/
theorem historical_snapshot_attempt
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    (hcut : CutObservations tr H) {y i k ell} {P C : Blk sp} {deadline : Time}
    (hr : SA.ToFGAt tr.projAC y i ell C)
    (ha : ∃ result, tr.CallAt y k (.fg (.attest C result)))
    (hik : i ≤ k) (ht : tr.time k ≤ deadline)
    (hbranch : Anc (tr.HonestBlocksAt H) P C) :
    ∃ l j ell' C' result, l ≤ j ∧ tr.time j ≤ deadline ∧
      SA.ToFGAt tr.projAC y l ell' C' ∧ tr.CallAt y j (.fg (.attest C' result)) ∧
      Anc (tr.HonestBlocksAt H) P C' := by
  sorry

/-- A selected appointment can be a real snapshot but not a joined signing
opportunity. A same-tick restart in particular does not earn signing credit. -/
def JoinedAwakeAppointment (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (v : V) (lo t : Time) : Prop :=
  lo ≤ t ∧ ∃ i q, SnapshotDuty rho hn v i q t ∧
    let st := policyStateAt rho hn (tickPrefix rho v i t q).1
    SA.joined (S.params (Model.pubOf E) hn) st.base.node.ac t

/-- Candidate public scope premise for one consuming window. It says nothing
about what the snapshot returns or whether a signed row fits the parent. -/
def JoinedWindowQuorum (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (lo deadline terminal : Time) : Prop :=
  ∃ ids : Finset V, (S.params (Model.pubOf E) hn).toParams.fg.q ≤ ids.card ∧
    ∀ v ∈ ids, rho.point.HonestAt v terminal ∧ ∃ u ≤ deadline, JoinedAwakeAppointment rho hn v lo u

/-- A poll can have an empty cut slice. Its time is the engine tick time,
not the time of the next materialized cut. -/
def ProjectedAppointment
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B)
    (z : Fin (Fintype.card V)) (k : Nat) (t : Time) : Prop :=
  ∃ e q, SnapshotDuty rho hn (M.key.symm z) e q t ∧ k = B.first e + cuts.offset e q ∧
    SA.joined (S.params (Model.pubOf E) hn) (tr.state z k).ac t ∧
    ((Node.acToFG (tr.state z k) t).2.2.isSome → k + 1 < B.first e + cuts.offset e (q + 1))

theorem appointment_cohort_of_joined_window
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B) {d deadline b : Time}
    (hq : JoinedWindowQuorum rho hn d deadline b) :
    AppointmentCohort tr H (ProjectedAppointment rho hn M B cuts) d deadline b := by
  sorry

theorem joined_appointment_of_ready_and_restart_time
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {v : V} {i q : Nat} {lo t : Time}
    (hd : SnapshotDuty rho hn v i q t) (hlo : lo ≤ t)
    (hr : let sp := S.params (Model.pubOf E) hn
      let st := policyStateAt rho hn (tickPrefix rho v i t q).1
      st.base.node.ac.restartTime ≤ ((sp.ts ((sp.slot t : Int) - 1) : Time) : WithBot Time)) :
    JoinedAwakeAppointment rho hn v lo t := by
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
      ∃ t i q, tr.time k ≤ t ∧ t ≤ max g (tr.time k) + R ∧
        (TickDutyRelease rho v i q t (M.reindex a) ∨
          DeliveryDutyRelease rho v i q t (M.reindex a))) :
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
    (hsignGrid : ∀ y k a, tr.SignAt y k a → sp.toParams.IsPublic (tr.time k))
    (hcal : ∀ y t, 0 ≤ t → sp.toParams.IsPublic t →
      (p sp.n (Model.pubOf E).ΔAC).releaseAt y t ≤ t + (R - slack))
    (hwin : PublicServiceWindow tr H g b slack) : ReleaseService U H g b R := by
  sorry

/-- A per-report time bound is valid only if awake calendar intersections are
bounded from the clamped due time; an ordinary awake public poll does not suffice. -/
theorem sign_duty_coverage_of_awake_appointments
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (p : Rules sp.n)
    {g b D slack : Time} (hs : 0 ≤ slack) (hD : slack ≤ D)
    (hm : Antitone H)
    (hcal : ∀ y t, 0 ≤ t → signingDue p y t ≤ t + (D - slack))
    (ht : ∀ i, 0 ≤ tr.time i)
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

/-- First awake signing appointment after the clamped lower bound. The minimum
is over public calendar points, not all ticks. -/
def FirstAwakeAppointment (tr : GoldilocksTrace sp ro) (rule : Rules sp.n)
    (y : Fin sp.n) (lo u : Time) : Prop :=
  let eligible := fun t => sp.toParams.IsPublic t ∧ rule.signAt y t = t ∧ tr.awake y t
  lo ≤ u ∧ eligible u ∧ ∀ t, lo ≤ t → eligible t → u ≤ t

/-- A bound for a fixed validator outside a full ready interval needs this
intersection property. A regime's population or committee count alone is not it. -/
def AwakeCalendarBound (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (rule : Rules sp.n) (g b slack : Time) : Prop :=
  ∀ y lo, max g 0 ≤ lo → lo + slack ≤ b → y ∈ H (lo + slack) →
    ∃ u, lo ≤ u ∧ u ≤ lo + slack ∧ sp.toParams.IsPublic u ∧
      rule.signAt y u = u ∧ tr.awake y u

theorem first_awake_appointment_of_bound
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (rule : Rules sp.n)
    {y : Fin sp.n} {g b due slack : Time} (hbound : AwakeCalendarBound tr H rule g b slack)
    (hhi : max (max g 0) due + slack ≤ b) (hh : y ∈ H (max (max g 0) due + slack)) :
    ∃ u ≤ max (max g 0) due + slack,
      FirstAwakeAppointment tr rule y (max (max g 0) due) u := by
  sorry

theorem first_awake_appointment_in_ready_window
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (rule : Rules sp.n)
    {y : Fin sp.n} {g due c deadline slack : Time}
    (hready : Regimes.Growing.ReadyAt tr H c y deadline)
    (hcal : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + slack ∧
      sp.toParams.IsPublic u ∧ rule.signAt y u = u)
    (hroom : max (max g due) (max 0 (deadline - c - 1)) + slack ≤ deadline) :
    ∃ u ≤ deadline, FirstAwakeAppointment tr rule y
      (max (max g due) (max 0 (deadline - c - 1))) u := by
  sorry

theorem first_awake_appointment_healthy
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (rule : Rules sp.n)
    {y : Fin sp.n} {g due b slack : Time} (hh : y ∈ H b) (hm : Antitone H)
    (hawake : ∀ t, max g 0 ≤ t → t ≤ b → y ∈ H t → tr.awake y t)
    (hcal : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + slack ∧
      sp.toParams.IsPublic u ∧ rule.signAt y u = u)
    (hroom : max (max g 0) due + slack ≤ b) :
    ∃ u ≤ max (max g 0) due + slack,
      FirstAwakeAppointment tr rule y (max (max g 0) due) u := by
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

theorem first_awake_appointment_executes_snapshot
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (hv : rho.ExecutionValid)
    {v : V} {lo u : Time} (hlo : 0 ≤ lo) (hb : u ≤ rho.horizon)
    (hhonest : M.key v ∈ H u)
    (hkey : M.key v = rho.ownKey v)
    (hfirst : FirstAwakeAppointment tr (p _ (Model.pubOf E).ΔAC) (M.key v) lo u) :
    ∃ e q, SnapshotDuty rho hn v e q u := by
  sorry

/-- Charge one grid step for the initial wake and two slots for joining before
rounding to a signing appointment. Earlier restarts remain unrestricted. -/
theorem joined_appointment_in_ready_window
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (hv : rho.ExecutionValid)
    {v : V} {g c due deadline slack : Time}
    (hr : Regimes.Growing.ReadyAt tr H c (M.key v) deadline)
    (hb : deadline ≤ rho.horizon)
    (hcal : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + slack ∧
      (S.params (Model.pubOf E) hn).toParams.IsPublic u ∧
      (p _ (Model.pubOf E).ΔAC).signAt (M.key v) u = u)
    (hroom : max (max g due) (max 0 (deadline - c - 1) +
      9 * (S.params (Model.pubOf E) hn).Δ) + slack ≤ deadline) :
    ∃ u ≤ deadline, JoinedAwakeAppointment rho hn v (max g due) u := by
  sorry

/-- Healthy supplies the full terminal-honest population; it does not make
their snapshots useful. The next producer must prove that at the parent. -/
theorem healthy_joined_appointment_quorum
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (hv : rho.ExecutionValid)
    {g due deadline terminal slack : Time} (hterminal : deadline ≤ terminal)
    (hb : terminal ≤ rho.horizon) (hhealthy : rho.point.HealthyOn (1 / 3) g terminal)
    (hcal : ∀ v t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + slack ∧
      (S.params (Model.pubOf E) hn).toParams.IsPublic u ∧
      (p _ (Model.pubOf E).ΔAC).signAt (M.key v) u = u)
    (hroom : max due (max 0 g + 9 * (S.params (Model.pubOf E) hn).Δ) + slack ≤ deadline) :
    JoinedWindowQuorum rho hn (max g due) deadline terminal := by
  sorry

/-- Transport the actual ready population, including the whole awake interval.
This does not assert an appointment fits within that interval. -/
theorem policy_ready_iff
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    {v : V} {c t : Time} (ht : 0 ≤ t) (hb : t ≤ rho.horizon) :
    rho.point.Ready c v t ↔ Regimes.Growing.ReadyAt tr H c (M.key v) t := by
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
    (horizon : deadline ≤ rho.horizon) {slack : Time}
    (hcalendar : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + slack ∧
      sp.toParams.IsPublic u ∧ (p sp.n (Model.pubOf E).ΔAC).signAt (M.key v) u = u)
    (hroom : max (max g due) (max 0 (deadline - c - 1)) + slack ≤ deadline) :
    ∃ (t : Time) (i : Nat), max (max g due) (max 0 (deadline - c - 1)) ≤ t ∧
      t ≤ deadline ∧ (p sp.n (Model.pubOf E).ΔAC).signAt (M.key v) t = t ∧
      sp.toParams.IsPublic t ∧ rho.events[i]? = some (Model.Event.tick v t) := by
  sorry

theorem release_at_awake_tick
    (rho : Model.Run (compiled (delayedFamily S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {v : V} {k : Nat} {a : FG.Att sp.n} {t : Time}
    (hs : tr.SignAt (M.key v) k a) (ht : tr.time k < t)
    (hawake : tr.awake (M.key v) t) (hhonest : M.key v ∈ H t)
    (hpublic : sp.toParams.IsPublic t)
    (hhorizon : t ≤ rho.horizon)
    (hdue : (p sp.n (Model.pubOf E).ΔAC).releaseAt (M.key v) (tr.time k) ≤ t) :
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

/-- On the partial-synchrony leg, only the receiver's awake interval starting
at guarded release (clamped to GST) is used. This is not a signing premise. -/
theorem released_delivery_of_psync
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    {tr : GoldilocksTrace sp ro} {H U} (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) {g b : Time} (hb : b ≤ rho.horizon)
    (hΔ : 0 < E.ΔFG) (hnet : rho.log.PSync rho.point g) :
    ReleasedDelivery U H g E.ΔFG b := by
  sorry

end NetworkStatements

section ResetStatements

open SA (Payload gbar)
open Healing (cutZ)
open Healing.Growing

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}

/-- Honest payload bits cannot originate at release or at replay. A held row
must be attributed to its original earlier signature. -/
def PayloadSignOrigins (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) : Prop :=
  ∀ y k (P : Blk sp) a, y ∈ H (tr.time k) → P ∈ (tr.state y k).fg.tree →
    a ∈ P.fgPayload → a.val ∈ H (tr.time k) → ∃ j < k, tr.SignAt a.val j a

theorem payload_sign_origins_of_engine
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
    {p : (n : Nat) → Time → Rules n}
    (rho : Model.Run (compiled (delayedFamily S p)) E)
    {U : Publication tr} (M : EngineProjection rho tr H U)
    (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) : PayloadSignOrigins tr H := by
  sorry

/-- Pull an entry-height signature out of an earlier carrier. Payload use must
have a same-run signature origin; raw availability alone cannot prove it. -/
theorem first_high_signature_of_entry {g : Time} {y : Fin sp.n} {k : Nat}
    {a : FG.Att sp.n} {acp₀ : Payload sp.n}
    (hcut : CutObservations tr H)
    (hreachable : Store.Reachable acp₀ (tr.state y k).fg)
    (hsource : ∃ C : Blk sp, C ∈ (tr.state y k).fg.tree ∧
      ((tr.state y k).fg.σ C.root).h = a.h)
    (hpayload : ∀ (Y : Blk sp) row, Y ∈ (tr.state y k).fg.tree → row ∈ Y.fgPayload →
      row.val ∈ H (max (cutZ sp.toParams g) (tr.time k)) →
      ∃ j < k, tr.SignAt row.val j row)
    (hy : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (hf : (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    (hs : tr.SignAt y k a) (hh : HZ tr H g + 1 ≤ a.h) :
    ∃ z j row, z ∈ H (max (cutZ sp.toParams g) (tr.time j)) ∧ j ≤ k ∧
      tr.SignAt z j row ∧ row.h = HZ tr H g + 1 := by
  sorry

/-- Reset is indexed by signing, never by network release. A refusal at a
high attempted source must be resolved using an earlier actual signature.
The cut-level port of `Generic.reset_of_high_source_at_from` must derive this
from the persistent record and not require the immediate-update group law. -/
theorem reset_of_high_policy_attempt {g : Time} {y : Fin sp.n} {k : Nat}
    {C : Blk sp} {result : Option (FG.Att sp.n)} {acp₀ : Payload sp.n}
    (hcut : CutObservations tr H) (hsources : SourceFacts tr H)
    (horigins : RecordOrigins tr H)
    (hstep : ∀ i v ℓ, tr.CallAt v i ℓ → Node.CutStep v (tr.time i) (tr.state v i) ℓ (tr.post i))
    (hreachable : ∀ v i, v ∈ H (tr.time i) → Store.Reachable acp₀ (tr.state v i).fg)
    (hlock : ∀ v i h r, v ∈ H (tr.time i) → (tr.state v i).record.lock h = some r →
      ∃ j < i, ∃ a, tr.SignAt v j a ∧ a.fin = some (h, r) ∧ h < a.h)
    (hentry : ∀ v i a, v ∈ H (max (cutZ sp.toParams g) (tr.time i)) → tr.SignAt v i a →
      HZ tr H g + 1 ≤ a.h → (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q →
      ∃ z j row, z ∈ H (max (cutZ sp.toParams g) (tr.time j)) ∧ j ≤ i ∧
        tr.SignAt z j row ∧ row.h = HZ tr H g + 1)
    (hy : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (hf : ∀ i ≤ k, (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q)
    (ha : tr.CallAt y k (.fg (.attest C result)))
    (high : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k := by
  sorry

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
structure WarmRowDemand (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (g b D R : Time) (s₀ N floor u x i j : Nat)
    (kindJ : Prop) (J P X C : Blk sp) : Prop where
  frame : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J
  start : gbar g + 4 * sp.Δ ≤ sp.ts s₀
  horizon : sp.ts N + 2 * sp.Δ ≤ b
  warm : s₀ + 2 * sp.k ≤ u
  timeout : u + sp.toParams.fg.δt ≤ x
  last : x ≤ N
  honestWarm : proposer u ∈ H (sp.ts u + sp.Δ)
  honestConsumer : proposer x ∈ H (tr.time j)
  warmSlot : P.slot = u
  consumerSlot : X.slot = x
  warmProposal : tr.ProposesAt (proposer u) i P
  consumerProposal : tr.ProposesAt (proposer x) j X
  parent : X.parent = some C.root
  held : C ∈ (tr.state (proposer x) j).fg.tree
  bounded : tr.time j ≤ b
  noHigh : NoHighSignBefore tr H g (sp.ts (u + 1) + 2 * sp.Δ + D + R + 1)
  notHigher : ((tr.state (proposer x) j).fg.σ C.root).h ≤ ((tr.state (proposer x) j).fg.σ P.root).h

/-- The height shortcut does not request appointments. -/
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
          ∀ v ∈ ids, v ∈ H b ∧
            ∃ l k ell C' result, l ≤ k ∧ k < j ∧ sp.ts s₀ ≤ tr.time l ∧ tr.time k ≤ d + D ∧
              SA.ToFGAt tr.projAC v l ell C' ∧ tr.CallAt v k (.fg (.attest C' result)) ∧
              Anc (tr.HonestBlocksAt H) P C' ∧ h ≤ ((tr.state v k).fg.σ C'.root).h)

/-- Consume joined opportunities on the actual parent window. The old `d` is the
cutoff for candidate availability, not for reports or signatures. The source
producer must justify a new snapshot or a particular historical discharge. -/
theorem warm_report_window_of_drain {g b D R ΔF : Time} {G Ld : Nat}
    {proposer : Nat → Fin sp.n} (hcut : CutObservations tr H)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hbase : BaseService tr H g)
    (hdrain : DrainOutputs tr proposer H g G Ld b)
    (appointment : Fin sp.n → Nat → Time → Prop)
    (hcohort : ∀ {s₀ N floor u x i j : Nat} {kindJ : Prop} {J P X C : Blk sp},
      WarmRowDemand tr H proposer g b D R s₀ N floor u x i j kindJ J P X C →
      gbar g ≤ sp.ts (u + 1) + 2 * sp.Δ → sp.ts (u + 1) + 2 * sp.Δ + D + R + ΔF ≤ tr.time j →
      ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
        ∀ v ∈ ids, v ∈ H b ∧ ∃ k t, appointment v k t ∧ k < j ∧
          sp.ts (u + 1) + 2 * sp.Δ ≤ t ∧ t ≤ sp.ts (u + 1) + 2 * sp.Δ + D)
    (hsource : ∀ {s₀ N floor u x i j k : Nat} {t : Time} {kindJ : Prop}
      {v : Fin sp.n} {J P X C : Blk sp},
      WarmRowDemand tr H proposer g b D R s₀ N floor u x i j kindJ J P X C →
      appointment v k t → v ∈ H b → k < j →
      sp.ts (u + 1) + 2 * sp.Δ ≤ t → t ≤ sp.ts (u + 1) + 2 * sp.Δ + D →
      ∃ l m ell C' result, l ≤ m ∧ m < j ∧ tr.time m ≤ t ∧ (m < k ∨ l = k ∧ m = k + 1) ∧
        sp.ts s₀ ≤ tr.time l ∧ SA.ToFGAt tr.projAC v l ell C' ∧
        tr.CallAt v m (.fg (.attest C' result)) ∧ Anc (tr.HonestBlocksAt H) P C' ∧
        ((tr.state (proposer x) j).fg.σ P.root).h ≤ ((tr.state v m).fg.σ C'.root).h)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hΔF : 0 < ΔF)
    (hfit : 6 * sp.Δ + D + R + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time)) :
    WarmReportWindow tr H proposer g b D R := by
  sorry

/-- Pre-reset assembly. The report window is upstream of signing, and the
local bridge is downstream of signing and actual receipt. The bridge must
discharge the low-floor refusal and parent-entry comparison, not assume that
the earlier report signed the timeout row. -/
theorem warm_timeout_rows_of_report_window {g b D R : Time}
    {proposer : Nat → Fin sp.n} (U : Publication tr)
    (hwindow : WarmReportWindow tr H proposer g b D R)
    (hlocal : ∀ {s₀ N floor u x i j : Nat} {kindJ : Prop} {J P X C : Blk sp},
      WarmRowDemand tr H proposer g b D R s₀ N floor u x i j kindJ J P X C →
      ∀ (v : Fin sp.n) (l k : Nat) (C' : Blk sp),
      let y := proposer x
      let d := sp.ts (u + 1) + 2 * sp.Δ
      d + D + R ≤ tr.time j → tr.time j ≤ b → v ∈ H b → l ≤ k → k < j →
      sp.ts s₀ ≤ tr.time l → tr.time k ≤ d + D →
      (∃ ell, SA.ToFGAt tr.projAC v l ell C') →
      (∃ result, tr.CallAt v k (.fg (.attest C' result))) →
      Anc (tr.HonestBlocksAt H) P C' →
      ((tr.state y j).fg.σ P.root).h ≤ ((tr.state v k).fg.σ C'.root).h →
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

/-- A historical report in the active window extends the common `J` in
kind J: selection extends the report's fork-choice root, and the logged
frame is the held store's frame. Batch membership is not used. -/
theorem historical_report_extends_frame_J {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {v l ell J C'} (hframe : FrameWindow tr H lo hi floor kindJ J) (hkind : kindJ)
    (hv : v ∈ H (tr.time l)) (hlo : lo ≤ tr.time l) (hhi : tr.time l ≤ hi)
    (hreport : SA.ToFGAt tr.projAC v l ell C') (hfr : ell.frame = Node.frame (tr.state v l)) :
    (tr.state v l).fg.Anc J C' := by
  sorry

/-- The refuser's frame kind must be read at the actual attempt cut. When
the floor is the justified height, transport the report's common `J` to
that cut and reconstruct ancestry there from the held source. -/
theorem warm_low_floor_kind {b g D R : Time} {s₀ N floor u x i j l k : Nat}
    {proposer : Nat → Fin sp.n} {kindJ : Prop} {J P X C C' : Blk sp}
    {v : Fin sp.n} {acp₀ : Payload sp.n}
    (hdemand : WarmRowDemand tr H proposer g b D R s₀ N floor u x i j kindJ J P X C)
    (hcut : CutObservations tr H) (hv : v ∈ H b) (hlk : l ≤ k) (hkj : k < j)
    (hl : sp.ts s₀ ≤ tr.time l) (hk : tr.time k ≤ sp.ts N + 2 * sp.Δ)
    (hreach : Store.Reachable acp₀ (tr.state v k).fg)
    (hheld : C' ∈ (tr.state v k).fg.tree)
    (hfloor : floor ≤ ((tr.state v k).fg.σ C'.root).h)
    (hroot : kindJ → (tr.state v l).fg.Anc J C')
    (hlift : (tr.state v l).fg.Anc J C' → (tr.state v k).fg.Anc J C') :
    let h := ((tr.state v k).fg.σ C'.root).h
    h = HZ tr H g ∨ (tr.state v k).fg.hj < h ∨
      ((tr.state v k).fg.hj = h ∧ (tr.state v k).fg.Anc (tr.state v k).fg.J C') := by
  sorry

/-- Move the witness block and its immutable entry state from the earlier
signature to the refusal cut. The old cache itself is not transported. -/
theorem warm_lock_origin_at_refusal (hcut : CutObservations tr H) (hsrc : SourceFacts tr H)
    {v m k h root a B} (hm : m < k) (hv : v ∈ H (tr.time k))
    (ha : tr.SignAt v m a) (hfin : a.fin = some (h, root))
    (hB : B ∈ (tr.state v m).fg.tree)
    (hJ : ((tr.state v m).fg.σ B.root).hj = h ∧ ((tr.state v m).fg.σ B.root).J = root) :
    B ∈ (tr.state v k).fg.tree ∧ (tr.state v k).fg.σ B.root = (tr.state v m).fg.σ B.root ∧
      ((tr.state v k).fg.σ B.root).hj = h ∧ ((tr.state v k).fg.σ B.root).J = root := by
  sorry

/-- Cut-level port of the low-floor lock argument. The historical justification
is attributed to the earlier signature and compared with the actual cache,
not assumed compatible with the attempted source. -/
theorem warm_lock_free_or_entry {g T : Time} {v : Fin sp.n} {k h : Nat} {C E : Blk sp}
    {acp₀ : Payload sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hv : v ∈ H (max (cutZ sp.toParams g) (tr.time k))) (hk : tr.time k < T)
    (hf : (H (tr.time k))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hna : NoHighSignBefore tr H g T)
    (hreach : ∀ i ≤ k, Store.Reachable acp₀ (tr.state v i).fg)
    (hE : Healing.EntryOf (tr.state v k).fg C E h)
    (hCh : ((tr.state v k).fg.σ C.root).h = h)
    (hkind : h = HZ tr H g ∨ (tr.state v k).fg.hj < h ∨
      ((tr.state v k).fg.hj = h ∧ (tr.state v k).fg.Anc (tr.state v k).fg.J C))
    (hlockOrigin : ∀ root, (tr.state v k).record.lock h = some root →
      ∃ m < k, ∃ a B, tr.SignAt v m a ∧ a.fin = some (h, root) ∧ h < a.h ∧
        B ∈ (tr.state v m).fg.tree ∧ ((tr.state v m).fg.σ B.root).hj = h ∧
        ((tr.state v m).fg.σ B.root).J = root ∧ B ∈ (tr.state v k).fg.tree ∧
        (tr.state v k).fg.σ B.root = (tr.state v m).fg.σ B.root)
    (hsafe : ∀ a a' : FG.Att sp.n, a.val ∈ H (tr.time k) →
      (∃ i ≤ k, ∃ B, B ∈ (tr.state v i).fg.tree ∧ a ∈ B.fgPayload) →
      (∃ i ≤ k, ∃ B, B ∈ (tr.state v i).fg.tree ∧ a' ∈ B.fgPayload) → ¬ FG.slashable a a') :
    (tr.state v k).record.lock h = none ∨ (tr.state v k).record.lock h = some E.root := by
  sorry

/-- Port `client_progress_of_lock` to the actual attest cut. `SentOK` ties the
refusal predicate to the durable target/timeout record. An earlier row keeps
all original bits; here progress requires its exact height and entry, not a
freshly computed finality pair. -/
theorem warm_attest_matching_entry (horigin : RecordOrigins tr H)
    {v : Fin sp.n} {k h : Nat} {C E : Blk sp} {result : Option (FG.Att sp.n)}
    {acp₀ : Payload sp.n} (hv : v ∈ H (tr.time k))
    (hreach : Store.Reachable acp₀ (tr.state v k).fg)
    (ha : tr.CallAt v k (.fg (.attest C result)))
    (hstep : Node.CutStep v (tr.time k) (tr.state v k) (.fg (.attest C result)) (tr.post k))
    (hE : Healing.EntryOf (tr.state v k).fg C E h)
    (hCh : ((tr.state v k).fg.σ C.root).h = h)
    (hsent : Healing.Client.SentOK (tr.state v k).record)
    (hsigner : ∀ i a, tr.SignAt v i a → a.val = v)
    (hlock : (tr.state v k).record.lock h = none ∨ (tr.state v k).record.lock h = some E.root) :
    ∃ m ≤ k, ∃ a, tr.SignAt v m a ∧ a.val = v ∧ a.h = h ∧ a.T = E.root := by
  sorry

/-- Both branches extend the held warm proposal. At the common height the
entry cannot change on either extension. Keep the historical row intact and
test it at the consuming parent, which need not be an entry block itself. -/
theorem warm_row_matches_consumer {v y : Fin sp.n} {k j m h : Nat}
    {P C C' E : Blk sp} {a : FG.Att sp.n} {acp₀ : Payload sp.n}
    (hv : v ∈ H (tr.time k)) (hy : y ∈ H (tr.time j))
    (hrv : Store.Reachable acp₀ (tr.state v k).fg)
    (hry : Store.Reachable acp₀ (tr.state y j).fg)
    (hE : Healing.EntryOf (tr.state v k).fg C' E h)
    (hPC' : (tr.state v k).fg.Anc P C') (hPC : (tr.state y j).fg.Anc P C)
    (hP : (tr.state v k).fg.σ P.root = (tr.state y j).fg.σ P.root)
    (hheight : ((tr.state v k).fg.σ C'.root).h = h ∧
      ((tr.state y j).fg.σ P.root).h = h ∧ ((tr.state y j).fg.σ C.root).h = h)
    (hrow : tr.SignAt v m a ∧ a.val = v ∧ a.h = h ∧ a.T = E.root) :
    a.h = ((tr.state y j).fg.σ C.root).h ∧ a.T = ((tr.state y j).fg.σ C.root).Th ∧
      ((tr.state y j).fg.σ C.root).validAtt a := by
  sorry

/-- Cut-level port of `KernelProof.origins_compatible_before_at`. Compare
the actual lock writers through AC votes below the induction cut. In
particular the proof must not assume either writer remains honest until `b`. -/
theorem policy_high_origins_compatible_before {g b : Time} {k : Nat}
    {K : SA.CommitteeDict sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hK : CommitteeHalfUpTo tr H K g b)
    (hcoherent : ∀ x i ell, tr.projAC.CallAt x i ell → x ∈ H (tr.time i) →
      FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H)
    (hvote : ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ z m e, m < k → z ∈ H (tr.time m) → tr.time m ≤ b →
        SA.VoteAt tr.projAC z m e → j < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z i j r l B O} (hB : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hi : i < k ∨ ∀ m, tr.time m < sp.ts (j + 1 : Nat) → m < k)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) (hr : r < k) :
    Compatible (tr.HonestBlocksAt H) B O := by
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

/-- The warm induction's parent and post-state glue is separate from the row
producer. A scalar height observation does not identify the consuming parent. -/
theorem warm_round_rise_of_timeout_rows {g b D R : Time} {G Ld : Nat}
    {proposer : Nat → Fin sp.n} (U : Publication tr)
    (hcut : CutObservations tr H) (hbase : BaseService tr H g)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hdrain : DrainOutputs tr proposer H g G Ld b)
    (hrows : WarmTimeoutRows tr H U proposer g b D R)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    (hpost : ∀ i y ℓ, tr.CallAt y i ℓ → tr.state y (i + 1) = tr.post i)
    {acp₀ : Payload sp.n}
    (hreachable : ∀ y k, y ∈ H (tr.time k) → Store.Reachable acp₀ (tr.state y k).fg) :
    WarmRoundRise tr H proposer g b D R := by
  sorry

/-- Ledger for the five key windows. Relay is paid inside the warm-round span,
not again in the terminal tail. If that fit fails this span cannot be used. -/
theorem policy_reset_debit_ledger (r Δ D R : Time) (δ G Ld HZ : Nat) (hG : 1 ≤ G) :
    let lo := r + 4 * Δ
    let drain := 4 * Δ * ((Ld : Time) + 2)
    let span := 4 * Δ * ((δ + G - 1 : Nat) : Time)
    let tail := 2 * Δ - 1 + D + R
    lo + ∑ j ∈ Finset.range 5,
      (Healing.riseLen drain span tail HZ (2 * HZ + j) + 2 * Δ) =
      Obligations.resetBoundRounds r Δ (2 * Δ) δ G Ld + 5 * (D + R) - 5 := by
  sorry

/-- The earliest legal consuming slot must leave time for strict receipt. The
same inequality implies fit for every later slot in the proposal-gap search. -/
theorem policy_warm_round_receipt_room {u x : Nat} {D R ΔF : Time}
    (hx : u + sp.toParams.fg.δt ≤ x)
    (hfit : 6 * sp.Δ + D + R + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time)) :
    sp.ts (u + 1) + 2 * sp.Δ + D + R + ΔF ≤ sp.ts x := by
  sorry

/-- One recursive rise uses one timeout plus the proposer-gap overshoot.
The next rise inherits the remaining span; only the terminal branch pays
the signing and release tail. `hnext` is the actual proposal-gap selection. -/
theorem policy_reset_round_debit {u x G rounds : Nat} {D R T : Time}
    (hG : 1 ≤ G) (hnext : x < u + sp.toParams.fg.δt + G)
    (hbudget : sp.ts (u + (rounds + 1) * (sp.toParams.fg.δt + G - 1) + 1 : Nat) +
      2 * sp.Δ + D + R ≤ T) :
    sp.ts (x + rounds * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ + D + R ≤ T := by
  sorry

/-- Convert the actual per-attempt signing and release tails to coefficient
units. The network delay was already charged by `policy_warm_round_receipt_room`. -/
theorem policy_reset_bound_le_coefficient (r D R : Time) (X : ℕ+) (S : Setup)
    (hΔ : 0 ≤ sp.Δ) {L : Nat} (hbudget : D + R ≤ (L : Time) * sp.Δ) :
    Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) S.δt X (healthyDrainLen S X) +
      5 * (D + R) ≤ r + ((Obligations.healthyResetCoeff S X + 5 * L : Nat) : Time) * sp.Δ := by
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

/-- The clean AC protection must be produced on this delayed trace. For a
two-label gap it protects the collector's predecessor votes; the adjacent
case uses optimistic evidence, not an update that has not run yet. -/
def ProtectedAnchorHeads (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (a b : Time) : Prop :=
  ∀ {x y r m s} {L Q : Blk sp} {CV},
    x ∈ H (tr.time r) → SA.FastLockAt tr.projAC x r s L CV →
    Healing.cleanLabel sp a + sp.k + 2 ≤ s →
    Healing.drainTime sp a ≤ sp.ts Q.slot →
    y ∈ H (tr.time m) → tr.ProposesAt y m Q → tr.time m ≤ b →
    tr.time r + sp.Δ ≤ tr.time m →
    (s + 2 ≤ Q.slot ∨ s + 1 = Q.slot ∧ SA.OptimisticLockAt tr.projAC x r s L CV) →
    ∀ {C}, Q.parent = some C.root → C ∈ (tr.state y m).fg.tree →
      Anc (tr.HonestBlocksAt H) L C

/-- Port the two clean proposal routes from the same cut replay, not from
the legacy run predicate. The proof owes voter participation and collector
visibility across restart, in addition to the clean-window invariant. -/
theorem protected_anchor_heads_of_clean_windows {g a b : Time}
    {K : SA.CommitteeDict sp.n} (hcut : CutObservations tr H)
    (hreset : IsReset tr H g a) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hbase : BaseService tr H g) (hK : CommitteeHalfUpTo tr H K g b)
    (hfacts : Compose.Growing.CommitteeFacts tr H K)
    (hclean : ∀ {x r s m L CV}, x ∈ H (tr.time r) → SA.FastLockAt tr.projAC x r s L CV →
      Healing.cleanLabel sp a + sp.k + 2 ≤ s → s ≤ m → sp.ts m + 2 * sp.Δ ≤ b →
      Compose.Growing.Clean tr H s m L)
    (hstep : ∀ i y ℓ, tr.CallAt y i ℓ → Node.CutStep y (tr.time i) (tr.state y i) ℓ (tr.post i))
    (hawake : ∀ y t, gbar g ≤ t → t ≤ b → y ∈ H t → tr.awake y t) :
    ProtectedAnchorHeads tr H a b := by
  sorry

/-- Produce usable polls from post-drain voting on the delayed trace. A slot
update does not itself emit a report, and a missed snapshot cannot be replayed.
If the slot lock aged out, the proof needs a fresh lock or a real earlier
attempt for each counted signer, or an actual crossing. The short budget fits
the age of the anchor-slot lock; it does not alone imply lock retention. -/
theorem post_drain_anchor_poll_availability
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
    {p : (n : Nat) → Time → Rules n}
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B) (hv : rho.ExecutionValid)
    {g a b D R : Time} {K : SA.CommitteeDict (Fintype.card V)}
    (hcut : CutObservations tr H) (hbase : BaseService tr H g)
    (hreset : IsReset tr H g a)
    (hcatch : CatchRun tr H g (2 * (S.params (Model.pubOf E) hn).Δ))
    (hK : CommitteeHalfUpTo tr H K g b) (hfacts : Compose.Growing.CommitteeFacts tr H K)
    {w y i m P Q C T} (hdemand : AnchorRowDemand tr H g a b D R w y i m P Q C T)
    (hunanimous : ∀ {z j e}, z ∈ H (tr.time j) → SA.VoteAt tr.projAC z j e →
      tr.time j ≤ b → e.msg.slot = P.slot → e.msg.head = P.root)
    (hawake : ∀ z t, gbar g ≤ t → t ≤ b → z ∈ H t → tr.awake z t)
    (hD : 0 ≤ D) (hshort : D < 6 * (S.params (Model.pubOf E) hn).Δ) :
    let sp := S.params (Model.pubOf E) hn
    let appointment := ProjectedAppointment rho hn M B cuts
    let d := sp.ts (P.slot + 1) + 2 * sp.Δ
    AppointmentCohort tr H appointment d (d + D) b →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H b ∧ ∃ k u, appointment z k u ∧ d ≤ u ∧ u ≤ d + D ∧
        AnchorPollAvailable tr H P z k u) ∨
    ∃ x r ell B, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r ell B ∧
      Anc (tr.HonestBlocksAt H) P B ∧ d ≤ tr.time r ∧ tr.time r ≤ d + D ∧
      ((tr.state y m).fg.σ T.root).h < ((tr.state x r).fg.σ B.root).h := by
  sorry

/-- Replay supplies the originating lock write and the AC protection proof.
The collector deadline is charged from the actual report, irrespective of
whether the report preceded d or came from a scheduled poll. -/
theorem delayed_crossing_raises_parent {a b : Time} (hcut : CutObservations tr H)
    (hprotected : ProtectedAnchorHeads tr H a b)
    (hlock : ∀ {x k ell B}, x ∈ H (tr.time k) → SA.ToFGAt tr.projAC x k ell B →
      Healing.drainTime sp a ≤ tr.time k →
      ∃ r ≤ k, ∃ s L CV, SA.FastLockAt tr.projAC x r s L CV ∧ s ≤ sp.slot (tr.time k) ∧
        Healing.cleanLabel sp a + sp.k + 2 ≤ s ∧ Anc (tr.HonestBlocksAt H) B L)
    (hheight : ∀ {x y k m B C}, x ∈ H (tr.time k) → y ∈ H (tr.time m) →
      B ∈ (tr.state x k).fg.tree → C ∈ (tr.state y m).fg.tree →
      Anc (tr.HonestBlocksAt H) B C →
      ((tr.state x k).fg.σ B.root).h ≤ ((tr.state y m).fg.σ C.root).h)
    (hsrc : SourceFacts tr H) {x y k m ell h} {A B Q C : Blk sp}
    (hx : x ∈ H (tr.time k)) (hr : SA.ToFGAt tr.projAC x k ell B)
    (hdrain : Healing.drainTime sp a ≤ sp.ts A.slot)
    (hAB : Anc (tr.HonestBlocksAt H) A B)
    (hslot : sp.ts A.slot ≤ tr.time k)
    (hlt : h < ((tr.state x k).fg.σ B.root).h)
    (hy : y ∈ H (tr.time m)) (hq : tr.ProposesAt y m Q) (hb : tr.time m ≤ b)
    (hp : Q.parent = some C.root) (hm : C ∈ (tr.state y m).fg.tree)
    (hroom : tr.time k + sp.Δ ≤ tr.time m) :
    Anc (tr.HonestBlocksAt H) B C ∧ h < ((tr.state y m).fg.σ C.root).h := by
  sorry

/-- Collector and FG forwarding are distinct obligations at the same anchor gap.
Only the three edges of the selected quartet can request appointments. -/
theorem published_anchor_steps {g a b ΔF D R : Time} {c s₀ : Nat} {P : Fin 4 → Blk sp}
    {proposer : Nat → Fin sp.n} (U : Publication tr)
    {appointment : Fin sp.n → Nat → Time → Prop}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hreset : IsReset tr H g a) (hbase : BaseService tr H g)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hsupply : PublishedRows (H := H) U appointment g a b D R)
    (hcross : ∀ {x y k m ell h} {A B Q C : Blk sp},
      Healing.drainTime sp a ≤ sp.ts A.slot →
      x ∈ H (tr.time k) → SA.ToFGAt tr.projAC x k ell B → Anc (tr.HonestBlocksAt H) A B →
      tr.time k ≤ sp.ts (A.slot + 1) + 2 * sp.Δ + D → tr.time k + sp.Δ ≤ tr.time m →
      h < ((tr.state x k).fg.σ B.root).h →
      y ∈ H (tr.time m) → tr.ProposesAt y m Q → tr.time m ≤ b →
      Q.parent = some C.root → C ∈ (tr.state y m).fg.tree → h < ((tr.state y m).fg.σ C.root).h)
    (hprop : ∀ l, HonestProposalRun tr H proposer (s₀ + ![0, c, 2 * c, 3 * c] l) (P l))
    (hdrain : Healing.drainTime sp a ≤ sp.ts s₀) (hb : sp.ts (s₀ + 3 * c) ≤ b)
    (hhigh : ∃ y k, y ∈ H (tr.time k) ∧ P 0 ∈ (tr.state y k).fg.tree ∧
      HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h)
    (hcohort : ∀ (i : Fin 3) {z y k j C T},
      AnchorRowDemand tr H g a b D R z y k j (P i.castSucc) (P i.succ) C T →
      let d := sp.ts ((P i.castSucc).slot + 1) + 2 * sp.Δ
      d + D + R + ΔF ≤ tr.time j → AppointmentCohort tr H appointment d (d + D) b)
    (hdelivery : ReleasedDelivery U H g ΔF b)
    (hawake : ∀ y t, gbar g ≤ t → t ≤ b → y ∈ H t → tr.awake y t)
    (hc : 2 ≤ c) (hspan : 3 * c ≤ sp.toParams.fg.δt) (hD : 0 ≤ D) (hR : 0 ≤ R) (hΔF : 0 < ΔF)
    (hforward : 6 * sp.Δ + D + R + ΔF ≤ 4 * sp.Δ * c)
    (hcollector : 7 * sp.Δ + D + R ≤ 4 * sp.Δ * c) :
    ∀ i : Fin 3, Obligations.Growing.AnchorStepAt tr H (P i.castSucc) (P i.succ) := by
  sorry

/-- An anchor is covered in the last proposer's carrier store, not necessarily
in its current finalized cache. The store result is reused after transporting
ancestry and entry heights at honest cuts of the policy trace. -/
theorem policy_four_anchor_carrier {g : Time} {P : Fin 4 → Blk sp} {acp₀ : Payload sp.n}
    (hsteps : ∀ i : Fin 3, Obligations.Growing.AnchorStepAt tr H (P i.castSucc) (P i.succ))
    (hhigh : ∃ y k, y ∈ H (tr.time k) ∧ P 0 ∈ (tr.state y k).fg.tree ∧
      HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h)
    {z : Fin sp.n} {k : Nat} (hz : z ∈ H (tr.time k)) (hown : tr.ProposesAt z k (P 3))
    (hstore : Store.Reachable acp₀ (tr.state z (k + 1)).fg)
    (hmem : P 3 ∈ (tr.state z (k + 1)).fg.tree)
    (hchain : ∀ i, Anc (tr.HonestBlocksAt H) (P i) (P 3))
    (hspan : (P 3).slot ≤ (P 0).slot + sp.toParams.fg.δt)
    (hentry : ∀ i : Fin 3, Obligations.Growing.AnchorStepAt tr H (P i.castSucc) (P i.succ) →
      ((tr.state z (k + 1)).fg.σ (P i.castSucc).root).h + 1 ≤
        ((tr.state z (k + 1)).fg.σ (P i.succ).root).h)
    (hancestry : (tr.state z (k + 1)).fg.Anc (P 0) (P 3))
    (hout : ∀ F, (tr.state z (k + 1)).fg.Anc (P 0) F → Anc (tr.HonestBlocksAt H) (P 0) F) :
    ∃ F, (tr.state z (k + 1)).fg.blocks ((tr.state z (k + 1)).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocksAt H) (P 0) F := by
  sorry

end ResetStatements

section CarrierStatements

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {p : (n : Nat) → Time → Rules n}

/-- Canonical raw block at the compiled wire type. -/
noncomputable def engineCarrierObj (_rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (C : Blk (S.params (Model.pubOf E) hn)) :
    (Model.protoOf (compiled (delayedFamily S p)) E).Object :=
  blockObj (S.params (Model.pubOf E) hn) (binding := S.vote) C

/-- Serialization alone does not identify the root. Decode with the real run hash. -/
noncomputable def engineCarrierRaw (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (o : (Model.protoOf (compiled (delayedFamily S p)) E).Object)
    (C : Blk (S.params (Model.pubOf E) hn)) : Prop :=
  decodeBlock (S.params (Model.pubOf E) hn) (binding := S.vote)
    (Model.digests rho.hash o) o = some C

/-- Decode with the actual run's digests before crossing into trace blocks. -/
noncomputable def engineCarrierForward (rho : Model.Run (compiled (delayedFamily S p)) E)
    (hn : 1 ≤ Fintype.card V) (o : (Model.protoOf (compiled (delayedFamily S p)) E).Object)
    (z : Fin (Fintype.card V)) (s : Time) (C : Blk (S.params (Model.pubOf E) hn)) : Prop :=
  ∃ parent, Simulation.decodeForward (S.params (Model.pubOf E) hn) (binding := S.vote)
    (Model.digests rho.hash o) o = some (z, s, parent, C)

/-- Honest proposal provenance and guarded own release in the actual event,
using the same raw block and digest as the projected proposal. -/
theorem policy_carrier_release
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision)
    {z k C} (hz : z ∈ H (tr.time k)) (hC : tr.ProposesAt z k C) :
    ∃ acc, ∃ hcall : tr.CallAt z k (.fg (.block C acc)),
      let e := (M.occurrence k ⟨z, _, hcall⟩).1
      rho.events[e]? = some (.tick (M.key.symm z) (tr.time k)) ∧
        engineCarrierObj rho hn C ∈ rho.releasesAt e ∧
        engineCarrierRaw rho hn (engineCarrierObj rho hn C) C := by
  sorry

/-- Receipt of the exact raw carrier or its exact forwarding wrapper must
precede the actual read boundary. Processing may reject a carrier already
behind the reader's finalized block. -/
theorem policy_carrier_processed_before_read
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) {v : V} {C} {d t : Time}
    (hy : M.key v ∈ H t) (hd : d < t) (hb : t ≤ rho.horizon)
    (hheld : ∃ o, rho.log.Held rho.point v o d ∧
      (engineCarrierRaw rho hn o C ∨
        ∃ z s, z ∈ H s ∧ engineCarrierForward rho hn o z s C)) :
    ∃ k < B.first ((chainTrace rho).endCut t), tr.BlockCallAt (M.key v) k C ∧ tr.time k ≤ d := by
  sorry

/-- Port the conditional acceptance and finalized-prefix argument to the
actual reader, rather than appeal to the legacy run or assume receipt implies acceptance. -/
theorem policy_carrier_cache_at_read
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {x y : Fin sp.n}
    {k j : Nat} {t : Time} {A C F : Blk sp}
    (hcut : CutObservations tr H) (hx : x ∈ H (tr.time k)) (hy : y ∈ H t)
    (ht : tr.time k ≤ t) (hread : ∀ i < j, tr.time i ≤ t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hC : C ∈ (tr.state x (k + 1)).fg.tree)
    (hF : (tr.state x (k + 1)).fg.blocks ((tr.state x (k + 1)).fg.σ C.root).F = some F)
    (hAF : Anc (tr.HonestBlocksAt H) A F)
    (hcompare : Compatible (tr.HonestBlocksAt H) F (tr.state y j).fg.F)
    (hcover : Anc (tr.HonestBlocksAt H) F C)
    (hcall : ∃ i < j, tr.BlockCallAt y i C)
    (haccept : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F C → ∃ i < j, tr.AcceptAt y i C)
    (htransfer : (∃ i < j, tr.AcceptAt y i C) → Anc (tr.HonestBlocksAt H) F (tr.state y j).fg.F) :
    Anc (tr.HonestBlocksAt H) A (tr.state y j).fg.F := by
  sorry

end CarrierStatements

section ScopedWindowStatements

open SA (Payload gbar)
open Healing.Growing

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {p : (n : Nat) → Time → Rules n}

/-- Scope (b): one actual post-drain consuming edge. The quorum provides
joined opportunities only in this window; source and row matching still go
through `published_rows_of_appointments`. This is not a Healthy-final query. -/
theorem policy_anchor_step_of_joined_window
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (cuts : ProjectedTickDutyBoundaries rho hn M B)
    {g a D R ΔF : Time} {x j : Nat} {P Q C : Blk (S.params (Model.pubOf E) hn)}
    {y : Fin (Fintype.card V)}
    {dg : Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V))}
    (hcut : CutObservations tr H) (hnc : Compose.NoCollRun dg tr)
    (hreset : IsReset tr H g a) (hbase : BaseService tr H g)
    (hcatch : CatchRun tr H g (2 * (S.params (Model.pubOf E) hn).Δ))
    (hrows : PublishedRows (H := H) U (ProjectedAppointment rho hn M B cuts) g a rho.horizon D R)
    (hdelivery : ReleasedDelivery U H g ΔF rho.horizon)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hΔF : 0 < ΔF)
    (hx : P.slot + 2 ≤ x) (hslot : Q.slot = x)
    (hP : P ∈ tr.HonestBlocksAt H)
    (hdrain : Healing.drainTime (S.params (Model.pubOf E) hn) a ≤
      (S.params (Model.pubOf E) hn).ts P.slot)
    (hy : y ∈ H (tr.time j)) (hj : tr.time j ≤ rho.horizon)
    (hq : tr.ProposesAt y j Q) (hp : Q.parent = some C.root)
    (hC : C ∈ (tr.state y j).fg.tree)
    (hPC : Anc (tr.HonestBlocksAt H) P C)
    (hhigh : ∃ z k, z ∈ H (tr.time k) ∧ P ∈ (tr.state z k).fg.tree ∧
      HZ tr H g + 2 ≤ ((tr.state z k).fg.σ P.root).h)
    (hd : let sp := S.params (Model.pubOf E) hn
      gbar g ≤ sp.ts (P.slot + 1) + 2 * sp.Δ)
    (hroom : let sp := S.params (Model.pubOf E) hn
      sp.ts (P.slot + 1) + 2 * sp.Δ + D + R + ΔF ≤ tr.time j)
    (hready : let sp := S.params (Model.pubOf E) hn
      ∀ t, sp.ts (P.slot + 1) + 2 * sp.Δ ≤ t → t ≤ tr.time j → tr.awake y t)
    (hquorum : ((tr.state y j).fg.σ C.root).h ≤ ((tr.state y j).fg.σ P.root).h →
      let sp := S.params (Model.pubOf E) hn
      let d := sp.ts (P.slot + 1) + 2 * sp.Δ
      JoinedWindowQuorum rho hn d (d + D) rho.horizon) :
    Obligations.Growing.AnchorStepAt tr H P Q := by
  sorry

end ScopedWindowStatements

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
including when the original due point preceded GST. -/
theorem round_start_schedule_bounds {Δ : Time} (hΔ : 1 ≤ Δ)
    (offsets : (n : Nat) → Option (Fin n → Time))
    (aligned : ∀ n (f : Fin n → Time), offsets n = some f → ∀ y, Δ ∣ f y) :
    ScheduleBounds (fun n tick => Rules.roundStart n tick (offsets n))
      Δ ⟨5, 4, 0⟩ := by
  sorry

theorem sign_at_release_schedule_bounds {Δ : Time} (hΔ : 1 ≤ Δ)
    (offsets : (n : Nat) → Fin n → Time) (aligned : ∀ n y, Δ ∣ offsets n y) :
    ScheduleBounds (fun n tick => Rules.signAtRelease n tick (offsets n)) Δ ⟨5, 1, 0⟩ := by
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

/-- Arithmetic target for the provisional reserve; the reset induction must
independently fit its actual debits in this budget. -/
theorem policy_heal_pays_reset_placement (X : ℕ+) (hδ : 6 ≤ S.δt) :
    (contract_catchUp S A : Nat) +
      (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 34) + 3 + 5 * B.total ≤
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

/-- The current anchor-availability route only covers signing budgets shorter
than the age margin of the anchor-slot lock at the update. Longer calendars
need a separate supplier; bounded waiting alone does not give that margin. -/
def PolicySchedule : Prop :=
  p = Rules.responsive ∨ B.signSteps < 6 ∧ ∀ Δ : Time, 1 ≤ Δ → ScheduleBounds p Δ B

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

/-- Charge the proposed five-window reserve at the actual query. This is
conditional on the delayed induction really paying at most this reset bound. -/
theorem policy_final_reset_placement
    {V : Type} [Fintype V] [DecidableEq V] (Q : PolicyFinalQuery S A window p B V)
    (a : Time) (ha0 : 0 ≤ a)
    (ha : let sp := S.params (Model.pubOf Q.run.1) Q.positive
      let ready := (Sys (family S p) V).ready (windowContract S A window B) Q.gst Q.run
      a ≤ Obligations.resetBoundRounds ready sp.Δ (2 * sp.Δ) S.δt Q.index
        (healthyDrainLen S Q.index) + 5 * B.total * sp.Δ) :
    let sp := S.params (Model.pubOf Q.run.1) Q.positive
    let ready := (Sys (family S p) V).ready (windowContract S A window B) Q.gst Q.run
    max (max ready 0) (sp.ts (sp.slot a + 2 * sp.k + 5) - 1) +
      ((Q.index : Nat) + S.δt : Nat) * (4 * sp.Δ) ≤ Q.query + 4 * sp.Δ := by
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

/-- Exact compiled reader target for the final-window package. `InBy` must be
proved at every ready reader's actual kept read, not at an abstract trace tip. -/
def PolicyFinalWitness {V : Type} [Fintype V] [DecidableEq V]
    (Q : PolicyFinalQuery S A window p B V) : Prop :=
  let deadline := Q.query + ((windowContract S A window B).params.latency .final
    (policyIndex S A window B Q.index) : Time) * Q.run.1.ΔAC
  ∀ g, schema.output .final = some g →
    (∃ v, Q.run.2.point.Ready ((Sys (family S p) V).cDur (windowContract S A window B) Q.run)
      v deadline) →
    ∃ τ k h, Q.query < τ ∧
      Q.run.2.point.Ready ((Sys (family S p) V).cDur (windowContract S A window B) Q.run)
        (Q.run.2.key k) τ ∧ HonestProposal Q.run.2 τ k h ∧
      InBy Q.run.2 ((Sys (family S p) V).cDur (windowContract S A window B) Q.run) g h deadline

/-- Transport the finalized chain at the actual end-of-time cut, not at an
arbitrary earlier cut witnessing the last carrier. -/
theorem policy_final_read_at_end_cut
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled (delayedFamily S p)) E) (hn : 1 ≤ Fintype.card V)
    {tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _)} {H U}
    (M : EngineProjection rho tr H U) (B : EventBoundaries rho hn M)
    (hv : rho.ExecutionValid) {v : V} {t : Time} (ht : 0 ≤ t) (hb : t ≤ rho.horizon)
    (hh : M.key v ∈ H t) {g} (hg : schema.output .final = some g) :
    let trace := chainTrace rho
    let st := tr.state (M.key v) (B.first (trace.endCut t))
    trace.readAt g v t = AsChainShape.outOf st t .finalized := by
  sorry

theorem policy_model_adequate (V : Type) [Fintype V] [DecidableEq V] :
    (Sys (family S p) V).Adequate (shapeProgress (family S p) V) := by
  sorry

theorem final_live_of_query_witnesses
    (hwitness : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (Q : PolicyFinalQuery S A window p B V), PolicyFinalWitness S A window p B Q) :
    HealthyLiveSupply S A window p B .final := by
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

/-- The warm folds and each of the three post-drain height steps request
service only in the window they actually consume. The scope adapter supplies
the joined quorum for those windows; it cannot supply sources or rows. -/
def FinalAppointmentSupply {V : Type} [Fintype V] [DecidableEq V]
    (Q : PolicyFinalQuery S A window p B V) : Prop :=
  p ≠ Rules.responsive →
    ∀ (rho : Model.Run (compiled (delayedFamily S p)) Q.run.1), HEq rho Q.run.2 →
    ∀ (tr : GoldilocksTrace (S.params (Model.pubOf Q.run.1) Q.positive) (S.ro _))
      (H : Time → Set (Fin (Fintype.card V))) (U : Publication tr),
    ∀ (M : EngineProjection rho tr H U) (_ : EventBoundaries rho Q.positive M),
    let proposer : Nat → Fin (Fintype.card V) := fun s =>
      if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
      else ⟨0, Q.positive⟩
    let sp := S.params (Model.pubOf Q.run.1) Q.positive
    let D := (B.signSteps : Time) * sp.Δ
    let R := (B.publishSteps : Time) * sp.Δ
    let b := rho.horizon
    let readyFor := (Sys (family S p) V).cDur (windowContract S A window B) Q.run
    let deadline := Q.query + ((windowContract S A window B).params.latency .final
      (policyIndex S A window B Q.index) : Time) * Q.run.1.ΔAC
    (∃ v, rho.point.Ready readyFor v deadline) →
    (∀ {s₀ N floor u x i j : Nat} {kindJ : Prop} {J P X C : Blk sp},
      WarmRowDemand tr H proposer Q.gst b D R s₀ N floor u x i j kindJ J P X C →
      SA.gbar Q.gst ≤ sp.ts (u + 1) + 2 * sp.Δ →
      sp.ts (u + 1) + 2 * sp.Δ + D + R + Q.run.1.ΔFG ≤ tr.time j →
      JoinedWindowQuorum rho Q.positive
        (sp.ts (u + 1) + 2 * sp.Δ) (sp.ts (u + 1) + 2 * sp.Δ + D) b) ∧
    (∀ {s₀ : Nat} {P : Fin 4 → Blk sp},
      (∀ l, Healing.Growing.HonestProposalRun tr H proposer
        (s₀ + ![0, window.fgSlots, 2 * window.fgSlots, 3 * window.fgSlots] l) (P l)) →
      Q.query < sp.ts s₀ →
      sp.ts (s₀ + 3 * window.fgSlots) + sp.Δ ≤ deadline →
      (∀ l,
        let s := s₀ + ![0, window.fgSlots, 2 * window.fgSlots, 3 * window.fgSlots] l
        HonestReadyIn rho.point rho.key (fun s => rho.sel (.proposer s)) s
          readyFor (sp.ts s) sp.Δ) →
      ∀ (i : Fin 3) {a z y k j C T},
      AnchorRowDemand tr H Q.gst a b D R z y k j (P i.castSucc) (P i.succ) C T →
      let d := sp.ts ((P i.castSucc).slot + 1) + 2 * sp.Δ
      d + D + R + Q.run.1.ΔFG ≤ tr.time j →
      JoinedWindowQuorum rho Q.positive d (d + D) b)

/-- Concrete compiled witness, pending only which scope supplies the named
appointment premise. A responsive query uses the legacy endpoint. -/
theorem policy_final_query_witness
    {V : Type} [Fintype V] [DecidableEq V] (Q : PolicyFinalQuery S A window p B V)
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B)
    (happointments : FinalAppointmentSupply S A window p B Q) :
    PolicyFinalWitness S A window p B Q := by
  sorry

/-- Healthy-only scope candidate. This discharges opportunities, not the
useful-source part of the final witness. It is not a claim about sleep or outage. -/
theorem healthy_final_appointments
    {V : Type} [Fintype V] [DecidableEq V] (Q : PolicyFinalQuery S A window p B V)
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B) :
    FinalAppointmentSupply S A window p B Q := by
  sorry

/-- Scope (a): the Healthy-final adapter supplies the appointment premise
internally, not as an extra condition on the protocol headline. -/
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

/-- Healthy-final headline target (scope (a)). The scope (b) conditional
window theorem is separate and supplies no universal coverage premise here. -/
theorem policy_correct_protocol
    (hsched : PolicySchedule p B) (htiming : TimingRoom A window B)
    (V : Type) [Fintype V] [DecidableEq V] :
    CorrectProtocol (Model.sysOf schema (compiled (family S p)) V)
      (shapeProgress (family S p) V) (windowContract S A window B) ∧
      (windowContract S A window B).params.OptimalFaultTolerance := by
  sorry

end EndpointStatements

end Consensus.Goldilocks.VotingPolicyPlan
