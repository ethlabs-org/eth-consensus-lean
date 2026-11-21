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

/-- Earliest eligible public duty, measured from report and signing respectively.
A schedule may differ by validator. An overdue duty can be served after wake. -/
structure Rules (n : Nat) where
  signAt : Fin n → Time → Time
  releaseAt : Fin n → Time → Time → Time

def Rules.responsive (n : Nat) : Rules n := ⟨fun _ t => t, fun _ _ t => t⟩

/-- Fixed signing and independently scheduled release. For a fixed signing time with
immediate publication take `nextRelease y t = t`; to sign at release take `nextSign`
to be the release calendar and again publish immediately. -/
def Rules.scheduled {n : Nat} (nextSign nextRelease : Fin n → Time → Time) : Rules n :=
  ⟨nextSign, fun y _ t => nextRelease y t⟩

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

/-- Preserve each reported source at its own deadline, including across wake. This draft
does not permit a newer report to borrow an earlier report's signing appointment. -/
noncomputable def report (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding :=
  let r := Node.acToFG st.base.node st.base.now
  let pending := r.2.2.elim st.pending fun C =>
    let due := max st.base.now (p.signAt st.base.self st.base.now)
    st.pending ++ [(due, st.base.now, C)]
  { st with base := { st.base with node := r.1, fgDue := false }, pending }

/-- Charge the anti-slashing record at the real attempt. The immutable row is not admitted
to the proposal pool or outbox before its release gate. A refusal never overwrites a held row. -/
noncomputable def attempt (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × List (Blk sp × Option (FG.Att sp.n)) :=
  let ready := st.pending.filter (fun q => q.1 ≤ st.base.now)
  let later := st.pending.filter (fun q => st.base.now < q.1)
  ready.foldl (fun (nd, logs) (_, r, C) =>
    match nd.base.node.fg.attest nd.base.node.record nd.base.self C with
      | none => (nd, logs ++ [(C, none)])
      | some (a, record) =>
        let u := max st.base.now (p.releaseAt st.base.self r st.base.now)
        ({ nd with
          base := { nd.base with node := { nd.base.node with record } }
          held := nd.held ++ [⟨C, r, st.base.now, u, a⟩] }, logs ++ [(C, some a)]))
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
  { st with base := AsChainShape.restore self st.base t }

/-- Leading polls can flush held rows before a proposal. Respect the ordinary outbox
and forwarding order, then append due rows as separate guarded candidates. Do not put a
wake burst behind the one-body ordinary drain. -/
noncomputable def preparePoll (p : Rules sp.n) (st : PolicyState sp ro binding) :
    PolicyState sp ro binding × List (Held sp) :=
  flush (if st.base.fgDue then (attempt p (report p st)).1 else st)

noncomputable def policyOps (p : Rules sp.n) :
    NodeAsChainShape.Ops sp.n binding.Kind Info Body Out (PolicyState sp ro binding) where
  init k q := ⟨(nodeOps sp ro binding).init k q, [], []⟩
  clock st t := { st with base := { st.base with now := t } }
  propose st s := let r := AsChainShape.propose st.base s; ({ st with base := r.1 }, r.2)
  pollPropose st _ := ({ st with base := nodeTick st.base }, none)
  poll st t :=
    let r := AsChainShape.poll { st.base with fgDue := false } t
    ({ st with base := r.1 }, r.2)
  pollBatch st t :=
    let (st, ready) := preparePoll p st
    let r := AsChainShape.pollBatch st.base t
    ({ st with base := r.1 }, r.2 ++ ready.map (fun h => (.att (encodeAtt h.row), [])))
  gossip st t := (nodeOps sp ro binding).gossip st.base t
  process st o hs := { st with base := AsChainShape.process st.base o hs }
  recordOwn st o hs := { st with base := AsChainShape.recordOwn st.base o hs }
  restore := restore
  out g st := outOf st.base.node st.base.now g

/-- Proposed family with the same wire format and duty selection, including `n = 0`. -/
noncomputable def family (S : Setup) (p : (n : Nat) → Rules n) : ChainShapeFamily schema Info :=
  fun pub =>
    NodeAsChainShape.shape (skeleton pub S.vote)
      (NodeAsChainShape.familyOps fun hn =>
        policyOps (sp := S.params pub hn) (ro := S.ro _) (binding := S.vote) (p pub.n))
      (S.vote.candidateRole pub.n) (dependencies pub.n (binding := S.vote))
      (conflicts (binding := S.vote)) (isFGAtt (binding := S.vote))

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

noncomputable def contract (S : Setup) (A : ContractAssumptions S) (B : Budget) :
    Contract ProgressReq :=
  let K := goldilocksContract A (coefficients S A B)
  { K with params := { K.params with
      fgDelay := ⟨max 1 ((A.fgDelay : Nat) - B.total),
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ } }

/-- Keep both collector and forwarding slack at the maximum network delay. -/
def TimingRoom {S : Setup} (A : ContractAssumptions S) (B : Budget) : Prop :=
  7 + B.total ≤ 4 * A.fgSlots

/-- Public schedule bounds do not assert any node was awake or any row was released. -/
structure ScheduleBounds (p : (n : Nat) → Rules n) (B : Budget) : Prop where
  sign : ∀ n y t, 0 ≤ t → (p n).signAt y t ≤ t + B.signSteps
  release : ∀ n y r t, 0 ≤ r → r ≤ t →
    (p n).releaseAt y r t ≤ t + B.publishSteps

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
    ∃ t, max (tr.time i) (p.signAt y (tr.time i)) ≤ t ∧
      t ≤ max g (tr.time i) + D ∧ sp.toParams.IsPublic t ∧ tr.awake y t

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
structure PublishedRows (U : Publication tr) (g b D : Time) : Prop where
  supply : ∀ {T : Blk sp} {y : Fin sp.n} {m : Nat} {t : Time},
    0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
    ∀ {σT : FG.ChainState sp.n}, (tr.state y m).fg.σ T.root = σT → σT.Th = T.root →
    HZ tr H g + 1 ≤ σT.h → (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) →
    ∀ {d : Time}, gbar g ≤ d → d + D ≤ b →
    (∀ z, z ∈ H (max (cutZ sp.toParams g) d) → ∃ r ell C,
      SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ d ∧
        Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) (d + D)) ∧ ∃ a j,
        tr.SignAt z j a ∧ tr.time j ≤ d + D ∧ ReleasedBy U H z a (d + D) ∧
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

theorem published_rows_of_attempts (U : Publication tr) {g b a ΔF D R : Time}
    {proposer : Nat → Fin sp.n}
    (hreset : IsReset tr H g a) (hab : a ≤ b) (hservice : ResetService tr H g ΔF b)
    (hquorum : ∀ t, gbar g ≤ t → t ≤ b → sp.toParams.fg.q ≤ (H t).ncard)
    (hcut : CutObservations tr H)
    (hmatching : ∀ (T : Blk sp) (σT : FG.ChainState sp.n) y m t z r k ell C s,
      0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
      (tr.state y m).fg.σ T.root = σT → σT.Th = T.root → HZ tr H g + 1 ≤ σT.h →
      (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) → r ≤ k →
      z ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)) → tr.time k ≤ b →
      SA.ToFGAt tr.projAC z r ell C → tr.CallAt z k (.fg (.attest C s)) →
      Anc (tr.HonestBlocksAt H) T C → ((tr.state z r).fg.σ C.root).h = σT.h →
      ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time k ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)))
    (hattempt : ExactService tr H (gbar g) b D) (hrelease : ReleaseService U H (gbar g) b R)
    (hD : 0 ≤ D) (hR : 0 ≤ R) : PublishedRows (H := H) U g b (D + R) := by
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

end RunStatements

section EngineStatements

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup} {p : (n : Nat) → Rules n}

/-- A canonical adapter must use this exact release relation: no hypothetical queue and no
replacement signature. Membership in the actual event's output includes the engine guard. -/
def EngineRelease (rho : Model.Run (compiled (family S p)) E)
    (v : V) (a : FG.Att (Fintype.card V)) (t : Time) : Prop :=
  rho.releases v (attObj (binding := S.vote) a) t

def EngineReleaseAt (rho : Model.Run (compiled (family S p)) E)
    (i : Nat) (a : FG.Att (Fintype.card V)) : Prop :=
  attObj (binding := S.vote) a ∈ rho.releasesAt i

theorem prepared_rank (p : Rules sp.n) (st : PolicyState sp ro binding) (t : Time)
    (i : Nat) (h : Held sp) (hi : ((preparePoll p st).2)[i]? = some h) :
    let prior := (AsChainShape.pollBatch (preparePoll p st).1.base t).2
    ((policyOps (ro := ro) (binding := binding) p).pollBatch st t).2[prior.length + i]? =
      some (Body.att (encodeAtt h.row), []) := by
  sorry

/-- Transfer the real guard and timing, in both directions, in the same run. `key` and
`reindex` are the concrete enumeration bijections; they do not change attestation bits. -/
structure EngineProjection {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) where
  key : V ≃ Fin sp.n
  reindex : FG.Att sp.n → FG.Att (Fintype.card V)
  cutLaws : CutObservations tr H
  timeNonneg : ∀ i, 0 ≤ tr.time i
  honest_iff : ∀ v t, key v ∈ H t ↔ v ∉ rho.faultyAt t
  awake_eq : ∀ v t, tr.awake (key v) t ↔ E.awake v t = true
  signer_eq : ∀ a, (reindex a).val = rho.ownKey (key.symm a.val)
  release_iff : ∀ v a t, U.released (key v) a t ↔ EngineRelease rho v (reindex a) t

/-- Open replay target: construct the projected cuts from the actual run. In particular
the new `.attest` cut must be separate from own receipt at `flush`. -/
theorem engine_projection (rho : Model.Run (compiled (family S p)) E)
    (hvalid : rho.ExecutionValid) (hn : 1 ≤ Fintype.card V) :
    ∃ (tr : GoldilocksTrace (S.params (Model.pubOf E) hn) (S.ro _))
      (H : Time → Set (Fin (Fintype.card V))) (U : Publication tr),
      Nonempty (EngineProjection rho tr H U) := by
  sorry

theorem due_report_is_attempted
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid)
    (hpublic : ∀ y i ell R, SA.ToFGAt tr.projAC y i ell R → sp.toParams.IsPublic (tr.time i))
    {y i ell R t} (hreport : SA.ToFGAt tr.projAC y i ell R) (hit : tr.time i ≤ t)
    (hy : y ∈ H t) (hawake : tr.awake y t) (ht : sp.toParams.IsPublic t)
    (hdue : (p sp.n).signAt y (tr.time i) ≤ t) :
    ∃ k s, i ≤ k ∧ tr.time k ≤ t ∧ tr.CallAt y k (.fg (.attest R s)) := by
  sorry

theorem exact_service_of_awake_duties
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    {g b D : Time} (coverage : SignDutyCoverage tr H (p sp.n) g b D)
    (htrace : ∀ y i ell R t, SA.ToFGAt tr.projAC y i ell R → tr.time i ≤ t →
      y ∈ H t → tr.awake y t → sp.toParams.IsPublic t →
      (p sp.n).signAt y (tr.time i) ≤ t →
      ∃ k s, i ≤ k ∧ tr.time k ≤ t ∧ tr.CallAt y k (.fg (.attest R s))) :
    ExactService tr H g b D := by
  sorry

/-- Preliminary opportunity only. An awake tick does not bound the queue rank. -/
structure RowPollOpportunity {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (g b R : Time) : Prop where
  due : ∀ v k a, tr.SignAt (M.key v) k a → tr.time k + R ≤ b →
    M.key v ∈ H (max g (tr.time k + R)) →
    ∃ (t : Time) (i : Nat), tr.time k ≤ t ∧ t ≤ max g (tr.time k + R) ∧
      rho.events[i]? = some (Model.Event.tick v t)

theorem release_of_poll_output
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
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
    (rho : Model.Run (compiled (family S p)) E) (tr : GoldilocksTrace sp ro)
    (H : Time → Set (Fin sp.n)) (U : Publication tr) (M : EngineProjection rho tr H U)
    (hvalid : rho.ExecutionValid) {g b R slack : Time}
    (horizon : b ≤ rho.horizon) (hslack : 0 ≤ slack) (hR : slack ≤ R)
    (hcal : ∀ y r t, 0 ≤ r → r ≤ t → (p sp.n).releaseAt y r t ≤ t + (R - slack))
    (hwin : PublicServiceWindow tr H g b slack) : ReleaseService U H g b R := by
  sorry

theorem sign_duty_coverage_of_calendar
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (p : Rules sp.n)
    {g b D slack : Time} (hs : 0 ≤ slack) (hD : slack ≤ D)
    (hcal : ∀ y t, p.signAt y t ≤ t + (D - slack))
    (hwin : PublicServiceWindow tr H g b slack) : SignDutyCoverage tr H p g b D := by
  sorry

theorem healthy_service_window (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    {g b : Time} (hg : 0 ≤ g)
    (hgrid : ∀ t, 0 ≤ t → ∃ u, t ≤ u ∧ u ≤ t + sp.Δ ∧ sp.toParams.IsPublic u)
    (hcut : CutObservations tr H)
    (hawake : ∀ y t, g ≤ t → t ≤ b → y ∈ H t → tr.awake y t) :
    PublicServiceWindow tr H g b sp.Δ := by
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
def PublishedDelivery (U : Publication tr) (H : Time → Set (Fin sp.n)) (g ΔF b : Time) : Prop :=
  ∀ x a u, x ∈ H u → U.released x a u →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max u g) ΔF ≤ tr.time j → ∃ k ≤ j, tr.ProcessAttAt y k a

theorem row_service_of_publication (U : Publication tr) {g ΔF b R : Time}
    (hR : 0 ≤ R) (hrel : ReleaseService U H g b R) (hnet : PublishedDelivery U H g ΔF b)
    {x y : Fin sp.n} {i j : Nat} {att : FG.Att sp.n}
    (hsign : tr.SignAt x i att) (hx : x ∈ H (max g (tr.time i) + R))
    (hxb : max g (tr.time i) + R ≤ b)
    (hy : y ∈ H (tr.time j)) (hcall : tr.IsCall y j) (hjb : tr.time j ≤ b)
    (hdeadline : tr.deadline y j (max g (tr.time i) + R) ΔF ≤ tr.time j)
    (hmono : ∀ u ≤ max g (tr.time i) + R,
      tr.deadline y j (max u g) ΔF ≤ tr.deadline y j (max g (tr.time i) + R) ΔF) :
    ∃ k ≤ j, tr.ProcessAttAt y k att := by
  sorry

/-- Unlike the landed reset kernel, this target does not assume `NoRestartUpTo`.
Its service is for a GST-clamped deadline and includes actual publication. `ResetService`
must be furnished by the policy projection, not by the old same-tick run predicate. -/
theorem reset_of_policy_service {g ΔF b r D R : Time} {G Ld : Nat}
    {K : SA.CommitteeDict sp.n} {proposer : Nat → Fin sp.n} (U : Publication tr)
    (hcut : CutObservations tr H)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hattempt : Attempts tr H (gbar g) b D) (hrel : ReleaseService U H (gbar g) b R)
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

end ResetStatements

section EndpointStatements

variable (S : Setup) (A : ContractAssumptions S) (p : (n : Nat) → Rules n) (B : Budget)

/-- Timing only. A separate placement proof must show that these budgets pay for the
actual selected window, actual relay, and the reset induction. -/
theorem forwarding_and_collector_room (h : TimingRoom A B) {Δ ΔF : Time}
    (hΔ : 0 ≤ Δ) (hnet : ΔF ≤ ((contract S A B).params.fgDelay : Time) * Δ) :
    6 * Δ + (B.total : Time) * Δ + ΔF ≤ 4 * Δ * (A.fgSlots : Time) ∧
      7 * Δ + (B.total : Time) * Δ ≤ 4 * Δ * (A.fgSlots : Time) := by
  sorry

theorem zero_contract (hB : B.total = 0) :
    contract S A B = goldilocksContract A (contract_coefficients S A) := by
  sorry

theorem final_heal_reserve (X : ℕ+) :
    (contract_catchUp S A : Nat) + healMargin S X + 5 * B.total ≤
      (coefficients S A B).heal .final X := by
  sorry

/-- Final liveness is the only claim in this supplier. Do not put the queue or
signature conclusions into the environment's Healthy or progress hypotheses. -/
def FinalLiveSupply : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] g,
    schema.output .final = some g → ∀ (i : (contract S A B).Idx) (gst : Time),
    (Sys (family S p) V).Holds
      (fun r => (Sys (family S p) V).Healthy (shapeProgress (family S p) V).toExternal
          (contract S A B) gst r ∧
        (Sys (family S p) V).prog (shapeProgress (family S p) V) (contract S A B) .final i
          ((Sys (family S p) V).ready (contract S A B) gst r) ((Sys (family S p) V).pt r).horizon r)
      (fun r => ProposalLiveReady r.2 ((Sys (family S p) V).cDur (contract S A B) r) g
        ((Sys (family S p) V).heal (contract S A B) .final i gst r)
        ((contract S A B).params.latency .final i))

theorem obligations_of_policy_suppliers
    (hsched : ScheduleBounds p B) (htiming : TimingRoom A B)
    (hfinal : FinalLiveSupply S A p B) (hguard : GuardIdleAlways (family S p)) :
    ShapeObligationsAs .ebbAndFlow (family S p) (contract S A B) := by
  sorry

/-- End-to-end target under the existing healthy regime, with no per-run
signing/publication premise. If the bounded-queue or reset targets fail, this statement
requires a handler or contract revision before proof work. -/
theorem final_live_of_policy
    (hsched : ScheduleBounds p B) (htiming : TimingRoom A B) : FinalLiveSupply S A p B := by
  sorry

theorem headline_of_policy_obligations
    (h : ShapeObligationsAs .ebbAndFlow (family S p) (contract S A B))
    (V : Type) [Fintype V] [DecidableEq V] :
    CorrectProtocol (Model.sysOf schema (compiled (family S p)) V)
      (shapeProgress (family S p) V) (contract S A B) ∧
      (contract S A B).params.OptimalFaultTolerance := by
  sorry

end EndpointStatements

end Consensus.Goldilocks.VotingPolicyPlan
