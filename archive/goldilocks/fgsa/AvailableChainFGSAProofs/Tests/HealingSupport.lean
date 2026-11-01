module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportFrame -- shake: keep (S0 tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads -- shake: keep (H.2 tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportPerm -- shake: keep (S4 tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow -- shake: keep (S2 tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelay -- shake: keep (relay adapters)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer -- shake: keep (H.1 tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportWrite -- shake: keep (S3 tests)

set_option linter.privateModule false

/-! H-SUPPORT tests. The S0 relay has no source-frame premise. The last-write
theorem takes the exact `writes` text of `fgsa_leaseOrigins_lastWrite`. The run
below satisfies the RXing, source-frame and receiver-frame premises together. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingSupport
open AvailableChain.SimplexFG

section Signatures

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedReceiptRootCollisionFree p c E rho)

-- S0: the settled frame at the strict cut needs no GST premise.
example (crossing : RXing p c E rho) (u v : Time) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hp : PhaseInterval p c E rho u v m J contested) (i : Nat) (x : V)
    (hui : V2.D.Run.idxBefore rho u ≤ i) (hiv : i ≤ timeIdx rho v) (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested :=
  healing_settled_frame_strict p c E rho crossing u v m J contested hp i x hui hiv hx

-- S0: the HEAD at u = v_s and the receipt at the phase end, with no hsrc or hhor.
example (_mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hv : V2.D.ExecutionValid E rho) (_hnr : V2.D.NoRestart rho) (_hdelta : E.Δ = p.Δ)
    {ΔF : Time} (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    {y : V} (hy : y ∈ rho.honest) (hServices : HeadCarrierScope E rho i x s y)
    (_hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (_hphase : PhaseInterval p c E rho (SA.voteTime p.toParams s)
      (SA.voteTime p.toParams s + p.Δ) m J contested) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        Gen.V2.Duty.HoldsBefore E rho
          (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
          (SA.voteTime p.toParams s + p.Δ) y :=
  healing_head_witness_relay_on (hroots := hroots) p c E rho crossing hv hx hi hy hServices

-- S3: a written key has the release level and the slow or fast admission test.
example (hs : V2.D.ExecutionValid E rho) {j : Nat} {x : V} {w : Slot} {B : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho j x w)
    (hpass : gatePassedAt p c E rho j) (hres : gateResultAt p c E rho j = some (some B))
    {K : Block} {g : Nat}
    (hkey : (K, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w B)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k)) :
    PhaseBody p c E rho w K :=
  healing_support_phaseBody_of_write p c E rho hs.toScheduleWellFormed hx ht hpass hres hkey
    hwindow

-- S3: the last write deadline is at or before the vote time l when w + k + 1 ≤ l.
example {w l : Slot} (hwl : w + p.k + 1 ≤ l) :
    SA.gateTime p.toParams w + SA.lifetime p.toParams ≤ SA.voteTime p.toParams l :=
  healing_support_deadline_le_vote p hwl

-- H.1 fast: the first honest HEAD after the gate covers a fast-written block.
example [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD []) {y : V} (hy : y ∈ rho.honest)
    (hv : SA.voteTime p.toParams (s + 1) ≤ v) {H : Block}
    (hScopes : ∀ ix iy,
      rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)) →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      FirstTransferScope E rho ix iy x y s)
    (hH : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq B H :=
  healing_first_transfer_fast E rho hrec mono crossing hgst hphase hhead hgate hx hnd hB
    hy hv hScopes hH

-- H.2 fast: with the lease premise after s+1, every later honest HEAD inside v covers B.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hFast : FastSupportScope E rho s v x)
    (hCut : HealingWindow p E 1 s)
    (hlease : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      ∀ iy y, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B)
    {i : Slot} (hi : s + 2 ≤ i) (hv : SA.voteTime p.toParams i ≤ v)
    {y : V} (hy : y ∈ rho.honest) {H : Block}
    (hH : headAtLabel p c E rho y i = some H) : Block.Preceq B H :=
  healing_fast_heads_transfer E rho hrec mono crossing hgst hphase hhead hCut hgate hx hnd hB
    (fun ix iy y hy hi hj => hFast.firstOn ix iy y hy hi hj
      (le_trans (by
        change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤
          4 * p.Δ * (s : Int) + 6 * p.Δ
        push_cast; linarith [p.deltaPos]) hgate)
      (healing_recovery_joined_vote_next E rho hrec hCut hy hj)) hFast.next hlease
    i ((Nat.le_succ _).trans hi) hv y hy H hH

-- G5: the release is a lower bound; a fast-supported block forces every conflicting
-- lease out at the next HEAD tick once finality is at or below the block.
example (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hScope : FirstTransferScope E rho ix iy x y s) {B : Block}
    (hτ : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s B)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B :=
  healing_support_release_compat (hroots := hroots) E rho hE hDelta s hSync hx hy hix hiy
    hScope hτ hFB

-- S2: a synchronous-window slow body covers every honest HEAD at s+1 inside v.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
    (hScopes : SlowSupportScope E rho s v x)
    (hCut : HealingWindow p E 1 s) {y : V} (hy : y ∈ rho.honest)
    (hv : SA.voteTime p.toParams (s + 1) ≤ v) {H : Block}
    (hH : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq B H :=
  healing_slow_first_transfer E rho hrec mono crossing writes hgst hphase hhead hgate hx hgw
    hst hres hBC hel hjx hScopes hCut hy hv hH

-- S4 (B31): each PhaseBody arm gives the three Transfers clauses; S3 is guarded.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) (hbody : PhaseBody p c E rho s B)
    {x : V} (hx : x ∈ rho.honest) (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ v)
    {i : Nat} (hai : afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i)
    (hiv : i ≤ timeIdx rho v) : Block.Preceq B (S_at p c E rho i x) :=
  (healing_phase_transfers E rho hrec mono crossing writes
    hready hphase hServices hhead hgate hbody).2.2
    i x hx hguard hai hiv

-- S4: the phase adapter returns Transfers after its source-window argument.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {s : Slot} {B : Block}
    (hhead : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    (hbody : PhaseBody p c E rho s B) : Transfers p c E rho s B v :=
  healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices hhead hgate hbody

/- B31 sketch (comment only). Without the guard the old S3 clause failed at the horizon edge.
Take v = horizon with d_s ≤ v < d_s + 4Δ = d_(s+1), two honest nodes x and y, and a fast
body B at x. No tick is at or after d_(s+1), so afterTicksIdx (d_s + 4Δ) = events.length
= timeIdx v. The unguarded clause then asks B ⪯ S_at events.length y. The gate of y at
d_s can veto or confirm a block below B, and no later gate of y happens. Then S_y does
not cover B, but every premise of the old TPerm holds. -/

end Signatures

/-! Negative fixture. One validator is honest and asleep. The trace has ticks at 0, 1 and 2,
so it emits and receives nothing, and its FG store stays at genesis. The source
HEAD is at v_0 = 1 and the receipt deadline is the horizon 2. -/

private abbrev p1 : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 4, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev rho1 : V2.D.Run (Fin 1) (fgsa p1 unitCodec) where
  honest := {0}
  horizon := 2
  events := [.tick 0 0, .tick 0 1, .tick 0 2]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

private abbrev env1 : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => false⟩

private theorem mem1 {e : V2.Event (Fin 1) (fgsa p1 unitCodec).Object}
    (he : e ∈ rho1.events) : e = .tick 0 0 ∨ e = .tick 0 1 ∨ e = .tick 0 2 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using he

private theorem schedule1 : V2.D.ScheduleWellFormed env1 rho1 where
  horizon_nonneg := by decide
  sorted := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (by decide))
  nodup := by decide
  in_horizon := by
    intro e he
    rcases mem1 he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  honest_only := by
    intro e he
    rcases mem1 he with rfl | rfl | rfl <;> exact Finset.mem_singleton_self _
  tick_public := by
    intro v t ht
    rcases mem1 ht with he | he | he <;> cases he
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  tick_total := by
    intro v hv t ⟨k, hk⟩ ht hh
    have hv : v = 0 := Finset.mem_singleton.mp hv
    subst v
    change t = (k : Int) * 1 at hk
    rw [mul_one] at hk
    subst t
    change ((k : Int)) ≤ 2 at hh
    have hk2 : k ≤ 2 := by exact_mod_cast hh
    interval_cases k <;> simp

private theorem noDelivery1 (i : Nat) (v : Fin 1) (o : (fgsa p1 unitCodec).Object)
    (t : Time) : rho1.events[i]? ≠ some (.deliver v o t) := by
  intro h
  have he := mem1 (List.mem_of_getElem? h)
  rcases he with he | he | he <;> cases he

private theorem noRestart1 : V2.D.NoRestart rho1 := by
  intro i v t h
  have he := mem1 (List.mem_of_getElem? h)
  rcases he with he | he | he <;> cases he

-- The all-asleep tick trace is a negative fixture under the sleep model.
private theorem invalid1 : ¬ V2.D.ExecutionValid env1 rho1 := by
  intro h
  have ht := h.tick_awake 0 1
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  change false = true at ht
  cases ht

private theorem noEmit1 (v : Fin 1) (o : (fgsa p1 unitCodec).Object) (t : Time) :
    ¬ V2.D.Run.emits env1 rho1 v o t := by
  rintro ⟨i, hi, ho⟩
  rw [(V2.D.Run.step_tick_eq env1 rho1 hi).2, V2.D.tick_asleep env1 rho1 _ rfl] at ho
  exact List.not_mem_nil ho

-- No node is awake, so both synchrony clauses are vacuous.
private theorem sync1 (ΔF : Time) :
    Gen.V2.Duty.PartialSynchronyBy env1 rho1 (fgsaDelay env1.Δ ΔF) where
  broadcast_emitted := by
    intro v _ o t he
    exact (noEmit1 v o t he).elim
  relay_accepted := by
    rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
    exact (noDelivery1 i v o' t hi).elim

private theorem fg_fold (es : List (V2.Event (Fin 1) (fgsa p1 unitCodec).Object))
    (hes : ∀ e ∈ es, ∃ t, e = .tick 0 t) (w : V2.D.World (Fin 1) (fgsa p1 unitCodec))
    (hw : ∀ y, (w y).st.fg = (initial p1.n).fg) :
    ∀ y, ((es.foldl (V2.D.World.step env1 rho1) w) y).st.fg = (initial p1.n).fg := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    obtain ⟨t, rfl⟩ := hes e List.mem_cons_self
    apply ih (fun e he => hes e (List.mem_cons_of_mem _ he))
    intro y
    change (Function.update w 0 (V2.D.tick env1 rho1 (w 0) 0 t).1 y).st.fg = _
    rw [V2.D.tick_asleep env1 rho1 _ rfl]
    by_cases hy : y = 0
    · subst y
      rw [Function.update_self]
      exact (clock_fg p1 (w 0).st t).trans (hw 0)
    · rw [Function.update_of_ne hy]
      exact hw y

-- Every store of the run keeps the initial FG store.
private theorem fg1 (i : Nat) (y : Fin 1) :
    (storeAt p1 unitCodec env1 rho1 i y).fg = (initial p1.n).fg := by
  apply fg_fold _ _ _ (fun _ => rfl) y
  intro e he
  rcases mem1 (List.mem_of_mem_take he) with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

private theorem R1 (i : Nat) (y : Fin 1) :
    R_at p1 unitCodec env1 rho1 i y =
      KitFG.storeControlsView (heightView p1) (initial p1.n).fg := by
  change KitFG.treeStoreControlsView (heightView p1) (storeAt p1 unitCodec env1 rho1 i y).fg = _
  rw [fg1]
  exact KitFG.treeStoreControlsView_eq _ _ (fun W _ _ _ => KitFG.genesis_preceq W)

private theorem roots1 : NamedRootCollisionFree p1 unitCodec env1 rho1 := by
    have hnone : ∀ x o t, V2.Event.deliver x o t ∉ rho1.events := by
      intro x o t hd
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
      exact noDelivery1 i x o t hi
    have hg {A : NamedProposal p1.n} (hA : NamedProposalInRun p1 unitCodec env1 rho1 A) :
        A = .genesis := by
      rcases namedProposalInRun_genesis_or_delivered env1 rho1
        (by intro x o t b hd; exact (hnone x o t hd).elim) hA with h | hd
      · exact h
      · obtain ⟨x, o, t, hd, _⟩ := hd
        exact (hnone x o t hd).elim
    refine ⟨?_⟩
    intro B C hB hC A D hA hD _
    have scopeX {X : NamedProposal p1.n} (hX : NamedProposal.Preceq X B ∨
        NamedProposal.Preceq X C) :
        NamedProposalInRun p1 unitCodec env1 rho1 X := by
      rcases hX with hX | hX
      · exact namedScope_ancestor env1 rho1 hB hX
      · exact namedScope_ancestor env1 rho1 hC hX
    exact (hg (scopeX hA)).trans (hg (scopeX hD)).symm

private theorem mono1 : RMono p1 unitCodec env1 rho1 := by
  intro _ i j x _ _
  dsimp only
  rw [fg1, fg1]
  exact ⟨KitFG.preceq_refl _, le_rfl, le_rfl⟩

private theorem crossing1 : RXing p1 unitCodec env1 rho1 := by
  intro i _ x _ _ W _ _ _ _ _ _
  rw [fg1]
  exact KitFG.genesis_preceq W

private theorem frame1 (i : Nat) (y : Fin 1) :
    SettledPhaseFrame p1 (storeAt p1 unitCodec env1 rho1 i y) 1 (some .genesis) false := by
  apply healing_phase_frame p1 unitCodec env1 rho1 crossing1 (Finset.mem_singleton.mpr
    (Subsingleton.elim y 0)) le_rfl <;> rw [R1] <;> decide

-- The RXing, source-frame and receiver-frame premises hold together.
example : RXing p1 unitCodec env1 rho1 ∧
    SettledPhaseFrame p1 (storeAt p1 unitCodec env1 rho1 1 0) 1 (some .genesis) false ∧
    ∀ y ∈ rho1.honest, SettledPhaseFrame p1 (storeAt p1 unitCodec env1 rho1
      (V2.D.Run.idxBefore rho1 (SA.voteTime p1.toParams 0 + p1.Δ)) y) 1 (some .genesis) false :=
  ⟨crossing1, frame1 1 0, fun y _ => frame1 _ y⟩

-- The structural frame facts do not make the asleep tick trace a valid execution.
example : ¬ V2.D.ExecutionValid env1 rho1 := invalid1

-- The structural phase predicate holds on the invalid trace at m = 1.
example : PhaseInterval p1 unitCodec env1 rho1 1 2 1 (some .genesis) false := by
  refine ⟨by decide, le_rfl, le_rfl, ?_⟩
  intro i x _ _ _
  rw [R1]
  decide

end AvailableChain.FGSA.Run.Tests.HealingSupport
end

public section
namespace AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep
open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 1, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0, RLarge := by decide,
    digest := fun d => ⟨d.slot + 1⟩ }

def env : Generic.Env (Fin 2) :=
  ⟨1, by decide, 9, by decide, fun v t => decide (v = 1 ∨ t < 1 ∨ 9 ≤ t)⟩

def run : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := {0}
  horizon := 18
  events := [.tick 0 0, .restart 0 9, .tick 0 9, .tick 0 10, .tick 0 11, .tick 0 12,
    .tick 0 13, .tick 0 14, .tick 0 15, .tick 0 16, .tick 0 17, .tick 0 18]
  seatOf := fun l q => match l with | .base _ => q | _ => 1
  input := fun _ _ => ()

private theorem fgp_no_delivery (v : Fin 2) (o : Obj p) (t : Time) :
    ¬ V2.D.Run.processes run v o t := by
  rintro ⟨i, hi⟩
  have hm := List.mem_of_getElem? hi
  simp [run] at hm

/-- A finite valid sleep execution restarts at GST, then has an enabled HEAD read. -/
theorem fgp_valid : V2.D.ExecutionValid env run := by
  refine { toSleepWellFormed := ?_, toScheduleWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e h
      simp [run] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide
    · intro e h
      simp [run] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide
    · intro v t h
      simp [run] at h
      refine ⟨t.toNat, ?_⟩
      simp [env]; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t ≤ 18 at hh
      simp [env] at hk ha
      simp [run]; dsimp [Time] at *; omega
  · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t hi <;> exact (fgp_no_delivery v o t ⟨i, hi⟩).elim
  · refine ⟨?_, ?_⟩
    · intro v o t hp; exact (fgp_no_delivery v o t hp).elim
    · intro v o t hp; exact (fgp_no_delivery v o t hp).elim
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v t h
      simp [run] at h
      have hv : v = 0 := by tauto
      subst v
      simp [env]; dsimp [Time] at *; omega
    · intro v o t h; simp [run] at h
    · intro v t h
      simp [run] at h
      rcases h with ⟨rfl, rfl⟩; decide
    · intro v hv t _ _ h
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      have ht : t = 9 := by simp [V2.D.Wakes, env] at h; dsimp [Time] at *; omega
      subst t; simp [run]

private theorem bodies_genesis (i : Nat) :
    (run.stateBefore env i 0).st.namedBodies = [.genesis] := by
  by_cases hi : i < run.events.length
  · change i < 12 at hi
    interval_cases i <;> decide +kernel
  · unfold V2.D.Run.stateBefore
    rw [List.take_of_length_le (le_of_not_gt hi)]
    decide +kernel

private def proposals_absent_check (i : Nat) : Bool := (run.emitsAt env i).all (fun o =>
    match o.payload with | .proposal _ => false | _ => true)

private theorem proposals_absent (i : Nat) : proposals_absent_check i = true := by
  unfold proposals_absent_check
  by_cases hi : i < run.events.length
  · change i < 12 at hi
    interval_cases i <;> decide +kernel
  · unfold V2.D.Run.emitsAt
    rw [List.getElem?_eq_none (le_of_not_gt hi)]
    rfl

private theorem scope_genesis (N : NamedProposal p.n)
    (h : NamedProposalReceiptScope p unitCodec env run N) : N = .genesis := by
  rcases h with h | ⟨v, hv, o, t, M, ⟨i, _, ho⟩, he, _⟩
  · obtain ⟨B, hB, hNB⟩ := h
    rcases hB with ⟨v, o, t, hm, _⟩ | ⟨v, hv, i, hm⟩
    · simp [run] at hm
    · have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      rw [bodies_genesis, List.mem_singleton] at hm
      subst B
      simpa only [NamedProposal.Preceq, NamedProposal.preceq, decide_eq_true_eq] using hNB
  · have hh := List.all_eq_true.mp (proposals_absent i) o ho
    rw [he] at hh
    cases hh

private theorem fgp_roots : NamedReceiptRootCollisionFree p unitCodec env run := by
  intro A B hA hB _
  exact (scope_genesis A hA).trans (scope_genesis B hB).symm

private theorem finality_genesis (i : Nat) : (run.stateBefore env i 0).st.fg.F = .genesis := by
  by_cases hi : i < run.events.length
  · change i < 12 at hi
    interval_cases i <;> decide +kernel
  · unfold V2.D.Run.stateBefore
    rw [List.take_of_length_le (le_of_not_gt hi)]
    decide +kernel

private theorem crossing : RXing p unitCodec env run := by
  intro i _ x _ _ W hx _ _ _ _ _
  have hx0 : x = 0 := Finset.mem_singleton.mp hx
  subst x
  change FGBlock.Preceq (run.stateBefore env i 0).st.fg.F W
  rw [finality_genesis]
  exact KitFG.genesis_preceq W

/-- The HEAD and FG committees have bijective seat assignments. -/
theorem base_seats_bijective :
    (∀ s, Function.Bijective (run.seatOf (.base (.head s)))) ∧
    Function.Bijective (run.seatOf (.base .fg)) := by
  constructor
  · intro s
    exact Function.bijective_id
  · exact Function.bijective_id

/-- The read is nonempty and its HEAD duty executes after the join delay. -/
theorem read_nonempty :
    fullTree p (clock p (storeAt p unitCodec env run 10 0) 17) ≠ ∅ ∧
    ofHead p ⟨.seat (.head 4) 0, genesisRoot⟩ ∈ run.emitsAt env 10 := by
  constructor
  · decide +kernel
  · rw [(V2.D.Run.step_tick_eq env run (show run.events[10]? =
        some (.tick 0 17) from rfl)).2]
    exact (fgsa_emits_head env run _ _ _ 4 (⟨0, by decide⟩ : Fin p.n) genesisRoot).mpr
      ⟨by decide, rfl, rfl, by decide +kernel, by decide +kernel⟩

/-- The selected genesis witness has real frame, ancestry and receiver-floor facts. -/
theorem carrier : HeadCarrierScope env run 10 0 4 0 := by
  constructor
  refine ⟨.genesis, ?_, ?_, .genesis, ?_, ?_, ?_, ?_,
    fgsa_target_service_genesis env run _ 0⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact KitFG.preceq_refl _
  · decide +kernel
  · have hf : (run.stateBeforeTime env 18 0).st.fg.F = .genesis := by decide +kernel
    change Block.Compatible .genesis (eraseFG (run.stateBeforeTime env 18 0).st.fg.F)
    rw [hf]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl .genesis)
      (Gen.Pure.block_preceq_refl .genesis)

/-- The repaired relay consumes these services on a valid, nonempty executed read. -/
theorem relay_positive :
    ∃ K ∈ fullTree p (clock p (storeAt p unitCodec env run 10 0) 17),
      eraseFG K = headVote p (clock p (storeAt p unitCodec env run 10 0) 17) 4 ∧
      ∃ W ∈ (clock p (storeAt p unitCodec env run 10 0) 17).fg.TF,
        FGBlock.Preceq K W ∧
        (controls p (clock p (storeAt p unitCodec env run 10 0) 17)).lo ≤
          (heightView p W).h ∧
        Gen.V2.Duty.HoldsBefore env run
          (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF) 18 0 := by
  exact healing_head_witness_relay_on p unitCodec env run crossing fgp_valid
    (i := 10) (x := (0 : Fin 2)) (s := 4) (y := (0 : Fin 2))
    (by decide) (by rfl) (by decide) carrier fgp_roots

/-- The review's restart-at-9 gate is suppressed; its false cutoff is not needed. -/
theorem early_gate_suppressed :
    IsGateTick p unitCodec run 7 0 2 ∧ ¬ enabledGateAt p unitCodec env run 7 0 2 ∧
    ¬ env.t_GST ≤ slotStartZ p ((2 : Int) - 1) := by
  constructor
  · rfl
  constructor
  · intro he
    have hc := he.2
    change (9 : Time) ≤ 8 at hc
    exact (by decide : ¬ ((9 : Time) ≤ 8)) hc
  · decide

/-- The suppressed gate saves no result and adds no lease or stable record. -/
theorem suppressed_writes :
    GridCO.savedGenuine (clock p (storeAt p unitCodec env run 7 0) 14).base 2 = some none ∧
    (run.stateBefore env 8 0).st.base.obligations =
      (run.stateBefore env 7 0).st.base.obligations ∧
    (run.stateBefore env 8 0).st.base.stableRecord =
      (run.stateBefore env 7 0).st.base.stableRecord := by
  constructor
  · exact fgsa_gate_saved_unjoined env run fgp_valid.toScheduleWellFormed
      (show run.events[7]? = some (.tick 0 14) from rfl) (by decide +kernel)
  constructor <;> decide +kernel

/-- A label-0 actor without a restart is joined even though the sufficient GST cut fails. -/
theorem label_zero_guard :
    joinedAtTime p none (SA.gateTime p.toParams 0) = true ∧
    ¬ (0 : Time) ≤ slotStartZ p (-1) := by
  constructor <;> decide

end AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep
end

#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.fgp_valid
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.read_nonempty
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.carrier
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.relay_positive
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.early_gate_suppressed
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.suppressed_writes
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.label_zero_guard
#print axioms AvailableChain.FGSA.Run.Tests.HealingSupport.PositiveSleep.base_seats_bijective
