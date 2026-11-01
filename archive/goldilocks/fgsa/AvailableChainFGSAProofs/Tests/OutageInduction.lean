module
public import AvailableChainFGSAProofs.Proofs.Outage.Induction -- shake: keep (privacy audit)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageInduction

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho)


/-! O-INDUCT plan §10. Concrete tests use the actual model operations.
The delayed-disclosure tests use real run stores and exact RQCOrigin
witnesses; they do not assume the successor source history or frame. -/

/-- The all-ticks cut excludes the same-time delivery; the public cut includes it. -/
example (x y : V) (o : Obj p) :
    let run := { rho with events := [.tick x 18, .deliver y o 18] }
    afterTicksIdx run 18 = 1 ∧ timeIdx run 18 = 2 := by
  intro run
  change (List.filter (fun e : V2.Event V (Obj p) => decide (e.key ≤ toLex (18, 1)))
    [.tick x 18, .deliver y o 18]).length = 1 ∧
      (List.filter (fun e : V2.Event V (Obj p) => decide (e.time ≤ 18))
        [.tick x 18, .deliver y o 18]).length = 2
  change (1 : Nat) = 1 ∧ (2 : Nat) = 2
  exact ⟨rfl, rfl⟩

/-- A same-time honest row is already in the all-ticks seed, before the delivery. -/
public theorem same_time_disclosure (hs : V2.D.ScheduleWellFormed E rho)
    {k i : Nat} {x y : V} {r : Nat} {a : RowWire p.n} {o : Obj p}
    (ha : HonestRowAt p c E rho k y r a)
    (hi : rho.events[i]? = some (.deliver x o (p.actionTime r))) :
    k < afterTicksIdx rho (p.actionTime r) ∧ k < i := by
  have hcut : k < afterTicksIdx rho (p.actionTime r) := by
    by_contra hn
    have hbad := outage_tick_after_cut hs ha.2.1 (Nat.le_of_not_gt hn)
    exact lt_irrefl _ hbad
  exact ⟨hcut, fgsa_tick_before_delivery E rho hs ha.2.1 hi⟩

/-- A newly stored W can finalize an older target while its latest J differs.
The retained target is identified through the prior justification carrier. -/
public theorem delayed_old_W_finalization (hroots : NamedRootCollisionFree p c E rho)
    (hqc : RQCOrigin p c E rho)
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β W : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hnew : W ∉ (storeAt p c E rho i x).fg.TF)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    (hne : (finalityView p W).F ≠ .genesis)
    (hdifferent : (finalityView p W).F ≠ (heightView p W).J) :
    W ∉ (storeAt p c E rho i x).fg.TF ∧
      ∃ carrier, FGBlock.Preceq carrier W ∧
        (heightView p carrier).J = (finalityView p W).F ∧
        (heightView p carrier).J ≠ (heightView p W).J ∧
        (FGBlock.Preceq (finalityView p W).F β ∨ FGBlock.Preceq β (finalityView p W).F) := by
  obtain ⟨carrier, hp, hJ, _, hcompat⟩ := outage_disclosed_finalization (hroots := hroots) hqc
      hi hx hβ hist hW hne
  exact ⟨hnew, carrier, hp, hJ, hJ ▸ hdifferent, hcompat⟩

/-- The same old history covers a newly disclosed crossing QC, including timeout rows. -/
example (hqc : RQCOrigin p c E rho) {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β W X : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    {m : Nat} (hm : 1 ≤ m) (hlt : m < (heightView p W).h)
    (hX : FGBlock.Preceq X W) (hheight : (heightView p X).h = m)
    {Q : Finset (Fin p.n)} {rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)}
    (hQ : p.E.IsQuorum Q)
    (hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧ (rows k).2.height_pair.matchesEntry m X.root = true) :
    FGBlock.Preceq X β ∨ FGBlock.Preceq β X :=
  (outage_disclosed_crossing (hroots := hroots) hqc hi hx hβ hist hW hm hlt hX hheight hQ hr).2

/-- A raised contested frame uses every old source, not the old receiver's visible certificates. -/
public theorem delayed_contested_frame (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) (hx : x ∈ rho.honest)
    {B : Block} {β : FGBlock (Fin p.n)} (hβ : eraseFG β = B)
    (hist : OutageSourceHistory p c E rho B i)
    (hcontest : (R_at p c E rho (i + 1) x).contest = true) :
    ∀ W ∈ (storeAt p c E rho (i + 1) x).fg.TF,
      (heightView p W).h = (R_at p c E rho (i + 1) x).H →
      ¬ FGBlock.Preceq (R_at p c E rho (i + 1) x).J W → FGBlock.Preceq β W := by
  have hn : OutageNamedHistory p c E rho β (i + 1) :=
    outage_named_of_source_history (hroots := hroots) hβ (outage_source_history_delivery hi
        hist) hnamed
  have _ := hframe
  have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
  exact ((hcp (i + 1) x β hx hn.history).2.2.2.2 hcontest).2

/-- A delivery can leave F unchanged while the successor frame is contested.
The selected row keeps its exact deadline before the frame is recomputed. -/
example {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) {B : Block} {g : Nat} {dl : Time}
    (hm : (B, g, dl) ∈ (storeAt p c E rho i x).base.obligations)
    (hF : (storeAt p c E rho (i + 1) x).fg.F = (storeAt p c E rho i x).fg.F)
    (hc : Block.Compatible B (F_at p c E rho i x)) :
    (B, g, dl) ∈ (storeAt p c E rho (i + 1) x).base.obligations := by
  have hpost : storeAt p c E rho (i + 1) x =
      FGSA.process p (storeAt p c E rho i x) (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho hi]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  rw [hpost]
  rcases arming_process_lease p (storeAt p c E rho i x) (toWire p o) with h | h
  · rw [h.1]; exact hm
  · rw [h.1]
    apply List.mem_filter.mpr
    refine ⟨hm, ?_⟩
    change Block.compatible B
      (eraseFG (FGSA.process p (storeAt p c E rho i x) (toWire p o)).fg.F) = true
    rw [← hpost, hF]
    exact hc

/-- Different descendants above B can conflict; normalization retains B and loses the old suffix. -/
example :
    let B := Block.node .genesis 1 ⟨1⟩ 0
    let S := Block.node B 2 ⟨2⟩ 0
    let F := Block.node B 2 ⟨3⟩ 1
    Gen.AC.normalizeOutput F S = F ∧
      Block.Preceq B (Gen.AC.normalizeOutput F S) ∧
      ¬ Block.Preceq S (Gen.AC.normalizeOutput F S) := by
  decide

/-- A raw conflicting result is saved but creates no fast-write source. -/
public theorem raw_conflicting_saved (p : Params) (st : State p.n) (s : Slot) {B C : Block}
    (hnew : GridCO.savedGenuine st.base s = none) (hjoined : joinedNow p st = true)
    (hraw : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s = some C)
    {dl : Time} (hrow : (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations)
    (hconflict : ¬ Block.Compatible B C) :
    GridCO.savedGenuine (FGSA.gateStep p st s).base s = some (some C) ∧
      FGSA.fastSet p (eraseFG st.fg.F) (FGSA.actView st) s = [] := by
  have hguard :
      (FGSA.actView st).obligations.any (fun row => !Block.compatible row.1 C) = true := by
    apply List.any_eq_true.mpr
    refine ⟨(B, SA.releaseThreshold p.toParams, dl), hrow, ?_⟩
    have hf : Block.compatible B C = false := Bool.eq_false_iff.mpr hconflict
    rw [hf]
    rfl
  refine ⟨?_, ?_⟩
  · rw [(gateStep_fresh p st s hnew hjoined).1, hraw]
  · unfold FGSA.fastSet
    rw [hraw]
    change (if (FGSA.actView st).obligations.any (fun row => !Block.compatible row.1 C)
      then [] else _) = []
    rw [hguard]
    rfl

/-- Only label j+1 can be in flight across d(j). -/
example (p : Params) (j r : Slot)
    (hv : SA.voteTime p.toParams r ≤ SA.gateTime p.toParams j)
    (hq : SA.gateTime p.toParams j < SA.releaseTime p.toParams r) : r = j + 1 :=
  arming_inflight p j r hv hq

/-- FaultQ does not imply the strict release bound. -/
example : 3 < (2 * 5 + 2) / 3 ∧ ¬ 3 < (5 + 1) / 2 := by decide

/-- The threshold equality cannot satisfy a healthy-batch count. -/
example (n h : Nat) (hhealthy : (n + 1) / 2 < h) : ¬ h ≤ n - (n + 1) / 2 := by omega

/-- Slow below τ and fast exactly at τ both permit a strict healthy batch. -/
example : 1 < 2 ∧ 2 ≤ 5 - 1 ∧ 2 < (5 + 1) / 2 ∧
    1 < 3 ∧ 3 ≤ 5 - 1 ∧ 3 = (5 + 1) / 2 := by decide

/-- Equality expires; a strict earlier time retains the selected row. -/
example :
    let B := Block.node .genesis 1 ⟨1⟩ 0
    let st : GridCO.State 1 .root := { GridCO.initial 1 .root with obligations := [(B, 1, 10)] }
    (GridCO.expire st 10).obligations = [] ∧
      (B, 1, 10) ∈ (GridCO.expire st 9).obligations := by decide

/-- A shorter renewal keeps the greater deadline. -/
example :
    let B := Block.node .genesis 1 ⟨1⟩ 0
    let st : GridCO.State 1 .root := { GridCO.initial 1 .root with obligations := [(B, 1, 20)] }
    (B, 1, 20) ∈ (GridCO.writeObligation st B 1 10).obligations := by decide

/-- Pending beyond the endpoint, equality, and an empty interval need no gate evaluation. -/
example (d b₁ t : Time) (hbd : b₁ ≤ d) (hdt : d ≤ t) : ¬ t < b₁ :=
  not_lt_of_ge (hbd.trans hdt)
example (d t : Time) (hdt : d ≤ t) : ¬ t < d := not_lt_of_ge hdt
example (b t : Time) (hbt : b ≤ t) : ¬ t < b := not_lt_of_ge hbt
example (d b₁ hor t : Time) (hd : hor < d) (hb : b₁ ≤ hor) (ht : d ≤ t) : ¬ t < b₁ :=
  not_lt_of_ge (hb.trans (hd.le.trans ht))

/-- Budget equality still gives a strict pending deadline. -/
example (p : Params) (l : Slot) (b₀ b₁ : Time)
    (hcut : b₀ < SA.gateTime p.toParams (l + 1)) (hbudget : b₁ - b₀ ≤ L p) :
    b₁ < SA.gateTime p.toParams (l + 1) + L p := by
  have hb : b₁ ≤ b₀ + L p := by
    simpa only [add_comm] using (sub_le_iff_le_add.mp hbudget)
  exact hb.trans_lt (add_lt_add_of_lt_of_le hcut le_rfl)

/-- Sleeping suppresses emissions and still runs the clock. -/
example (nd : Node p) (x : V) (t : Time) (hasleep : E.awake x t = false) :
    (V2.D.tick E rho nd x t).2 = [] ∧
      (V2.D.tick E rho nd x t).1.st = FGSA.clock p nd.st t :=
  ⟨(fgsa_tick_asleep E rho nd x t hasleep).1, tick_st (c := c) E rho nd x t⟩

/-- Slot zero has a genesis HEAD even for an arbitrary store. -/
example (p : Params) (st : State p.n) : FGSA.headVote p st 0 = .genesis := rfl

/-- Timeout and target names identify the same entry. -/
example (h : Nat) (root : BlockId) :
    namedEntry (.vote h root true) = namedEntry (.vote h root false) := rfl

/-- Restart keeps durable obligations at the exact wake time. -/
public theorem restart_keeps_obligations (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.base.obligations =
      nd.st.base.obligations := by
  change (acRestart p nd.st w).base.obligations = _
  exact acRestart_obligations p nd.st w

/-- A restart event preserves the selected covering lock without a NoRestart input. -/
public theorem restart_keeps_protection {B : Block} {j : Slot} {i : Nat} {x : V} {w : Time}
    (he : rho.events[i]? = some (.restart x w))
    (hp : OutageProtection p B j (storeAt p c E rho i x)) :
    OutageProtection p B j (storeAt p c E rho (i + 1) x) :=
  outage_restart_protection_at he hp

#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.same_time_disclosure
#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.delayed_old_W_finalization
#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.delayed_contested_frame
#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.raw_conflicting_saved
#print axioms AvailableChain.FGSA.Run.outage_disclosed_crossing
#print axioms AvailableChain.FGSA.Run.outage_disclosed_finalization
#print axioms AvailableChain.FGSA.Run.outage_liveRoot_covers
#print axioms AvailableChain.FGSA.Run.outage_good_release_bound
#print axioms AvailableChain.FGSA.Run.outage_event_induction_scoped
#print axioms AvailableChain.FGSA.Run.outage_armed_induction_scoped
#print axioms AvailableChain.FGSA.Run.outage_armed_read_scoped
#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.restart_keeps_obligations
#print axioms AvailableChain.FGSA.Run.Tests.OutageInduction.restart_keeps_protection

end AvailableChain.FGSA.Run.Tests.OutageInduction
