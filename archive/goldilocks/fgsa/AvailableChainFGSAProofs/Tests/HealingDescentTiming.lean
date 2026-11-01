module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTimingRFProv
-- shake: keep (boundary examples)
public import AvailableChainFGSAProofs.Proofs.Foundations.Cap
-- shake: keep (INLINE supplier examples)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.HealingDescentTiming
open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

local instance : DecidableEq (KitFG.FGCertEntry (Fin 1)) := fun a b =>
  decidable_of_iff (a.j = b.j ∧ a.X = b.X ∧ a.Q = b.Q) (by cases a; cases b; simp)

-- Different honest nodes can have ordered tick indices at the same time.
-- This order supplies no complete period.
private def sameTicks : List (V2.Event Bool (Obj params)) :=
  [.tick false 6, .tick true 6]

example : sameTicks[0]? = some (.tick false 6) ∧
    sameTicks[1]? = some (.tick true 6) ∧
    false ∈ ({false, true} : Finset Bool) ∧ true ∈ ({false, true} : Finset Bool) ∧
    (V2.Event.tick false 6 : V2.Event Bool (Obj params)).key ≤
      (V2.Event.tick true 6 : V2.Event Bool (Obj params)).key ∧
    ¬ (params.actionTime 0 + P params ≤ params.actionTime 0) := by decide

-- Same-time delivery is after all ticks. A saved receipt strictly before
-- an action tick must therefore have strictly smaller time.
example {In V : Type} [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa params c)) (hs : V2.D.ScheduleWellFormed E rho)
    {k i : Nat} {x z : V} {o : Obj params} {t : Time} {r : Nat}
    (hki : k < i) (hk : rho.events[k]? = some (.deliver x o t))
    (hi : rho.events[i]? = some (.tick z (params.actionTime r))) :
    t < params.actionTime r :=
  healing_receipt_before_tick params c E rho hs hki hk hi

example : params.actionTime 0 + P params ≤ params.actionTime 1 :=
  healing_action_period params (by decide)

private def progressBlock : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨1⟩ 0 [⟨0, .vote 1 genesisRoot true, none⟩]
private def signerHead : FGBlock (Fin 1) :=
  .node progressBlock 2 ⟨2⟩ 0 [⟨0, .vote 2 progressBlock.root false, none⟩]
private def latestBirth : FGBlock (Fin 1) :=
  .node signerHead 3 ⟨3⟩ 0 [⟨0, .vote 3 signerHead.root false, none⟩]
private def oldChoice : FGBlock (Fin 1) :=
  .node latestBirth 4 ⟨4⟩ 0 [⟨0, .empty, some ⟨2, progressBlock.root⟩⟩]

-- The honest finality signer's justification can differ from the eventual
-- carrier's latest J. The pair retains the exact height and root.
example : (heightView params signerHead).h_j = 2 ∧
    (heightView params signerHead).J = progressBlock ∧
    finality_pair Record.initial
      (Window.headFields params 2 signerHead) =
      some ⟨2, progressBlock.root⟩ ∧
    (heightView params oldChoice).h_j = 3 ∧
    (heightView params oldChoice).J = signerHead ∧
    (heightView params signerHead).J ≠ (heightView params oldChoice).J := by decide

-- The selected F is an older window entry. Its h_F is retained, while
-- the later justification remains in the window.
example : (Window.certificateSelection params 2).chosen oldChoice =
      some ⟨2, progressBlock, {0}⟩ ∧
    (finalityView params oldChoice).F = progressBlock ∧
    (finalityView params oldChoice).h_F = 2 ∧
    (Window.certificateSelection params 2).afterPrune oldChoice =
      [⟨3, signerHead, ∅⟩] := by decide

private def genesisBirth : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨1⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def genesisFinal : FGBlock (Fin 1) :=
  .node genesisBirth 2 ⟨5⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩]

-- A positive certificate height does not require a non-genesis F.
example : (finalityView params genesisFinal).F = .genesis ∧
    (finalityView params genesisFinal).h_F = 1 := by decide

-- The release q_(sStar) is before the reset action. RFProv's lower cut
-- cannot supply a proof at this release. T1 must cover this earlier cut.
example (p : Params) (r : Nat) :
    SA.releaseTime p.toParams (r * p.R) < p.actionTime r := by
  change 4 * p.Δ * ((r * p.R : Nat) : Int) + 5 * p.Δ <
    4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
  nlinarith [p.deltaPos]

-- The clock adapter accepts any read index after the saved receipt,
-- including a read past the final event. No awake premise is present.
example {In V : Type} [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa params c)) (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) {k j r : Nat} {x z : V} {o : Obj params} {t : Time}
    (hk : rho.events[k]? = some (.deliver x o t))
    (hj : rho.events[j]? = some (.tick z (params.actionTime r)))
    (ht : params.actionTime r ≤ t) :
    params.actionTime r ≤ (storeAt params c E rho (rho.events.length + 7) x).base.now := by
  have hkl := (List.getElem?_eq_some_iff.mp hk).1
  exact healing_delivery_clock params c E rho hv hnr (by omega) hk hj ht

-- The receipt round must agree with the honest row's actual round,
-- even when the INLINE witness starts with a different round variable.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hv : V2.D.ExecutionValid E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {i : Nat} {x z : V} {a : RowWire p.n}
    {W : FGBlock (Fin p.n)} {u : Row (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hu : u ∈ chainRows W)
    (hb : HonestRowBefore p c E rho i z 0 a) (hd : a.toRow? = some u) :
    ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧ p.actionTime 0 ≤ t :=
  healing_row_delivery p c E rho hv heldRows hW hu hb hd

-- T2 also applies after the event list ends. It needs no reset or future tick.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    {x : V} (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho (rho.events.length + 7) x).fg.h_j ≠ 0) :
    ∃ K s, SourceBefore p c E rho (rho.events.length + 7) K s ∧
      (heightView p K).h = (storeAt p c E rho (rho.events.length + 7) x).fg.h_j ∧
      (heightView p K).T_h = (storeAt p c E rho (rho.events.length + 7) x).fg.J ∧
      SA.gateTime p.toParams s ≤
        (storeAt p c E rho (rho.events.length + 7) x).base.now :=
  healing_justified_source_clock (hroots := hroots) p c E rho hv hnr origin heldRows hx hj

-- The low arm includes the exact after-action cut, and a certificate
-- height equal to M. Its hypothesis concerns h_F of the carrier.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (xing : RXing p c E rho) (w : HealingWitness) (h0 : H0 p c E rho w)
    {x : V} {D : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hD : D ∈ (storeAt p c E rho (afterTicksIdx rho (p.actionTime w.rStar)) x).fg.TF)
    (hDF : (finalityView p D).F =
      (storeAt p c E rho (afterTicksIdx rho (p.actionTime w.rStar)) x).fg.F)
    (hcert : (finalityView p D).h_F = w.M) :
    Block.Preceq (F_at p c E rho (afterTicksIdx rho (p.actionTime w.rStar)) x) w.CStar :=
  healing_low_finality_at_reset p c E rho hs hnr xing w h0 hx le_rfl hD hDF hcert.le

-- These are the exact Assembly suppliers for Cap, held rows, and hhead.
-- T1 keeps the carrier certificate height at an end-of-events prefix.
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hnr : V2.D.NoRestart rho) (origin : RQCOrigin p c E rho)
    {x : V} (hx : x ∈ rho.honest)
    (hF : (storeAt p c E rho (rho.events.length + 7) x).fg.F ≠ .genesis) :
    ∃ D ∈ (storeAt p c E rho (rho.events.length + 7) x).fg.TF,
      (finalityView p D).F = (storeAt p c E rho (rho.events.length + 7) x).fg.F ∧
      ∃ K s, SourceBefore p c E rho (rho.events.length + 7) K s ∧
        (heightView p K).h = (finalityView p D).h_F ∧
        (heightView p K).T_h = (storeAt p c E rho (rho.events.length + 7) x).fg.F ∧
        SA.gateTime p.toParams s + P p ≤
          (storeAt p c E rho (rho.events.length + 7) x).base.now :=
  healing_finality_source_clock (hroots := hroots) p c E rho hv hnr origin
    (held_chain_row_origin_before p c E rho hv.toUnforgeableSignatures hv.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hL hv hQ) (cap_finality_head p c E rho) hx hF

-- The full clause-1 producer has the exact RFProv F-branch conclusion.
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hnr : V2.D.NoRestart rho) (origin : RQCOrigin p c E rho)
    (xing : RXing p c E rho) (w : HealingWitness) (h0 : H0 p c E rho w)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i) :
    Block.Preceq (F_at p c E rho i x) w.CStar ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
        SA.gateTime p.toParams s + P p ≤ (storeAt p c E rho i x).base.now ∧
        Block.Preceq (F_at p c E rho i x) (eraseFG K) :=
  healing_rFProv_finality (hroots := hroots) p c E rho hv hnr origin
    (held_chain_row_origin_before p c E rho hv.toUnforgeableSignatures hv.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hL hv hQ) (cap_finality_head p c E rho) xing w h0 i x hx hi

-- A restart retains the last tick clock after a receipt on a well-formed schedule.
-- The reader sleeps throughout. Delivery and public ticks still occur.
private def restartEnv : Generic.Env Unit :=
  ⟨1, by decide, 0, by decide, fun _ _ => false⟩
private def restartObj : Obj params := ⟨.none, .row (.vote ⟨.empty, none⟩)⟩
private def restartRun : V2.D.Run Unit (fgsa params unitCodec) :=
  { honest := {()}, horizon := 7,
    events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3,
      .tick () 4, .tick () 5, .tick () 6, .deliver () restartObj 6,
      .restart () 7, .tick () 7],
    seatOf := fun _ _ => (), input := fun _ _ => () }

private theorem restartSchedule : V2.D.ScheduleWellFormed restartEnv restartRun where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by decide
  honest_only := by decide
  tick_public := by
    intro v t ht
    change V2.Event.tick v t ∈
      [.tick () 0, .tick () 1, .tick () 2, .tick () 3,
        .tick () 4, .tick () 5, .tick () 6, .deliver () restartObj 6,
        .restart () 7, .tick () 7] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with he | he | he | he | he | he | he | he | he | he <;> cases he
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
  tick_total := by
    intro v hv t ⟨k, hk⟩ ht hh
    cases v
    change t = (k : Int) * 1 at hk
    rw [mul_one] at hk
    subst t
    change (k : Int) ≤ 7 at hh
    have hk7 : k ≤ 7 := by exact_mod_cast hh
    interval_cases k <;> decide

private theorem healing_restart_wake_clock_fixture :
    V2.D.ScheduleWellFormed restartEnv restartRun ∧
    restartRun.events[7]? = some (.deliver () restartObj 6) ∧
    restartRun.events[6]? = some (.tick () (params.actionTime 0)) ∧
    ¬ V2.D.NoRestart restartRun ∧
    (storeAt params unitCodec restartEnv restartRun 9 ()).base.now = 7 := by
  refine ⟨restartSchedule, rfl, rfl, ?_, ?_⟩
  · intro hnr
    exact hnr 8 () 7 rfl
  · decide +kernel

#print axioms healing_restart_wake_clock_fixture

end AvailableChain.FGSA.Run.Tests.HealingDescentTiming
