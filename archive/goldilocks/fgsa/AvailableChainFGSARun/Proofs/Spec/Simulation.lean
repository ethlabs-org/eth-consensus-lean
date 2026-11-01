module
public import AvailableChainFGSA.Proofs.Spec.Clock -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Spec.Handlers -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Restore -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule

public section

namespace AvailableChain.FGSA.Spec

/-! WP12b: Ruling U's simulation-only filter removes non-Assigned proposal chains.
The identity gate, store invariant, emission identity, and event stutter are proved below.
The old raw-erasure trace remains as regression evidence. A second initialized trace
checks block acceptance after restart with the retained clock of ruling Y.
Ruling X fixes row targets as root names in spec pin f54e403a.
Dependency/freshness normalization has a complete target-state induction and validity proof.
The independent source-handler, clock/lock relation and regime transfer remain unproved.
No Lean protocol or existing claim is changed. -/

/-- The last-tick cutoff can be removed at a gate when all stored votes precede it. -/
theorem spec_lateVotes_eq_pool (p : Params) (st : GridCO.State p.n .root) (s : Slot)
    (h : ∀ o ∈ GridCO.votesAt st s, GridCO.stampVote st o < SA.gateTime p.toParams s) :
    GridCO.lateVotes p.toParams.engine st s = GridCO.votesAt st s := by
  apply List.filter_eq_self.mpr
  intro o ho
  exact decide_eq_true (h o ho)

/-- The run adapter preserves the existing all-wire boundary check. -/
theorem spec_run_wire_check (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    (Run.fgsa p Run.unitCodec).wellFormed (Run.ofWire p (deliveryWire assigned o)) =
      (wellFormed p o && admissionValid assigned o) := by
  change FGSA.wellFormed p (Run.toWire p (Run.ofWire p (deliveryWire assigned o))) = _
  have hw : Run.toWire p (Run.ofWire p (deliveryWire assigned o)) =
      deliveryWire assigned o := (Run.toWireEquiv p).right_inv _
  rw [hw]
  exact delivery_check_embedding p assigned o

/-- Restart keeps the anti-slashing record and sets the exact wake clock. -/
theorem spec_restart_durable_retained (p : Params) (nd : Run.Node p) (w : Time) :
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd) w).record =
      nd.record ∧
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd) w).st.base.now =
      w := by
  refine ⟨rfl, ?_⟩
  change (acRestart p nd.st w).base.now = w
  exact acRestart_now p nd.st w

/-- Restore sets the wake clock without an extra tick or duty. -/
theorem spec_restart_clock_retained (p : Params) (st : FGSA.State p.n)
    (record : SimplexFG.RecordOnce) (w : Time) :
    ((Run.fgsa p Run.unitCodec).restore (st, record) w).st.base.now = w :=
  by
    change (acRestart p st w).base.now = w
    exact acRestart_now p st w

/-- Computable recursive proposer test, used only by the simulation. -/
def specAssignedCheck {n : Nat} (assigned : Slot → Fin n) : Block n → Bool
  | .genesis => true
  | .node P s i _ _ _ _ => (i == assigned s) && specAssignedCheck assigned P

theorem spec_assigned_check_iff {n : Nat} (assigned : Slot → Fin n) (B : Block n) :
    specAssignedCheck assigned B = true ↔ B.Assigned assigned := by
  induction B with
  | genesis =>
      dsimp only [specAssignedCheck]
      simp [Block.Assigned]
  | node P s i r rows raw support ih =>
      dsimp only [specAssignedCheck]
      simp [Block.Assigned, ih]

/-- The two identity conditions of FG admission. Other checks can only refuse more. -/
def specIdentityGate {n : Nat} (assigned : Slot → Fin n) (held : List (Block n)) :
    Block n → Bool
  | .genesis => false
  | .node P s i _ _ _ _ => (i == assigned s) && decide (P ∈ held)

/-- Initialization and admitted-parent closure supply Assigned; it is not a claim premise. -/
theorem spec_identity_gate_assigned {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : specIdentityGate assigned held B = true) :
    B.Assigned assigned := by
  cases B with
  | genesis => trivial
  | node P s i r rows raw support =>
      dsimp only [specIdentityGate] at hB
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      exact ⟨hB.1, hheld P hB.2⟩

/-- A non-Assigned payload fails before writes or carried-object handlers. -/
theorem spec_identity_gate_refused {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : ¬ B.Assigned assigned) :
    specIdentityGate assigned held B = false := by
  cases h : specIdentityGate assigned held B
  · rfl
  · exact False.elim (hB (spec_identity_gate_assigned assigned held hheld B h))

/-- Refusal keeps both states and produces no output, for every remaining block handler. -/
theorem spec_identity_refusal_step {n : Nat} {σ α O : Type}
    (assigned : Slot → Fin n) (held : List (Block n))
    (hheld : ∀ B ∈ held, B.Assigned assigned) (B : Block n)
    (hB : ¬ B.Assigned assigned) (next : σ × α → (σ × α) × List O) (st : σ × α) :
    (if specIdentityGate assigned held B then next st else (st, [])) = (st, []) := by
  rw [spec_identity_gate_refused assigned held hheld B hB]
  rfl

/-- Admitted blocks have Assigned parents, so plain Lean membership is exact here. -/
theorem spec_assigned_parent_membership {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : B.Assigned assigned) :
    B.embed.parent ∈ held.map Block.embed ↔ B.parent ∈ held := by
  have hp : B.parent.Assigned assigned := by
    cases B with
    | genesis => trivial
    | node P s i r rows raw support => exact hB.2
  rw [embed_parent, List.mem_map]
  constructor
  · rintro ⟨P, hP, heq⟩
    exact (assigned_embed_injective assigned P B.parent (hheld P hP) hp heq) ▸ hP
  · intro h
    exact ⟨B.parent, h, rfl⟩

/-- Identity-store cuts: the trace keeps refusals, accepted blocks, and restarts.
The Boolean is the result of the remaining admission checks. -/
def specIdentityStoreStep {n : Nat} (assigned : Slot → Fin n) (held : List (Block n)) :
    Option (Block n × Bool) → List (Block n)
  | none => [.genesis]
  | some (B, accepted) =>
      if specIdentityGate assigned held B && accepted then held ++ [B] else held

/-- The identity invariant follows by induction from initialization, at every cut.
This is the identity-store projection, not the full matched-state induction. -/
theorem spec_identity_store_induction {n : Nat} (assigned : Slot → Fin n)
    (events : List (Option (Block n × Bool))) :
    ∀ B ∈ events.foldl (specIdentityStoreStep assigned) [.genesis], B.Assigned assigned := by
  have step (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
      (event : Option (Block n × Bool)) :
      ∀ B ∈ specIdentityStoreStep assigned held event, B.Assigned assigned := by
    cases event with
    | none =>
        dsimp only [specIdentityStoreStep]
        simp [Block.Assigned]
    | some item =>
        rcases item with ⟨B, accepted⟩
        dsimp only [specIdentityStoreStep]
        split_ifs with h
        · intro C hC
          rcases List.mem_append.mp hC with hc | hc
          · exact hheld C hc
          · have heq := List.mem_singleton.mp hc
            subst C
            simp only [Bool.and_eq_true] at h
            exact spec_identity_gate_assigned assigned held hheld B h.1
        · exact hheld
  have fold (xs : List (Option (Block n × Bool))) (held : List (Block n))
      (hheld : ∀ B ∈ held, B.Assigned assigned) :
      ∀ B ∈ xs.foldl (specIdentityStoreStep assigned) held, B.Assigned assigned := by
    induction xs generalizing held with
    | nil => exact hheld
    | cons x xs ih => exact ih _ (step held hheld x)
  exact fold events [.genesis] (by simp [Block.Assigned])

/-- An honest proposal from a held parent passes the recursive identity filter. -/
theorem spec_assigned_proposal_emission {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (P : Block n) (hP : P ∈ held) (s : Slot) (root : BlockId)
    (rows : List (RowWire n)) (raw support : List (HeadWire n)) :
    specAssignedCheck assigned (.node P s (assigned s) root rows raw support) = true :=
  (spec_assigned_check_iff assigned _).mpr ⟨rfl, hheld P hP⟩

/-- Full source objects remain available; this filter constructs only target deliveries.
A removed source delivery maps to zero target events, never to absent authentication. -/
def specSimulationWire (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    Option (Run.Obj p) :=
  let identities := match o.payload with
    | .proposal B => specAssignedCheck assigned B
    | _ => true
  if identities && wellFormed p o && admissionValid assigned o then
    some (Run.ofWire p (deliveryWire assigned o)) else none

/-- Non-Assigned chains are stutters in the target event list. -/
theorem spec_simulation_wire_stutter (p : Params) (assigned : Slot → Fin p.n)
    (auth : Auth Label p.n) (B : Block p.n) (hB : ¬ B.Assigned assigned) :
    specSimulationWire p assigned ⟨auth, .proposal B⟩ = none := by
  have hb : specAssignedCheck assigned B = false := by
    cases h : specAssignedCheck assigned B
    · rfl
    · exact False.elim (hB ((spec_assigned_check_iff assigned B).mp h))
  dsimp only [specSimulationWire]
  simp [hb]

/-- Every retained delivery passes the target wire check. Dependency and freshness
checks still need the state relation; this is not an ExecutionValid theorem. -/
theorem spec_simulation_wire_valid (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (q : Run.Obj p) (hq : specSimulationWire p assigned o = some q) :
    (Run.fgsa p Run.unitCodec).wellFormed q = true := by
  dsimp only [specSimulationWire] at hq
  split_ifs at hq with h
  · have hg : (wellFormed p o && admissionValid assigned o) = true := by
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1.2, h.2⟩
    cases Option.some.inj hq
    rw [spec_run_wire_check, hg]

/-- A valid Assigned proposal keeps its authentication and all its signed lists. -/
theorem spec_simulation_proposal_retained (p : Params) (assigned : Slot → Fin p.n)
    (auth : Auth Label p.n) (B : Block p.n) (hB : B.Assigned assigned)
    (hw : wellFormed p ⟨auth, .proposal B⟩ = true)
    (ha : admissionValid assigned ⟨auth, .proposal B⟩ = true) :
    specSimulationWire p assigned ⟨auth, .proposal B⟩ =
      some (Run.ofWire p (Wire.embed ⟨auth, .proposal B⟩)) := by
  have ha' := ha
  simp only [admissionValid, Bool.and_eq_true] at ha'
  have hp := ha'.1
  dsimp only [specSimulationWire]
  simp [(spec_assigned_check_iff assigned B).mpr hB, hw, ha,
    deliveryWire, hp]

/-- Preserve ticks and restarts; filter refused deliveries without changing time or node. -/
def specSimulationEvent {V : Type} (p : Params) (assigned : Slot → Fin p.n) :
    V2.Event V (Wire p.n) → Option (V2.Event V (Run.Obj p))
  | .tick v t => some (.tick v t)
  | .restart v t => some (.restart v t)
  | .deliver v o t => (specSimulationWire p assigned o).map (fun q => .deliver v q t)

theorem spec_simulation_event_stutter {V : Type} (p : Params)
    (assigned : Slot → Fin p.n) (v : V) (t : Time) (auth : Auth Label p.n)
    (B : Block p.n) (hB : ¬ B.Assigned assigned) :
    specSimulationEvent p assigned (.deliver v ⟨auth, .proposal B⟩ t) = none := by
  dsimp only [specSimulationEvent]
  simp [spec_simulation_wire_stutter p assigned auth B hB]

theorem spec_simulation_event_key {V : Type} (p : Params) (assigned : Slot → Fin p.n)
    (e : V2.Event V (Wire p.n)) (f : V2.Event V (Run.Obj p))
    (h : specSimulationEvent p assigned e = some f) :
    f.key = e.key ∧ f.node = e.node := by
  cases e with
  | tick v t => cases Option.some.inj h; exact ⟨rfl, rfl⟩
  | restart v t => cases Option.some.inj h; exact ⟨rfl, rfl⟩
  | deliver v o t =>
      dsimp only [specSimulationEvent] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨q, _, rfl⟩ := h
      exact ⟨rfl, rfl⟩


/-- Missing dependencies cause no writes, for arbitrary target states and inputs. -/
theorem spec_missing_dependency_stutter (p : Params) (st : State p.n) (q : Run.Obj p)
    (h : Run.depsS p st q = false) : process p st (Run.toWire p q) = st := by
  unfold Run.depsS at h
  unfold process
  cases hd : (Run.toWire p q).decode with
  | none => simp [hd] at h
  | some x =>
    cases x with
    | vote s i b => simp [hd] at h
    | row i a => simp [hd] at h
    | block s N =>
      simp only [hd] at h
      change admitBlock p st s N = st
      delta admitBlock
      cases hn : namedParentHeld st N with
      | false => rfl
      | true =>
        cases hp : parentFG st N.erase with
        | none => rfl
        | some P => simp [hn, hp] at h

/-- A duplicate delivery causes no writes, including votes, rows and proposals. -/
theorem spec_duplicate_delivery_stutter (p : Params) (st : State p.n) (q : Run.Obj p)
    (h : Run.processedS p st q = true) : process p st (Run.toWire p q) = st := by
  unfold Run.processedS at h
  unfold process
  cases hd : (Run.toWire p q).decode with
  | none => simp [hd] at h
  | some x =>
    cases x with
    | vote s i b =>
      simp only [hd, decide_eq_true_eq] at h
      change (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes at h
      dsimp only [admitHead]
      simp [GridCO.admitVote, h]
    | row i a =>
      simp only [hd, decide_eq_true_eq] at h
      have ha : (Run.toWire p q).auth = .seat .fg i := by
        cases hw : Run.toWire p q with
        | mk auth payload =>
          rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
            cases payload <;> simp_all [FGSA.Wire.decode]
      dsimp only [admitRow, RowWire.decode?]
      simp [ha, h]
    | block s N =>
      simp only [hd, decide_eq_true_eq] at h
      have hb (P : SimplexFG.FGBlock (Fin p.n)) : blockAccepted p st s N P = false := by
        dsimp only [blockAccepted]
        simp [named_erase_root, h]
      change admitBlock p st s N = st
      delta admitBlock
      split
      · rfl
      · cases hp : parentFG st N.erase <;> simp [hb]

/-- Second simulation stage: test dependencies and freshness in the current target state.
The first stage retains the complete source identity. Row targets use root names (W2). -/
def specReadyWire (p : Params) (assigned : Slot → Fin p.n) (st : State p.n)
    (o : Wire p.n) : Option (Run.Obj p) :=
  match specSimulationWire p assigned o with
  | none => none
  | some q => if Run.depsS p st q && !Run.processedS p st q then some q else none

/-- All three delivery conditions hold for each retained wire. -/
theorem spec_ready_wire_valid (p : Params) (assigned : Slot → Fin p.n) (st : State p.n)
    (o : Wire p.n) (q : Run.Obj p) (h : specReadyWire p assigned st o = some q) :
    (Run.fgsa p Run.unitCodec).wellFormed q = true ∧
      Run.depsS p st q = true ∧ Run.processedS p st q = false := by
  cases hr : specSimulationWire p assigned o with
  | none =>
      dsimp only [specReadyWire] at h
      simp [hr] at h
  | some r =>
    dsimp only [specReadyWire] at h
    simp only [hr] at h
    split_ifs at h with hd
    · cases Option.some.inj h
      exact ⟨spec_simulation_wire_valid p assigned o q hr,
        by simpa only [Bool.and_eq_true, Bool.not_eq_true'] using hd⟩

/-- Dependency/freshness filtering preserves the target process step after the wire stage.
This is not a source-handler correspondence: the first stage needs the source refusal proof. -/
theorem spec_ready_wire_step (p : Params) (assigned : Slot → Fin p.n) (st : State p.n)
    (o : Wire p.n) :
    ((specReadyWire p assigned st o).map (fun q => process p st (Run.toWire p q))).getD st =
      ((specSimulationWire p assigned o).map
        (fun q => process p st (Run.toWire p q))).getD st := by
  cases hq : specSimulationWire p assigned o with
  | none =>
      dsimp only [specReadyWire]
      simp [hq]
  | some q =>
    dsimp only [specReadyWire]
    simp only [hq, Option.map_some, Option.getD_some]
    cases hd : Run.depsS p st q <;> cases hf : Run.processedS p st q
    · simp [spec_missing_dependency_stutter p st q hd]
    · simp [spec_missing_dependency_stutter p st q hd]
    · rfl
    · simp [spec_duplicate_delivery_stutter p st q hf]

/-- The full-parent gate agrees with the identity-filtered block step. This covers the
identity and refusal shell; the remaining handler here is still the Lean `process` kernel.
`hstore` and `hheld` are state-relation invariants, not new protocol claim premises. -/
theorem spec_block_identity_step (p : Params) (assigned : Slot → Fin p.n)
    (held : List (Block p.n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (st : State p.n) (hstore : st.namedBodies = held.map Block.embed)
    (auth : Auth Label p.n) (B : Block p.n)
    (hw : wellFormed p ⟨auth, .proposal B⟩ = true)
    (ha : admissionValid assigned ⟨auth, .proposal B⟩ = true) :
    (if specIdentityGate assigned held B then
      process p st (Wire.embed ⟨auth, .proposal B⟩) else st) =
    ((specReadyWire p assigned st ⟨auth, .proposal B⟩).map
      (fun q => process p st (Run.toWire p q))).getD st := by
  rw [spec_ready_wire_step]
  by_cases hb : B.Assigned assigned
  · rw [spec_simulation_proposal_retained p assigned auth B hb hw ha]
    simp only [Option.map_some, Option.getD_some]
    have he : Run.toWire p (Run.ofWire p (Wire.embed ⟨auth, .proposal B⟩)) =
        Wire.embed ⟨auth, .proposal B⟩ := (Run.toWireEquiv p).right_inv _
    rw [he]
    split_ifs with hg
    · rfl
    · have hp : B.parent ∉ held := by
        cases B with
        | genesis => simp [admissionValid, proposerAllowed] at ha
        | node P s i root rows raw support =>
          dsimp only [specIdentityGate] at hg ⊢
          simpa [Block.parent, hb.1] using hg
      have hn : namedParentHeld st B.embed = false := by
        simp only [namedParentHeld, hstore]
        exact decide_eq_false
          (fun h => hp ((spec_assigned_parent_membership assigned held hheld B hb).mp h))
      cases auth with
      | none => rfl
      | seat l i => cases l <;> rfl
      | proposer s =>
        change st = admitBlock p st s B.embed
        dsimp only [admitBlock]
        simp [hn]
  · rw [spec_identity_gate_refused assigned held hheld B hb,
      spec_simulation_wire_stutter p assigned auth B hb]
    rfl

/-- A target delivery is kept precisely when its dependencies are present and it is fresh.
Ticks and restarts remain in place; W1 restricts the source of the full simulation to NoRestart. -/
def specKeepEvent {V : Type} (p : Params)
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) :
    V2.Event V (Run.fgsa p Run.unitCodec).Object → Bool
  | .deliver v q _ => Run.depsS p (w v).st q && !Run.processedS p (w v).st q
  | _ => true

/-- Every discarded target event is a state stutter. No reachability premise is needed. -/
theorem spec_discarded_event_step {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) (e : V2.Event V (Run.fgsa p Run.unitCodec).Object)
    (h : specKeepEvent p w e = false) : V2.D.World.step E rho w e = w := by
  cases e with
  | restart v t =>
      dsimp only [specKeepEvent] at h
      simp at h
  | tick v t =>
      dsimp only [specKeepEvent] at h
      simp at h
  | deliver v q t =>
    have hp : process p (w v).st (Run.toWire p q) = (w v).st := by
      cases hd : Run.depsS p (w v).st q
      · exact spec_missing_dependency_stutter p (w v).st q hd
      · have hf : Run.processedS p (w v).st q = true := by
          dsimp only [specKeepEvent] at h ⊢
          simpa [hd] using h
        exact spec_duplicate_delivery_stutter p (w v).st q hf
    change Function.update w v { w v with st := process p (w v).st (Run.toWire p q) } = w
    rw [hp]
    exact Function.update_eq_self v w

/-- Normalize target events after the identity/wire stage, using the state at each cut.
The raw fold is used to compute that state; discarded events have no effect. -/
def specPruneEvents {V : Type} [DecidableEq V] (p : Params) (E : Generic.Env V)
    (rho : V2.D.Run V (Run.fgsa p Run.unitCodec)) :
    V2.D.World V (Run.fgsa p Run.unitCodec) →
      List (V2.Event V (Run.fgsa p Run.unitCodec).Object) →
      List (V2.Event V (Run.fgsa p Run.unitCodec).Object)
  | _, [] => []
  | w, e :: es =>
      let tail := specPruneEvents p E rho (V2.D.World.step E rho w e) es
      if specKeepEvent p w e then e :: tail else tail

/-- Matched-cut induction for the dependency/freshness stage, for every finite prefix.
The equality includes all nodes, their complete Lean stores and their durable records.
It does not assert that the input fold is the independent spec execution. -/
theorem spec_prune_matched_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (events : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) :
    (specPruneEvents p E rho w events).foldl (V2.D.World.step E rho) w =
      events.foldl (V2.D.World.step E rho) w := by
  induction events generalizing w with
  | nil => rfl
  | cons e es ih =>
    dsimp only [specPruneEvents]
    cases hk : specKeepEvent p w e
    · have hs := spec_discarded_event_step p E rho w e hk
      simp only [Bool.false_eq_true, ↓reduceIte, hs]
      change _ = es.foldl (V2.D.World.step E rho) (V2.D.World.step E rho w e)
      rw [hs]
      exact ih w
    · simp only [↓reduceIte]
      exact ih (V2.D.World.step E rho w e)

/-- Normalization only deletes deliveries; it preserves event order, nodes and times. -/
theorem spec_prune_sublist {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (events : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) :
    List.Sublist (specPruneEvents p E rho w events) events := by
  induction events generalizing w with
  | nil => exact List.Sublist.refl []
  | cons e es ih =>
    dsimp only [specPruneEvents]
    split
    · exact (ih _).cons_cons e
    · exact (ih _).cons e

/-- Appending a suffix starts normalization from the corresponding raw prefix cut. -/
theorem spec_prune_append {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (xs ys : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) :
    specPruneEvents p E rho w (xs ++ ys) = specPruneEvents p E rho w xs ++
      specPruneEvents p E rho (xs.foldl (V2.D.World.step E rho) w) ys := by
  induction xs generalizing w with
  | nil => rfl
  | cons e es ih =>
    change specPruneEvents p E rho w (e :: (es ++ ys)) = _
    dsimp only [specPruneEvents]
    split <;> simp only [ih, List.cons_append] <;> rfl

/-- Every surviving delivery has dependencies and is fresh at its new list position. -/
theorem spec_prune_delivery_conditions {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (events : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) (i : Nat) (v : V) (q : Run.Obj p)
    (t : Time) (h : (specPruneEvents p E rho w events)[i]? = some (.deliver v q t)) :
    let st := (((specPruneEvents p E rho w events).take i).foldl
      (V2.D.World.step E rho) w v).st
    Run.depsS p st q = true ∧ Run.processedS p st q = false := by
  induction events generalizing w i with
  | nil =>
      dsimp only [specPruneEvents] at h
      simp at h
  | cons e es ih =>
    cases hk : specKeepEvent p w e
    · have hs := spec_discarded_event_step p E rho w e hk
      dsimp only [specPruneEvents] at h ⊢
      simp only [hk, Bool.false_eq_true, ↓reduceIte, hs] at h ⊢
      exact ih w i h
    · dsimp only [specPruneEvents] at h ⊢
      simp only [hk, ↓reduceIte] at h ⊢
      cases i with
      | zero =>
        have he := Option.some.inj h
        subst e
        change Run.depsS p (w v).st q = true ∧ Run.processedS p (w v).st q = false
        dsimp only [specKeepEvent] at hk ⊢
        simpa only [Bool.and_eq_true, Bool.not_eq_true'] using hk
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        simp only [List.take_succ_cons]
        exact ih _ i h

/-- No tick is removed. -/
theorem spec_prune_tick_mem {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (events : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) (v : V) (t : Time) :
    .tick v t ∈ specPruneEvents p E rho w events ↔ .tick v t ∈ events := by
  induction events generalizing w with
  | nil => rfl
  | cons e es ih =>
    dsimp only [specPruneEvents]
    split_ifs with hk
    · simp only [List.mem_cons, ih]
    · have he : (.tick v t : V2.Event V (Run.fgsa p Run.unitCodec).Object) ≠ e := by
        rintro rfl
        exact hk rfl
      simp only [List.mem_cons, he, false_or, ih]

/-- No restart is removed. -/
theorem spec_prune_restart_mem {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (events : List (V2.Event V (Run.fgsa p Run.unitCodec).Object))
    (w : V2.D.World V (Run.fgsa p Run.unitCodec)) (v : V) (t : Time) :
    .restart v t ∈ specPruneEvents p E rho w events ↔ .restart v t ∈ events := by
  induction events generalizing w with
  | nil => rfl
  | cons e es ih =>
    dsimp only [specPruneEvents]
    split_ifs with hk
    · simp only [List.mem_cons, ih]
    · have he : (.restart v t : V2.Event V (Run.fgsa p Run.unitCodec).Object) ≠ e := by
        rintro rfl
        exact hk rfl
      simp only [List.mem_cons, he, false_or, ih]

/-- The revised target run keeps the fixed identities, inputs, honest set and horizon. -/
def specPruneRun {V : Type} [DecidableEq V] (p : Params) (E : Generic.Env V)
    (rho : V2.D.Run V (Run.fgsa p Run.unitCodec)) :
    V2.D.Run V (Run.fgsa p Run.unitCodec) :=
  { rho with events := specPruneEvents p E rho V2.D.World.init rho.events }

/-- Schedule validity survives the deletion of delivery stutters. -/
theorem spec_prune_schedule {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (h : V2.D.ScheduleWellFormed E rho) :
    V2.D.ScheduleWellFormed E (specPruneRun p E rho) := by
  have hs := spec_prune_sublist p E rho rho.events V2.D.World.init
  refine ⟨h.horizon_nonneg, h.sorted.sublist hs, h.nodup.sublist hs, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact h.in_horizon e (hs.subset he)
  · intro e he
    exact h.honest_only e (hs.subset he)
  · intro v t ht
    exact h.tick_public v t (hs.subset ht)
  · intro v hv t ht h0 hh hawake
    exact (spec_prune_tick_mem p E rho rho.events V2.D.World.init v t).mpr
      (h.tick_total v hv t ht h0 hh hawake)

/-- The construction preserves ruling W1's NoRestart scope. -/
theorem spec_prune_no_restart {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (h : V2.D.NoRestart rho) : V2.D.NoRestart (specPruneRun p E rho) := by
  intro i v t he
  have hm := List.mem_of_getElem? he
  have hr := (spec_prune_sublist p E rho rho.events V2.D.World.init).subset hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  exact h j v t hj

/-- Dependency and freshness conditions are derived, not added as claim premises.
The premise describes only the preceding identity/wire stage. -/
theorem spec_prune_delivery_valid {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (hw : ∀ v q t, .deliver v q t ∈ rho.events →
      (Run.fgsa p Run.unitCodec).wellFormed q = true) :
    V2.D.DeliveryWellFormed E (specPruneRun p E rho) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i v q t he
    exact hw v q t ((spec_prune_sublist p E rho rho.events V2.D.World.init).subset
      (List.mem_of_getElem? he))
  · intro i v q t he
    exact (spec_prune_delivery_conditions p E rho rho.events V2.D.World.init i v q t he).1
  · intro i v q t he
    exact (spec_prune_delivery_conditions p E rho rho.events V2.D.World.init i v q t he).2

/-- Full final-state equality for the target normalization stage. -/
theorem spec_prune_final {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec)) :
    V2.D.Run.final E (specPruneRun p E rho) = V2.D.Run.final E rho :=
  spec_prune_matched_cut p E rho rho.events V2.D.World.init

/-- Every raw tick has a target tick at the same time with the same input state.
This supplies the emission witness needed by the signature conditions. -/
theorem spec_prune_tick_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (i : Nat) (v : V) (t : Time) (hi : rho.events[i]? = some (.tick v t)) :
    ∃ j, (specPruneRun p E rho).events[j]? = some (.tick v t) ∧
      V2.D.Run.stateBefore E (specPruneRun p E rho) j = V2.D.Run.stateBefore E rho i := by
  let xs : List (V2.Event V (Run.fgsa p Run.unitCodec).Object) := rho.events.take i
  let ys : List (V2.Event V (Run.fgsa p Run.unitCodec).Object) := rho.events.drop (i + 1)
  have he : rho.events = xs ++ .tick v t :: ys := by
    have ht := List.take_append_drop (i + 1) rho.events
    rw [List.take_add_one, hi] at ht
    simpa only [Option.toList_some, List.append_assoc, List.singleton_append] using ht.symm
  let pre := specPruneEvents p E rho V2.D.World.init xs
  let w := xs.foldl (V2.D.World.step E rho) V2.D.World.init
  have hout : (specPruneRun p E rho).events = pre ++ .tick v t ::
      specPruneEvents p E rho (V2.D.World.step E rho w (.tick v t)) ys := by
    change specPruneEvents p E rho V2.D.World.init rho.events = _
    rw [he, spec_prune_append]
    rfl
  refine ⟨pre.length, ?_, ?_⟩
  · rw [hout]
    simp
  · change (((specPruneRun p E rho).events.take pre.length).foldl
      (V2.D.World.step E rho) V2.D.World.init) = _
    rw [hout, List.take_left]
    exact spec_prune_matched_cut p E rho xs V2.D.World.init

/-- Honest emission witnesses survive normalization with their original times. -/
theorem spec_prune_emits {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (v : V) (q : Run.Obj p) (t : Time) (h : V2.D.Run.emits E rho v q t) :
    V2.D.Run.emits E (specPruneRun p E rho) v q t := by
  obtain ⟨i, hi, hq⟩ := h
  obtain ⟨j, hj, hs⟩ := spec_prune_tick_cut p E rho i v t hi
  refine ⟨j, hj, ?_⟩
  simp only [V2.D.Run.emitsAt, hi] at hq
  simp only [V2.D.Run.emitsAt, hj, hs]
  exact hq

/-- Signature and carried-signature witnesses survive the revised construction. -/
theorem spec_prune_signatures {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (h : V2.D.UnforgeableSignatures E rho) :
    V2.D.UnforgeableSignatures E (specPruneRun p E rho) := by
  have hp v q t (hx : V2.D.Run.processes (specPruneRun p E rho) v q t) :
      V2.D.Run.processes rho v q t := by
    obtain ⟨i, hi⟩ := hx
    exact List.mem_iff_getElem?.mp
      ((spec_prune_sublist p E rho rho.events V2.D.World.init).subset
        (List.mem_of_getElem? hi))
  constructor
  · intro v q t hx u hu hh
    obtain ⟨t', ht, he⟩ := h.unforgeable v q t (hp v q t hx) u hu hh
    exact ⟨t', ht, spec_prune_emits p E rho u q t' he⟩
  · intro v q t hx q' hc u hu hh
    obtain ⟨t', ht, he⟩ := h.carried v q t (hp v q t hx) q' hc u hu hh
    exact ⟨t', ht, spec_prune_emits p E rho u q' t' he⟩

/-- Delivery normalization keeps the full sleep conditions. -/
theorem spec_prune_sleep {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (h : V2.D.SleepWellFormed E rho) : V2.D.SleepWellFormed E (specPruneRun p E rho) := by
  have hs := spec_prune_sublist p E rho rho.events V2.D.World.init
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v t ht; exact h.tick_awake v t (hs.subset ht)
  · intro v o t ht; exact h.deliver_awake v o t (hs.subset ht)
  · intro v t ht; exact h.restart_awake v t (hs.subset ht)
  · intro v hv t ht hh hw
    exact (spec_prune_restart_mem p E rho rho.events V2.D.World.init v t).mpr
      (h.wake_restart v hv t ht hh hw)

/-- Complete target validity after dependency/freshness normalization. The input run may
have missing-dependency and duplicate deliveries. This theorem does not supply the source
schedule or signature correspondence; those are separate simulation obligations. -/
theorem spec_prune_execution_valid {V : Type} [DecidableEq V] (p : Params)
    (E : Generic.Env V) (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (hs : V2.D.ScheduleWellFormed E rho) (ha : V2.D.UnforgeableSignatures E rho)
    (hSleep : V2.D.SleepWellFormed E rho)
    (hw : ∀ v q t, .deliver v q t ∈ rho.events →
      (Run.fgsa p Run.unitCodec).wellFormed q = true) :
    V2.D.ExecutionValid E (specPruneRun p E rho) :=
  { spec_prune_schedule p E rho hs, spec_prune_delivery_valid p E rho hw,
    spec_prune_signatures p E rho ha, spec_prune_sleep p E rho hSleep with }

/-- The first-stage event list is valid on the wire, including arbitrary refused inputs. -/
theorem spec_mapped_delivery_wire {V : Type} (p : Params) (assigned : Slot → Fin p.n)
    (events : List (V2.Event V (Wire p.n))) (v : V) (q : Run.Obj p) (t : Time)
    (h : .deliver v q t ∈ events.filterMap (specSimulationEvent p assigned)) :
    (Run.fgsa p Run.unitCodec).wellFormed q = true := by
  obtain ⟨e, _, he⟩ := List.mem_filterMap.mp h
  cases e with
  | tick u s =>
      dsimp only [specSimulationEvent] at he
      simp at he
  | restart u s =>
      dsimp only [specSimulationEvent] at he
      simp at he
  | deliver u o s =>
    dsimp only [specSimulationEvent] at he
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨r, hr, hh⟩ := he
    cases hh
    exact spec_simulation_wire_valid p assigned o q hr

/-- The concrete second-stage construction yields a valid NoRestart target execution.
The wire premise is discharged from the ruling-U mapping. Schedule and signature
correspondence from an independent spec run remain obligations of the first stage.
This is not the full spec-execution or protocol-claim transfer theorem. -/
theorem spec_revised_target_execution {V : Type} [DecidableEq V] (p : Params)
    (assigned : Slot → Fin p.n) (E : Generic.Env V)
    (events : List (V2.Event V (Wire p.n)))
    (rho : V2.D.Run V (Run.fgsa p Run.unitCodec))
    (hm : rho.events = events.filterMap (specSimulationEvent p assigned))
    (hs : V2.D.ScheduleWellFormed E rho) (ha : V2.D.UnforgeableSignatures E rho)
    (hn : V2.D.NoRestart rho) (hSleep : V2.D.SleepWellFormed E rho) :
    V2.D.ExecutionValid E (specPruneRun p E rho) ∧
      V2.D.NoRestart (specPruneRun p E rho) ∧
      (specPruneRun p E rho).honest = rho.honest ∧
      (specPruneRun p E rho).horizon = rho.horizon ∧
      (specPruneRun p E rho).seatOf = rho.seatOf ∧
      (specPruneRun p E rho).input = rho.input ∧
      V2.D.Run.final E (specPruneRun p E rho) = V2.D.Run.final E rho := by
  refine ⟨spec_prune_execution_valid p E rho hs ha hSleep ?_, spec_prune_no_restart p E rho hn,
    rfl, rfl, rfl, rfl, spec_prune_final p E rho⟩
  intro v q t h
  rw [hm] at h
  exact spec_mapped_delivery_wire p assigned events v q t h

/-- A small parameter set with distinct parent and child roots. -/
abbrev parentIdentityParams : Params :=
  { Δ := 1, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun d => ⟨d.slot + 6⟩ }

def parentIdentityAssigned (_ : Slot) : Fin 2 := 0

def parentIdentityHeld : Block 2 := .node .genesis 1 0 ⟨7⟩ [] [] []

def parentIdentityAbsent : Block 2 := .node .genesis 1 1 ⟨7⟩ [] [] []

def parentIdentityChild : Block 2 := .node parentIdentityAbsent 2 0 ⟨8⟩ [] [] []

def parentIdentityGoodChild : Block 2 := .node parentIdentityHeld 2 0 ⟨8⟩ [] [] []

abbrev parentIdentityWire : Wire 2 := ⟨.proposer 2, .proposal parentIdentityChild⟩

/-- One awake local tick for validator 1, with immediate self-delivery.
Validator 1 has no proposal duty under the fixed assignment. -/
def parentIdentityTick (nd : Run.Node parentIdentityParams) (t : Nat) :
    Run.Node parentIdentityParams := Id.run do
  let p := parentIdentityParams
  let mut nd := { nd with st := FGSA.clock p nd.st t }
  let s := p.slotOf t
  if (t : Time) = SA.voteTime p.toParams s then
    let H := Next.headVoteNext p nd.st s
    nd := { nd with st := process p nd.st ⟨.seat (.head s) 1, .head H.root⟩ }
  if (t : Time) = p.actionTime ((s - 1) / p.R) then
    let (row, record) := Next.attestNext p nd.st nd.record 1
    nd := { nd with record := record }
    if let some a := row then
      nd := { nd with st := process p nd.st ⟨.seat .fg 1, .row a⟩ }
  return nd

/-- Public ticks 0 through 4, the valid parent delivery at 4, then ticks 5 through 8. -/
def parentIdentityBefore : Run.Node parentIdentityParams :=
  let nd := (List.range 5).foldl parentIdentityTick
    ⟨FGSA.initial 2, SimplexFG.RecordOnce.initial⟩
  let nd := { nd with
    st := process parentIdentityParams nd.st
      (Wire.embed ⟨.proposer 1, .proposal parentIdentityHeld⟩) }
  ([5, 6, 7, 8] : List Nat).foldl parentIdentityTick nd

/-- The all-wire erasure loses an ancestor identity even with a valid top proposer. -/
theorem spec_parent_identity_erasure :
    parentIdentityAbsent ≠ parentIdentityHeld ∧
    parentIdentityChild.parent ∉ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityGoodChild.parent ∈ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityChild.embed = parentIdentityGoodChild.embed ∧
    deliveryWire parentIdentityAssigned parentIdentityWire =
      deliveryWire parentIdentityAssigned
        ⟨.proposer 2, .proposal parentIdentityGoodChild⟩ := by decide

set_option maxRecDepth 4096 in
/-- Concrete refusal mismatch at time 8, after every earlier public tick.
The checked parent set is exactly genesis and the first received proposal. -/
theorem spec_parent_identity_trace :
    parentIdentityBefore.st.namedBodies = [.genesis, parentIdentityHeld.embed] ∧
    parentIdentityBefore.st.base.now = 8 ∧
    wellFormed parentIdentityParams parentIdentityWire = true ∧
    admissionValid parentIdentityAssigned parentIdentityWire = true ∧
    FGSA.wellFormed parentIdentityParams
      (deliveryWire parentIdentityAssigned parentIdentityWire) = true ∧
    namedParentHeld parentIdentityBefore.st parentIdentityChild.embed = true ∧
    (process parentIdentityParams parentIdentityBefore.st
      (deliveryWire parentIdentityAssigned parentIdentityWire)).proposals.length = 2 := by
  decide

/-- Proposer-only aliases share a root without distinct digest inputs. -/
theorem spec_parent_identity_root : parentIdentityAbsent.root = parentIdentityHeld.root := by
  decide

/-- The old ancestor counterexample is removed by the simulation filter. -/
theorem spec_parent_identity_filtered :
    specSimulationWire parentIdentityParams parentIdentityAssigned parentIdentityWire = none ∧
    specIdentityGate parentIdentityAssigned [.genesis, parentIdentityHeld]
      parentIdentityChild = false := by decide

/-- A restart at 9 is strictly between public ticks 8 and 10. -/
abbrev specRestartParams : Params :=
  { Δ := 2, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun d => ⟨d.slot + 6⟩ }

def specRestartEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun _ _ => true⟩

def specRestartWire : Wire 2 := ⟨.proposer 1, .proposal parentIdentityHeld⟩

/-- The empty post-restart spec store, represented with the current clock.
This does not run an extra tick or duty. -/
def specRestartCurrent : State 2 := { FGSA.initial 2 with base.now := 9 }

/-- The exact prefix has every public tick and immediate HEAD self-delivery.
The only honest node is 1; proposer 0 can supply the empty proposal. -/
def specRestartRun : V2.D.Run (Fin 2) (Run.fgsa specRestartParams Run.unitCodec) where
  honest := {1}
  horizon := 9
  events := [.tick 1 0, .tick 1 2,
    .deliver 1 (Run.ofWire specRestartParams ⟨.seat (.head 0) 1, .head genesisRoot⟩) 2,
    .tick 1 4, .tick 1 6, .tick 1 8, .restart 1 9,
    .deliver 1 (Run.ofWire specRestartParams specRestartWire.embed) 9]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation unfolds the eight-event engine prefix and the block handler.
/-- All identity, parent, slot and row checks of the spec accept this empty block.
Lean keeps tick 8 through the restart at 9 and accepts the same block. The last
two conjuncts compute the initialized engine prefix and the post-delivery cut. -/
theorem spec_restart_retained_block_trace :
    parentIdentityHeld.Assigned parentIdentityAssigned ∧
    wellFormed specRestartParams specRestartWire = true ∧
    admissionValid parentIdentityAssigned specRestartWire = true ∧
    specIdentityGate parentIdentityAssigned [.genesis] parentIdentityHeld = true ∧
    blockAccepted specRestartParams specRestartCurrent 1 parentIdentityHeld.embed
      .genesis = true ∧
    (process specRestartParams specRestartCurrent specRestartWire.embed).proposals.length = 1 ∧
    (V2.D.Run.stateBefore specRestartEnv specRestartRun 7 1).st.base.now = 9 ∧
    (V2.D.Run.final specRestartEnv specRestartRun 1).st.proposals.length = 1 := by
  refine ⟨⟨rfl, trivial⟩, ?_⟩
  decide

set_option maxRecDepth 4096 in
/-- The restart trace obeys the engine's ordered, total public-tick schedule. -/
theorem spec_restart_schedule : V2.D.ScheduleWellFormed specRestartEnv specRestartRun := by
  constructor
  · decide
  · decide
  · decide
  · intro e he
    dsimp only [specRestartRun] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    dsimp only [specRestartRun] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v t ht
    dsimp only [specRestartRun] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      V2.Event.tick.injEq, reduceCtorEq, or_false, false_or] at ht
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · intro v hv t ht _ ht9
    have hv' : v = 1 := Finset.mem_singleton.mp hv
    subst v
    obtain ⟨k, rfl⟩ := ht
    change (k : Int) * 2 ≤ 9 at ht9
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The only deliveries in the restart fixture, with their exact list positions. -/
theorem spec_restart_delivery_cases (i : Nat) (v : Fin 2) (o : Run.Obj specRestartParams)
    (t : Time) (h : specRestartRun.events[i]? = some (.deliver v o t)) :
    (i = 2 ∧ v = 1 ∧
      o = Run.ofWire specRestartParams ⟨.seat (.head 0) 1, .head genesisRoot⟩ ∧ t = 2) ∨
    (i = 7 ∧ v = 1 ∧ o = Run.ofWire specRestartParams specRestartWire.embed ∧ t = 9) := by
  have hi : i < 8 := (List.getElem?_eq_some_iff.mp h).1
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [specRestartRun] at h
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The accepted block meets every engine delivery condition. -/
theorem spec_restart_delivery_valid :
    V2.D.DeliveryWellFormed specRestartEnv specRestartRun := by
  constructor
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

set_option maxRecDepth 4096 in
/-- Honest signatures come from the immediate HEAD emission; proposer 0 is faulty. -/
theorem spec_restart_signatures :
    V2.D.UnforgeableSignatures specRestartEnv specRestartRun := by
  constructor
  · intro v o t hp u hu hh
    obtain ⟨i, hi⟩ := hp
    have hu' : u = 1 := Finset.mem_singleton.mp hu
    subst u
    rcases spec_restart_delivery_cases i v o t hi with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · refine ⟨2, le_rfl, 1, rfl, ?_⟩
      change _ ∈ [Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩]
      exact List.mem_singleton_self _
    · change some (0 : Fin 2) = some 1 at hh
      contradiction
  · intro v o t hp o' hc
    obtain ⟨i, hi⟩ := hp
    rcases spec_restart_delivery_cases i v o t hi with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact False.elim hc
    · change o' ∈ [] ∨ o' ∈ [] ∨ o' ∈ [] at hc
      simp at hc

/-- The target trace is a valid execution, not only an arbitrary handler state. -/
theorem spec_restart_execution_valid : V2.D.ExecutionValid specRestartEnv specRestartRun :=
  { spec_restart_schedule, spec_restart_delivery_valid, spec_restart_signatures with
    tick_awake := by intros; rfl
    deliver_awake := by intros; rfl
    restart_awake := by intros; rfl
    wake_restart := by
      intro v hv t ht hh hw
      have hfalse := hw.2
      change true = false at hfalse
      cases hfalse }

set_option maxRecDepth 4096 in
/-- Every self-visible emission is delivered immediately, before the next tick. -/
theorem spec_restart_self_delivery : V2.D.SelfDelivery specRestartEnv specRestartRun := by
  intro i v t h o ho _
  have hi : i < 8 := (List.getElem?_eq_some_iff.mp h).1
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [specRestartRun] at h
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, V2.Event.tick.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · change o ∈ [] at ho
    contradiction
  · have heq : o = Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩ := by
      change o ∈ [Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩] at ho
      exact List.mem_singleton.mp ho
    subst o
    exact ⟨2, by decide, rfl⟩
  · change o ∈ [] at ho
    contradiction
  · change o ∈ [] at ho
    contradiction
  · change o ∈ [] at ho
    contradiction

/-- A tick at 9 would violate the target's public-time condition. -/
theorem spec_restart_no_public_tick : ¬ V2.PublicTime specRestartEnv 9 := by
  rintro ⟨k, hk⟩
  change (9 : Int) = (k : Int) * 2 at hk
  omega

/-- The restart trace is outside the W1 NoRestart domain. -/
theorem spec_restart_outside_no_restart : ¬ V2.D.NoRestart specRestartRun := by
  intro h
  exact h 6 1 9 rfl

end AvailableChain.FGSA.Spec
end
