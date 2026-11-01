module
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.SafetyClient -- shake: keep (examples)

public section

/-! Behavior controls of the generic FG finality safety contracts (P13).
Each control is a small concrete run or a generic consequence of the laws.
The expected failures of the opposite claims are compiled in
`scripts/check-fg-compose-controls.py`. -/

namespace AvailableChain.FGCompose.Tests.SafetyControls
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### 1. Unordered inclusive reads

`readAt` replays the events with time `≤ t` in list order. In an unsorted
trace this is not a prefix replay, so monotonicity of inclusive reads needs
sortedness. Row origins come from the original trace. -/

abbrev counter : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := 0
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st o => 2 * st + o.payload
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

abbrev envU : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

abbrev unordered : V2.D.Run Unit counter where
  honest := {()}
  horizon := 2
  events := [.deliver () ⟨.none, 1⟩ 2, .deliver () ⟨.none, 2⟩ 1]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

theorem unordered_not_sorted :
    ¬ unordered.events.Pairwise (fun a b => a.time ≤ b.time) := by decide

/-- The inclusive read at time 1 replays only the second listed event. -/
theorem unordered_read : V2.D.Run.readAt envU unordered 1 () = 2 := by decide

/-- No prefix replay of the trace has the state of that read. -/
theorem unordered_read_not_prefix :
    ∀ i, i ≤ 2 → V2.D.Run.stateBefore envU unordered i () ≠ 2 := by decide

example : V2.D.Run.readAt envU unordered 2 () = 4 := by decide

/-- The replayed delivery is an event of the original trace. -/
example : V2.Event.deliver () ⟨.none, 2⟩ 1 ∈ unordered.events := by decide

/-! ### 2. Repeated signed rows -/

/-- A row wire carried twice decodes to one row with one signer. -/
theorem repeated_carriage_one_signer {n : Nat} {Wire : Type}
    (decode : Wire → Option (Row (Fin n))) (a : Wire) (u : Row (Fin n))
    (h : decode a = some u) :
    ([a, a].filterMap decode).toFinset = {u} ∧
      (([a, a].filterMap decode).map Row.signer).toFinset = {u.signer} := by
  simp [h]

/-- The client releases no content twice, also on a repeated input. -/
theorem repeated_input_released_once {n : Nat} (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (i : Fin n) (inp : Option (FGBlock (Fin n)) × HeadFields) (Λ : RecordOnce) :
    ((clientRunOnce Ef cfg i Λ [inp, inp]).map Row.onceKey).Nodup :=
  clientRunOnce_keys_nodup Ef cfg i [inp, inp] Λ

/-- Processing the same wire twice leaves the client record unchanged. -/
theorem repeated_delivery_record {In : Type} {P : V2.ProtocolSpecD In} {n : Nat} {Wire : Type}
    {S : FGSafetyReads P n Wire} {Ef : Electorate (Fin n)} {cfg : FGConfig}
    (J : FGSafetyClientLaws S Ef cfg) (nd : P.State) (o : P.Object) :
    S.record (P.process (P.process nd o) o) = S.record nd := by
  rw [J.process_record, J.process_record]

/-! ### 3. A nontrivial FG seat permutation -/

abbrev twoSeats : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 2
  Payload := Nat
  Durable := Unit
  init := 0
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

abbrev swapReads : FGSafetyReads twoSeats 2 Unit where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, 0⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.swap 0 1
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

abbrev seatRun : V2.D.Run (Fin 2) twoSeats where
  honest := {0, 1}
  horizon := 1
  events := []
  seatOf := fun _ j => j
  input := fun _ _ => ()

/-- FG seat 0 is held by node 1: attribution follows the permutation. -/
theorem swap_holder : safetyHolder swapReads seatRun 0 = 1 := by decide

/-- The `tick_rows` bijection is the permutation; node 1 signs as seat 0. -/
theorem swap_tick_bijection :
    (∀ i, seatRun.seatOf swapReads.fgLabel (swapReads.fgSeats i) = Equiv.swap 0 1 i) ∧
      (Equiv.swap (0 : Fin 2) 1).symm 1 = 0 := by decide

/-! ### 4. A restore that loses the durable record Λ -/

def sentOne : RecordOnce := ⟨Record.initial, [(.empty, none)]⟩

abbrev lossy : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := RecordOnce.initial
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => RecordOnce.initial
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

abbrev kept : V2.ProtocolSpecD Unit :=
  { lossy with Durable := RecordOnce, durable := id, restore := fun st _ => st }

abbrev lossyReads : FGSafetyReads lossy 1 Unit where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, 0⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := id
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

abbrev keptReads : FGSafetyReads kept 1 Unit where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, 0⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := id
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

/-- A restore that resets Λ loses a nonempty sent record. -/
theorem lossy_restart_record_fails :
    ¬ ∀ nd t, lossyReads.record (lossy.restore (lossy.durable nd) t) = lossyReads.record nd := by
  intro h
  have hl := congrArg (fun r : RecordOnce => r.sent.length) (h sentOne 0)
  exact absurd hl (by decide)

/-- So the lossy client has no client-law producer. -/
theorem lossy_no_client_laws (Ef : Electorate (Fin 1)) (cfg : FGConfig) :
    ¬ FGSafetyClientLaws lossyReads Ef cfg :=
  fun J => lossy_restart_record_fails J.restart_record

/-- A durable Λ meets `restart_record`. -/
theorem kept_restart_record :
    ∀ nd t, keptReads.record (kept.restore (kept.durable nd) t) = keptReads.record nd :=
  fun _ _ => rfl

/-! ### 5. An emitted-only tip is not a direct named-scope seed

The tip `tip` is emitted at time 1 and never delivered. It is a run block,
but the scope laws hold for a scope without it. Its parent is in scope. -/

def eraseZ : FGBlock (Fin 0) → Block
  | .genesis => .genesis
  | .node p s r x _ => .node (eraseZ p) s r x

private theorem rows_nil (rs : List (Row (Fin 0))) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons row _ => exact Fin.elim0 row.signer

theorem eraseZ_inj : Function.Injective eraseZ := by
  intro A
  induction A with
  | genesis =>
    intro B h
    cases B <;> simp [eraseZ] at h ⊢
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [eraseZ] at h
    | node p' s' r' x' rs' =>
      simp only [eraseZ, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hx⟩ := h
      have hpp := ih hp
      subst p' s' r' x'
      rw [rows_nil rs, rows_nil rs']

def tipBlock : Block := .node .genesis 1 ⟨7⟩ 0

def tip : FGBlock (Fin 0) := .node .genesis 1 ⟨7⟩ 0 []

abbrev emitter : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 0
  Payload := Unit
  Durable := Unit
  init := ()
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ t => if t = 1 then [()] else []
  process := fun st _ => st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => ()
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

abbrev emitReads : FGCoreReads emitter 0 Unit Unit Unit where
  core _ := ⟨(), Store.init, [], []⟩
  erase := eraseZ
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

abbrev emitSafety : FGSafetyReads emitter 0 Unit where
  proposalErase := fun _ => some tipBlock
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, ()⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

abbrev emitRun : V2.D.Run Unit emitter where
  honest := {()}
  horizon := 1
  events := [.tick () 1]
  seatOf := fun _ i => Fin.elim0 i
  input := fun _ _ => ()

/-- The scope of delivered proposals and genesis. -/
def deliveredScope (b : Block) : Prop :=
  b = .genesis ∨ ∃ x o t, V2.Event.deliver x o t ∈ emitRun.events ∧
    emitSafety.proposalErase o = some b

theorem tip_emitted : V2.D.Run.emits envU emitRun () ⟨.none, ()⟩ 1 :=
  ⟨0, rfl, by decide⟩

theorem tip_runBlock : safetyRunBlock emitReads emitSafety envU emitRun tip :=
  ⟨⟨.none, ()⟩, tipBlock, rfl, Or.inl ⟨(), 1, tip_emitted⟩, by decide⟩

private theorem emitRun_no_delivery (x : Unit) (o : emitter.Object) (t : Time) :
    V2.Event.deliver x o t ∉ emitRun.events := by
  simp

private theorem runBlock_parent (K : FGBlock (Fin 0))
    (hK : safetyRunBlock emitReads emitSafety envU emitRun K) : K.parent = .genesis := by
  obtain ⟨o, b, hb, _, hpre⟩ := hK
  cases hb
  cases K with
  | genesis => rfl
  | node p s r x rs =>
    change Block.preceq (.node (eraseZ p) s r x) tipBlock = true at hpre
    change (decide (Block.node (eraseZ p) s r x = tipBlock) ||
      Block.preceq (.node (eraseZ p) s r x) .genesis) = true at hpre
    rcases Bool.or_eq_true_iff.mp hpre with he | hg
    · have he := of_decide_eq_true he
      simp only [tipBlock, Block.node.injEq] at he
      have hp : p = .genesis := eraseZ_inj (by rw [he.1]; rfl)
      exact hp
    · change decide (Block.node (eraseZ p) s r x = .genesis) = true at hg
      exact absurd (of_decide_eq_true hg) (by simp)

/-- The scope laws hold without the emitted-only tip. -/
theorem delivered_scope_laws :
    FGSafetyScopeLaws emitReads emitSafety envU emitRun deliveredScope where
  genesis_scope _ _ := Or.inl rfl
  delivered_scope x o t _ hd _ := absurd hd (emitRun_no_delivery x o t)
  parent_scope K hK hne := absurd (runBlock_parent K hK) hne

theorem tip_not_seed : ¬ deliveredScope (emitReads.erase tip) := by
  rintro (h | ⟨x, o, t, hd, _⟩)
  · exact absurd h (by decide)
  · exact emitRun_no_delivery x o t hd

/-- The parent-scope route remains valid for the tip. -/
theorem tip_parent_in_scope : deliveredScope (emitReads.erase tip.parent) := Or.inl rfl

end AvailableChain.FGCompose.Tests.SafetyControls

end
