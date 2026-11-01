module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (anonymous lock and non-vacuity examples)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.RowPermission
open AvailableChain.SimplexFG

private abbrev p1 : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 4, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev rho0 : V2.D.Run (Fin 1) (fgsa p1 unitCodec) where
  honest := {0}
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

private abbrev env0 : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem schedule0 : V2.D.ScheduleWellFormed env0 rho0 where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by
    intro e he
    have heq := List.mem_singleton.mp he
    subst e
    exact Finset.mem_singleton_self _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v hv t _ ht hh _
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Finset.mem_singleton.mp hv
    subst v
    exact List.mem_singleton_self _

private theorem noDelivery0 (i : Nat) (v : Fin 1) (o : (fgsa p1 unitCodec).Object)
    (t : Time) : rho0.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

private theorem noEmission0 (x : Fin 1) (o : Obj p1) (t : Time) :
    ¬ V2.D.Run.emits env0 rho0 x o t := by
  rintro ⟨i, hi, ho⟩
  cases i with
  | zero =>
    change some (V2.Event.tick 0 0) = some (.tick x t) at hi
    have he : V2.Event.tick x t = .tick 0 0 := Option.some.inj hi.symm
    cases he
    change o ∈ [] at ho
    exact List.not_mem_nil ho
  | succ i => simp only [List.getElem?_cons_succ, List.getElem?_nil] at hi; cases hi

-- One honest validator at a real scheduled tick; no delivery is required.
private theorem base0 : Base₂ p1 unitCodec env0 rho0 where
  valid := {
    toScheduleWellFormed := schedule0
    tick_awake := by intros; rfl
    deliver_awake := by intros; rfl
    restart_awake := by intros; rfl
    wake_restart := by
      intro v hv t ht hhor _
      change t ≤ 0 at hhor
      exact ((not_lt_of_ge hhor) ht).elim
    wire := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    deps := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    fresh := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim }
  receiptIdealization := by
    have hnone : ∀ x o t, V2.Event.deliver x o t ∉ rho0.events := by
      intro x o t hd
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
      exact noDelivery0 i x o t hi
    have hg {A : NamedProposal p1.n} (hA : NamedProposalInRun p1 unitCodec env0 rho0 A) :
        A = .genesis := by
      rcases namedProposalInRun_genesis_or_delivered env0 rho0
        (by intro x o t b hd; exact (hnone x o t hd).elim) hA with h | hd
      · exact h
      · obtain ⟨x, o, t, hd, _⟩ := hd
        exact (hnone x o t hd).elim
    have scopeX {X : NamedProposal p1.n}
        (hX : NamedProposalReceiptScope p1 unitCodec env0 rho0 X) : X = .genesis := by
      rcases hX with hX | ⟨v, _, o, t, N, he, _, _⟩
      · exact hg hX
      · exact (noEmission0 v o t he).elim
    intro A D hA hD _
    exact (scopeX hA).trans (scopeX hD).symm
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun _ => rfl⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun i : Fin 1 => i)
      exact Function.bijective_id
    · exact hℓ.elim
    · exact hℓ.elim
  restartsAtWakes := by
    intro v t he
    have he : V2.Event.restart v t = .tick 0 0 := List.mem_singleton.mp he
    cases he
  delta := rfl


private theorem fault0 : (Gen.V2.Duty.faulty rho0).card ≤ (p1.n - 1) / 3 := by decide +kernel

-- Non-vacuity of every premise of the stronger, phase-free lock theorem.
-- The source is the in-band genesis block at an actual honest post-clock read.
example : ∃ nd : Node p1,
    Base₂ p1 unitCodec env0 rho0 ∧
    (Gen.V2.Duty.faulty rho0).card ≤ (p1.n - 1) / 3 ∧
    (0 : Fin 1) ∈ rho0.honest ∧ postClock env0 rho0 0 0 = some nd ∧
    FGBlock.genesis ∈ FGSA.fullTree p1 nd.st ∧
    (FGSA.controls p1 nd.st).lo ≤ (heightView p1 FGBlock.genesis).h := by
  refine ⟨(fgsa p1 unitCodec).clock (V2.D.Run.stateBefore env0 rho0 0 0) 0,
    base0, fault0, by decide, rfl, ?_, ?_⟩ <;> decide +kernel

example :
    let nd := (fgsa p1 unitCodec).clock (V2.D.Run.stateBefore env0 rho0 0 0) 0
    own_lock nd.record.toRecord ((heightView p1 FGBlock.genesis).h)
        (finality_pair nd.record.toRecord (fgInputs p1 nd.st).2) = none ∨
      own_lock nd.record.toRecord ((heightView p1 FGBlock.genesis).h)
        (finality_pair nd.record.toRecord (fgInputs p1 nd.st).2) =
          some (heightView p1 FGBlock.genesis).T_h.root :=
  rowPermission_own_lock env0 rho0 base0 fault0 0 (by decide) 0 _ rfl .genesis
    (by decide +kernel) (by decide +kernel)

private def b1 : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨1⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def b2 : FGBlock (Fin 1) :=
  .node b1 2 ⟨2⟩ 0 [⟨0, .vote 2 b1.root false, none⟩]
private def b1alt : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨3⟩ 1 [⟨0, .vote 1 genesisRoot false, none⟩]
private def b2alt : FGBlock (Fin 1) :=
  .node b1alt 6 ⟨4⟩ 0 [⟨0, .vote 2 b1alt.root true, none⟩]

-- Local client computations for the four IF.3(b) cases. They use W head fields.
-- Frontier case c=m=2: the head's justification is below the source height.
example : hOf p1.E p1.cfg b1 = 2 ∧
    namedEntry (height_pair Record.initial (some (2, b1.root))
      (finality_pair Record.initial (Window.headFields p1 p1.K_W b1))) = some (2, b1.root) := by
  decide +kernel

-- Gap case c=m-1=2: a height-3 progress carrier has no top justification at 2.
example : hOf p1.E p1.cfg b2alt = 3 ∧ (heightView p1 b2alt).h_j = 1 ∧
    namedEntry (height_pair Record.initial (some (2, b1alt.root))
      (finality_pair Record.initial (Window.headFields p1 p1.K_W b2alt))) =
        some (2, b1alt.root) := by
  decide +kernel

-- Top-J case c=m-1=2: the provisional lock and the source entry match.
example : (heightView p1 b2).h_j = 2 ∧ (heightView p1 b2).J = b1 ∧
    namedEntry (height_pair Record.initial (some (2, b1.root))
      (finality_pair Record.initial (Window.headFields p1 p1.K_W b2))) = some (2, b1.root) := by
  decide +kernel

-- Contest case c=m=3: a conflicting top-J lock at 2 does not block height 3.
example : ¬ FGBlock.Preceq b1 b2alt ∧ hOf p1.E p1.cfg b2alt = 3 ∧
    namedEntry (height_pair Record.initial (some (3, b2alt.root))
      (finality_pair Record.initial (Window.headFields p1 p1.K_W b2))) = some (3, b2alt.root) := by
  decide +kernel

-- A nonempty computed pair does not imply a fresh emission on a repeated source.
example :
    let hd := Window.headFields p1 p1.K_W b1
    let step := createRowOnce p1.E p1.cfg RecordOnce.initial 0 (some b1) hd
    step.1.isSome = true ∧
      namedEntry (height_pair step.2.toRecord (some (2, b1.root))
        (finality_pair step.2.toRecord hd)) = some (2, b1.root) ∧
      (createRowOnce p1.E p1.cfg step.2 0 (some b1) hd).1 = none := by
  decide +kernel

end AvailableChain.FGSA.Run.Tests.RowPermission
