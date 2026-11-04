module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Spec.Model.Conditions

@[expose] public section

/-! # The model as a system of the consensus problem (L1)

`sysOf O F V` is the `Consensus.System` of family `F` (with output schema `O`)
and validators `V`: its schema is `O`; its runs
are pairs of an environment and a run in it; valid runs are valid executions;
reads are the protocol's output ledgers at event cuts; the communication log is
the run's log (`Run.log`: engine releases, deliveries and inboxes) with every
object tagged with the environment (`sysOf_log_faithful`); evidence is objects
seen; conviction is slashability under the protocol's rule; the excuse is an
observed hash collision. All are definitions: the model fixes the meaning of
every field that the problem layer leaves abstract.

Evidence is generic: a validator is slashable on a set of objects if two of
them (possibly the same one) are signed by its key (through the run's PKI) and
the protocol's rule `conflicts` convicts them.

The hash is arbitrary run data. `HashCollision`: two distinct observed items
with one digest. No digest is reserved: a root (such as a genesis block) is an
explicit constructor of the protocol's parent references, not a digest. An
item is observed if it occurs in an object that an honest node released or
received, at any depth, under any signature; this is exactly the set of items
whose digests the engine passes to honest code. Honest code still chooses what
it signs, so collision resistance is an assumption about the deployed hash, not
a theorem. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Run

variable {O : OutputSchema} {F : ProtocolFamily O} {E : Env V} (rho : Run F E)

/-- `x` is slashable on the objects `A`. -/
def Slashable (A : Set (protoOf F E).Object) (x : V) : Prop :=
  ∃ o ∈ A, ∃ o' ∈ A, rho.signerOf o = some x ∧ rho.signerOf o' = some x ∧
    (protoOf F E).conflicts o o' = true

/-- An item is observed: it is said by an object the honest nodes saw. -/
def ObservedItem (x : (protoOf F E).Item) : Prop :=
  ∃ o ∈ rho.Observed, o.item? = some x

/-- A hash collision was observed: two distinct observed items with one
digest. -/
def HashCollision : Prop :=
  ∃ x y, x ≠ y ∧ rho.ObservedItem x ∧ rho.ObservedItem y ∧ rho.hash x = rho.hash y

end Run

/-- A log over the objects of environment `E`, each tagged with `E`; a tagged
object is a row exactly when it is a row of `L`. -/
def tagLog {M : Env V → Type} (E : Env V) (L : CommLog V (M E)) : CommLog V (Σ E, M E) :=
  ⟨fun v m t => ∃ o, m = ⟨E, o⟩ ∧ L.sent v o t, fun v m t => ∃ o, m = ⟨E, o⟩ ∧ L.recv v o t,
    L.inbox, fun m => ∃ o, m = ⟨E, o⟩ ∧ L.row o⟩

/-- The system of family `F`. Reducible by unfolding: `(sysOf O F V).schema`
is `O` by definition. -/
def sysOf (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V] [DecidableEq V] :
    Consensus.System V where
  schema := O
  Run := Σ E : Env V, Run F E
  trace r := ⟨r.2.point, r.2.events.length, r.2.cutTime, r.2.readIdx⟩
  Valid r := r.2.ExecutionValid
  Obs := Σ E : Env V, (protoOf F E).Object
  log r := tagLog r.1 r.2.log
  view r v i := {o | ∃ o' ∈ r.2.ViewIdx v i, o = ⟨r.1, o'⟩}
  convicts r A x := r.2.Slashable {o' | ⟨r.1, o'⟩ ∈ A} x
  Excuse r := r.2.HashCollision

/-- The external data of a compiled run: its PKI and its selection, fixed
before execution; admissible = the protocol's selection spec. Progress
requirements of a shape read only these and the environment point. -/
def sysExternal (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V] [DecidableEq V] :
    External (sysOf O F V) where
  Ext E := (Fin (Fintype.card V) ≃ V) × ((protoOf F E).Role → Finset (Fin (Fintype.card V)))
  ext r := (r.2.key, r.2.sel)
  Admits E e := (protoOf F E).SelAdmits e.2

end Consensus.Model

end
