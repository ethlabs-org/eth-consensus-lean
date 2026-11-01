module
public import AvailableChainFGSARun.Model.Families -- shake: keep (re-export)
public import AvailableChainSimplexFG.Evidence

@[expose] public section
namespace AvailableChain.FGSA.Run
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)

/-- The node releases this signed row at an actual tick event. -/
def EmitsRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (x : V)
    (a : RowWire p.n) : Prop :=
  ∃ k t, rho.events[k]? = some (.tick x t) ∧ ofRow p a ∈ V2.D.Run.emitsAt E rho k

/-- Any two decoded rows emitted by this node are not slashable. -/
def EmittedRowsNoSlash (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (x : V) : Prop :=
  ∀ a a', EmitsRow p c E rho x a → EmitsRow p c E rho x a' →
    ∀ u v, RowWire.toRow? a = some u → RowWire.toRow? a' = some v →
      ¬ SimplexFG.Slashable u v

/-- Decode a run object as a signed row through the store wire adapter. -/
def decodeRowObject (o : Obj p) : Option (SimplexFG.Row (Fin p.n)) :=
  match (toWire p o).payload with
  | .row body => RowWire.toRow? ⟨(toWire p o).auth, body⟩
  | _ => none

/-- An awake FG action, with its event index, time, round and client input.
The event index distinguishes repeated times and equal input bodies. -/
def fgClientEvent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (x : V) (k : Nat) :
    Option (Nat × Time × Nat ×
      (Option (SimplexFG.FGBlock (Fin p.n)) × SimplexFG.HeadFields)) :=
  match rho.events[k]? with
  | some (.tick v t) =>
      let r := (p.slotOf t - 1) / p.R
      if v = x ∧ E.awake v t = true ∧ p.actionTime r = t then
        some (k, t, r, fgInputs p (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st t))
      else none
  | _ => none

/-- Awake FG actions before `i`, in event order, including actions after restart. -/
def fgClientEvents (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (x : V) (i : Nat) :=
  (List.range i).filterMap (fgClientEvent p c E rho x)

end AvailableChain.FGSA.Run
end
