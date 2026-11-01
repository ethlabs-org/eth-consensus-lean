module
public import AvailableChainPCSAClaims.Statements.FinalityApi
public import AvailableChainPCSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Duty.Slashing
public import AvailableChainSimplexFG.Evidence

@[expose] public section

/-! [PC-SA claims, W0; FG-SA Run/Statements/Slashing.lean, Run/Statements/
Client.lean, Claims/Statements/Channels.lean, ChannelProps.lean; port over
`pcsa` runs] The slashing observation reads of the finality safety claims:
the slashing interface (evidence = the rows on stored FG chains), the rows a
node emits, and the carriage of finality rows. The reads are pure FG
(pcsa34-r4 5.8.2: UNCHANGED rows); they name no FG-SA object. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA claims, W0; FG-SA fgsaSlashing; DC Protocol/Evidence.lean
store_attestations] The slashing interface of PC-SA. Validators are the
fixed FG seats (`V = Fin p.n`); the evidence of a read is the row set of its
stored FG chains (`pcFinalityRows`); `v` is slashed when two honest or faulty
reads hold rows of one FG seat held by `v` that are slashable between them. -/
def pcsaSlashing (p : Params) {In : Type} (c : AppCodec In) {m : FGMode}
    (E : Generic.Env (Fin p.n)) :
    Gen.V2.Duty.SlashingInterface (V := Fin p.n) (pcsaWith m p c) where
  toInterface := (pcsaInterface p c (m := m)).toInterface
  finalized := pcsaFinalizedOut
  slashes rho v := ∃ (u u' : Fin p.n) (t t' : Time) (i : Fin p.n),
    SlashableBetween
      (pcFinalityRows p (V2.D.Run.readAt E rho t u).st)
      (pcFinalityRows p (V2.D.Run.readAt E rho t' u').st) i ∧
    rho.seatOf (.base .fg) i = v

theorem pcsa_pcsaSlashing_slashes_def (p : Params) {In : Type} (c : AppCodec In)
    {m : FGMode} (E : Generic.Env (Fin p.n)) (rho : V2.D.Run (Fin p.n) (pcsaWith m p c))
    (v : Fin p.n) :
    (pcsaSlashing p c E).slashes rho v =
      (∃ (u u' : Fin p.n) (t t' : Time) (i : Fin p.n),
        SlashableBetween
          (pcFinalityRows p (V2.D.Run.readAt E rho t u).st)
          (pcFinalityRows p (V2.D.Run.readAt E rho t' u').st) i ∧
        rho.seatOf (.base .fg) i = v) := rfl

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA claims, W0; FG-SA EmitsRow] Node `x` releases the signed row `a`
at a tick event. -/
def PCEmitsRow (x : V) (a : RowWire p.n) : Prop :=
  ∃ k t, rho.events[k]? = some (.tick x t) ∧ ofRow p a ∈ V2.D.Run.emitsAt E rho k

theorem pcsa_PCEmitsRow_def (x : V) (a : RowWire p.n) :
    PCEmitsRow p c E rho x a =
      (∃ k t, rho.events[k]? = some (.tick x t) ∧ ofRow p a ∈ V2.D.Run.emitsAt E rho k) := rfl

/-- [PC-SA claims, W0; FG-SA EmittedRowsNoSlash] No two decoded rows that
node `x` emits are slashable. -/
def PCEmittedRowsNoSlash (x : V) : Prop :=
  ∀ a a', PCEmitsRow p c E rho x a → PCEmitsRow p c E rho x a' →
    ∀ u v, RowWire.toRow? a = some u → RowWire.toRow? a' = some v → ¬ Slashable u v

theorem pcsa_PCEmittedRowsNoSlash_def (x : V) :
    PCEmittedRowsNoSlash p c E rho x =
      (∀ a a', PCEmitsRow p c E rho x a → PCEmitsRow p c E rho x a' →
        ∀ u v, RowWire.toRow? a = some u → RowWire.toRow? a' = some v →
          ¬ Slashable u v) := rfl

omit [DecidableEq V] in
/-- [PC-SA claims, W0; FG-SA RowSigner] The FG seat of the signed row `a`
belongs to `x`. -/
def PCRowSigner (a : RowWire p.n) (x : V) : Prop :=
  ∃ i, a.auth = .seat .fg i ∧ rho.seatOf (.base .fg) i = x

omit [DecidableEq V] in
theorem pcsa_PCRowSigner_def (a : RowWire p.n) (x : V) :
    PCRowSigner p c rho a x = (∃ i, a.auth = .seat .fg i ∧ rho.seatOf (.base .fg) i = x) :=
  rfl

/-- [PC-SA claims, W0; FG-SA HonestRowAt] The honest node `y` emits the
signed row `a` at the action `a_r` of round `r`, at event `j`. -/
def PCHonestRowAt (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) : Prop :=
  y ∈ rho.honest ∧ rho.events[j]? = some (.tick y (p.actionTime r)) ∧
    ofRow p a ∈ V2.D.Run.emitsAt E rho j

theorem pcsa_PCHonestRowAt_def (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    PCHonestRowAt p c E rho j y r a =
      (y ∈ rho.honest ∧ rho.events[j]? = some (.tick y (p.actionTime r)) ∧
        ofRow p a ∈ V2.D.Run.emitsAt E rho j) := rfl

/-- [PC-SA claims, W0; FG-SA FinalityRowCarriage] Every row of `A` has a
signed wire on its signer's FG seat, and when that seat belongs to an honest
node, the node emitted the wire at an FG action. -/
def PCFinalityRowCarriage (A : Finset (Row (Fin p.n))) : Prop :=
  ∀ u ∈ A, ∃ a : RowWire p.n,
    a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
    ∀ z : V, PCRowSigner p c rho a z → z ∈ rho.honest →
      ∃ j r, PCHonestRowAt p c E rho j z r a

theorem pcsa_PCFinalityRowCarriage_def (A : Finset (Row (Fin p.n))) :
    PCFinalityRowCarriage p c E rho A =
      (∀ u ∈ A, ∃ a : RowWire p.n,
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∀ z : V, PCRowSigner p c rho a z → z ∈ rho.honest →
          ∃ j r, PCHonestRowAt p c E rho j z r a) := rfl

end AvailableChain.PCSA.Run

end
