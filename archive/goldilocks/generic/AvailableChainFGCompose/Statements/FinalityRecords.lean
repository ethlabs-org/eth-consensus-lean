module
public import AvailableChainFGCompose.Statements.FinalityHistory
public import AvailableChainFGCompose.Statements.RowPermission -- shake: keep (checkpoint API)
public import AvailableChainFGCompose.Statements.Service -- shake: keep (checkpoint API)
public import AvailableChainFGCompose.Statements.ChannelLaws -- shake: keep (checkpoint API)
public import AvailableChainKitFG.ProvenanceCoreDef

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- One representative for the whole run, including selections before service starts. -/
noncomputable def highRecordEntry (y : Nat) : BlockId := by
  classical
  exact if h : ∃ x r C, x ∈ rho.honest ∧
      actionSourceFG R E rho T x r = some (some C) ∧ (O.height C).h = y
    then (O.height (Classical.choose (Classical.choose_spec
      (Classical.choose_spec h)))).T_h.root else genesisRoot

/-- The guards and the sent-row invariant use the same representative. -/
def HighRecordInvariant (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce) : Prop :=
  ∀ y, M + 1 ≤ y →
    (Λ.target y = none ∨ Λ.target y = some (entry y)) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some (entry y)) ∧
    ∀ b ∈ Λ.sent, ∀ U timeout, b.1 = .vote y U timeout → U = entry y ∧ timeout = false

/-- Freshness includes the durable send-once record. -/
def HighRecordFresh (y : Nat) (Λ : RecordOnce) : Prop :=
  Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
    ∀ b ∈ Λ.sent, ∀ U timeout, b.1 ≠ .vote y U timeout

/-- The three record fields used by the middle and row consumers. -/
abbrev HighRecordGuard_W (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) : Prop :=
  (Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some U.root)

/-- Every actual named row names its actual source at the same action read. -/
def HighRecordNames (D : FGHistoryWireReads S) : Prop :=
  ∀ j x r a e, HonestRowAt S E rho T j x r a →
    namedEntry (D.heightPair a) = some e →
    ∃ C, actionSourceFG R E rho T x r = some (some C) ∧
      e = ((O.height C).h, (O.height C).T_h.root)

/-- Exact client output at an honest emission, with its full decoded row. -/
def HighRecordEmission (Ef : Electorate (Fin n)) (cfg : FGConfig) : Prop :=
  ∀ j x r a u, HonestRowAt S E rho T j x r a → S.decode a = some u →
    (createRowOnce Ef cfg (S.record (V2.D.Run.stateBefore E rho j x)) u.signer
      (S.inputs (P.clock (V2.D.Run.stateBefore E rho j x) (T.action r))).1
      (S.inputs (P.clock (V2.D.Run.stateBefore E rho j x) (T.action r))).2).1 = some u

/-- An actual own write retains its node, event, wire, and decoded content. -/
def HighRecordOwnOrigin : Prop :=
  ∀ j x o u, x ∈ rho.honest →
    o ∈ (if (rho.events[j]?).map V2.Event.node = some x then
      (V2.D.Run.emitsAt E rho j).filter P.objSelfVisible else []) →
    S.decodeObject o = some u →
    ∃ r a, HonestRowAt S E rho T j x r a ∧ S.decode a = some u

/-- The client head fields come from a held head, or from the exact empty-head read. -/
def HighRecordHead : Prop :=
  ∀ i x t, x ∈ rho.honest →
    (S.inputs (P.clock (V2.D.Run.stateBefore E rho i x) t)).2 = ⟨0, genesisRoot, 0⟩ ∨
    ∃ K, K ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF ∧
      (S.inputs (P.clock (V2.D.Run.stateBefore E rho i x) t)).2 =
        certificateHeadFields O.height O.finality K

/-- The shield bounds actual signed rows strictly before its cutoff, of either sign. -/
def HighRecordShieldRows (D : FGHistoryWireReads S) (X : FGBlock (Fin n))
    (b : Nat) (cutoff : Time) : Prop :=
  ∀ j x r a y U timeout, HonestRowAt S E rho T j x r a → T.action r < cutoff →
    D.heightPair a = .vote y U timeout →
    y ≤ b ∧ (y = b → U = (O.height X).T_h.root)

/-- Explicit seed leaves. The shield cutoff can precede the service start. -/
def HighRecordSeedLeaves (D : FGHistoryWireReads S) (pt : FGServicePoint)
    (X : FGBlock (Fin n)) (b : Nat) (cutoff : Time) : Prop :=
  R.erase X = pt.seed ∧ (O.height X).h = b ∧ pt.reset.M + 1 ≤ b ∧
    cutoff ≤ pt.serviceStart ∧ HighRecordShieldRows R S O T E rho D X b cutoff

end AvailableChain.FGCompose
end
