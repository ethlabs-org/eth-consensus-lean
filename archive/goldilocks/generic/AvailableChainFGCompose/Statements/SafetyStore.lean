module
public import AvailableChainFGCompose.Statements.SafetyReads
public import AvailableChainKitFG.StoreSafetyDef

@[expose] public section

/-! PROVISIONAL safety contracts. S1 does not freeze these laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

structure FGSafetyWireLaws (S : FGSafetyReads P n Wire) : Prop where
  encode_injective : Function.Injective S.encode
  decode_encode : ∀ a, S.decodeObject (S.encode a) = S.decode a
  decode_auth : ∀ a u, S.decode a = some u →
    (S.encode a).auth = .seat S.fgLabel (S.fgSeats u.signer)
  decoded_visible : ∀ o u, S.decodeObject o = some u →
    P.objSelfVisible o = true
  carried : ∀ o a, a ∈ S.proposalRows o → P.carries o (S.encode a)

structure FGSafetyStoreLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (H : FGHeightView (Fin n))
    (f : FGFinalityView (Fin n)) (Good : P.State → Prop) : Prop where
  initial_good : Good P.init
  clock_good : ∀ nd t, Good nd → Good (P.clock nd t)
  process_good : ∀ nd o, Good nd → Good (P.process nd o)
  own_good : ∀ nd o, Good nd → Good (P.recordOwn nd o)
  restart_good : ∀ nd t, Good nd → Good (P.restore (P.durable nd) t)
  invariant : ∀ nd, Good nd → FGStoreInvariant H f (R.core nd).fg
  initial_tf : ∀ B ∈ (R.core P.init).fg.TF, B = .genesis
  restart_tf : ∀ nd t B, Good nd →
    B ∈ (R.core (P.restore (P.durable nd) t)).fg.TF → B ∈ (R.core nd).fg.TF
  process_new : ∀ nd o B, Good nd →
    B ∈ (R.core (P.process nd o)).fg.TF → B ∉ (R.core nd).fg.TF →
    S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode

structure FGSafetyRestartLaws {In : Type} {P : V2.ProtocolSpecD In}
    {n : Nat} {Base Proposal Wire : Type}
    (R : FGCoreReads P n Base Proposal Wire) : Prop where
  restart_F : ∀ nd t, (R.core (P.restore (P.durable nd) t)).fg.F = (R.core nd).fg.F

structure FGSafetyOrderLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) : Prop where
  process_F : ∀ nd o,
    FGBlock.Preceq (R.core nd).fg.F (R.core (P.process nd o)).fg.F
  erase_prefix : ∀ A B, FGBlock.Preceq A B →
    Block.Preceq (R.erase A) (R.erase B)
  output_eq : ∀ nd, S.finalizedOut nd = R.erase (R.core nd).fg.F
structure FGSafetyScopeLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (E : Generic.Env V)
    (rho : V2.D.Run V P) (Q : Block → Prop) : Prop where
  genesis_scope : ∀ x, x ∈ rho.honest → Q (R.erase .genesis)
  delivered_scope : ∀ x o t b, V2.Event.deliver x o t ∈ rho.events →
    S.proposalErase o = some b → Q b
  parent_scope : ∀ K, safetyRunBlock R S E rho K →
    K.parent ≠ .genesis → Q (R.erase K.parent)

def safetyScopedRoots (Q : Block → Prop) : Prop :=
  ∀ K W, Q (R.erase K) → Q (R.erase W) → RootInjectiveOn K W

theorem safetyScopedRoots_def (Q : Block → Prop) :
    safetyScopedRoots R Q =
      (∀ K W, Q (R.erase K) → Q (R.erase W) → RootInjectiveOn K W) := rfl

end AvailableChain.FGCompose
end
