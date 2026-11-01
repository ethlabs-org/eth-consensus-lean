module
public import AvailableChainFGCompose.Statements.Channels

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming)
variable (entry : Wire → Option (Height × BlockId))
variable (storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)

variable (SourceService : V → Nat → (FGBlock (Fin n)) → Prop)

def RXing : Prop := ∀ i i' x y K W,
  x ∈ rho.honest → i ≤ i' →
  K ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
  (O.finality K).F = (R.core (V2.D.Run.stateBefore E rho i x)).fg.F →
  HeldAt R E rho i' y W → (O.finality K).h_F < (O.height W).h →
  FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F W

def RCap : Prop := ∀ y i x W,
  HeldAt R E rho i x W → y + 2 ≤ (O.height W).h →
  ∃ j z r, ∃ (a : Wire) (e : BlockId), j < i ∧
    HonestRowAt S E rho T j z r a ∧ entry a = some (y + 1, e) ∧
    a ∈ chainWireRows (V2.D.Run.stateBefore E rho i x) (R.erase W)

def RStrat : Prop := ∀ i x W, x ∈ rho.honest →
  W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
  ∀ e ∈ certified R O W, e ≠ .genesis →
    ∃ y r, ∃ a : Wire, HonestRowBefore S E rho T i y r a ∧
      entry a = some ((O.height e).h, e.root)

def RQCOrigin (Ef : Electorate (Fin n)) : Prop :=
  ∀ i x W, x ∈ rho.honest →
  W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
  let origin := fun (carrier : (FGBlock (Fin n))) (a : Row (Fin n)) =>
    ∃ y r, ∃ wire : Wire, HonestRowBefore S E rho T i y r wire ∧ S.decode wire = some a ∧
      storedCarrier (V2.D.Run.stateBefore E rho i x) carrier wire ∧
      ∃ C, actionSourceFG R E rho T y r = some (some C) ∧
        namedEntry a.height_pair = some ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C ∧ SourceService y r C
  (∀ m X (Q : Finset (Fin n)) (rows : Fin n → (FGBlock (Fin n)) × Row (Fin n)),
    1 ≤ m → m < (O.height W).h → FGBlock.Preceq X W →
    (O.height X).h = m → Ef.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧ (rows k).2.height_pair.matchesEntry m X.root = true) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  (∀ (Q : Finset (Fin n)) (rows : Fin n → (FGBlock (Fin n)) × Row (Fin n)),
    (O.height W).h_j ≠ 0 → Ef.IsQuorum Q →
    (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
      (rows k).2.signer = k ∧
      (rows k).2.height_pair = .vote (O.height W).h_j (O.height W).J.root false) →
    ∃ k ∈ Q, origin (rows k).1 (rows k).2) ∧
  ((O.finality W).F ≠ .genesis →
    ∃ C, FGBlock.Preceq C W ∧ (O.height C).J = (O.finality W).F ∧
      (O.height C).h_j = (O.finality W).h_F ∧
      ∃ (Q : Finset (Fin n)) (rows : Fin n → (FGBlock (Fin n)) × Row (Fin n)),
        Ef.IsQuorum Q ∧
        (∀ k ∈ Q, FGBlock.Preceq (rows k).1 C ∧ (rows k).2 ∈ (rows k).1.rows ∧
          (rows k).2.signer = k ∧
          (rows k).2.height_pair = .vote (O.height C).h_j (O.height C).J.root false) ∧
        ∃ k ∈ Q, origin (rows k).1 (rows k).2)

end AvailableChain.FGCompose
end
