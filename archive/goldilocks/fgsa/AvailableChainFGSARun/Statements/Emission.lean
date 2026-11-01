module
public import AvailableChainFGSARun.Model.Families -- shake: keep (re-export)

@[expose] public section
namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Every pool row and every row in a stored proposal passes the row check. -/
def EmissionRowsValid {p : Params} (st : State p.n) : Prop :=
  (∀ a ∈ st.rowPool, a.valid = true) ∧
    ∀ w ∈ st.proposals, ∀ s N,
      w.decode = some (.block s N) → ∀ a ∈ N.rows, a.valid = true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Decode the application value of a block. -/
def decode {In : Type} (c : AppCodec In) (b : Block) : Option In :=
  c.unapp (appOf b.body)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The wire check holds for every object released by an honest awake node. -/
def HonestEmissionWellFormed (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ i v t, rho.events[i]? = some (.tick v t) → v ∈ rho.honest →
    E.awake v t = true → ∀ o ∈ V2.D.Run.emitsAt E rho i, (fgsa p c).wellFormed o = true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Each released proposal decodes to its proposer's input at that tick. -/
def HonestProposalDecodes (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ i v s, rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s)) →
    0 < s → v = rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ →
    E.awake v (SA.proposalTime p.toParams s) = true →
    ∀ N,
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho i → decode c N.erase = some (rho.input v (SA.proposalTime
          p.toParams s))

/-- [ROOT-DIGEST-2 W1; DC goldfish_vote] Observe the actual selected sender body. -/
def HeadTargetAtEmission (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (o : Obj p) (t : Time) (H : Block) : Prop :=
  ∃ i s j, rho.events[i]? = some (.tick x t) ∧ o ∈ V2.D.Run.emitsAt E rho i ∧
    o = ofHead p ⟨.seat (.head s) j, H.root⟩ ∧
    H = headVote p (clock p (V2.D.Run.stateBefore E rho i x).st t) s

end AvailableChain.FGSA.Run
end
