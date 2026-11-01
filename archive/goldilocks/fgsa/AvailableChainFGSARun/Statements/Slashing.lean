module
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Duty.Slashing
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- DC `DecoupledConsensusModel/Protocol/Evidence.lean:67–68` defines
`store_attestations st := st.T.biUnion chain_attestations`: the rows carried
in stored block chains. This accessor uses the same set in FG-SA:
`nd.st.fg.TF` is the cumulative admitted tree, and `chainRows` reads its rows.
TS `spec/fgsa-protocol.tex:493–500` maps that tree to DC's `Σ.T`.
The row pool (`Σ.attestations`, spec:573–580) is not part of this set.
FG blocks already carry decoded `SimplexFG.Row` values; this accessor has no
wire decoder and drops no stored row. FG-SA admission decodes signed rows
with `RowWire.toRow?`; a wire that fails to decode is not an FG row.
DC carries `CombinedAttestation` values; FG-SA carries FG rows only. -/
def fgsaEvidence {p : Params} (nd : Node p) : Finset (SimplexFG.Row (Fin p.n)) :=
  nd.st.fg.TF.biUnion SimplexFG.chainRows

/-- Slashable evidence belongs to the validator that holds its fixed FG
seat. The evidence domain is the rows on stored block chains. `Linked`
supplies a bijection when a theorem needs to express the seat as `e.symm v`. -/
def fgsaSlashing (p : Params) {In : Type} (c : AppCodec In)
    (E : Generic.Env (Fin p.n)) : Gen.V2.Duty.SlashingInterface (V := Fin p.n) (fgsa p c) where
  toInterface := fgsaInterface p c
  finalized := finalizedOut
  slashes rho v := ∃ (u u' : Fin p.n) (t t' : Time) (i : Fin p.n),
    SimplexFG.SlashableBetween
      (fgsaEvidence (V2.D.Run.readAt E rho t u))
      (fgsaEvidence (V2.D.Run.readAt E rho t' u')) i ∧
    rho.seatOf (.base .fg) i = v

end AvailableChain.FGSA.Run
