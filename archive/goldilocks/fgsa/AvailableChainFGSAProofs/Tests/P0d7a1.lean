module
public import AvailableChainFGSAProofs.Proofs.Finality.History
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0d7a1
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
variable (horigin : ∀ i x B, HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
    ∃ (a : RowWire p.n) (r : Nat), a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
      ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho a z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

include horigin in
private theorem d7f_prebatch (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : PreBatchPrem p c E rho q y U X) : NoMixedOnPath p X y :=
  noMixedPreBatchParent p c E rho horigin q y U X h

include horigin in
private theorem d7f_fresh (q y : Nat) (U X : FGBlock (Fin p.n)) (hX : X ≠ .genesis)
    (hentry : EntryAt p U y) (hpath : FGBlock.Preceq U X.parent)
    (hcover : (heightView p X.parent).h = y → CoveredByChild p .target X U y)
    (hnomix : NoMixedOnPath p X y) (h : FreshPrem p c E rho q y X) :
    (heightView p X).h = y + 1 ∧ (heightView p X).J = U ∧
      (heightView p X).h_j = y ∧ (Window.derive p p.K_W X).h_F < y ∧
      Window.RetainedW p X y U :=
  justifyFresh_W p c E rho horigin q y U X hX hentry hpath hcover hnomix h

-- The d6a cap uses the actual emission tick and its actual source producer.
omit [Fintype V] in
private theorem d7f_reset_row_cap (hs : V2.D.ScheduleWellFormed E rho)
    {j r h : Nat} {z : V} {a : RowWire p.n} {e : BlockId}
    (ha : HonestRowAt p c E rho j z r a)
    (he : namedEntry a.payload.height_pair = some (h, e)) :
    h ≤ honestFrontier p c E rho (p.actionTime r) :=
  reset_row_cap p c E rho hs (emittedName_window p c E rho hs)
    ha ha.2.1 le_rfl he

#print axioms d7f_reset_row_cap
#print axioms d7f_prebatch
#print axioms d7f_fresh
#print axioms AvailableChain.FGSA.Run.noMixedPreBatchParent
#print axioms AvailableChain.FGSA.Run.justifyFresh_W
#print axioms AvailableChain.FGSA.Run.raw_causal_cap_before
#print axioms AvailableChain.FGSA.Run.raw_causal_cap_at_tick
#print axioms AvailableChain.FGSA.Run.raw_causal_cap_through_action

end AvailableChain.FGSA.Run.Tests.P0d7a1
end
