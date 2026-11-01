module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService -- shake: keep (example tests)

set_option linter.privateModule false

section
namespace AvailableChain.FGSA.Run.Tests.RowService
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- A pre-GST send is held by GST + ΔF in the receiver epoch after GST.
example (ΔF : Time) (hΔ : E.Δ = p.Δ) (hv : V2.D.ExecutionValid E rho)
    (hEpoch : ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1))
    (hs : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) {j r : Nat} {y x : V} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a) (hpre : p.actionTime r < E.t_GST)
    (hhor : E.t_GST + ΔF ≤ rho.horizon) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (E.t_GST + ΔF) := by
  have hmax : max (p.actionTime r) E.t_GST = E.t_GST := max_eq_right (le_of_lt hpre)
  simpa only [hmax] using
    fgsa_rowService_receipt_sleep p c E rho ΔF hΔ hv hEpoch hs hΔF hAwake ha
    (hmax.symm ▸ hhor) x hx

-- The strict deadline read excludes an event at exactly the deadline.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro h
  have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp h
  exact (lt_irrefl d) ht

-- Carriage requires R6 and only one post-GST row delay, including equality.
example (ΔF : Time) (hs : TRowsSync p c E rho ΔF) {j r s : Nat} {y : V}
    {a : RowWire p.n} {Q : Block} {rows : List (RowWire p.n)}
    (ha : HonestRowAt p c E rho j y r a) (hg : E.t_GST ≤ p.actionTime r)
    (hc : HonestCarrier p c E rho s Q rows) (hv : ValidForParent p c E rho s Q a)
    (ht : p.actionTime r + ΔF = SA.proposalTime p.toParams s) :
    a ∈ rows ∨ onParentChain p c E rho s Q a :=
  (hs j y r a ha hg).2 s Q rows hc hv (le_of_eq ht)

-- Exact parent-chain content is excluded by R7.
example (st : State p.n) (s : Slot) (H : Block) (a : RowWire p.n)
    (ha : a ∈ chainWireRows st H) : a ∉ proposalRowsFor p st s H := by
  intro h
  exact ((mem_proposalRowsFor_iff p st s H a).mp h).choose_spec.2.2.2 ha

-- Earlier-or-current height witnesses retain the explicit fresh-arm match.
example [Fintype V] (ΔF : Time) (k : RowKind) (q y : Nat) (U X : FGBlock (Fin p.n))
    (hb : BatchPrem p c E rho ΔF k q y U X)
    (hh : (derive p.E p.cfg X.parent).h = y) : CoveredByChild p k X U y :=
  fgsa_batchCoverage p ΔF k c E rho q y U X hb (by
    simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
      using hh)

end AvailableChain.FGSA.Run.Tests.RowService
end
