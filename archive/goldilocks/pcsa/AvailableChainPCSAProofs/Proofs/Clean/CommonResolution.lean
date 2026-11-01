module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody

public section

/-! C6 common root resolution at indexed run reads. -/
namespace AvailableChain.PCSA
variable {n : Nat}

private theorem pcsa_head_resolved_root (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (r : BlockId) (B : Block)
    (ht : GridCO.headTarget? o = some r) (hb : GridCO.resolvedHead? v o = some B) : B.root = r := by
  delta GridCO.resolvedHead? at hb
  rw [ht] at hb
  change ((GridCO.resolveTarget .root (GridCO.resolutionTree v) r).bind fun C =>
    if C ∈ v.blocks then some C else none) = some B at hb
  cases hr : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
  | none => rw [hr] at hb; cases hb
  | some C =>
    rw [hr] at hb
    change (if C ∈ v.blocks then some C else none) = some B at hb
    split at hb
    · cases hb
      exact Block.findByRoot?_root hr
    · contradiction
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- One signed HEAD resolves to the same body at two honest run reads. -/
theorem pcsa_run_common_head_resolution (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (i j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (t u : Time) (o : GridCO.Wire p.n .root) (A B : Block)
    (hA : GridCO.resolvedHead?
      (actView (clock p (V2.D.Run.stateBefore E rho i x).st t)) o = some A)
    (hB : GridCO.resolvedHead?
      (actView (clock p (V2.D.Run.stateBefore E rho j y).st u)) o = some B) :
    A = B := by
  have ha := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hA)).1
  have hb := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hB)).1
  have hAs := pcsa_clock_body_scope p (RootBlockInRun p c E rho) _ t
    (pcsa_body_scope E rho i x hx) A ha
  have hBs := pcsa_clock_body_scope p (RootBlockInRun p c E rho) _ u
    (pcsa_body_scope E rho j y hy) B hb
  cases ht : GridCO.headTarget? o with
  | none =>
    delta GridCO.resolvedHead? at hA
    rw [ht] at hA
    cases hA
  | some r =>
    have har := pcsa_head_resolved_root _ o r A ht hA
    have hbr := pcsa_head_resolved_root _ o r B ht hB
    exact pcsa_scoped_root_eq E rho h.idealization A B hAs hBs (har.trans hbr.symm)
end AvailableChain.PCSA.Run
end
