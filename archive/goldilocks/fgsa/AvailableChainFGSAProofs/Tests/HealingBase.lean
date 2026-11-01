module
public import AvailableChainFGSAProofs.Proofs.Healing.Base -- shake: keep (boundary tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Cap -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (fault bound)

set_option linter.privateModule false

section
namespace AvailableChain.FGSA.Run.Tests.HealingBase
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The existing foundation producers discharge the lane arguments under HealingSet.
example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF) : RXing p c E rho :=
  healing_rXing p c E rho h (fgsa_apiFinalLockClaim_body p c E rho ())

example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF) : RCap p c E rho := by
  apply healing_rCap p c E rho
  intro y i x W hW hh
  apply fgsa_rCap p c E rho h.base.linked h.base.valid h.faultQ y i x W hW
  simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] using hh

-- A pre-GST row reaches the common cut under the receiver awake service.
example (ΔF : Time) (hΔ : E.Δ = p.Δ) (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hawake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true)
    {j r : Nat} {y x : V} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a) (hpre : p.actionTime r < E.t_GST)
    (hhor : E.t_GST + ΔF ≤ rho.horizon) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (E.t_GST + ΔF) :=
  healing_phase_receipt p c E rho ΔF hv.toScheduleWellFormed hnr
    (fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF hawake) ha hpre.le le_rfl hhor hx

-- A delivery exactly at the deadline is outside the strict receipt read.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro h
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp h)

-- The source bound covers proposal and HEAD without an honest-reader premise.
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams u))) : s + 2 ≤ u :=
  healing_source_time p c E rho hs hsource hi (Or.inl rfl)

example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams u))) : s + 2 ≤ u :=
  healing_source_time p c E rho hs hsource hi (Or.inr rfl)

-- Natural subtraction must not allow an earlier source at slot 1.
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams 1))) : False := by
  have h := healing_source_time p c E rho hs hsource hi (Or.inr rfl)
  exact Nat.not_succ_le_self 1 ((Nat.le_add_left 2 s).trans h)

end AvailableChain.FGSA.Run.Tests.HealingBase
end
