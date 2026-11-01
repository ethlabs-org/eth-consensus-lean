module
public import AvailableChainFGSARun.Statements.Slashing
public import AvailableChainFGSARun.Proofs.ClientTrace

/-! The seat-to-holder step of `fgsaSlashing` under one FG seat bijection. -/

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In : Type} {c : AppCodec In}

/-- With one seat bijection `e` for every FG round, `slashes` is DC's
attribution: slashable evidence for the seat `e.symm v`. -/
theorem fgsaSlashing_slashes_iff_of_seats {E : Generic.Env (Fin p.n)}
    {rho : V2.D.Run (Fin p.n) (fgsa p c)} (e : Fin p.n ≃ Fin p.n)
    (he : ∀ j, rho.seatOf (.base .fg) j = e j) (v : Fin p.n) :
    (fgsaSlashing p c E).slashes rho v ↔ ∃ (u u' : Fin p.n) (t t' : Time),
      SlashableBetween (fgsaEvidence (V2.D.Run.readAt E rho t u))
        (fgsaEvidence (V2.D.Run.readAt E rho t' u')) (e.symm v) := by
  constructor
  · rintro ⟨u, u', t, t', i, hs, hi⟩
    have hiv : i = e.symm v := by rw [← hi, he i, Equiv.symm_apply_apply]
    subst hiv
    exact ⟨u, u', t, t', hs⟩
  · rintro ⟨u, u', t, t', hs⟩
    exact ⟨u, u', t, t', e.symm v, hs, (he (e.symm v)).trans (e.apply_symm_apply v)⟩

/-- Under `Linked`, `slashes` is DC's attribution through the seat bijection
of `fgsa_linked_seats`. -/
theorem fgsaSlashing_slashes_iff_of_linked {E : Generic.Env (Fin p.n)}
    {rho : V2.D.Run (Fin p.n) (fgsa p c)} (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∃ e : Fin p.n ≃ Fin p.n, (∀ j, rho.seatOf (.base .fg) j = e j) ∧
      ∀ v, ((fgsaSlashing p c E).slashes rho v ↔ ∃ (u u' : Fin p.n) (t t' : Time),
        SlashableBetween (fgsaEvidence (V2.D.Run.readAt E rho t u))
          (fgsaEvidence (V2.D.Run.readAt E rho t' u')) (e.symm v)) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  exact ⟨e, he, fgsaSlashing_slashes_iff_of_seats e he⟩

end AvailableChain.FGSA.Run
