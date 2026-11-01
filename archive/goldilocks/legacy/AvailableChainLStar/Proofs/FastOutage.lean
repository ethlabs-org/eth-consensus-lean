module
public import AvailableChainLStar.Statements.Contract

@[expose] public section
namespace AvailableChain.LStar

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Equal arming lags make fast P1 a consequence of general P1.
The L* general P1 proof is still pending. -/
theorem fastP1_of_general {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (n : Nat) (E : Env V) (G : Time)
    (general : ∀ (rho : Run V (lstar p n)) T b₀ b₁,
      OutageRegime (lstar p n) E (lstarInterface p n) (lstarConstants p G) rho T b₀ b₁ →
      PersistsThrough (lstar p n) rho stable T b₀ b₁) :
    ∀ (rho : Run V (lstar p n)) T b₀ b₁,
      FastOutageRegime (lstar p n) E (lstarInterface p n) (lstarConstants p G) rho T b₀ b₁ →
      PersistsThrough (lstar p n) rho stable T b₀ b₁ := by
  intro rho T b₀ b₁ ho
  exact general rho T b₀ b₁ ho.toOutageRegime

end AvailableChain.LStar
end

#print axioms AvailableChain.LStar.fastP1_of_general
