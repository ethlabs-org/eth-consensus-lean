module
public import AvailableChainLStar.Model.Protocol
public import AvailableChainStatements.Generic.Claims

@[expose] public section

namespace AvailableChain.LStar

open AvailableChain.Generic
open AvailableChain.Statements.Generic

def lstarInterface (p : Params) (n : Nat) : Interface (lstar p n) where
  confirmed := confirmed
  stable := stable
  block := block
  opening := fun _ => True

/-- Paper constants from guarded-override.md §§10.2–10.3 and
two-set-recovery.md §7 (ρ = L + G + 11Δ with the expiry guard
`Params.lockPhase`). The recovery gap `G` is a premise parameter. -/
def lstarConstants (p : Params) (G : Time) : Constants where
  θ := 3 / 4
  θrec := 3 / 4
  recoveryFull := true
  η := p.η
  D_c := 6 * p.Δ
  D_s := 6 * p.Δ
  D_f := 6 * p.Δ
  armingLag := 4 * p.Δ
  fastArmingLag := 4 * p.Δ
  budget := min p.η (p.L - 4 * p.Δ)
  recoveryBound := p.L + G + 11 * p.Δ
  proposerGap := G

theorem lstarConstants_valid (p : Params) (G : Time) (hG : 0 < G) :
    (lstarConstants p G).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [lstarConstants]
  · norm_num [lstarConstants]
  · norm_num [lstarConstants]
  · norm_num [lstarConstants]
  · exact p.etaNonneg
  · dsimp [lstarConstants]
    have h : 0 ≤ 6 * p.Δ := mul_nonneg (by norm_num) (le_of_lt p.deltaPos)
    exact ⟨h, h, h⟩
  · dsimp [lstarConstants]
    linarith [p.deltaPos]
  · dsimp [lstarConstants]; linarith [p.deltaPos]
  · exact le_refl _
  · dsimp [lstarConstants]
    exact le_min p.etaNonneg (by linarith [p.lockLong])
  · dsimp [lstarConstants]
    exact min_le_left _ _
  · dsimp [lstarConstants]
    linarith [p.lockLong, p.deltaPos, hG]
  · exact hG

/-- Statement only. No claim proof is supplied in this instance job.
The matching environment slot length is explicit and nonvacuous. -/
def LStarContract {V : Type} [DecidableEq V] [Fintype V] (n : Nat)
    (p : Params) (G : Time) (E : Env V) : Prop :=
  E.Δ = p.Δ ∧
    AvailableChain (lstar p n) E (lstarInterface p n) (lstarConstants p G)

end AvailableChain.LStar
end
