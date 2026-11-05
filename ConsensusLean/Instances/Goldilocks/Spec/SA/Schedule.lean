module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params

@[expose] public section

/-! # Goldilocks SA: schedule and parameters

`specs/goldilocks/tex/goldilocks-spec.tex` §"Schedule":
slot `s` starts at `t_s = 4Δs`, so `slot(t) = ⌊t/(4Δ)⌋`, and its committee is all of `V`. The
formula `t_s = 4Δs` also gives the times of negative slots (`ts` takes an integer slot), which
the rules read at slot `0` (`t_{-1} + 3Δ`, `t_{slot(t)-1}`). The lock window is `k ≥ 2` slots
and the fast increment `c ≥ 2` slots.

`SAParams` extends the shared parameters (`Params`) by the lock window, the fast increment and
the hypothesis that the shared slot times are the SA's. `R`, `K_W`, `δ_t`'s lower bound and the
source delay are the FG's and the regimes' (goldilocks-spec §"Schedule"); no SA rule reads them. -/

namespace Consensus.Goldilocks.SA

/-- The SA's parameters: the shared parameters, whose slot times are `t_s = 4Δs`, the lock
window `k ≥ 2` and the fast increment `c ≥ 2`. -/
structure SAParams where
  /-- The shared parameters. -/
  toParams : Params
  /-- Slot `s` starts at `4Δs`. -/
  slotTime_eq : ∀ s : Nat, toParams.slotTime s = 4 * toParams.Δ * s
  /-- The slow window: a slow lock of slot `j` lives through slot `j + k`; no lock the SA writes
  lives longer. -/
  k : Nat
  /-- The window is at least two slots. -/
  two_le_k : 2 ≤ k
  /-- The fast increment: each fast lock extends the node's fast deadline by `c` slots. -/
  c : Nat
  /-- The increment is at least two slots. -/
  two_le_c : 2 ≤ c

namespace SAParams

variable (sp : SAParams)

/-- The number of validators. -/
abbrev n : Nat := sp.toParams.n

/-- The delivery parameter `Δ`. -/
abbrev Δ : Time := sp.toParams.Δ

/-- The start `t_s = 4Δs` of slot `s`, also for negative `s`. -/
def ts (s : Int) : Time := 4 * sp.Δ * s

/-- The slot `slot(t)` of time `t` (the shared definition). -/
abbrev slot (t : Time) : Nat := sp.toParams.slotOf t

/-- The genesis root. -/
abbrev genesisRoot : Nat := sp.toParams.genesisRoot

end SAParams

end Consensus.Goldilocks.SA

end
