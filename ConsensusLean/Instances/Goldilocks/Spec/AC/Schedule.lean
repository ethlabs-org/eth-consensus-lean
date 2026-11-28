module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params

@[expose] public section

/-! # Goldilocks AC: schedule and parameters

`specs/goldilocks/tex/goldilocks-spec.tex` §"Schedule":
slot `s` starts at `t_s = 4Δs`, so `slot(t) = ⌊t/(4Δ)⌋`, and in the spec its committee is all of
`V`. The formula `t_s = 4Δs` also gives the times of negative slots (`ts` takes an integer slot),
which the rules read at slot `0` (`t_{-1} + 3Δ`, `t_{slot(t)-1}`). The lock window is `k ≥ 2`
slots and the fast increment `c ≥ 2` slots.

`ACParams` extends the shared parameters (`Params`) by the lock window, the fast increment, the
hypothesis that the shared slot times are the AC's, and the public committee size
`committeeSize`, the denominator of the fixed vote thresholds (fast, optimistic, unlock). The
spec's all-of-`V` committee is the specialization `committeeSize = n` (the default). The switch
`optimistic`, one value for the whole protocol, says whether the optimistic confirmation runs;
the spec's protocol runs it (the default). The switch `deepDepth`, one value for the whole
protocol, says whether `ac_to_fg` falls back to deep sources and at which depth `D` (in slots);
the spec's protocol reads fast locks only (`none`, the default). `K_W`, `δ_t`'s lower bound and
the source delay are the FG's and the regimes' (goldilocks-spec §"Schedule"); no AC rule reads
them. -/

namespace Consensus.Goldilocks.AC

/-- The AC's parameters: the shared parameters, whose slot times are `t_s = 4Δs`, the lock
window `k ≥ 2`, the fast increment `c ≥ 2`, the public committee size, the optimistic switch
and the deep-source depth. -/
structure ACParams where
  /-- The shared parameters. -/
  toParams : Params
  /-- Slot `s` starts at `4Δs`. -/
  slotTime_eq : ∀ s : Nat, toParams.slotTime s = 4 * toParams.Δ * s
  /-- The slow window: a slow lock of slot `j` lives through slot `j + k`; no lock the AC writes
  lives longer. -/
  k : Nat
  /-- The window is at least two slots. -/
  two_le_k : 2 ≤ k
  /-- The fast increment: each fast lock extends the node's fast deadline by `c` slots. -/
  c : Nat
  /-- The increment is at least two slots. -/
  two_le_c : 2 ≤ c
  /-- Public size of the voting committee; stock uses the whole population. -/
  committeeSize : Nat := toParams.n
  /-- Whether the optimistic confirmation runs, for the whole protocol; stock runs it. -/
  optimistic : Bool := true
  /-- The deep-source depth `D` in slots, for the whole protocol: with `some D`, `ac_to_fg`
  falls back to a deep candidate when it has no fast-lock candidate; stock (`none`) reads fast
  locks only. -/
  deepDepth : Option Nat := none

namespace ACParams

variable (sp : ACParams)

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

end ACParams

end Consensus.Goldilocks.AC

end
