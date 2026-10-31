module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs

public section

/-! # Structural transport of node outputs to engine chains -/

namespace Consensus.Goldilocks.Refinement

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {rho : Model.Run (compiled (family S)) E} {hn : 1 ≤ Fintype.card V}
  {tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)} {ι : Nat → Nat}

omit [DecidableEq V] in
/-- The honest engine reader's key is honest in its simulating run. -/
theorem honest_ownKey {v : V} (hv : v ∈ rho.honest) : rho.ownKey v ∈ honestKeys S rho := by
  simpa only [honestKeys, Set.mem_ofPred_eq, Model.Run.ownKey, Equiv.apply_symm_apply] using hv

/-- Read the finalized chain directly from the simulating node cut. -/
theorem read_finalized (hs : Simulates S rho hn tr ι) {v : V} (hv : v ∈ rho.honest)
    {i : Nat} (hi : i ≤ rho.events.length) :
    (chainTrace rho).read .finalized v i =
      chainTo (tr.state (rho.ownKey v) (ι i)).fg.blocks
        ((tr.finalizedAt (rho.ownKey v) (ι i)).slot + 1)
        (tr.finalizedAt (rho.ownKey v) (ι i)) := by
  rw [readIsOut V S E rho hn, outOf, hs.state v hv i hi]
  rfl

/-- Finalized engine reads extend at every pair of ordered cuts, without `NoColl`. -/
theorem finalized_monotone (hs : Simulates S rho hn tr ι) :
    (chainTrace rho).Monotone .finalized 0 := by
  intro v i j hi hij hj hv _
  have hy := honest_ownKey (S := S) hv
  have hri := Compose.fg_reachable hs.run.toLocalRun hy (ι i)
  have hrj := Compose.fg_reachable hs.run.toLocalRun hy (ι j)
  rw [read_finalized hs hv hi.1, read_finalized hs hv hj.1]
  simp only [RunTrace.finalizedAt]
  rw [chainTo_mono hri (Compose.tree_mono hs.run.toLocalRun hy (hs.ι_mono hij))
    (Store.cache_invariants _ _ _ _ hri).1]
  exact chainTo_prefix hrj (Regimes.finalized_monotone _ _ _ _ _ hs.run _ hy _ _
    (hs.ι_mono hij))

/-- Nesting holds at the shape's actual clock; it need not equal the next node cut's time. -/
theorem outputs_nested (hs : Simulates S rho hn tr ι) :
    (chainTrace rho).Nested .finalized .confirmed := by
  intro v hv i hi
  have hy := honest_ownKey (S := S) hv
  have hr := Compose.fg_reachable hs.run.toLocalRun hy (ι i)
  have hΦ := (Store.frame_realization _ _ _ _ hr).1
  have hC := (Regimes.sa_tips (A := (tr.state (rho.ownKey v) (ι i)).ac) hΦ
    (stateAt S rho hn v i).now).1
  have ha := hΦ.rooted.2 _ hC
  rw [readIsOut V S E rho hn, readIsOut V S E rho hn]
  simp only [outOf, hs.state v hv i hi]
  exact chainTo_prefix hr (ha.mono (fun _ h => h.1))

end Consensus.Goldilocks.Refinement

end
