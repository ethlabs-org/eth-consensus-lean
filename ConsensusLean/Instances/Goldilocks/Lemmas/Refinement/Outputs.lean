module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Chains
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
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

/-- Transport ancestry of the actual stored-clock tips, at arbitrary engine
cuts. Neither an end-of-time observation nor clock equality is required. -/
theorem confirmed_prefix_of_anc (hs : Simulates S rho hn tr ι)
    (hnc : Compose.NoCollRun (digestOf S rho) tr)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {i j : Nat} (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length)
    (ha : Anc (tr.HonestBlocks (honestKeys S rho))
      (Regimes.readAfter tr (rho.ownKey u) (ι i) (stateAt S rho hn u i).now)
      (Regimes.readAfter tr (rho.ownKey v) (ι j) (stateAt S rho hn v j).now)) :
    (chainTrace rho).read .confirmed u i <+: (chainTrace rho).read .confirmed v j := by
  let C := fun v i => Regimes.readAfter tr (rho.ownKey v) (ι i)
    (stateAt S rho hn v i).now
  have hC : ∀ v ∈ rho.honest, ∀ i,
      C v i ∈ (tr.state (rho.ownKey v) (ι i)).fg.tree := by
    intro v hv' i
    exact (Regimes.sa_tips (A := (tr.state (rho.ownKey v) (ι i)).ac)
      (Store.frame_realization _ _ _ _ (Compose.fg_reachable hs.run.toLocalRun
        (honest_ownKey (S := S) hv') (ι i))).1 _).1.1
  have hread : ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (chainTrace rho).read .confirmed v i =
        chainTo (tr.state (rho.ownKey v) (ι i)).fg.blocks
          ((C v i).slot + 1) (C v i) := by
    intro v hv' i hi'
    rw [readIsOut V S E rho hn, outOf, hs.state v hv' i hi']
    rfl
  have hri := Compose.fg_reachable hs.run.toLocalRun (honest_ownKey (S := S) hu) (ι i)
  have hrj := Compose.fg_reachable hs.run.toLocalRun (honest_ownKey (S := S) hv) (ι j)
  have hsi : (tr.state (rho.ownKey u) (ι i)).fg.tree ⊆ tr.HonestBlocks (honestKeys S rho) :=
    fun _ h => ⟨_, honest_ownKey (S := S) hu, _, h⟩
  have hsj : (tr.state (rho.ownKey v) (ι j)).fg.tree ⊆ tr.HonestBlocks (honestKeys S rho) :=
    fun _ h => ⟨_, honest_ownKey (S := S) hv, _, h⟩
  have hU := Compose.honest_blocks_coherent hs.run.toLocalRun hnc
  have ha' := anc_in_store hrj hU hsj ha (hC v hv j)
  have hm : C u i ∈ (tr.state (rho.ownKey v) (ι j)).fg.tree := by
    by_cases he : C u i = C v j
    · exact he ▸ hC v hv j
    · exact (Anc.mem ha' he).1
  rw [hread u hu i hi, hread v hv j hj,
    chainTo_agree hri hrj hU hsi hsj (hC u hu i) hm]
  exact chainTo_prefix hrj ha'

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
  exact chainTo_prefix hrj (Regimes.finalized_monotone _ _ _ _ _ _ hs.run _ hy _ _
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
