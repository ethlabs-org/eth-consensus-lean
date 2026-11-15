module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Signed-object provenance at the observation cut

Objects in the closure of a reader's seen log, including nested payloads and objects retained
across restarts, have genuine earlier releases when their signer is honest at that cut.
No claim is made for a signer compromised before delivery.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- A signed object in a view has an earlier genuine release when its signer is honest
at the observation cut. `ViewIdx` includes recursive containment and survives restart. -/
theorem signed_view_released_at (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {o : (Model.protoOf (compiled (goldilocks S)) E).Object}
    (ho : o ∈ rho.ViewIdx v i) {y : Fin (Fintype.card V)}
    (hy : y ∈ honestKeysAt S rho (rho.cutTime i))
    (hs : rho.signerOf o = some (rho.key y)) :
    ∃ j < i, ∃ t, rho.SendsAt (rho.key y) j t ∧ o ∈ rho.releasesAt j := by
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
  have ht := hlaws.cutTime_le_horizon i hi
  change rho.cutTime i ≤ rho.horizon at ht
  have hy' : rho.key y ∉ rho.faultyAt (rho.cutTime i) := by
    rw [mem_honestKeysAt_iff] at hy
    rwa [min_eq_left ht] at hy
  exact rho.signed_seen_released hv hi (rho.viewIdx_closure ho) hy' hs

/-- The same provenance holds for every nested object carried by an object in the view. -/
theorem contained_view_released_at (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {o o' : (Model.protoOf (compiled (goldilocks S)) E).Object}
    (ho : o ∈ rho.ViewIdx v i) (hc : Model.Obj.Contains o o')
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeysAt S rho (rho.cutTime i))
    (hs : rho.signerOf o' = some (rho.key y)) :
    ∃ j < i, ∃ t, rho.SendsAt (rho.key y) j t ∧ o' ∈ rho.releasesAt j := by
  apply signed_view_released_at S rho hv (v := v) hi ?_ hy hs
  obtain ⟨k, o₀, hk, he, hc₀⟩ := rho.mem_viewIdx_iff.mp ho
  exact rho.mem_viewIdx_iff.mpr ⟨k, o₀, hk, he, hc₀.trans hc⟩

end Consensus.Goldilocks.Simulation
