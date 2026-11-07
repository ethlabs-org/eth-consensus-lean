module
public import ConsensusLean.Lemmas.Model.Canonical.Construction
public import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Causal runs convict nobody

Every signed object in a causal run has genuine release provenance, even
after its signer is compromised. The engine's persistent slashing guard
therefore excludes conflicting evidence for every validator. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

/-- In a causal run every observed signature has genuine release provenance. -/
theorem released_of_causal (hc : rho.Causal) {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) {u : V} (hs : rho.signerOf o = some u) :
    ∃ j t, rho.SendsAt u j t ∧ o ∈ rho.releasesAt j := by
  obtain ⟨v, i, _, _, hov⟩ := ho
  obtain ⟨p, hp, hpo⟩ := (mem_closure_iff _ _).mp hov
  have hsafe := (rho.causal_safe hc i).1 v p hp
  obtain ⟨j, t, _, hj, hr⟩ :=
    signedBefore_iff.mp (safeBefore_iff.mp hsafe o hpo) u hs
  exact ⟨j, t, hj, hr⟩

theorem not_slashable_of_causal (hc : rho.Causal) (x : V) :
    ¬ rho.Slashable rho.Observed x :=
  rho.not_slashable_of_released fun _ ho hs => rho.released_of_causal hc ho hs

end Run

/-- Horizon-bounded honest evidence convicts nobody in a causal run. -/
theorem convicted_honestEvidence_eq_empty (rho : Run F E) (hv : rho.ExecutionValid)
    (h : ∀ x, ¬ rho.Slashable rho.Observed x) :
    Consensus.convicted ((sysOf O F V).convicts ⟨E, rho⟩)
      ((sysOf O F V).honestEvidenceBy ⟨E, rho⟩ rho.horizon) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hconv : (sysOf O F V).convicts ⟨E, rho⟩
      ((sysOf O F V).honestEvidenceBy ⟨E, rho⟩ rho.horizon) x := by
    unfold Consensus.convicted at hx
    simpa using hx
  apply h x
  obtain ⟨o, ho, o', ho', h1, h2, h3⟩ := hconv
  exact ⟨o, (mem_honestEvidence_iff rho hv o).mp ho,
    o', (mem_honestEvidence_iff rho hv o').mp ho', h1, h2, h3⟩

end Consensus.Model
end
