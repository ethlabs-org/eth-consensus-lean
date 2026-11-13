module
public import ConsensusLean.Lemmas.Problem.AdequateObs
public import ConsensusLean.Lemmas.Model.Adequate
public import ConsensusLean.Lemmas.Model.TruncateExt

/-! # Model witnesses preserving identities and the complete slot dictionary

The arbitrary role plan is not asserted to be implemented by an engine or to be public.
Same-environment preservation proves no cross-environment reader publicity. -/

public section

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V]
  {O : OutputSchema} {F : ProtocolFamily O}

/-- Observe the identity equivalence together with all slot committees under a role plan. -/
def dictObs (voteRole : ∀ E : Env V, Nat → (protoOf F E).Role) :
    ExtObs (sysOf O F V) (sysExternal O F V)
      ((Fin (Fintype.card V) ≃ V) × (Nat → Finset (Fin (Fintype.card V)))) :=
  ⟨fun E e => (e.1, fun s => e.2 (voteRole E s))⟩

theorem dictObs_obs (voteRole : ∀ E : Env V, Nat → (protoOf F E).Role)
    (E : Env V) (e : (sysExternal O F V).Ext E) :
    (dictObs voteRole).obs E e = (e.1, fun s => e.2 (voteRole E s)) := by rfl

/-- Concrete prefix and canonical covering witnesses keep the PKI and slot dictionary. -/
theorem sysOf_adequateObs {Prog : Type} (Y : Progress (sysOf O F V) Prog)
    (hY : Y.toExternal = sysExternal O F V)
    (voteRole : ∀ E : Env V, Nat → (protoOf F E).Role) :
    (sysOf O F V).AdequateObs Y (hY.symm ▸ dictObs voteRole) := by
  have ha := sysOf_adequate Y hY
  obtain ⟨X, holds, mono, shrink, submit_irrel⟩ := Y
  cases hY
  refine ⟨ha, ?_, ?_⟩
  · rintro ⟨E, rho⟩ hv b hb0 hbh
    obtain ⟨hP, hview, hlog, hexc⟩ := rho.truncate_prefix (O := O) hv b
    refine ⟨⟨E, rho.truncate b⟩, rho.truncate_valid hv hb0 hbh,
      hP, hview, hlog, hexc, ?_, ?_⟩
    · intro π c s t _ h
      rw [Run.truncate_eq]
      exact shrink hbh h
    · simp only [Run.truncate_key, Run.truncate_sel]
      rfl
  · rintro p hp ⟨key, sel⟩ hsel g
    obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf F p.env).Item
    obtain ⟨relay, events, hvalid, heager⟩ :=
      canonical_run_from O F V p.env p.faultyAt p.faultyAt_mono p.horizon hp
        key sel hsel p.submit hash g
    refine ⟨⟨p.env, Run.mk p.faultyAt p.faultyAt_mono p.horizon
      events key sel p.submit relay hash⟩,
      hvalid, ?_, rfl, sysOf_eagerFrom _ heager, fun _ _ _ _ h => h, ?_⟩
    · rintro ⟨x, y, hxy, -, -, hh⟩
      exact hxy (hinj hh)
    · rfl

end Consensus.Model

end
