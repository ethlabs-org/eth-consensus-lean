module
public import ConsensusLean.Lemmas.Model.Canonical.Construction
public import ConsensusLean.Lemmas.Model.Truncate

public section

/-! # The model is adequate (L1)

`sysOf_adequate`: for every progress reader whose external data are the
model's (`sysExternal`: the PKI and the selection), the system `sysOf O F V`
meets the L0 acceptance interface `System.Adequate`:

* admissible external data in every environment: the PKI
  `Fintype.equivFin` and, per role, a selection from `SelSpec.admits_exists`;
* coverage, from `canonical_run_from`: every point with `0 ≤ horizon`, PKI,
  admissible selection and GST `g` has a valid run whose log is eager from `g`;
  with an injective hash (items are countable, so one exists) it has no hash
  collision, hence no excuse; its point and external data are the given ones,
  so progress carries over unchanged;
* prefix closure, from `Run.truncate`: the truncation at `b` is valid, is the
  L0 prefix of the run, and has the same PKI and selection; progress carries
  over by `Progress.shrink` (the horizon shrinks to `b`). -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

/-- The hash is injective: no collision can occur. -/
def Run.InjectiveHash (rho : Run F E) : Prop := Function.Injective rho.hash

omit [DecidableEq V] in
theorem Run.injectiveHash_iff {rho : Run F E} : rho.InjectiveHash ↔ Function.Injective rho.hash :=
  Iff.rfl

/-- An injective hash has no collision. -/
theorem Run.not_hashCollision_of_injective {rho : Run F E} (hi : rho.InjectiveHash) :
    ¬ rho.HashCollision := by
  rintro ⟨x, y, hne, _, _, he⟩
  exact hne (hi he)

/-- An eager run log is an eager system log. -/
theorem sysOf_eagerFrom (rho : Run F E) {g : Time}
    (h : CommLog.EagerFrom rho.point rho.log g) :
    CommLog.EagerFrom ((sysOf O F V).trace ⟨E, rho⟩).point ((sysOf O F V).log ⟨E, rho⟩) g := by
  refine ⟨?_, ?_, h.txs⟩
  · rintro v m t ⟨o, rfl, hs⟩ hv w a ha hah hw haw
    exact ⟨o, rfl, h.recv v o t hs hv w a ha hah hw haw⟩
  · rintro w m t ⟨o, rfl, hr⟩
    exact h.quiet w o t hr

/-- The model system is adequate for every progress reader over the model's
external data. -/
theorem sysOf_adequate {Prog : Type} (Y : Progress (sysOf O F V) Prog)
    (hY : Y.toExternal = sysExternal O F V) : (sysOf O F V).Adequate Y := by
  obtain ⟨X, holds, mono, shrink, _⟩ := Y
  cases hY
  refine ⟨fun E => ?_, ?_, ?_⟩
  · exact ⟨((Fintype.equivFin V).symm, fun ρ => Classical.choose
      ((protoOf F E).selSpec ρ).admits_exists), fun ρ => Classical.choose_spec
      ((protoOf F E).selSpec ρ).admits_exists⟩
  · rintro p hp ⟨key, sel⟩ hsel g
    obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf F p.env).Item
    obtain ⟨relay, events, hvalid, heager⟩ :=
      canonical_run_from O F V p.env p.faultyAt p.faultyAt_mono p.horizon hp
        key sel hsel p.submit hash g
    refine ⟨⟨p.env, Run.mk p.faultyAt p.faultyAt_mono p.horizon
      events key sel p.submit relay hash⟩,
      hvalid, ?_, rfl, sysOf_eagerFrom _ heager, (fun _ _ _ _ h => h), fun _ => rfl⟩
    rintro ⟨x, y, hxy, -, -, hh⟩
    exact hxy (hinj hh)
  · rintro ⟨E, rho⟩ hv b hb0 hbh
    obtain ⟨hP, hview, hlog, hexc⟩ := rho.truncate_prefix (O := O) hv b
    exact ⟨⟨E, rho.truncate b⟩, rho.truncate_valid hv hb0 hbh, hP, hview, hlog, hexc,
      (fun _ _ _ _ _ h => by rw [Run.truncate_eq]; exact shrink hbh h),
      fun _ => by rw [Run.truncate_eq]; rfl⟩

end Consensus.Model

end
