module
public import ConsensusModelProofs.Canonical
public import ConsensusModelProofs.Truncate
public import Mathlib.Tactic

@[expose] public section

/-! # The model is adequate (L1)

`sysOf_adequate`: for every progress reader whose external data are the
model's (`sysExternal`: the PKI and the selection), the system `sysOf O F V`
meets the L0 acceptance interface `System.Adequate`:

* coverage, from `canonical_run_from`: every well-formed point, PKI,
  admissible selection and GST `g` has a valid run whose log is eager from `g`;
  with an injective hash (items are `Encodable`, so one exists) it has no hash
  collision, hence no excuse; its point and external data are the given ones,
  so progress carries over unchanged;
* prefix closure, from `Run.truncate`: the truncation at `b` is valid, is the
  L0 prefix of the run, and has the same PKI and selection; progress carries
  over by `Progress.shrink` (the horizon shrinks to `b`). -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

/-- An eager run log is an eager system log. -/
theorem sysOf_eagerFrom (rho : Run F E) {g : Time}
    (h : CommLog.EagerFrom rho.point rho.log g) :
    CommLog.EagerFrom ((sysOf O F V).trace ⟨E, rho⟩).point ((sysOf O F V).log ⟨E, rho⟩) g := by
  refine ⟨?_, ?_, h.txs⟩
  · rintro v hv m t ⟨o, rfl, hs⟩ w hw a ha hah haw
    exact ⟨o, rfl, h.recv v hv o t hs w hw a ha hah haw⟩
  · rintro w m t ⟨o, rfl, hr⟩
    exact h.quiet w o t hr

/-- The model system is adequate for every progress reader over the model's
external data. -/
theorem sysOf_adequate {Prog : Type} (Y : Progress (sysOf O F V) Prog)
    (hY : Y.toExternal = sysExternal O F V) : (sysOf O F V).Adequate Y := by
  obtain ⟨⟨Ext, ext, Admits⟩, holds, mono, shrink⟩ := Y
  simp only [sysExternal, External.mk.injEq] at hY
  obtain ⟨rfl, hext, hadm⟩ := hY
  cases eq_of_heq hext
  cases eq_of_heq hadm
  constructor
  · rintro p hp ⟨key, sel⟩ hsel g
    obtain ⟨relay, events, hvalid, heager⟩ :=
      canonical_run_from O F V p.env p.honest p.horizon hp key sel hsel p.submit
        Encodable.encode g
    refine ⟨⟨p.env, mkRun p.honest p.horizon key sel p.submit relay Encodable.encode events⟩,
      hvalid, ?_, rfl, sysOf_eagerFrom _ heager, fun _ _ _ _ h => h⟩
    rintro ⟨x, y, hxy, -, -, hh⟩
    exact hxy (Encodable.encode_injective hh)
  · rintro ⟨E, rho⟩ hv b hb0 hbh
    obtain ⟨hP, hview, hlog, hexc⟩ := rho.truncate_prefix (O := O) hv b
    exact ⟨⟨E, rho.truncate b⟩, rho.truncate_valid hv hb0 hbh, hP, hview, hlog, hexc,
      fun _ _ _ _ _ h => shrink hbh h⟩

end Consensus.Model

end
