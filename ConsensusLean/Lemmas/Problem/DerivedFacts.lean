module
public import ConsensusLean.Lemmas.Problem.Derived

public section

/-! # Derived notions not read by instance statements (L0, not protected)

`Trace.map` and `CommLog.SendsFromZero` with their characterising lemmas: read by
the L0 facts and the proofs, by no instance statement. Split from `Derived.lean`
so that editing them needs no tag move (#38 follow-up). Importers use this file;
it re-exports `Derived.lean`. -/

namespace Consensus

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- The same trace with every read mapped by `f`. -/
def map {β : Type} (f : List α → List β) : Trace V β Id :=
  ⟨tr.point, tr.cuts, tr.cutTime, fun g v i => f (tr.read g v i)⟩

theorem map_eq {β : Type} (f : List α → List β) :
    tr.map f = ⟨tr.point, tr.cuts, tr.cutTime, fun g v i => f (tr.read g v i)⟩ := by rfl

@[simp] theorem map_point {β : Type} (f : List α → List β) : (tr.map f).point = tr.point := by rfl
@[simp] theorem map_cuts {β : Type} (f : List α → List β) : (tr.map f).cuts = tr.cuts := by rfl
@[simp] theorem map_cutTime {β : Type} (f : List α → List β) :
    (tr.map f).cutTime = tr.cutTime := by rfl
@[simp] theorem map_read {β : Type} (f : List α → List β) (g : Id) (v : V) (i : Nat) :
    (tr.map f).read g v i = f (tr.read g v i) := by rfl

end Trace

namespace CommLog

variable {V M : Type} (p : EnvPoint V) (L : CommLog V M)

/-- No honest send before time `0`. Every valid model run's log has this
(`Model.Run.log_sendsFromZero`). -/
def SendsFromZero : Prop := ∀ v ∈ p.honest, ∀ m t, L.sent v m t → 0 ≤ t

variable {p L} in
theorem sendsFromZero_iff : SendsFromZero p L ↔ ∀ v ∈ p.honest, ∀ m t, L.sent v m t → 0 ≤ t :=
  Iff.rfl

end CommLog

end Consensus

end
