module
public import ConsensusShapeTests.Values
public import Mathlib.Tactic
@[expose] public section

/-! # Equivalence record of the simplicity passes

Each definition that was reformulated rather than moved or deleted is
restated here in its old form (`Old*`, body verbatim; deleted helpers are
inlined), with a lemma `new ↔ old` (or `new = old`) checked by Lean.

* B1: `System.AccountablySafe`/`System.convicted` were abbreviations, inlined
  at their uses; `GoldilocksBindings` is a `def` instead of a one-field
  structure; `streamletContract`/`tendermintContract` are the specializations
  of the shared `bftContract`. -/

namespace Consensus.Shape.Tests.Reformulations

open Consensus Blocks Shape

/-! ## B1 -/

section Accountable

variable {V : Type} [Fintype V] (S : System V) (r : S.Run)

/-- The old `System.convicted`. -/
noncomputable def OldConvicted (A : Set S.Obs) : Finset V :=
  Consensus.convicted (S.convicts r) A

/-- The old `System.AccountablySafe`. -/
abbrev OldAccountablySafe (α : ℚ) (g : S.schema.Id) (t₀ : Time) : Prop :=
  (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀

theorem convicted_eq (A : Set S.Obs) :
    Consensus.convicted (S.convicts r) A = OldConvicted S r A := rfl

theorem accountablySafe_iff (α : ℚ) (g : S.schema.Id) (t₀ : Time) :
    (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀ ↔
      OldAccountablySafe S r α g t₀ := Iff.rfl

end Accountable

section Bindings

variable {Info : Type} [DecidableEq Info] [Encodable Info]

/-- The old one-field structure. -/
structure OldGoldilocksBindings (F : ShapeFamily goldilocksSchema Info) : Prop where
  skel : ∀ pub, (F pub).skel = goldilocksSkeleton pub.n

theorem goldilocksBindings_iff (F : ShapeFamily goldilocksSchema Info) :
    GoldilocksBindings F ↔ OldGoldilocksBindings F :=
  ⟨fun h => ⟨h⟩, fun h => h.skel⟩

end Bindings

section Values

/-- The old Streamlet contract (with `streamletPattern := Pattern.range 5`
inlined). -/
def OldStreamletContract (catchUp : Nat) (heal latency : Affine) :
    Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ k => catchUp + 1 + heal.eval k)
    (fun _ k => latency.eval k)
  progress _ k := .recur ⟨Pattern.range 5, k⟩

/-- The old Tendermint contract. -/
def OldTendermintContract (catchUp : Nat) (heal latency : Affine) :
    Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ m => catchUp + 1 + heal.eval m)
    (fun _ m => latency.eval m)
  progress _ m := .notReadyAtMost m

theorem streamletContract_eq (catchUp : Nat) (heal latency : Affine) :
    streamletContract catchUp heal latency = OldStreamletContract catchUp heal latency := rfl

theorem tendermintContract_eq (catchUp : Nat) (heal latency : Affine) :
    tendermintContract catchUp heal latency = OldTendermintContract catchUp heal latency := rfl

end Values

end Consensus.Shape.Tests.Reformulations

end
