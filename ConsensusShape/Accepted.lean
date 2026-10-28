module
public import ConsensusShape.Realizable

@[expose] public section

/-! # Acceptance (layer 1): the review endpoint

`Accepted F K` is what an instance must establish: its shape claims
(`ShapeClaims`, proved by the protocol), the non-vacuity certificate of its
contract (`Contract.Realizable`), and that its schema serves a ledger
(`OutputSchema.Serves`: a final output, or an available one).
`Accepted.problemClaims` gives the layer-0 claims; `delivers` shows that every
provided output of a family with claims and a realizable contract delivers a
transaction to a ready honest reader that was never submitted it, in some
valid, collision-free run, so an instance with no service, a silent service or empty outputs is not
accepted (`Accepted.serves_and_delivers`).

`Accepted` means "meets this contract". Whether the contract is the intended
service (its premise terms, starts, latencies, escapes, capability choices and
skeleton) is read off the contract itself; see the README. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- An accepted instance: shape claims, a realizable contract, and a served
ledger. -/
structure Accepted (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- Every premise is realizable with active service. -/
  realizable : K.Realizable F
  /-- A final or an available output is provided. -/
  serves : O.Serves

/-- An accepted instance meets the layer-0 claims of its contract for every
finite validator type. -/
theorem Accepted.problemClaims {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    ProblemClaims (sysOf O (compiled F) V) (shapeExec F V) K :=
  refinement F K V h.claims

/-- Output `g` delivers: in some valid, collision-free compiled run, a
transaction never submitted to an honest validator `w` is in `w`'s read of `g`
at a time at which `w` is ready. -/
def Delivers (F : ShapeFamily O Info) (K : Contract O ProgressReq) (g : O.Id) : Prop :=
  ∃ (n : Nat) (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
    rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
    ∃ (x : Tx) (w : Fin (n + 1)) (t : Time), w ∈ rho.honest ∧ (∀ τ, x ∉ rho.submit w τ) ∧
      rho.point.Ready (((K.catchUp : Nat) : Time) * E.Δ) w t ∧
      x ∈ ((sysOf O (compiled F) (Fin (n + 1))).trace ⟨E, rho⟩).readAt g w t

/-- Every provided output of a family with shape claims and a realizable
contract delivers: the liveness witness of its capability, through
`refinement`, puts the witness's transaction in the ready reader's read. -/
theorem delivers {F : ShapeFamily O Info} {K : Contract O ProgressReq} (hc : ShapeClaims F K)
    (hr : K.Realizable F) {c : Capability} {g : O.Id} (hg : O.output c = some g) :
    Delivers F K g := by
  have h1 : (K.spec c).isSome := by rw [← hc.provided c, hg]; rfl
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨i⟩ := K.idx_nonempty
  obtain ⟨σ, n, E, rho, hw, ha⟩ := hr.live c s hs i
  have pc := refinement F K (Fin (n + 1)) hc
  rcases (pc.caps c g s hg hs).live i σ ⟨E, rho⟩ hw.valid hw.premise with hl | hx
  · obtain ⟨x, t, t', u, w, hst, ht0, hu, hua, hx, hwh, -, hnw, hdl, hth, hrd⟩ := ha
    exact ⟨n, E, rho, hw.valid, hw.noCollision, x, w, t', hwh, hnw, hrd,
      hl x t t' hst ⟨u, hu, t, ht0, le_rfl, hua, hx⟩ hdl hth w hrd⟩
  · exact absurd hx hw.noCollision

/-- An accepted instance provides a final or an available output, and that
output delivers. -/
theorem Accepted.serves_and_delivers {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) :
    ∃ c g, (c = .final ∨ c = .available) ∧ O.output c = some g ∧ Delivers F K g := by
  rcases h.serves with hb | ⟨ha, -⟩
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨.final, g, Or.inl rfl, hg, delivers h.claims h.realizable hg⟩
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ha
    exact ⟨.available, g, Or.inr rfl, hg, delivers h.claims h.realizable hg⟩

end Consensus.Shape

end
