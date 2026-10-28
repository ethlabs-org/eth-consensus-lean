module
public import ConsensusShape.Compile
public import ConsensusModelProofs

@[expose] public section

/-! # Shape vocabulary over compiled runs (L2)

For a run of a compiled shape family: the chain trace (what each node's
output chains are at each event cut, with the run's environment point and cut
times), honest proposals (a header released by an honest key in a proposal
role, at its release time), inclusion by a time, the liveness obligation
`ProposalLive` (D-14), output validity (linkage, increasing positions,
provenance), and the shape's progress reader `shapeProgress` (L0
`Progress`): pattern recurrence over the proposer roles of the grid, or a
bound on the validators that are not ready, read from the environment point
and the run's external data (PKI and selection, `Model.sysExternal`) only. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf sysExternal)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The chain trace of a run: the run's point and event cuts, and each node's
output chains at each cut. -/
def chainTrace (rho : Model.Run (compiled F) E) : Trace V (Header Info) O.Id :=
  ⟨rho.point, rho.events.length, rho.cutTime,
    fun g v i => (F (pubOf E)).out g (rho.stateBefore i v).st.1⟩

/-- Honest key `k` released header `h` at time `τ`, signed in a proposal role
(D-25). -/
def HonestProposal (rho : Model.Run (compiled F) E) (τ : Time) (k : Fin (Fintype.card V))
    (h : Header Info) : Prop :=
  rho.key k ∈ rho.honest ∧ ∃ r : ShapeRole (F (pubOf E)).skel.Kind, ∃ cs, ProposalRole h r ∧
    rho.releases (rho.key k) (Obj.mk (.signed k r) (.item h) cs) τ

/-- Header `h` is in the `g`-read, at the end of time `t`, of every node ready
at `t` with catch-up `c`. -/
def InBy (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (h : Header Info) (t : Time) :
    Prop :=
  ∀ v, rho.point.Ready c v t → h ∈ (chainTrace rho).readAt g v t

/-- D-14: for every `t ≥ start` (with `t + D·Δ` in the horizon), a header
released after `t`, at `τ`, by a key ready at `τ` in a proposal role, is in every
ready read by `t + D·Δ`. `τ` is not bounded above: the obligation is the
inclusion by `t + D·Δ`, not the release time. -/
def ProposalLive (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time) (D : Nat) :
    Prop :=
  ∀ t, start ≤ t → t + (D : Time) * E.Δ ≤ rho.horizon →
    ∃ τ k h, t < τ ∧ rho.point.Ready c (rho.key k) τ ∧
      HonestProposal rho τ k h ∧ InBy rho c g h (t + (D : Time) * E.Δ)

/-- Output validity of `g`: every honest read at every cut is linked from the
root under the run's hash, has increasing positions, and every header in it
was seen by the reader as an item signed in a proposal role. Unconditional
(holds even with collisions). No slot-time clause: poll positions are
heights, and the transaction bridge never uses it. -/
def OutputValid (rho : Model.Run (compiled F) E) (g : O.Id) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Linked rho.hash ((chainTrace rho).read g v i) ∧
    Chain.PosIncreasing ((chainTrace rho).read g v i) ∧
    Chain.Provenant (rho.ViewIdx v i) ProposalRole ((chainTrace rho).read g v i)

/-- In a valid run, every header in a valid honest output was seen by the
reader as an item signed in a proposal role by a key selected for that role. -/
theorem OutputValid.authorized {rho : Model.Run (compiled F) E} {g : O.Id}
    (hv : rho.ExecutionValid) (ho : OutputValid rho g) {v : V} (hvh : v ∈ rho.honest) {i : Nat}
    (hi : i ≤ rho.events.length) {h : Header Info} (hh : h ∈ (chainTrace rho).read g v i) :
    ∃ (k : Fin (Fintype.card V)) (r : ShapeRole (F (pubOf E)).skel.Kind), ∃ cs,
      ProposalRole h r ∧ k ∈ rho.sel r ∧ Obj.mk (.signed k r) (.item h) cs ∈ rho.ViewIdx v i := by
  obtain ⟨k, r, cs, hr, hs⟩ := (ho v hvh i hi).2.2 h hh
  refine ⟨k, r, cs, hr, ?_, hs⟩
  have hobs : Obj.mk (.signed k r) (.item h) cs ∈ rho.Observed := by
    obtain ⟨j, o₀, hj, hev, hc⟩ := hs
    exact ⟨v, hvh, j, o₀, lt_of_lt_of_le hj hi, hev, hc⟩
  exact rho.selected_of_observed hv hobs (.refl _) rfl

/-- The requirement `π` with catch-up `c` on `[start, stop]` at point `p`, PKI
`key` and selection `sel` of family `F`: pattern recurrence over the proposer
roles of the grid, or at most `m` validators not ready. A shape without slot
proposers (`proposerSel := .fixed ∅`, e.g. a poll shape) never meets a
recurrence with a window inside `[start, stop]` (`HonestReadyIn` needs a
nonempty selection); acceptance therefore requires `.recur` only of shapes
with one proposer per slot (`Contract.ProgressFits`). -/
def shapeHolds (F : ShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V] :
    ProgressReq → Time → Time → Time → (p : EnvPoint V) →
      (sysExternal O (compiled F) V).Ext p.env → Prop
  | .recur ρ, c, s, e, p, x =>
    PatternRecurrence (R := ShapeRole (F (pubOf p.env)).skel.Kind) p x.1 x.2
      ShapeRole.proposer (F (pubOf p.env)).skel.grid ρ c s e
  | .notReadyAtMost m, c, s, e, p, _ => NotReadyOn p m c s e

/-- The shape's progress reader: the model's external data (PKI and
selection) with `shapeHolds`. -/
def shapeProgress (F : ShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    Progress (sysOf O (compiled F) V) ProgressReq where
  toExternal := sysExternal O (compiled F) V
  holds := shapeHolds F
  mono := by
    intro π c s s' e e' p x hs he h
    cases π with
    | recur ρ => exact PatternRecurrence.mono h hs he
    | notReadyAtMost m => exact NotReadyOn.mono h hs he
  shrink := by
    intro π c s e p x b hb h
    cases π with
    | recur ρ => exact PatternRecurrence.shrink hb h
    | notReadyAtMost m => exact NotReadyOn.shrink hb h

/-! ## The L0 regimes and quantities at a compiled run

Shape-level names for the L0 definitions at the system run `⟨E, rho⟩` of the
compiled system; each is the L0 definition itself (`abbrev`). -/

section Regimes

variable (K : Contract O ProgressReq) (rho : Model.Run (compiled F) E)

/-- The catch-up duration `catchUp·Δ`. -/
abbrev shapeC : Time := (sysOf O (compiled F) V).cDur K ⟨E, rho⟩

/-- The sleepy regime (L0 `Regime.Sleepy`). -/
abbrev ShapeSleepy : Prop := (sysOf O (compiled F) V).Sleepy K ⟨E, rho⟩

/-- The healthy regime from GST `gst` (L0 `Regime.Healthy`). -/
abbrev ShapeHealthy (gst : Time) : Prop := (sysOf O (compiled F) V).Healthy K gst ⟨E, rho⟩

/-- The outage regime (L0 `Regime.Outage`). -/
abbrev ShapeOutage (T b₀ b₁ : Time) : Prop :=
  (sysOf O (compiled F) V).Outage K T b₀ b₁ ⟨E, rho⟩

/-- The heal point of `cap` at `i` after GST `gst`. -/
abbrev shapeHeal (cap : Capability) (i : K.Idx) (gst : Time) : Time :=
  (sysOf O (compiled F) V).heal K cap i gst ⟨E, rho⟩

/-- The start of progress windows after GST `gst`. -/
abbrev shapeReady (gst : Time) : Time := (sysOf O (compiled F) V).ready K gst ⟨E, rho⟩

/-- The progress requirement of `cap` at `i` holds on `[start, stop]`. -/
abbrev ShapeProg (cap : Capability) (i : K.Idx) (start stop : Time) : Prop :=
  (sysOf O (compiled F) V).prog (shapeProgress F V) K cap i start stop ⟨E, rho⟩

end Regimes

end Consensus.Shape

end
