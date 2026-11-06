module
public import ConsensusLean.Spec.Shape.Compile
public import ConsensusLean.Spec.Model.System

@[expose] public section

/-! # Shape vocabulary over compiled runs (L2)

For a run of a compiled shape family: the chain trace (what each node's
output chains are at each event cut, with the run's environment point and cut
times), honest proposals (a header released by an honest key in a proposal
role, at its release time), inclusion by a time, the liveness obligation
`ProposalLiveReady` (reader-conditional),
output validity (linkage, increasing positions,
provenance), and the shape's progress reader `shapeProgress` (L0
`Progress`): pattern recurrence over the proposer roles of the grid, or a
bound on the validators that are not ready, read from the environment point
and the run's external data (PKI and selection, `Model.sysExternal`) only. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf sysExternal)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- The compiled system of family `F` at validators `V` (L1 `sysOf`). Its runs
are pairs `r = ⟨E, rho⟩`; the L0 regimes and durations at `r` are the
`System` accessors (`(Sys F V).Sleepy K r`, `.cDur K r`, `.heal K cap i gst r`, …). -/
abbrev Sys (F : ChainShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] : System V :=
  sysOf O (compiled F) V

variable {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The chain trace of a run: the run's point and event cuts, and each node's
output chains at each cut. -/
def chainTrace (rho : Model.Run (compiled F) E) : Trace V (Header Info) O.Id :=
  ⟨rho.point, rho.events.length, rho.cutTime,
    fun g v i => (F (pubOf E)).out g (rho.stateBefore i v).st.1⟩

/-- Key `k`, honest at `τ`, released header `h` at time `τ`, signed in a proposal
role. -/
def HonestProposal (rho : Model.Run (compiled F) E) (τ : Time) (k : Fin (Fintype.card V))
    (h : Header Info) : Prop :=
  rho.point.HonestAt (rho.key k) τ ∧
    ∃ r : ShapeRole (F (pubOf E)).skel.Kind, ∃ cs, ProposalRole h r ∧
      rho.releases (rho.key k) (Obj.mk (.signed k r) (.item h) cs) τ

/-- Header `h` is in the `g`-read, at the end of time `t`, of every node ready
at `t` with catch-up `c`. -/
def InBy (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (h : Header Info) (t : Time) :
    Prop :=
  ∀ v, rho.point.Ready c v t → h ∈ (chainTrace rho).readAt g v t

/-- Reader-conditional: for every `t ≥ start` (with `t + D·ΔAC` in the
horizon) at which some node is ready at the inclusion deadline `t + D·ΔAC`, a
header released after `t`, at `τ`, by a key ready at `τ` in a proposal role, is
in every ready read by `t + D·ΔAC`. `τ` is not bounded above: the obligation is
the inclusion by `t + D·ΔAC`, not the release time. Reader-conditional as L0
`TxLive`, which has no obligation without a ready reader: under churn that
lets nobody be ready (e.g. a different validator asleep at each tick), no
ready proposer can be demanded. -/
def ProposalLiveReady (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time)
    (D : Nat) : Prop :=
  ∀ t, start ≤ t → t + (D : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready c v (t + (D : Time) * E.ΔAC)) →
    ∃ τ k h, t < τ ∧ rho.point.Ready c (rho.key k) τ ∧
      HonestProposal rho τ k h ∧ InBy rho c g h (t + (D : Time) * E.ΔAC)

/-- Output validity of `g`: every read at every cut at which its reader is honest
is linked from the
root under the run's hash, has increasing positions, and every header in it
was seen by the reader as an item signed in a proposal role. Unconditional
(holds even with collisions). No slot-time clause: poll positions are
heights, and the transaction bridge never uses it. -/
def OutputValid (rho : Model.Run (compiled F) E) (g : O.Id) : Prop :=
  ∀ v i, i ≤ rho.events.length → rho.point.HonestAt v (rho.cutTime i) →
    Chain.Linked rho.hash ((chainTrace rho).read g v i) ∧
    Chain.PosIncreasing ((chainTrace rho).read g v i) ∧
    Chain.Provenant (rho.ViewIdx v i) ProposalRole ((chainTrace rho).read g v i)

/-- The requirement `π` with catch-up `c` on `[start, stop]` at point `p`, PKI
`key` and selection `sel` of family `F`: pattern recurrence over the proposer
roles of the grid, or at most `m` validators not ready. A shape without slot
proposers (`proposerSel := fun _ => .fixed ∅`, e.g. a poll shape) never meets a
recurrence with a window inside `[start, stop]` (`HonestReadyIn` needs a
nonempty selection); the shape obligations therefore require `.recur` only of shapes
with one proposer per slot (`ProgressFits`). -/
def shapeHolds (F : ChainShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V] :
    ProgressReq → Time → Time → Time → (p : EnvPoint V) →
      (sysExternal O (compiled F) V).Ext p.env → Prop
  | .recur ρ, c, s, e, p, x =>
    PatternRecurrence p x.1 (fun s => x.2 (ShapeRole.proposer s)) (F (pubOf p.env)).skel.grid ρ
      c s e
  | .notReadyAtMost m, c, s, e, p, _ => NotReadyOn p m c s e

/-- The shape's progress reader: the model's external data (PKI and
selection) with `shapeHolds`. -/
def shapeProgress (F : ChainShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    Progress (Sys F V) ProgressReq where
  toExternal := sysExternal O (compiled F) V
  holds := shapeHolds F
  mono := by
    intro π c s s' e e' p x hs he h
    cases π with
    | recur ρ =>
      exact fun t ht hst hh => h t (le_trans (max_le_max hs le_rfl) ht) (le_trans hst he) hh
    | notReadyAtMost m =>
      exact fun t ht hst hh => h t (le_trans (max_le_max hs le_rfl) ht) (le_trans hst he) hh
  shrink := by
    intro π c s e p x b hb h
    cases π with
    | recur ρ =>
      intro t ht hst hh
      obtain ⟨s, h1, h2, h3⟩ := h t ht hst (le_trans hh hb)
      refine ⟨s, h1, h2, fun j hj => ?_⟩
      obtain ⟨hne, hk⟩ := h3 j hj
      exact ⟨hne, fun k hk' => ⟨(hk k hk').1, fun hf =>
        (hk k hk').2 (p.faultyAt_mono (min_le_min_left _ hb) hf)⟩⟩
    | notReadyAtMost m => exact fun t ht hst hh => h t ht hst (le_trans hh hb)

  submit_irrel := by
    intro π c s e p x σ h
    cases π <;> exact h

end Consensus.Shape

end
