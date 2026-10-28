module
public import ConsensusShape.Compile
public import ConsensusModelProofs

@[expose] public section

/-! # Shape vocabulary over compiled runs (layer 1)

For a run of a compiled shape family: the chain trace (what each node's
output chains are at each event cut, with the run's environment point and cut
times), honest proposals (a header released by an honest key in a proposal
role, at its release time), inclusion by a time, the liveness obligation
`ProposalLive` (D-14), output validity (linkage, increasing positions,
provenance), and the shape's interpretation of the `progress` premise atom
(pattern recurrence over the proposer roles of the grid). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf modelProfile)

/-! ## Engine facts used by the shape layer (any model family) -/

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {G : Model.Family O}
  {E : Env V}

omit [DecidableEq V] in
/-- A signed candidate comes from a due duty of its role, whose message and
carried objects it is. -/
theorem candidates_duty (rho : Model.Run G E) (st : (protoOf G E).State) (v : V) (t : Time)
    {a : Model.Auth (Fintype.card V) (protoOf G E).Role} {m cs}
    (ho : Obj.mk a m cs ∈ rho.candidates st v t) {k r} (ha : a = .signed k r) :
    ∃ d ∈ (protoOf G E).duties t, (protoOf G E).role d = r ∧
      (protoOf G E).act st d = some (m, cs) := by
  subst ha
  unfold Model.Run.candidates at ho
  rcases List.mem_append.mp ho with hs | hg
  · obtain ⟨d, hd, hm⟩ := List.mem_flatMap.mp hs
    cases hact : (protoOf G E).act st d with
    | none => simp [hact] at hm
    | some mc =>
      obtain ⟨m', cs'⟩ := mc
      rw [hact] at hm
      dsimp only at hm
      split at hm
      · rcases List.mem_singleton.mp hm with he
        injection he with h₁ h₂ h₃
        injection h₁ with _ hr
        cases h₂
        cases h₃
        exact ⟨d, hd, hr.symm, hact⟩
      · cases hm
  · obtain ⟨mc, _, he⟩ := List.mem_map.mp hg
    injection he with h₁
    cases h₁

/-- A released object is a candidate of the releasing tick, built from the
post-clock state, whose mempool is the node's mempool at the tick. -/
theorem releases_candidate (rho : Model.Run G E) {u : V} {o : (protoOf G E).Object} {τ : Time}
    (h : rho.releases u o τ) :
    ∃ st : (protoOf G E).State,
      o ∈ rho.candidates ((protoOf G E).clock st τ (Model.mempool rho.inbox u τ)) u τ := by
  obtain ⟨i, hi, ho⟩ := h
  simp only [Model.Run.releasesAt, hi] at ho
  unfold Model.Run.tick at ho
  split at ho
  · exact ⟨_, Model.releaseAll_subset _ _ _ _ o ho⟩
  · simp at ho

end Engine

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The start time of slot `s` in the run's environment. -/
def slotTime (_rho : Model.Run (compiled F) E) (s : Slot) : Time :=
  (F (pubOf E)).skel.grid.slotTime E.Δ s

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

/-- A slot proposal is released at its slot time. -/
theorem slotProposal_time (rho : Model.Run (compiled F) E) {u : V} {k : Fin (Fintype.card V)}
    {s : Slot} {h : Header Info} {cs} {τ : Time}
    (hr : rho.releases u (Obj.mk (.signed k (ShapeRole.proposer s)) (.item h) cs) τ) :
    τ = slotTime rho s := by
  obtain ⟨st, hc⟩ := releases_candidate rho hr
  obtain ⟨d, hd, hrole, -⟩ := candidates_duty rho _ u τ hc rfl
  have ht := ((protoOf (compiled F) E).duties_spec d τ).mp hd
  cases d with
  | propose s' _ =>
    change ShapeRole.proposer s' = ShapeRole.proposer s at hrole
    cases hrole
    exact ht.symm
  | act s' k' => cases hrole
  | pollPropose _ => cases hrole
  | poll _ => cases hrole

/-- Header `h` is in the `g`-read, at the end of time `t`, of every node ready
at `t` with catch-up `c`. -/
def InBy (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (h : Header Info) (t : Time) :
    Prop :=
  ∀ v, rho.point.Ready c v t → h ∈ (chainTrace rho).readAt g v t

/-- D-14: for every `t ≥ start` (with `t + D·Δ` in the horizon), a header
released after `t`, at `τ`, by a key ready at `τ` in a proposal role, is in every
ready read by `t + D·Δ`. -/
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

/-- The shape's interpretation of `progress`: pattern recurrence over the
proposer roles of the grid, at the run's point, PKI and selection. -/
def shapeExec (F : ShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    ExecProfile (sysOf O (compiled F) V) ProgressReq :=
  modelProfile O (compiled F) V fun π c start r =>
    PatternRecurrence (R := ShapeRole (F (pubOf r.1)).skel.Kind) r.2.point r.2.key r.2.sel
      ShapeRole.proposer (F (pubOf r.1)).skel.grid π c start

/-- Shape premises are layer-0 premises evaluated on the compiled run. -/
abbrev ShapePremise (K : Contract O ProgressReq) (P : Premise ProgressReq) (σ : Nat → Time)
    (rho : Model.Run (compiled F) E) : Prop :=
  P.eval (sysOf O (compiled F) V) (shapeExec F V) K.catchUp σ ⟨E, rho⟩

/-- The premise bridge: a shape premise is, by definition, the layer-0
evaluation on the compiled system. -/
theorem premiseBridge (K : Contract O ProgressReq) (P : Premise ProgressReq) (σ : Nat → Time)
    (rho : Model.Run (compiled F) E) :
    ShapePremise K P σ rho ↔ P.eval (sysOf O (compiled F) V) (shapeExec F V) K.catchUp σ ⟨E, rho⟩ :=
  Iff.rfl

end Consensus.Shape

end
