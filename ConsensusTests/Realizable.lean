module
public import ConsensusTests.Shape
public import ConsensusTests.Common
public import ConsensusTests.Good
public import ConsensusTests.Controls
public import ConsensusInstances
public import Mathlib.Tactic
@[expose] public section

/-! # Coverage and progress-fit tests

* `coverage_keeps_selection`: `coverage` at a 3-node point with a selection
  that is *not* the extremal one (the proposer of every slot is key 2) returns
  a valid, collision-free run with exactly that selection, for every GST.
* `allProposers_no_witness`: a family whose proposer selection is
  `.sized (max 1 n)` selects every key at every slot of a valid run, so on a
  run with a faulty validator its pattern recurrence fails as soon as one
  whole window fits in `[start, stop]` and the horizon: such a progress
  requirement has no witness with a faulty validator.
  (`allProposers_unfit`, `noProgressFit_contract`: acceptance rejects such
  requirements up front; see `Vacuity.lean`.)
* Rotating sleeper: four honest validators, a different one
  asleep at each tick, catch-up `3`: more than ⅔ awake at every tick
  (but not healthy: not every honest validator is awake), and nobody is ready from
  `3` on. `rotating_notReadyOn_false`: the not-ready bound fails
  for `m < 4` (nobody is ready); `rotating_notReadyOn_trivial`: it holds
  trivially for `m ≥ 4`;
  `rotating_proposalLive_vacuous`: the reader-conditional liveness the shape
  claims use owes nothing there, so no family is refuted by it.
* `tendermint_largeIdx_prog`: with a fixed population
  `Fin 5`, the Tendermint requirement at every index `m ≥ 5` holds on every
  run, so a large index never makes the contract unrealizable.
* Late witnesses: `healed_witness_late` — every good
  system has, at `Δ = 7` and GST `1000`, a clean healthy witness whose log has
  no receipt before `1000`, with progress, liveness and safety active after a
  heal point at or after `1000`; `outage_witness_late` — an active outage armed
  at or after `1000·Δ`. `healed_witness_late_control`,
  `outage_witness_late_control`: the same for the positive-control family
  (`Controls.lean`), so neither is vacuous. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- Without a ready node from `start + D·Δ` on, the reader-conditional
obligation is vacuous. -/
theorem ProposalLiveReady.of_noReady {rho : Model.Run (compiled F) E} {c : Time} {g : O.Id}
    {start : Time} {D : Nat}
    (h : ∀ t, start + (D : Time) * E.Δ ≤ t → ∀ v, ¬ rho.point.Ready c v t) :
    ProposalLiveReady rho c g start D := by
  rintro t hs - ⟨v, hv⟩
  exact absurd hv (h _ (by linarith) v)

end Consensus.Shape

namespace Consensus.Shape.Tests.Realizable
open Consensus Blocks Shape
open Consensus.Model (Public Key pubOf protoOf sysOf)
open Consensus.Shape.Tests.Shapes (trivialFamily pollSkel pollShape)

/-- Three validators, validator 0 faulty, everyone awake, `Δ = 1`, horizon
10, no submissions. -/
def point3 : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ.erase 0, 10, fun _ _ => []⟩

/-- Key 2 proposes at every slot; every key signs the committee kind; nobody
polls. -/
def sel3 : ShapeRole Unit → Finset (Fin (Fintype.card (Fin 3)))
  | .proposer _ => {⟨2, by simp⟩}
  | .duty _ _ => Finset.univ
  | .poll => ∅

theorem sel3_admits :
    ∀ r, ((protoOf (compiled trivialFamily) point3.env).selSpec r).Admits (sel3 r) := by
  intro r
  cases r with
  | proposer s =>
    change ({⟨2, by simp⟩} : Finset (Fin (Fintype.card (Fin 3)))).card =
      min 1 (Fintype.card (Fin 3))
    simp
  | duty s k => rfl
  | poll => rfl

/-- Coverage keeps a non-extremal selection, for every GST. -/
theorem coverage_keeps_selection (g : Time) :
    ∃ rho : Model.Run (compiled trivialFamily) point3.env, rho.point = point3 ∧
      rho.key = (pkiFin 3) ∧ rho.sel = sel3 ∧ rho.sel (ShapeRole.proposer 7) = {⟨2, by simp⟩} ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨rho, hp, hk, hs, hv, hn, -, he⟩ :=
    coverage trivialFamily point3 (show (0 : Time) ≤ 10 by norm_num) (pkiFin 3) sel3 sel3_admits g
  exact ⟨rho, hp, hk, hs, by rw [hs]; rfl, hv, hn, he⟩

/-- Review B2 regression: with `proposerSel := .sized (max 1 n)` every key is
selected at every slot of a valid run, so a faulty validator is always among
the proposers and `PatternRecurrence` (every selected key honest and ready)
fails whenever one window fits in the horizon. -/
theorem allProposers_no_witness {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E)
    (hsel : rho.SelValid) (hf : rho.point.faulty.Nonempty) (π : Recurrence) (c start stop : Time)
    (hs : max start 0 + (π.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ ≤ stop)
    (hw : max start 0 + (π.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ ≤ rho.horizon) :
    ¬ PatternRecurrence rho.point rho.key (fun s => rho.sel (ShapeRole.proposer s))
      (F (pubOf E)).skel.grid π c start stop := by
  intro h
  obtain ⟨f, hf⟩ := hf
  have hfh : f ∉ rho.honest := (Finset.mem_sdiff.mp hf).2
  obtain ⟨s, -, -, hall⟩ := h (max start 0) le_rfl hs hw
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ π.pattern.nonempty
  have hadm := hsel (ShapeRole.proposer (s + j))
  change ((F (pubOf E)).skel.proposerSel).Admits (rho.sel (ShapeRole.proposer (s + j))) at hadm
  rw [hF] at hadm
  change (rho.sel (ShapeRole.proposer (s + j))).card = min (max 1 (Fintype.card V))
    (Fintype.card V) at hadm
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨f⟩
  rw [max_eq_right hn, min_self] at hadm
  have huniv : rho.sel (ShapeRole.proposer (s + j)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hadm, Fintype.card_fin])
  have hk : rho.key.symm f ∈ rho.sel (ShapeRole.proposer (s + j)) := by
    rw [huniv]; exact Finset.mem_univ _
  have := ((hall j hj).2 _ hk).1
  rw [Equiv.apply_symm_apply] at this
  exact hfh this

section Rotating

open Consensus.Shape.Tests.Good (rotPoint healthy_rotating_sleeper)

/-- Below the validator count (`m < 4`) the not-ready bound fails on the
rotating sleeper, on any window `[start, stop]` with `max start 0 ≤ 3 ≤ stop`:
nobody is ready at `3`. -/
theorem rotating_notReadyOn_false {m : Nat} (hm : m < 4) {start stop : Time}
    (hs : max start 0 ≤ 3) (he : 3 ≤ stop) : ¬ NotReadyOn rotPoint m 3 start stop := by
  intro h
  have hne := h.readyAt_nonempty (by simpa using hm) hs he (by decide)
  rw [healthy_rotating_sleeper.2.2 3 le_rfl] at hne
  exact Finset.not_nonempty_empty hne

/-- From the validator count on (`m ≥ 4`) the bound holds trivially, even on
the rotating sleeper; what keeps it harmless is that the liveness it feeds is
reader-conditional (`rotating_proposalLive_vacuous`). -/
theorem rotating_notReadyOn_trivial {m : Nat} (hm : 4 ≤ m) (start stop : Time) :
    NotReadyOn rotPoint m 3 start stop :=
  NotReadyOn.of_card_le (by simpa using hm)

/-- Reader-conditional proposal liveness is vacuous on the rotating sleeper
from `3` on, for every family and run with that point: the shape claims
demand no ready proposer where nobody is ready. -/
theorem rotating_proposalLive_vacuous {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info] (F : ShapeFamily O Info) {E : Env (Fin 4)} (rho : Model.Run (compiled F) E)
    (hp : rho.point = rotPoint) (g : O.Id) {start : Time} (hs : 3 ≤ start) (D : Nat) :
    ProposalLiveReady rho 3 g start D := by
  apply ProposalLiveReady.of_noReady
  intro t ht v hv
  have hD : (0 : Time) ≤ (D : Time) * E.Δ := mul_nonneg (by positivity) E.Δ_pos.le
  have hmem : v ∈ rotPoint.readyAt 3 t := by
    rw [← hp]
    classical
    unfold EnvPoint.readyAt
    exact Finset.mem_filter.mpr ⟨hv.1, hv⟩
  rw [healthy_rotating_sleeper.2.2 t (by linarith)] at hmem
  exact Finset.notMem_empty _ hmem

end Rotating

section LargeIndex

/-- Review 3b r2 B1 (positive regression): for a fixed population (`Fin 5`)
and a Tendermint index at least the population (`m = 5`, and every larger
one), the progress requirement holds on every run of every family, window and
catch-up. L0 `Realizable` fixes `V` before the index, so no not-ready index of
an unbounded contract may be unsatisfiable. -/
theorem tendermint_largeIdx_prog (F : ShapeFamily bftCore Unit) (catchUp : Nat)
    (heal latency : Affine) (cap : Capability) (m : ℕ+) (hm : 5 ≤ (m : Nat))
    (r : (sysOf bftCore (compiled F) (Fin 5)).Run) (start stop : Time) :
    (sysOf bftCore (compiled F) (Fin 5)).prog (shapeProgress F (Fin 5))
      (tendermintContract catchUp heal latency) cap m start stop r :=
  NotReadyOn.of_card_le (by simpa using hm)

/-- The concrete counterexample of the rotating-sleeper case: `V = Fin 5`, `m = 5`. -/
example (F : ShapeFamily bftCore Unit) (cap : Capability)
    (r : (sysOf bftCore (compiled F) (Fin 5)).Run) (start stop : Time) :
    (sysOf bftCore (compiled F) (Fin 5)).prog (shapeProgress F (Fin 5))
      (tendermintContract 1 ⟨0, 0⟩ ⟨0, 0⟩) cap (5 : ℕ+) start stop r :=
  tendermint_largeIdx_prog F 1 _ _ cap 5 le_rfl r start stop

end LargeIndex

section Late

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/-- A late GST at a large `Δ`: every realizable system (so every good system
with at least five validators, `Good.realizable`) has, at `Δ = 7` and GST
`1000`, a clean healthy witness with no receipt before `1000`, whose heal
point is at or after `1000`, with progress from `ready`, and liveness and
safety active after the heal point. -/
theorem healed_witness_late (h : Realizable S X K) (cap : Capability)
    (i : K.Idx) :
    ∃ r, S.Witness r ∧ (S.pt r).env.Δ = 7 ∧ (∀ w m t, (S.log r).recv w m t → 1000 ≤ t) ∧
      S.Healthy K 1000 r ∧ 1000 ≤ S.heal K cap i 1000 r ∧
      S.prog X K cap i (S.ready K 1000 r) (S.pt r).horizon r ∧
      (S.pt r).TxLiveActive (S.cDur K r) (S.heal K cap i 1000 r) (S.lat K cap i r) ∧
      SafeActive (S.cDur K r) (S.heal K cap i 1000 r) (S.pt r) := by
  obtain ⟨r, hw, hΔ, ⟨he, hH, hp, ht⟩, hs⟩ :=
    h.healthy cap i 7 1000 (by norm_num) (by norm_num)
  refine ⟨r, hw, hΔ, he.quiet, hH, ?_, hp, ht, hs⟩
  unfold System.heal
  rw [hΔ]
  have : (0 : Time) ≤ (K.params.heal cap i : Time) * 7 := by positivity
  have h1 : (1000 : Time) ≤ max 1000 0 := le_max_left _ _
  linarith

/-- An arbitrarily late outage: every realizable system has, at `Δ = 7`, a
clean witness of an active outage armed at or after `1000·Δ`. -/
theorem outage_witness_late (h : Realizable S X K) :
    ∃ r T b₀ b₁, S.Witness r ∧ (S.pt r).env.Δ = 7 ∧ S.Outage K T b₀ b₁ r ∧
      OutageActive (S.cDur K r) T b₀ b₁ (S.pt r) ∧ 7000 ≤ T := by
  obtain ⟨r, T, b₀, b₁, hw, hΔ, ho, ha, hT⟩ := h.outage 7 1000 (by norm_num)
  exact ⟨r, T, b₀, b₁, hw, hΔ, ho, ha, by norm_num at hT; exact hT⟩

/-- Every good system with at least five validators has both late witnesses. -/
example (h : Good S X K) (h5 : 5 ≤ Fintype.card V) (cap : Capability) (i : K.Idx) :
    (∃ r, S.Witness r ∧ (S.pt r).env.Δ = 7 ∧ 1000 ≤ S.heal K cap i 1000 r ∧
      SafeActive (S.cDur K r) (S.heal K cap i 1000 r) (S.pt r)) ∧
    ∃ r T b₀ b₁, S.Witness r ∧ S.Outage K T b₀ b₁ r ∧ 7000 ≤ T := by
  obtain ⟨r, hw, hΔ, -, -, hh, -, -, hs⟩ := healed_witness_late (h.realizable h5) cap i
  obtain ⟨r', T, b₀, b₁, hw', -, ho, -, hT⟩ := outage_witness_late (h.realizable h5)
  exact ⟨⟨r, hw, hΔ, hh, hs⟩, r', T, b₀, b₁, hw', ho, hT⟩

open Consensus.Shape.Tests.Controls (ctrlFamily ctrlK ctrl_realizable)

/-- `healed_witness_late` at the positive-control family. -/
theorem healed_witness_late_control (cap : Capability) :
    ∃ r, (sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).Witness r ∧
      ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).pt r).env.Δ = 7 ∧
      (∀ w m t, ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).log r).recv w m t →
        1000 ≤ t) ∧
      (sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).Healthy ctrlK 1000 r ∧
      SafeActive ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).cDur ctrlK r)
        ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).heal ctrlK cap (1 : ℕ+) 1000 r)
        ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).pt r) := by
  obtain ⟨r, hw, hΔ, hq, hH, -, -, -, hs⟩ := healed_witness_late ctrl_realizable cap (1 : ℕ+)
  exact ⟨r, hw, hΔ, hq, hH, hs⟩

/-- `outage_witness_late` at the positive-control family. -/
theorem outage_witness_late_control :
    ∃ r T b₀ b₁, (sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).Witness r ∧
      ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).pt r).env.Δ = 7 ∧
      (sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).Outage ctrlK T b₀ b₁ r ∧
      OutageActive ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).cDur ctrlK r) T b₀ b₁
        ((sysOf goldilocksSchema (compiled ctrlFamily) (Fin 5)).pt r) ∧ 7000 ≤ T :=
  outage_witness_late ctrl_realizable

end Late

end Consensus.Shape.Tests.Realizable

end
