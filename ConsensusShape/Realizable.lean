module
public import ConsensusShape.Refinement
public import Mathlib.Tactic

@[expose] public section

/-! # Coverage, the extremal selection and generic realizability (L2)

* `coverage` (fixed selection): any well-formed environment point, with any
  PKI, any admissible selection and any GST `g`, is exactly the point, PKI and
  selection of a valid, collision-free, conviction-free compiled run whose log
  is eager from `g`. Progress requirements read only the point, the PKI and
  the selection, so whatever progress holds there holds on that run.
* The extremal selection (`extremalSel`) gives every `.sized m` role (`m`
  below the population) the keys `1, …, m`; a `.sized 1` proposer role selects
  exactly key `1` (`extremalSel_proposer_mem`), honest when only key `0` is
  faulty.
* `Contract.ProgressFits`: a recurrence requirement needs one proposer per
  slot (`.sized 1`).
* Generic realizability (`regimes_realizable`, `realizable_active`): L0
  `Realizable` for every family whose progress fits its skeleton, every
  admissible contract and at least five validators, with active progress
  windows (`ProgressActive`). Witnesses: `sleepy_witness`,
  `healthy_witness`, `outage_witness`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-! ## Fixed-selection coverage -/

/-- Fixed-selection coverage. Inputs are fixed, outputs preserve them: the
point `p`, the PKI `key`, an admissible selection `sel`, and a GST `g`. Some
valid, collision-free, conviction-free compiled run has exactly that point,
PKI and selection, and its log is eager from `g`. -/
theorem coverage (F : ShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V]
    (p : EnvPoint V) (hp : p.WellFormed) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf (compiled F) p.env).selSpec r).Admits (sel r)) (g : Time) :
    ∃ rho : Model.Run (compiled F) p.env, rho.point = p ∧ rho.key = key ∧ rho.sel = sel ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
      (sysOf O (compiled F) V).convicted ⟨p.env, rho⟩
        ((sysOf O (compiled F) V).honestEvidence ⟨p.env, rho⟩) = ∅ ∧
      CommLog.EagerFrom rho.point rho.log g := by
  let hash : (protoOf (compiled F) p.env).Item → Nat := fun x => Encodable.encode x + 1
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.honest p.horizon hp key sel hsel
      p.submit hash g
  let rho := Model.mkRun (F := compiled F) (E := p.env) p.honest p.horizon key sel p.submit
    relay hash events
  refine ⟨rho, rfl, rfl, rfl, hv, ?_, ?_, he⟩
  · apply Model.Run.not_hashCollision_of_injective
    intro a b hab
    exact Encodable.encode_injective (Nat.add_right_cancel hab)
  · exact Model.convicted_honestEvidence_eq_empty rho (rho.not_slashable_of_causal hv hc)

/-! ## The extremal selection -/

/-- An admissible key set for each selection specification on `Fin N`:
everybody, the fixed set, or the keys `1, …, m` for `.sized m` with `m < N`
(everybody otherwise). Key `0` is selected only when a specification forces
it. -/
def extremalKeys {N : Nat} : SelSpec N → Finset (Fin N)
  | .all => Finset.univ
  | .fixed T => T
  | .sized m => if m < N then Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m else Finset.univ

theorem extremalKeys_admits {N : Nat} (s : SelSpec N) : s.Admits (extremalKeys s) := by
  cases s with
  | all => rfl
  | fixed T => rfl
  | sized m =>
    change (if m < N then Finset.univ.filter (fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m)
      else Finset.univ).card = min m N
    split_ifs with hm
    · rw [min_eq_left hm.le]
      have : (Finset.univ.filter fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m).map Fin.valEmbedding =
          Finset.Icc 1 m := by
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Icc]
        constructor
        · rintro ⟨k, hk, rfl⟩; exact hk
        · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
      rw [← Finset.card_map, this, Nat.card_Icc]; omega
    · rw [Finset.card_univ, Fintype.card_fin, min_eq_right (by omega)]

/-- The extremal PKI on `Fin (n + 1)`: key `k` is validator `k`. -/
def extremalKey (n : Nat) : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
  finCongr (Fintype.card_fin _)

/-- The extremal selection: `extremalKeys` of every role's specification. -/
def extremalSel (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => extremalKeys ((protoOf (compiled F) E).selSpec r)

theorem extremalSel_admits (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    ∀ r, ((protoOf (compiled F) E).selSpec r).Admits (extremalSel F E r) :=
  fun _ => extremalKeys_admits _

/-- The relay is exercised: in a run partially synchronous with a GST at or
before `start` where every validator is always awake, an active liveness
witness (`TxLiveActive`) has an honest reader that receives the submitted
transaction by relay, never by its own submission. -/
theorem active_relay {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (rho : Model.Run (compiled F) E) {gst c start D : Time}
    (hs : CommLog.PSync rho.point rho.log gst) (hgs : gst ≤ start) (hD : 0 ≤ D)
    (hawake : ∀ v t, E.awake v t = true)
    (ha : ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive c start D) :
    ∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hw, -, hnw, hdl, hth, -⟩ := ha
  change u ∈ rho.honest at hu
  change w ∈ rho.honest at hw
  change x ∈ rho.submit u t at hx
  change ∀ τ, x ∉ rho.submit w τ at hnw
  change max t start + E.Δ + D ≤ t' at hdl
  change t' ≤ rho.horizon at hth
  have hm : max t gst ≤ max t start := max_le_max le_rfl hgs
  have hd : max t gst + E.Δ ≤ rho.horizon := by linarith
  obtain ⟨τ, hτ, -, hxτ⟩ := hs.txs u hu x t ht0 hua hx w hw t le_rfl hd hd (hawake w _)
  refine ⟨x, w, hw, hnw, τ, hτ, ?_⟩
  rcases List.mem_append.mp hxτ with h | h
  · exact absurd h (hnw τ)
  · exact h

/-! ## Progress fit -/

/-- A progress requirement fits a skeleton: a recurrence needs one proposer
per slot (`.sized 1`, independent of the population: with every key selected,
a faulty validator is always among the proposers and recurrence has no witness,
`allProposers_no_witness`); a bound on the validators not ready fits every
skeleton. -/
def _root_.Consensus.Blocks.ProgressReq.Fits {n : Nat} (sk : Skeleton n) : ProgressReq → Prop
  | .recur _ => sk.proposerSel = .sized 1
  | .notReadyAtMost _ => True

/-- Every progress requirement of the contract fits the family's skeleton at
every public parameter. -/
def _root_.Consensus.Contract.ProgressFits (K : Contract O ProgressReq)
    (F : ShapeFamily O Info) : Prop :=
  ∀ cap i pub, (K.progress cap i).Fits (F pub).skel

/-! ## Generic realizability

`realizable_active`: for every family whose progress fits its skeleton and
every admissible contract, with at least five validators, every regime of the
L0 table is met by a clean witness with active claims, at every `Δ`, every
GST and arbitrarily late outages; in addition, every progress window of the
sleepy and healthy witnesses lies inside the horizon (`ProgressActive`).

The witnesses: validator `key 0` faulty, every other validator honest; the
PKI `Fintype.equivFin`; the extremal selection (`.sized 1` proposer roles
select key `1`, honest and always awake); transaction `42` submitted to
`key 1` at time `0`, read by `key 2`.

* sleepy and healthy: everyone awake (for healthy, the fixed set is all the
  honest validators, awake throughout); the healthy witness is the canonical
  run from the GST `g`, whose log has no message receipt before `g` (protocol
  messages sent before `g` are received at `g` by the recipients awake then;
  transaction relay is part of the log too). The witness exercises delayed
  delivery only as far as the family sends messages before `g`;
* outage: honest `key 2` asleep exactly at `b₀`, so at most two validators
  are not ready at any time; with `n ≥ 5`, `n/2 < n − 2` gives the cover at
  `b₀` and η-sleepy participation for every look-back `η` (the look-back set
  has at most `n` members); this is where five validators are needed. The log
  is eager from `0`: the outage witness exercises participation (one honest
  sleeper in the window), not asynchrony.

Thresholds are proved at the standard bounds (`θ ≤ ½`, `φ ≤ ⅔`,
`cover ≤ ½`), which `Params.Admissible` guarantees. -/

section Realize

variable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The length of one window of the progress requirement of `cap` at `i` on
the grid at `Δ`, pattern span included (`0` for a bound on the validators
not ready). -/
def progLen (cap : Capability) (i : K.Idx) (E : Env V) : Time :=
  match K.progress cap i with
  | .recur ρ => (ρ.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ
  | .notReadyAtMost _ => 0

omit [DecidableEq V] in
theorem progLen_nonneg (cap : Capability) (i : K.Idx) (E : Env V) : 0 ≤ progLen F K cap i E := by
  unfold progLen
  split
  · exact mul_nonneg (by positivity) ((F (pubOf E)).skel.grid.slotLen_pos E.Δ_pos).le
  · exact le_rfl

/-- The progress requirement of `cap` at `i` is active from `start` (L2 only):
one whole window (with the pattern's span, for a recurrence) from
`max start 0` lies inside the horizon, so the requirement is not met
vacuously (`PatternRecurrence.exists_inside`; for a bound below the validator
count, `NotReadyOn.readyAt_nonempty`). -/
def ProgressActive (cap : Capability) (i : K.Idx) (start : Time) {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop :=
  max start 0 + progLen F K cap i E ≤ rho.horizon

/-- The sleepy and healthy regimes are realizable with active claims and
active progress windows (`ProgressActive`), and the outage regime as in L0
`Realizable`. Gives `Realizable` (`RealizableActive.toRealizable`). -/
structure RealizableActive (V : Type) [Fintype V] [DecidableEq V] : Prop where
  sleepyActive : ∀ cap i (Δ : Time), 0 < Δ → ∃ (E : Env V) (rho : Model.Run (compiled F) E),
    (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧ ShapeSleepy K rho ∧
      ShapeProg K rho cap i 0 rho.horizon ∧ ProgressActive F K cap i 0 rho ∧
      ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive (shapeC K rho) 0
        ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩)
  healthyActive : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g →
    ∃ (E : Env V) (rho : Model.Run (compiled F) E),
      (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧
      CommLog.EagerFrom ((sysOf O (compiled F) V).pt ⟨E, rho⟩)
        ((sysOf O (compiled F) V).log ⟨E, rho⟩) g ∧ ShapeHealthy K rho g ∧
      ShapeProg K rho cap i (shapeReady K rho g) rho.horizon ∧
      ProgressActive F K cap i (shapeReady K rho g) rho ∧
      ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive (shapeC K rho)
        (shapeHeal K rho cap i g) ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩) ∧
      SafeActive (shapeC K rho) (shapeHeal K rho cap i g) rho.point
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁,
    (sysOf O (compiled F) V).Witness r ∧ ((sysOf O (compiled F) V).pt r).env.Δ = Δ ∧
      (sysOf O (compiled F) V).Outage K T b₀ b₁ r ∧
      OutageActive ((sysOf O (compiled F) V).cDur K r) T b₀ b₁ ((sysOf O (compiled F) V).pt r) ∧
      (k : Time) * Δ ≤ T

/-- Active realizability gives L0 realizability. -/
theorem RealizableActive.toRealizable {V : Type} [Fintype V] [DecidableEq V]
    (h : RealizableActive F K V) : Realizable (sysOf O (compiled F) V) (shapeProgress F V) K where
  sleepy cap i Δ hΔ := by
    obtain ⟨E, rho, hw, hd, hs, hp, -, ht⟩ := h.sleepyActive cap i Δ hΔ
    exact ⟨⟨E, rho⟩, hw, hd, hs, hp, ht⟩
  healthy cap i Δ g hΔ hg := by
    obtain ⟨E, rho, hw, hd, he, hs, hp, -, ht, hsa⟩ := h.healthyActive cap i Δ g hΔ hg
    exact ⟨⟨E, rho⟩, hw, hd, he, hs, hp, ht, hsa⟩
  outage := h.outage

/-! ### The witness points -/

variable {F K}

/-- The witness point: `Δ`, awake profile `awake`, horizon `H`; validator
`key 0` faulty, every other validator honest; transaction `42` submitted to
`key 1` at time `0`. -/
def realPoint (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) (Δ : Time)
    (hΔ : 0 < Δ) (awake : V → Time → Bool) (H : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, awake⟩, Finset.univ.erase (key ⟨0, by omega⟩), H,
    fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩

/-- Everyone awake at every time. -/
def allAwake : V → Time → Bool := fun _ _ => true

/-- `s` asleep exactly at time `b`; everyone else always awake. -/
def sleepAt (s : V) (b : Time) : V → Time → Bool := fun v t => !(decide (v = s) && decide (t = b))

section Point

variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  (awake : V → Time → Bool) (H : Time)

/-- The validator of key `j`. -/
abbrev kv (j : Nat) (hj : j < 5) : V := key ⟨j, by omega⟩

omit [DecidableEq V] in
theorem kv_ne {j j' : Nat} {hj : j < 5} {hj' : j' < 5} (h : j ≠ j') :
    kv key hn j hj ≠ kv key hn j' hj' := by
  intro he
  have := congrArg Fin.val (key.injective he)
  exact h this

theorem realPoint_faulty : (realPoint key hn Δ hΔ awake H).faulty = {kv key hn 0 (by decide)} := by
  ext v; simp [EnvPoint.faulty, realPoint]

theorem realPoint_honest {j : Nat} (hj : j < 5) (h0 : j ≠ 0) :
    kv key hn j hj ∈ (realPoint key hn Δ hΔ awake H).honest :=
  Finset.mem_erase.mpr ⟨kv_ne key hn (hj' := by decide) h0, Finset.mem_univ _⟩

theorem realPoint_card_honest :
    (realPoint key hn Δ hΔ awake H).honest.card + 1 = Fintype.card V := by
  change (Finset.univ.erase _).card + 1 = _
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  omega

/-- A set of honest, always-awake validators is ready at every time. -/
theorem card_le_readyAt (A : Finset V)
    (hA : ∀ v ∈ A, v ∈ (realPoint key hn Δ hΔ awake H).honest ∧ ∀ t, awake v t = true)
    (c t : Time) : A.card ≤ ((realPoint key hn Δ hΔ awake H).readyAt c t).card := by
  classical
  apply Finset.card_le_card
  intro v hv
  unfold EnvPoint.readyAt
  obtain ⟨hh, ha⟩ := hA v hv
  exact Finset.mem_filter.mpr ⟨hh, hh, fun u _ _ => ha u⟩

/-- Everyone awake: all honest validators are ready at every time. -/
theorem allAwake_readyAt (c t : Time) :
    Fintype.card V ≤ ((realPoint key hn Δ hΔ allAwake H).readyAt c t).card + 1 := by
  have := card_le_readyAt key hn hΔ allAwake H _ (fun v hv => ⟨hv, fun _ => rfl⟩) c t
  have := realPoint_card_honest key hn hΔ allAwake H
  omega

/-- One sleeper `key 2`: all honest validators but one are ready at every
time. -/
theorem sleepAt_readyAt (b c t : Time) :
    Fintype.card V ≤ ((realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b) H).readyAt
      c t).card + 2 := by
  have h2 : kv key hn 2 (by decide) ∈
      (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b) H).honest :=
    realPoint_honest key hn hΔ _ H (by decide) (by decide)
  have h := card_le_readyAt key hn hΔ (sleepAt (kv key hn 2 (by decide)) b) H
    ((realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b) H).honest.erase
      (kv key hn 2 (by decide))) (fun v hv => by
      obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
      exact ⟨hv, fun t => by simp [sleepAt, hne]⟩) c t
  rw [Finset.card_erase_of_mem h2] at h
  have := realPoint_card_honest key hn hΔ (sleepAt (kv key hn 2 (by decide)) b) H
  omega

include hn in
/-- The numbers: with `n ≥ 5`, one faulty and at most two not ready, the
sleepy threshold `θ ≤ ½` holds. -/
theorem readyAbove_of_card {p : EnvPoint V} {θ : ℚ} (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2) (c t : Time)
    (hf : p.faulty.card = 1) (hr : Fintype.card V ≤ (p.readyAt c t).card + 2) :
    p.ReadyAbove θ c t := by
  unfold EnvPoint.ReadyAbove
  rw [hf]
  have hr' : ((Fintype.card V : Nat) : ℚ) ≤ ((p.readyAt c t).card : ℚ) + 2 := by exact_mod_cast hr
  have hn' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  push_cast
  nlinarith [hθ.1, hθ.2]

include hn in
omit [DecidableEq V] in
theorem readyOfAll_of_card {p : EnvPoint V} {φ : ℚ} (hφ : 0 ≤ φ ∧ φ ≤ 1 / 2) (c t : Time)
    (hr : Fintype.card V ≤ (p.readyAt c t).card + 2) : p.ReadyOfAll φ c t := by
  unfold EnvPoint.ReadyOfAll
  have hr' : ((Fintype.card V : Nat) : ℚ) ≤ ((p.readyAt c t).card : ℚ) + 2 := by exact_mod_cast hr
  have hn' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  nlinarith [hφ.1, hφ.2]

include hn in
/-- The numbers: with `n ≥ 5` and at most two not ready, η-sleepy
participation `θ ≤ ½` holds for every look-back (the look-back set has at
most `n` members). -/
theorem etaReadyAbove_of_card {p : EnvPoint V} {θ : ℚ} (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2) (η c t : Time)
    (hr : Fintype.card V ≤ (p.readyAt c t).card + 2) : p.EtaReadyAbove θ η c t := by
  have hr' : ((Fintype.card V : Nat) : ℚ) ≤ ((p.readyAt c t).card : ℚ) + 2 := by exact_mod_cast hr
  have hn' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  have key : ∀ A : Finset V, θ * (A.card : ℚ) < (p.readyAt c t).card := fun A => by
    have hs : (A.card : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast Finset.card_le_univ _
    nlinarith [hθ.1, hθ.2]
  unfold EnvPoint.EtaReadyAbove
  split_ifs
  · exact (p.readyAbove_iff_union θ c t).mpr (key _)
  · exact key _

include hn in
omit [DecidableEq V] in
/-- The numbers: with `n ≥ 5` and one validator not in `A`, `φ ≤ ⅔` gives
`φ·n < |A|`. -/
theorem lt_card_of_card {A : Finset V} {φ : ℚ} (hφ : 0 ≤ φ ∧ φ ≤ 2 / 3)
    (hr : A.card + 1 = Fintype.card V) : φ * Fintype.card V < (A.card : ℚ) := by
  have hr' : (A.card : ℚ) + 1 = ((Fintype.card V : Nat) : ℚ) := by exact_mod_cast hr
  have hn' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  nlinarith [hφ.1, hφ.2]

end Point

/-! ### Progress at the witness points -/

omit [DecidableEq V] in
/-- Under the extremal selection, a `.sized 1` proposer role selects exactly
key `1`. -/
theorem extremalSel_proposer_mem (F : ShapeFamily O Info) {E : Env V}
    (hF : (F (pubOf E)).skel.proposerSel = .sized 1) (h2 : 2 ≤ Fintype.card V) (s : Slot)
    (k : Fin (Fintype.card V)) :
    k ∈ extremalSel F E (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔
      k.val = 1 := by
  change k ∈ extremalKeys (F (pubOf E)).skel.proposerSel ↔ _
  rw [hF]
  have h1 : 1 < Fintype.card V := by omega
  simp only [extremalKeys, h1, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

section Witnesses

variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  (H : Time)

/-- Everyone awake, a fitting progress requirement holds on every window under
the extremal selection: key `1` (honest, always awake) is the proposer of every
slot, and every honest validator is ready at every time. -/
theorem allAwake_holds (hf : K.ProgressFits F) (cap : Capability) (i : K.Idx)
    (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ allAwake H)
      (key, extremalSel F (realPoint key hn Δ hΔ allAwake H).env) := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ allAwake H).env)
  revert hfit
  cases K.progress cap i with
  | recur ρ =>
    intro hfit
    change (F _).skel.proposerSel = .sized 1 at hfit
    apply patternRecurrence_of_all hΔ
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    have hh := realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)
    exact ⟨hh, hh, fun _ _ _ => rfl⟩
  | notReadyAtMost m =>
    intro _ t _ _ _
    exact le_trans (allAwake_readyAt key hn hΔ H c t) (Nat.add_le_add_left m.pos _)

/-- Everyone awake: liveness is active from `start`, with transaction `42`
submitted to `key 1` at `0` and read by `key 2` at the horizon. -/
theorem allAwake_txLiveActive {α Id : Type} (tr : Trace V α Id)
    (hp : tr.point = realPoint key hn Δ hΔ allAwake H) (c start D : Time)
    (hH : max 0 start + Δ + D ≤ H) : tr.TxLiveActive c start D := by
  unfold Trace.TxLiveActive
  rw [hp]
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide), rfl, ?_,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide),
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide), fun _ _ _ => rfl⟩
  · simp [realPoint]
  · intro τ
    have : kv key hn 2 (by decide) ≠ kv key hn 1 (by decide) := kv_ne key hn (by decide)
    simp [realPoint, this]

/-- Everyone awake: safety is active after `t₀` (keys `1` and `2` ready at
`t₀ + 1`, key `1` again at `t₀ + 2`). -/
theorem allAwake_safeActive (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (realPoint key hn Δ hΔ allAwake H) := by
  have h1 := realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)
  have h2 := realPoint_honest key hn hΔ allAwake H (j := 2) (by decide) (by decide)
  exact ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, by linarith, hH,
    ⟨h1, fun _ _ _ => rfl⟩, ⟨h2, fun _ _ _ => rfl⟩, ⟨h1, fun _ _ _ => rfl⟩⟩

/-- The canonical run at a witness point, from GST `g`: valid, no collision,
and eager from `g`; its point, PKI and selection are the given ones
definitionally (`mkRun`). -/
theorem real_run (F : ShapeFamily O Info) (p : EnvPoint V) (hp : 0 ≤ p.horizon) (g : Time) :
    ∃ relay events,
      let rho := Model.mkRun (F := compiled F) (E := p.env) p.honest p.horizon key
        (extremalSel F p.env) p.submit relay (fun x => Encodable.encode x + 1) events
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨relay, events, hv, he, -⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.honest p.horizon hp key
      (extremalSel F p.env) (extremalSel_admits F p.env) p.submit
      (fun x => Encodable.encode x + 1) g
  refine ⟨relay, events, hv, ?_, he⟩
  apply Model.Run.not_hashCollision_of_injective
  intro a b hab
  exact Encodable.encode_injective (Nat.add_right_cancel hab)

/-- The sleepy witness: everyone awake, the synchronous canonical run, horizon
`H` long enough for one liveness deadline and one progress window. -/
theorem sleepy_witness (ha : K.params.Admissible) (hf : K.ProgressFits F) (cap : Capability)
    (i : K.Idx)
    (hH : Δ + K.params.latDur Δ cap i + progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ allAwake H).env,
      rho.point = realPoint key hn Δ hΔ allAwake H ∧ rho.key = key ∧
      (sysOf O (compiled F) V).Witness ⟨_, rho⟩ ∧ ShapeSleepy K rho ∧
      ShapeProg K rho cap i 0 rho.horizon ∧ ProgressActive F K cap i 0 rho ∧
      ((sysOf O (compiled F) V).trace ⟨_, rho⟩).TxLiveActive (shapeC K rho) 0
        ((sysOf O (compiled F) V).lat K cap i ⟨_, rho⟩) := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
  have hlat : 0 ≤ K.params.latDur Δ cap i := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨relay, events, hv, hnc, he⟩ := real_run key F (realPoint key hn Δ hΔ allAwake H) hH0 0
  refine ⟨Model.mkRun (F := compiled F) (E := (realPoint key hn Δ hΔ allAwake H).env)
    (realPoint key hn Δ hΔ allAwake H).honest H key
    (extremalSel F (realPoint key hn Δ hΔ allAwake H).env)
    (realPoint key hn Δ hΔ allAwake H).submit relay (fun x => Encodable.encode x + 1) events,
    rfl, rfl, ⟨hv, hnc, ?_, ?_⟩, ⟨(Model.sysOf_eagerFrom _ he).psync le_rfl, ?_⟩,
    allAwake_holds key hn hΔ H hf cap i _ _ _, ?_, ?_⟩
  · change (realPoint key hn Δ hΔ allAwake H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)⟩
  · intro t _ _
    refine readyAbove_of_card hn ha.θ_range _ t ?_ ?_
    · change (realPoint key hn Δ hΔ allAwake H).faulty.card = 1
      rw [realPoint_faulty]; rfl
    · exact (allAwake_readyAt key hn hΔ H _ t).trans (Nat.le_succ _)
  · change max 0 0 + progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H
    simp only [max_self, zero_add]; linarith
  · refine allAwake_txLiveActive key hn hΔ H _ rfl _ _ _ ?_
    change max 0 0 + Δ + K.params.latDur Δ cap i ≤ H
    simp only [max_self, zero_add]; linarith

/-- The healthy witness at GST `g`: everyone awake (the fixed healthy set is
all the honest validators), the canonical run from `g` (no receipt before
`g`), horizon `H` long enough for one liveness deadline
after the heal point, two cuts after it, and one progress window from
`readyFrom`. -/
theorem healthy_witness (ha : K.params.Admissible) (hf : K.ProgressFits F) (cap : Capability)
    (i : K.Idx) (g : Time)
    (h1 : K.params.healPoint Δ cap i g + Δ + K.params.latDur Δ cap i ≤ H)
    (h2 : K.params.healPoint Δ cap i g + 2 ≤ H)
    (h3 : readyFrom (K.params.cDur Δ) g + progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ allAwake H).env,
      rho.point = realPoint key hn Δ hΔ allAwake H ∧ rho.key = key ∧
      (sysOf O (compiled F) V).Witness ⟨_, rho⟩ ∧
      CommLog.EagerFrom ((sysOf O (compiled F) V).pt ⟨_, rho⟩)
        ((sysOf O (compiled F) V).log ⟨_, rho⟩) g ∧ ShapeHealthy K rho g ∧
      ShapeProg K rho cap i (shapeReady K rho g) rho.horizon ∧
      ProgressActive F K cap i (shapeReady K rho g) rho ∧
      ((sysOf O (compiled F) V).trace ⟨_, rho⟩).TxLiveActive (shapeC K rho)
        (shapeHeal K rho cap i g) ((sysOf O (compiled F) V).lat K cap i ⟨_, rho⟩) ∧
      SafeActive (shapeC K rho) (shapeHeal K rho cap i g) rho.point := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
  have hc : 0 ≤ K.params.cDur Δ := mul_nonneg (by positivity) hΔ.le
  have hheal : 0 ≤ K.params.healPoint Δ cap i g :=
    add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
  have hrdy : 0 ≤ readyFrom (K.params.cDur Δ) g := by
    unfold readyFrom; have := le_max_right g 0; linarith
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨relay, events, hv, hnc, he⟩ := real_run key F (realPoint key hn Δ hΔ allAwake H) hH0 g
  have hse := Model.sysOf_eagerFrom (O := O) _ he
  refine ⟨Model.mkRun (F := compiled F) (E := (realPoint key hn Δ hΔ allAwake H).env)
    (realPoint key hn Δ hΔ allAwake H).honest H key
    (extremalSel F (realPoint key hn Δ hΔ allAwake H).env)
    (realPoint key hn Δ hΔ allAwake H).submit relay (fun x => Encodable.encode x + 1) events,
    rfl, rfl, ⟨hv, hnc, ?_, ?_⟩, hse, ⟨hse.psync le_rfl, ?_⟩,
    allAwake_holds key hn hΔ H hf cap i _ _ _, ?_, ?_,
    allAwake_safeActive key hn hΔ H _ _ h2⟩
  · change (realPoint key hn Δ hΔ allAwake H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)⟩
  · exact ⟨_, subset_rfl,
      lt_card_of_card hn ha.φ_range (realPoint_card_honest key hn hΔ allAwake H),
      fun _ _ _ _ _ => rfl⟩
  · change max (readyFrom (K.params.cDur Δ) g) 0 +
      progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H
    rw [max_eq_left hrdy]; exact h3
  · refine allAwake_txLiveActive key hn hΔ H _ rfl _ _ _ ?_
    change max 0 (K.params.healPoint Δ cap i g) + Δ + K.params.latDur Δ cap i ≤ H
    rw [max_eq_right hheal]; exact h1

/-- The outage witness `(T, [b₀, b₁))`: honest `key 2` asleep exactly at
`b₀`, everyone else always awake, the synchronous canonical run, horizon
`H ≥ b₁`. -/
theorem outage_witness (ha : K.params.Admissible) {T b₀ b₁ : Time}
    (hT : OutageTimes K.params Δ T b₀ b₁) (hTb : T < b₀) (hb : b₀ + Δ ≤ b₁) (hH : b₁ ≤ H) :
    ∃ rho : Model.Run (compiled F)
        (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env,
      rho.point = realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H ∧
      rho.key = key ∧ (sysOf O (compiled F) V).Witness ⟨_, rho⟩ ∧ ShapeOutage K rho T b₀ b₁ ∧
      OutageActive (shapeC K rho) T b₀ b₁ rho.point := by
  have hT0 : 0 ≤ T := hT.1
  have hH0 : 0 ≤ H := by linarith
  have h12 : kv key hn 1 (by decide) ≠ kv key hn 2 (by decide) := kv_ne key hn (by decide)
  obtain ⟨relay, events, hv, hnc, he⟩ :=
    real_run key F (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H) hH0 0
  let rho := Model.mkRun (F := compiled F)
    (E := (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env)
    (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).honest H key
    (extremalSel F (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env)
    (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).submit relay
    (fun x => Encodable.encode x + 1) events
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  have hawake1 : ∀ t, sleepAt (kv key hn 2 (by decide)) b₀ (kv key hn 1 (by decide)) t = true := by
    intro t; simp [sleepAt, h12]
  have hh1 := realPoint_honest key hn hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H (j := 1)
    (by decide) (by decide)
  have hh2 := realPoint_honest key hn hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H (j := 2)
    (by decide) (by decide)
  refine ⟨rho, rfl, rfl, ⟨hv, hnc, ?_, ⟨_, hh1⟩⟩, ⟨hT, ⟨?_, hse.psync (by linarith)⟩, ?_, ?_⟩,
    ⟨hT0, hTb, hb, hH, ⟨_, hh1, fun u _ _ => hawake1 u⟩,
      ⟨_, hh2, b₀, le_rfl, by linarith,
        show sleepAt (kv key hn 2 (by decide)) b₀ (kv key hn 2 (by decide)) b₀ = false by
          simp [sleepAt]⟩,
      ⟨_, hh1, fun u _ _ => hawake1 u⟩⟩⟩
  · change (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact (Model.sysOf_delivers_iff (O := O) rho _ _).mpr
      (he.syncUntil (Model.Run.log_sendsFromZero rho hv) le_rfl b₀)
  · intro t _ _
    exact etaReadyAbove_of_card hn ha.θ_range _ _ t (sleepAt_readyAt key hn hΔ H b₀ _ t)
  · exact readyOfAll_of_card hn ha.cover_range _ b₀ (sleepAt_readyAt key hn hΔ H b₀ _ b₀)

end Witnesses

/-- **Generic realizability** (active form): for every family whose progress
fits its skeleton and every admissible contract, with at least five
validators. -/
theorem realizable_active (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (ha : K.params.Admissible) (hf : K.ProgressFits F) (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) : RealizableActive F K V := by
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_, fun Δ k hΔ => ?_⟩
  · obtain ⟨rho, -, -, hw, hs, hp, hpa, ht⟩ := sleepy_witness key hn hΔ _ ha hf cap i le_rfl
    exact ⟨_, rho, hw, rfl, hs, hp, hpa, ht⟩
  · have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
    have hlat : 0 ≤ K.params.latDur Δ cap i := mul_nonneg (by positivity) hΔ.le
    have hheal : 0 ≤ K.params.healPoint Δ cap i g :=
      add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
    have hrdy : 0 ≤ readyFrom (K.params.cDur Δ) g := by
      unfold readyFrom Params.cDur
      have := le_max_right g 0
      have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
      linarith
    obtain ⟨rho, -, -, hw, he, hs, hp, hpa, ht, hsa⟩ := healthy_witness key hn hΔ
      (K.params.healPoint Δ cap i g + readyFrom (K.params.cDur Δ) g + K.params.latDur Δ cap i +
        progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) + Δ + 2) ha hf cap i g
      (by linarith) (by linarith) (by linarith)
    exact ⟨_, rho, hw, rfl, he, hs, hp, hpa, ht, hsa⟩
  · have hl : (0 : Time) ≤ (K.params.lag : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hk : (0 : Time) ≤ (k : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hbud : (1 : Time) ≤ (K.params.budget : Time) := by exact_mod_cast ha.budget_pos
    have hT : OutageTimes K.params Δ ((k : Time) * Δ)
        ((k : Time) * Δ + (K.params.lag : Time) * Δ + Δ)
        ((k : Time) * Δ + (K.params.lag : Time) * Δ + Δ + Δ) :=
      ⟨hk, by linarith, by linarith, by nlinarith⟩
    obtain ⟨rho, -, -, hw, ho, hoa⟩ := outage_witness (F := F) key hn hΔ _ ha hT (by linarith)
      le_rfl le_rfl
    exact ⟨⟨_, rho⟩, _, _, _, hw, rfl, ho, hoa, le_rfl⟩

/-- **Generic realizability**: L0 `Realizable` for every family whose progress
fits its skeleton and every admissible contract, with at least five
validators; in addition every progress window of the sleepy and healthy
witnesses is active (`RealizableActive`). -/
theorem regimes_realizable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (ha : K.params.Admissible) (hf : K.ProgressFits F) (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) :
    Realizable (sysOf O (compiled F) V) (shapeProgress F V) K ∧ RealizableActive F K V :=
  ⟨(realizable_active F K ha hf V hn).toRealizable, realizable_active F K ha hf V hn⟩

end Realize

end Consensus.Shape

end
