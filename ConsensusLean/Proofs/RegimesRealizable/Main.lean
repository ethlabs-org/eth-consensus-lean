module
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Lemmas.Shape.Payload
public import ConsensusLean.Spec.Shape.ProgressFit
public import Mathlib.Tactic

public section

/-! # Coverage, the extremal selection and generic realizability (L2)

* `coverage` (fixed selection): any environment point with `0 ≤ horizon`, with any
  PKI, any admissible selection and any GST `g`, is exactly the point, PKI and
  selection of a valid, collision-free, conviction-free compiled run whose log
  is eager from `g`. Progress requirements read only the point, the PKI and
  the selection, so whatever progress holds there holds on that run.
* The extremal selection (`extremalSel`) gives every `.sized m` role (`m`
  below the population) the keys `1, …, m`; a `.sized 1` proposer role selects
  exactly key `1` (`extremalSel_proposer_mem`), honest when only key `0` is
  faulty.
* Generic realizability (`regimes_realizable`): L0
  `Realizable` for every family whose progress fits its skeleton and every
  progress-tolerant admissible contract and at least five validators, with active progress
  windows (`ProgressActive`). Witnesses: `sleepy_witness`,
  `healthy_witness`, `outage_witness` and `sleepyStress_witness` (a bounded
  awake profile), and the L2-only bad-proposer witness (`healthy_witness_sel`
  under the bad-slot selection `badSel`, `bad_selection`): a faulty proposer
  slot in every progress window. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

section Activity

variable (F : ShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem progLen_nonneg (cap : Capability) (i : K.Idx) (E : Env V) : 0 ≤ progLen F K cap i E := by
  unfold progLen
  split
  · exact mul_nonneg (by positivity) (F (pubOf E)).skel.grid.slotLen_pos.le
  · exact le_rfl

/-- Active realizability gives L0 realizability (the four L0 witness
families, dropping `ProgressActive`; `badProposer` has no L0 counterpart). -/
theorem RealizableActive.toRealizable {V : Type} [Fintype V] [DecidableEq V]
    (h : RealizableActive F K V) : Realizable (Sys F V) (shapeProgress F V) K where
  sleepy cap i Δ hΔ := (h.sleepy cap i Δ hΔ).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  healthy cap i Δ g hΔ hg :=
    (h.healthy cap i Δ g hΔ hg).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  sleepyStress cap hc ho Δ hΔ := (h.sleepyStress cap hc ho Δ hΔ).imp fun _ h =>
    h.imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  outage := h.outage

end Activity

/-! ## Fixed-selection coverage -/

/-- Fixed-selection coverage. Inputs are fixed, outputs preserve them: the
point `p`, the PKI `key`, an admissible selection `sel`, and a GST `g`. Some
valid, collision-free, conviction-free compiled run has exactly that point,
PKI and selection, and its log is eager from `g`. -/
theorem coverage (F : ShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V]
    (p : EnvPoint V) (hp : 0 ≤ p.horizon) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) p.env).SelAdmits sel) (g : Time) :
    ∃ rho : Model.Run (compiled F) p.env, rho.point = p ∧ rho.key = key ∧ rho.sel = sel ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
      Consensus.convicted ((Sys F V).convicts ⟨p.env, rho⟩)
        ((Sys F V).honestEvidence ⟨p.env, rho⟩) = ∅ ∧
      CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.honest p.horizon hp key sel hsel
      p.submit hash g
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.honest p.horizon events key sel p.submit
      relay hash
  refine ⟨rho, rfl, rfl, rfl, hv, ?_, ?_, he⟩
  · exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  · exact Model.convicted_honestEvidence_eq_empty rho (rho.not_slashable_of_causal hv hc)

/-! ## The extremal selection -/

/-- An admissible key set for each selection specification on `Fin N`:
the fixed set, or the keys `1, …, m` for `.sized m` with `m < N`
(everybody otherwise). Key `0` is selected only when a specification forces
it. -/
def extremalKeys {N : Nat} : SelSpec N → Finset (Fin N)
  | .fixed T => T
  | .sized m => if m < N then Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m else Finset.univ

theorem extremalKeys_fixed {N : Nat} (T : Finset (Fin N)) :
    extremalKeys (.fixed T) = T := by rfl

theorem extremalKeys_sized {N : Nat} (m : Nat) :
    extremalKeys (N := N) (.sized m) =
      if m < N then Finset.univ.filter (fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m)
      else Finset.univ := by rfl

theorem extremalKeys_admits {N : Nat} (s : SelSpec N) : s.Admits (extremalKeys s) := by
  cases s with
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

/-- The extremal selection: `extremalKeys` of every role's specification. -/
def extremalSel (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => extremalKeys ((protoOf (compiled F) E).selSpec r)

theorem extremalSel_apply (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V)
    (r : (protoOf (compiled F) E).Role) :
    extremalSel F E r = extremalKeys ((protoOf (compiled F) E).selSpec r) := by rfl

theorem extremalSel_admits (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).SelAdmits (extremalSel F E) :=
  fun _ => extremalKeys_admits _

/-! ## The bad-slot selection -/

/-- A proposer role at a periodic bad slot: slot `s` with `s % P = P − 1`. -/
def badSlotRole {Kind : Type} (P : Nat) : ShapeRole Kind → Bool
  | .proposer s => decide (s % P = P - 1)
  | _ => false

theorem badSlotRole_proposer {Kind : Type} (P : Nat) (s : Slot) :
    badSlotRole (Kind := Kind) P (.proposer s) = decide (s % P = P - 1) := by rfl

theorem badSlotRole_duty {Kind : Type} (P : Nat) (k : Kind) (s : Slot) :
    badSlotRole P (.duty s k) = false := by rfl

theorem badSlotRole_poll {Kind : Type} (P : Nat) :
    badSlotRole (Kind := Kind) P .poll = false := by rfl

/-- The bad-slot selection with period `P`: key `0` (faulty at the witness
points) proposes at every slot `s` with `s % P = P − 1`; every other role is
selected as by `extremalSel`. -/
def badSel (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (hn : 0 < Fintype.card V) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => if badSlotRole (Kind := (F (pubOf E)).skel.Kind) P r then {⟨0, hn⟩}
    else extremalSel F E r

theorem badSel_apply (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (hn : 0 < Fintype.card V) (r : (protoOf (compiled F) E).Role) :
    badSel F E P hn r =
      if badSlotRole (Kind := (F (pubOf E)).skel.Kind) P r then {⟨0, hn⟩}
      else extremalSel F E r := by rfl

/-- With one proposer per slot, the bad-slot selection is admissible. -/
theorem badSel_admits (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (hn : 0 < Fintype.card V) (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1) :
    (protoOf (compiled F) E).SelAdmits (badSel F E P hn) := by
  intro r
  rw [badSel_apply]
  split_ifs with hb
  · change ShapeRole (F (pubOf E)).skel.Kind at r
    cases r with
    | proposer s =>
      change SelSpec.Admits ((F (pubOf E)).skel.proposerSel s) _
      rw [hF]
      change ({⟨0, hn⟩} : Finset (Fin (Fintype.card V))).card = min 1 (Fintype.card V)
      rw [Finset.card_singleton]; omega
    | duty _ _ => simp [badSlotRole_duty] at hb
    | poll => simp [badSlotRole_poll] at hb
  · exact extremalSel_admits F E r

/-- Under the bad-slot selection, the proposer of a bad slot is exactly
key `0`. -/
theorem badSel_bad (F : ShapeFamily O Info) {V : Type} [Fintype V] {E : Env V} {P : Nat}
    (hn : 0 < Fintype.card V) {s : Slot} (hs : s % P = P - 1) :
    badSel F E P hn (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) = {⟨0, hn⟩} := by
  simp [badSel_apply F E P hn (.proposer s), badSlotRole_proposer, hs]

/-! ## Generic realizability

`regimes_realizable`: for every family whose progress fits its skeleton and
every admissible, progress-tolerant contract, with at least five validators,
every regime of the
L0 table is met by a clean witness with active claims, at every `Δ`, every
GST and arbitrarily late outages; in addition, every progress window of the
sleepy and healthy witnesses lies inside the horizon (`ProgressActive`).

The witnesses: validator `key 0` faulty, every other validator honest; the
PKI `Fintype.equivFin`; the extremal selection (`.sized 1` proposer roles
select key `1`, honest and always awake); transaction `42` submitted to
`key 1` at time `0`, read by `key 2`.

* stress: two honest keys (`1`, `2`) awake (sleepy), whatever `n`;
* bad proposer: the healthy witness (everyone awake) under the bad-slot
  selection, where faulty key `0` proposes every slot `s` with
  `s % (span + 2) = span + 1` (so every window of a recurrence with
  `span + 2 ≤ gap` holds a faulty proposer slot and a whole good pattern);
* sleepy and healthy: everyone awake (healthy is full participation, and the
  one faulty validator is below `β·n` for `β ≥ ⅓`, `n ≥ 5`); the healthy witness is the canonical
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

Thresholds are proved at the standard bounds (`θ ≤ ½`, `β ≥ ⅓`,
`cover ≤ ½`), which `Params.Admissible` guarantees. -/

section Realize

variable (F : ShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The witness points -/

variable {F K}

/-- The witness point: `Δ`, awake profile `awake`, horizon `H`; validator
`key 0` faulty, every other validator honest; transaction `42` submitted to
`key 1` at time `0`. -/
def realPoint (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) (Δ : Time)
    (hΔ : 0 < Δ) (awake : V → Time → Bool) (H : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, awake⟩, Finset.univ.erase (key ⟨0, by omega⟩), H,
    fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩

theorem realPoint_eq (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) (Δ : Time)
    (hΔ : 0 < Δ) (awake : V → Time → Bool) (H : Time) :
    realPoint key hn Δ hΔ awake H =
      ⟨⟨Δ, hΔ, awake⟩, Finset.univ.erase (key ⟨0, by omega⟩), H,
        fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩ := by rfl

/-- Everyone awake at every time. -/
def allAwake : V → Time → Bool := fun _ _ => true

/-- `s` asleep exactly at time `b`; everyone else always awake. -/
def sleepAt (s : V) (b : Time) : V → Time → Bool := fun v t => !(decide (v = s) && decide (t = b))

omit [Fintype V] [DecidableEq V] in
theorem allAwake_apply (v : V) (t : Time) : allAwake v t = true := by rfl

omit [Fintype V] in
theorem sleepAt_apply (s : V) (b : Time) (v : V) (t : Time) :
    sleepAt s b v t = !(decide (v = s) && decide (t = b)) := by rfl

section Point

variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  (awake : V → Time → Bool) (H : Time)

/-- The validator of key `j`. -/
abbrev kv (j : Nat) (hj : j < 5) : V := key ⟨j, by omega⟩

omit [DecidableEq V] in
theorem kv_eq (j : Nat) (hj : j < 5) : kv key hn j hj = key ⟨j, by omega⟩ := by rfl

omit [DecidableEq V] in
theorem kv_ne {j j' : Nat} {hj : j < 5} {hj' : j' < 5} (h : j ≠ j') :
    kv key hn j hj ≠ kv key hn j' hj' := by
  intro he
  have := congrArg Fin.val (key.injective he)
  exact h this

theorem realPoint_env : (realPoint key hn Δ hΔ awake H).env = ⟨Δ, hΔ, awake⟩ := by rfl

theorem realPoint_horizon : (realPoint key hn Δ hΔ awake H).horizon = H := by rfl

theorem realPoint_faulty : (realPoint key hn Δ hΔ awake H).faulty = {kv key hn 0 (by decide)} := by
  ext v; simp [EnvPoint.faulty, realPoint_eq]

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
      exact ⟨hv, fun t => by simp [sleepAt_apply, hne]⟩) c t
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
/-- The numbers: with `n ≥ 5` and `β ≥ ⅓`, one faulty validator is below
`β·n`. -/
theorem one_lt_beta_mul_card {β : ℚ} (hβ : 1 / 3 ≤ β) : ((1 : Nat) : ℚ) < β * Fintype.card V := by
  have hn' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  push_cast
  nlinarith

end Point

/-! ### Progress at the witness points -/

omit [DecidableEq V] in
/-- Under the extremal selection, a `.sized 1` proposer role selects exactly
key `1`. -/
theorem extremalSel_proposer_mem (F : ShapeFamily O Info) {E : Env V}
    (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1) (h2 : 2 ≤ Fintype.card V)
    (s : Slot) (k : Fin (Fintype.card V)) :
    k ∈ extremalSel F E (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔
      k.val = 1 := by
  rw [extremalSel_apply F E (.proposer s)]
  change k ∈ extremalKeys ((F (pubOf E)).skel.proposerSel s) ↔ _
  rw [hF]
  have h1 : 1 < Fintype.card V := by omega
  simp only [extremalKeys_sized, h1, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

omit [DecidableEq V] in
/-- Under the bad-slot selection with one proposer per slot, the proposer of
a good slot is exactly key `1`. -/
theorem badSel_good_mem (F : ShapeFamily O Info) {E : Env V} {P : Nat}
    (hn : 0 < Fintype.card V) (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1)
    (h2 : 2 ≤ Fintype.card V) {s : Slot} (hs : s % P ≠ P - 1) (k : Fin (Fintype.card V)) :
    k ∈ badSel F E P hn (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔
      k.val = 1 := by
  have he : badSel F E P hn (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) =
      extremalSel F E (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) := by
    simp [badSel_apply F E P hn (.proposer s), badSlotRole_proposer, hs]
  rw [he]
  exact extremalSel_proposer_mem F hF h2 s k

/-- Keys up to `k` stay awake; all larger keys stay asleep. -/
def awakeUpTo (key : Fin (Fintype.card V) ≃ V) (k : Nat) : V → Time → Bool :=
  fun v _ => decide ((key.symm v).val ≤ k)

omit [DecidableEq V] in
theorem awakeUpTo_apply (key : Fin (Fintype.card V) ≃ V) (k : Nat) (v : V) (t : Time) :
    awakeUpTo key k v t = decide ((key.symm v).val ≤ k) := by rfl

/-- The honest awake set contains exactly keys `1` through `k`. -/
theorem awakeUpTo_card (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) (H : Time) (k : Nat) (hk : k < Fintype.card V) (t : Time) :
    ((realPoint key hn Δ hΔ (awakeUpTo key k) H).awakeAt t).card = k := by
  classical
  have he : ((realPoint key hn Δ hΔ (awakeUpTo key k) H).awakeAt t).map
      key.symm.toEmbedding = Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val ≤ k) := by
    ext j
    simp [EnvPoint.awakeAt, realPoint_eq, awakeUpTo_apply, Fin.ext_iff]
    omega
  have hi : (Finset.univ.filter (fun j : Fin (Fintype.card V) =>
      1 ≤ j.val ∧ j.val ≤ k)).map Fin.valEmbedding = Finset.Icc 1 k := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hj; exact ⟨⟨j, by omega⟩, hj, rfl⟩
  rw [← Finset.card_map, he, ← Finset.card_map, hi, Nat.card_Icc]
  omega

/-- Always-awake honest validators are ready, so the bounded profile has at
least `k` ready validators. -/
theorem awakeUpTo_ready (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) (H : Time) (k : Nat) (hk : k < Fintype.card V) (c t : Time) :
    k ≤ ((realPoint key hn Δ hΔ (awakeUpTo key k) H).readyAt c t).card := by
  conv_lhs => rw [← awakeUpTo_card key hn hΔ H k hk t]
  apply card_le_readyAt key hn hΔ (awakeUpTo key k) H
  intro v hv
  obtain ⟨hh, ha⟩ := Finset.mem_filter.mp hv
  exact ⟨hh, fun _ => ha⟩

section Witnesses

variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  (H : Time)

/-- Everyone awake, a fitting progress requirement holds on every window under
the extremal selection: key `1` (honest, always awake) is the proposer of every
slot, and every honest validator is ready at every time. -/
theorem allAwake_holds (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ allAwake H)
      (key, extremalSel F (realPoint key hn Δ hΔ allAwake H).env) := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ allAwake H).env)
  revert hfit
  cases K.progress cap i with
  | recur ρ =>
    intro hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    have hh := realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)
    exact ⟨hh, fun _ _ _ => rfl⟩
  | notReadyAtMost m =>
    intro _ t _ _ _
    exact le_trans (allAwake_readyAt key hn hΔ H c t) (Nat.add_le_add_left m.pos _)

/-- Everyone awake: liveness is active from `start`, with transaction `42`
submitted to `key 1` at `0` and read by `key 2` at the horizon. -/
theorem allAwake_txLiveActive (p : EnvPoint V)
    (hp : p = realPoint key hn Δ hΔ allAwake H) (c start D : Time)
    (hH : max 0 start + Δ + D ≤ H) : p.TxLiveActive c start D := by
  unfold EnvPoint.TxLiveActive
  rw [hp]
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide), rfl, ?_,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide),
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    realPoint_honest key hn hΔ allAwake H (by decide) (by decide), fun _ _ _ => rfl⟩
  · simp [realPoint_eq]
  · intro τ
    have : kv key hn 2 (by decide) ≠ kv key hn 1 (by decide) := kv_ne key hn (by decide)
    simp [realPoint_eq, this]

/-- Everyone awake: safety is active after `t₀` (keys `1` and `2` ready at
`t₀ + 1`, key `1` again at `t₀ + 2`). -/
theorem allAwake_safeActive (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (realPoint key hn Δ hΔ allAwake H) := by
  have h1 := realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)
  have h2 := realPoint_honest key hn hΔ allAwake H (j := 2) (by decide) (by decide)
  exact ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, by linarith, hH,
    ⟨h1, fun _ _ _ => rfl⟩, ⟨h2, fun _ _ _ => rfl⟩, ⟨h1, fun _ _ _ => rfl⟩⟩

/-- With key `1` always awake, a fitting recurrence holds under the extremal
selection; a bound tolerating the whole population holds on every profile. -/
theorem profile_holds (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i))
    (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ awake H)
      (key, extremalSel F (realPoint key hn Δ hΔ awake H).env) := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ awake H).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit ht
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    have hh := realPoint_honest key hn hΔ awake H (j := 1) (by decide) (by decide)
    exact ⟨hh, fun t _ _ => ha1 t⟩
  | notReadyAtMost m =>
    rw [hreq] at ht
    exact NotReadyOn.of_card_le ht

/-- With keys `1` and `2` always awake, liveness is active: key `1` submits
transaction `42` at `0`, and key `2` reads at the horizon. -/
theorem profile_txLiveActive (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (ha2 : ∀ t, awake (kv key hn 2 (by decide)) t = true) (p : EnvPoint V)
    (hp : p = realPoint key hn Δ hΔ awake H) (c start D : Time)
    (hH : max 0 start + Δ + D ≤ H) : p.TxLiveActive c start D := by
  unfold EnvPoint.TxLiveActive
  rw [hp]
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    realPoint_honest key hn hΔ awake H (by decide) (by decide), ha1 0, ?_,
    realPoint_honest key hn hΔ awake H (by decide) (by decide),
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    realPoint_honest key hn hΔ awake H (by decide) (by decide), fun t _ _ => ha2 t⟩
  · simp [realPoint_eq]
  · intro τ
    have : kv key hn 2 (by decide) ≠ kv key hn 1 (by decide) := kv_ne key hn (by decide)
    simp [realPoint_eq, this]

/-- With keys `1` and `2` always awake, safety is active after `t₀`. -/
theorem profile_safeActive (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (ha2 : ∀ t, awake (kv key hn 2 (by decide)) t = true) (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (realPoint key hn Δ hΔ awake H) := by
  have h1 := realPoint_honest key hn hΔ awake H (j := 1) (by decide) (by decide)
  have h2 := realPoint_honest key hn hΔ awake H (j := 2) (by decide) (by decide)
  exact ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, by linarith, hH,
    ⟨h1, fun t _ _ => ha1 t⟩, ⟨h2, fun t _ _ => ha2 t⟩, ⟨h1, fun t _ _ => ha1 t⟩⟩

/-- The canonical run at a witness point, from GST `g`, with some injective
hash and an admissible selection `sel`: valid, no collision, and eager from
`g`; its point, PKI and selection are the given ones definitionally
(a `Run` literal). -/
theorem real_run_sel (F : ShapeFamily O Info) (p : EnvPoint V) (hp : 0 ≤ p.horizon) (g : Time)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) p.env).SelAdmits sel) :
    ∃ hash relay events,
      let rho := Model.Run.mk (F := compiled F) (E := p.env) p.honest p.horizon events key sel
          p.submit relay hash
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, -⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.honest p.horizon hp key
      sel hsel p.submit hash g
  exact ⟨hash, relay, events, hv,
    Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj), he⟩

/-- The canonical run at a witness point under the extremal selection. -/
theorem real_run (F : ShapeFamily O Info) (p : EnvPoint V) (hp : 0 ≤ p.horizon) (g : Time) :
    ∃ hash relay events,
      let rho := Model.Run.mk (F := compiled F) (E := p.env) p.honest p.horizon events key
          (extremalSel F p.env) p.submit relay hash
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g :=
  real_run_sel key F p hp g _ (extremalSel_admits F p.env)

/-- The sleepy witness: everyone awake, the synchronous canonical run, horizon
`H` long enough for one liveness deadline and one progress window. -/
theorem sleepy_witness (ha : K.params.Admissible) (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx)
    (hH : Δ + (K.params.latency cap i : Time) * Δ +
      progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ allAwake H).env,
      rho.point = realPoint key hn Δ hΔ allAwake H ∧ rho.key = key ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧ (Sys F V).Sleepy K ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i 0 rho.horizon ⟨_, rho⟩ ∧
      ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩) 0
        ((Sys F V).lat K cap i ⟨_, rho⟩) := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run key F (realPoint key hn Δ hΔ allAwake H) hH0 0
  refine ⟨Model.Run.mk (F := compiled F) (E := (realPoint key hn Δ hΔ allAwake H).env)
      (realPoint key hn Δ hΔ allAwake H).honest H events key
      (extremalSel F (realPoint key hn Δ hΔ allAwake H).env)
      (realPoint key hn Δ hΔ allAwake H).submit relay hash,
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
    change max 0 0 + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    simp only [max_self, zero_add]; linarith

/-- The healthy witness at GST `g` under an admissible selection `sel` at
which the progress requirement holds: everyone awake (full participation, one
faulty validator), the canonical run from `g` (no receipt before
`g`), horizon `H` long enough for one liveness deadline
after the heal point, two cuts after it, and one progress window from
`ready`. -/
theorem healthy_witness_sel (ha : K.params.Admissible) (cap : Capability) (i : K.Idx) (g : Time)
    (sel : (protoOf (compiled F) (realPoint key hn Δ hΔ allAwake H).env).Role →
      Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) (realPoint key hn Δ hΔ allAwake H).env).SelAdmits sel)
    (hprog : ∀ c s e, shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ allAwake H)
      (key, sel))
    (h1 : max g 0 + (K.params.heal cap i : Time) * Δ + Δ + (K.params.latency cap i : Time) * Δ ≤ H)
    (h2 : max g 0 + (K.params.heal cap i : Time) * Δ + 2 ≤ H)
    (h3 : max g 0 + (K.params.catchUp : Time) * Δ + 1 +
      progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ allAwake H).env,
      rho.point = realPoint key hn Δ hΔ allAwake H ∧ rho.key = key ∧ rho.sel = sel ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧
      CommLog.EagerFrom ((Sys F V).pt ⟨_, rho⟩)
        ((Sys F V).log ⟨_, rho⟩) g ∧ (Sys F V).Healthy K g ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho.horizon
        ⟨_, rho⟩ ∧
      ProgressActive F K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩)
        ((Sys F V).heal K cap i g ⟨_, rho⟩) ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      SafeActive ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).heal K cap i g ⟨_, rho⟩) rho.point := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
  have hc : 0 ≤ ((K.params.catchUp : Time) * Δ) := mul_nonneg (by positivity) hΔ.le
  have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
    add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
  have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
    have := le_max_right g 0; linarith
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run_sel key F (realPoint key hn Δ hΔ allAwake H) hH0 g sel hsel
  have hse := Model.sysOf_eagerFrom (O := O) _ he
  refine ⟨Model.Run.mk (F := compiled F) (E := (realPoint key hn Δ hΔ allAwake H).env)
      (realPoint key hn Δ hΔ allAwake H).honest H events key sel
      (realPoint key hn Δ hΔ allAwake H).submit relay hash,
    rfl, rfl, rfl, ⟨hv, hnc, ?_, ?_⟩, hse, ⟨hse.psync le_rfl, ?_⟩,
    hprog _ _ _, ?_, ?_,
    allAwake_safeActive key hn hΔ H _ _ h2⟩
  · change (realPoint key hn Δ hΔ allAwake H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, realPoint_honest key hn hΔ allAwake H (j := 1) (by decide) (by decide)⟩
  · refine ⟨?_, fun _ _ _ _ _ => rfl⟩
    change ((realPoint key hn Δ hΔ allAwake H).faulty.card : ℚ) < K.params.β * Fintype.card V
    rw [realPoint_faulty, Finset.card_singleton]
    exact one_lt_beta_mul_card hn ha.β_range
  · change max ((max g 0 + (K.params.catchUp : Time) * Δ + 1)) 0 +
      progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H
    rw [max_eq_left hrdy]; exact h3
  · refine allAwake_txLiveActive key hn hΔ H _ rfl _ _ _ ?_
    change max 0 (max g 0 + (K.params.heal cap i : Time) * Δ) + Δ +
      (K.params.latency cap i : Time) * Δ ≤ H
    rw [max_eq_right hheal]; exact h1

/-- The healthy witness at GST `g` under the extremal selection (key `1`
proposes every slot). -/
theorem healthy_witness (ha : K.params.Admissible) (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx) (g : Time)
    (h1 : max g 0 + (K.params.heal cap i : Time) * Δ + Δ + (K.params.latency cap i : Time) * Δ ≤ H)
    (h2 : max g 0 + (K.params.heal cap i : Time) * Δ + 2 ≤ H)
    (h3 : max g 0 + (K.params.catchUp : Time) * Δ + 1 +
      progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ allAwake H).env,
      rho.point = realPoint key hn Δ hΔ allAwake H ∧ rho.key = key ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧
      CommLog.EagerFrom ((Sys F V).pt ⟨_, rho⟩)
        ((Sys F V).log ⟨_, rho⟩) g ∧ (Sys F V).Healthy K g ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho.horizon
        ⟨_, rho⟩ ∧
      ProgressActive F K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩)
        ((Sys F V).heal K cap i g ⟨_, rho⟩) ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      SafeActive ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).heal K cap i g ⟨_, rho⟩) rho.point := by
  obtain ⟨rho, hp, hk, -, h⟩ := healthy_witness_sel key hn hΔ H ha cap i g _
    (extremalSel_admits F _) (allAwake_holds key hn hΔ H hf cap i) h1 h2 h3
  exact ⟨rho, hp, hk, h⟩

/-- A selection for the bad-proposer witness at index `i` (tolerant of
`n` validators not ready and of bad slots), on a profile where key `1`
stays awake: for a recurrence, the bad-slot selection with period
`span + 2` (key `0`, faulty, proposes one slot in every `span + 2`), under
which the recurrence still holds and every window holds a faulty proposer
slot; for a bound on the validators not ready, the extremal selection (the
tolerant bound holds on every point). -/
theorem bad_selection (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i)) :
    ∃ sel : (protoOf (compiled F) (realPoint key hn Δ hΔ awake H).env).Role →
        Finset (Fin (Fintype.card V)),
      (protoOf (compiled F) (realPoint key hn Δ hΔ awake H).env).SelAdmits sel ∧
      (∀ c s e, shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ awake H)
        (key, sel)) ∧
      ∀ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ awake H).env, rho.sel = sel →
        rho.key = key → rho.honest = (realPoint key hn Δ hΔ awake H).honest →
        BadProposerEvery F K cap i rho := by
  have hn0 : 0 < Fintype.card V := by omega
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ awake H).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit ht
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    change ρ.BadSlotSlack at ht
    have hP : ρ.pattern.span + 2 - 1 = ρ.pattern.span + 1 := by omega
    refine ⟨badSel F (realPoint key hn Δ hΔ awake H).env (ρ.pattern.span + 2) hn0,
      badSel_admits F _ _ hn0 hfit, fun c s e => ?_, fun rho hs hk hh => ?_⟩
    · apply patternRecurrence_of_periodic ht
      intro sl j hsl hj
      have hg := Recurrence.pattern_good hsl hj
      have hmem := badSel_good_mem F hn0 hfit (by omega) (s := sl + j)
        (P := ρ.pattern.span + 2) (by rw [hP]; exact hg)
      refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
      have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
      subst hk1
      have hh1 := realPoint_honest key hn hΔ awake H (j := 1) (by decide) (by decide)
      exact ⟨hh1, fun t _ _ => ha1 t⟩
    · unfold BadProposerEvery
      rw [hreq]
      intro a
      obtain ⟨s, h1, h2, h3⟩ := Recurrence.exists_bad_slot ht a
      have hb := badSel_bad F (E := (realPoint key hn Δ hΔ awake H).env) hn0 (s := s)
        (P := ρ.pattern.span + 2) (by rw [hP]; exact h3)
      refine ⟨s, h1, h2, ?_, ?_⟩
      · rw [hs]; rw [hb]; exact Finset.singleton_nonempty _
      · rw [hs]; rw [hb]
        intro k hk'
        rw [Finset.mem_singleton.mp hk', hk, hh]
        intro hm
        have : kv key hn 0 (by decide) ∈ (realPoint key hn Δ hΔ awake H).faulty := by
          rw [realPoint_faulty]; exact Finset.mem_singleton_self _
        exact (Finset.mem_sdiff.mp this).2 hm
  | notReadyAtMost m =>
    rw [hreq] at ht
    refine ⟨extremalSel F _, extremalSel_admits F _, fun c s e => ?_, fun rho _ _ _ => ?_⟩
    · exact NotReadyOn.of_card_le ht
    · unfold BadProposerEvery; rw [hreq]; trivial

/-- Sleepy stress: only honest keys `1` and `2` stay awake, with active
liveness and progress on the synchronous canonical run: with one faulty
validator and `θ ≤ ½`, two ready honest validators meet the sleepy
threshold. -/
theorem sleepyStress_witness (ha : K.params.Admissible) (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx) (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i))
    (hH : Δ + (K.params.latency cap i : Time) * Δ +
      progLen F K cap i (⟨Δ, hΔ, (awakeUpTo key 2)⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ (awakeUpTo key 2) H).env,
      rho.point = realPoint key hn Δ hΔ (awakeUpTo key 2) H ∧ rho.key = key ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧ (Sys F V).Sleepy K ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i 0 rho.horizon ⟨_, rho⟩ ∧
      ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩) 0
        ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      rho.point.AwakeAtMost 2 := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, (awakeUpTo key 2)⟩ : Env V)
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run key F (realPoint key hn Δ hΔ (awakeUpTo key 2) H) hH0 0
  refine ⟨Model.Run.mk (F := compiled F) (E := (realPoint key hn Δ hΔ (awakeUpTo key 2) H).env)
      (realPoint key hn Δ hΔ (awakeUpTo key 2) H).honest H events key
      (extremalSel F (realPoint key hn Δ hΔ (awakeUpTo key 2) H).env)
      (realPoint key hn Δ hΔ (awakeUpTo key 2) H).submit relay hash,
    rfl, rfl, ⟨hv, hnc, ?_, ?_⟩, ⟨(Model.sysOf_eagerFrom _ he).psync le_rfl, ?_⟩,
    profile_holds key hn hΔ H _ (by intro t; simp [awakeUpTo_apply, kv_eq]) hf cap i ht _ _ _,
    ?_, ?_, ?_⟩
  · change (realPoint key hn Δ hΔ (awakeUpTo key 2) H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, realPoint_honest key hn hΔ (awakeUpTo key 2) H (j := 1) (by decide) (by decide)⟩
  · intro t _ _
    change (realPoint key hn Δ hΔ (awakeUpTo key 2) H).ReadyAbove K.params.θ
      ((K.params.catchUp : Time) * Δ) t
    unfold EnvPoint.ReadyAbove
    rw [realPoint_faulty, Finset.card_singleton]
    have hr := awakeUpTo_ready key hn hΔ H 2 (by omega) (((K.params.catchUp : Time) * Δ)) t
    have hr' : (2 : ℚ) ≤ ((realPoint key hn Δ hΔ (awakeUpTo key 2) H).readyAt
        (((K.params.catchUp : Time) * Δ)) t).card := by exact_mod_cast hr
    have := ha.θ_range.2
    push_cast
    nlinarith
  · change max 0 0 + progLen F K cap i (⟨Δ, hΔ, (awakeUpTo key 2)⟩ : Env V) ≤ H
    simp only [max_self, zero_add]; linarith
  · refine profile_txLiveActive key hn hΔ H _ (by intro t; simp [awakeUpTo_apply, kv_eq])
      (by intro t; simp [awakeUpTo_apply, kv_eq]) _ rfl _ _ _ ?_
    change max 0 0 + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    simp only [max_self, zero_add]; linarith
  · intro t _ _
    change ((realPoint key hn Δ hΔ (awakeUpTo key 2) H).awakeAt t).card ≤ _
    rw [awakeUpTo_card key hn hΔ H 2 (by omega)]

/-- The outage witness `(T, [b₀, b₁))`: honest `key 2` asleep exactly at
`b₀`, everyone else always awake, the synchronous canonical run, horizon
`H ≥ b₁`. -/
theorem outage_witness (ha : K.params.Admissible) {T b₀ b₁ : Time}
    (hT : OutageTimes K.params Δ T b₀ b₁) (hTb : T < b₀) (hb : b₀ + Δ ≤ b₁) (hH : b₁ ≤ H) :
    ∃ rho : Model.Run (compiled F)
        (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env,
      rho.point = realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H ∧
      rho.key = key ∧ (Sys F V).Witness ⟨_, rho⟩ ∧ (Sys F V).Outage K T b₀ b₁ ⟨_, rho⟩ ∧
      OutageActive ((Sys F V).cDur K ⟨_, rho⟩) T b₀ b₁ rho.point := by
  have hT0 : 0 ≤ T := hT.1
  have hH0 : 0 ≤ H := by linarith
  have h12 : kv key hn 1 (by decide) ≠ kv key hn 2 (by decide) := kv_ne key hn (by decide)
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run key F (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H) hH0 0
  let rho := Model.Run.mk (F := compiled F)
      (E := (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env)
      (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).honest H events key
      (extremalSel F (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).env)
      (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).submit relay hash
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  have hawake1 : ∀ t, sleepAt (kv key hn 2 (by decide)) b₀ (kv key hn 1 (by decide)) t = true := by
    intro t; simp [sleepAt_apply, h12]
  have hh1 := realPoint_honest key hn hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H (j := 1)
    (by decide) (by decide)
  have hh2 := realPoint_honest key hn hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H (j := 2)
    (by decide) (by decide)
  refine ⟨rho, rfl, rfl, ⟨hv, hnc, ?_, ⟨_, hh1⟩⟩, ⟨hT, ⟨?_, hse.psync (by linarith)⟩, ?_, ?_⟩,
    ⟨hT0, hTb, hb, hH, ⟨_, hh1, fun u _ _ => hawake1 u⟩,
      ⟨_, hh2, b₀, le_rfl, by linarith,
        show sleepAt (kv key hn 2 (by decide)) b₀ (kv key hn 2 (by decide)) b₀ = false by
          simp [sleepAt_apply]⟩,
      ⟨_, hh1, fun u _ _ => hawake1 u⟩⟩⟩
  · change (realPoint key hn Δ hΔ (sleepAt (kv key hn 2 (by decide)) b₀) H).faulty.Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact (Model.sysOf_delivers_iff (O := O) rho _ _).mpr
      (he.syncUntil (Model.Run.log_sendsFromZero rho hv) le_rfl b₀)
  · intro t _ _
    exact etaReadyAbove_of_card hn ha.θ_range _ _ t (sleepAt_readyAt key hn hΔ H b₀ _ t)
  · exact readyOfAll_of_card hn ha.cover_range _ b₀ (sleepAt_readyAt key hn hΔ H b₀ _ b₀)

end Witnesses

/-- **Generic realizability**: L0 `Realizable` (`RealizableActive.toRealizable`)
with active progress windows, for every family whose progress fits its
skeleton and every admissible, progress-tolerant contract, with at least five
validators. -/
theorem regimes_realizable (F : ShapeFamily O Info) (K : Contract ProgressReq)
    (ha : K.params.Admissible) (hf : ProgressFits K F) (ht : ProgressTolerant O K)
    (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) : RealizableActive F K V := by
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_,
    fun cap hc ho Δ hΔ => ?_, fun Δ k hΔ => ?_, fun cap ho Δ g hΔ hg => ?_⟩
  · obtain ⟨rho, -, -, hw, hs, hp, hpa, ht⟩ := sleepy_witness key hn hΔ _ ha hf cap i le_rfl
    exact ⟨⟨_, rho⟩, hw, rfl, ⟨hs, hp, ht⟩, hpa⟩
  · have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
    have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
      add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
    have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
      have := le_max_right g 0
      have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
      linarith
    obtain ⟨rho, -, -, hw, he, hs, hp, hpa, ht, hsa⟩ := healthy_witness key hn hΔ
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) + Δ + 2) ha hf cap i g
      (by linarith) (by linarith) (by linarith)
    exact ⟨⟨_, rho⟩, hw, rfl, ⟨he, hs, hp, ht⟩, hsa, hpa⟩
  · obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    obtain ⟨rho, -, -, hw, hs, hp, hpa, hl, hb⟩ :=
      sleepyStress_witness key hn hΔ _ ha hf cap i hi le_rfl
    exact ⟨i, ⟨_, rho⟩, hw, rfl, ⟨hs, hp, hl⟩, hb, hpa⟩
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
  · obtain ⟨i, hi⟩ := ht cap ho (Fintype.card V)
    have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V)
    have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
      add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
    have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
      have := le_max_right g 0
      have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
      linarith
    obtain ⟨sel, hsel, hprog, hbad⟩ := bad_selection key hn hΔ
      ((max g 0 + (K.params.heal cap i : Time) * Δ) +
        (max g 0 + (K.params.catchUp : Time) * Δ + 1) + (K.params.latency cap i : Time) * Δ +
        progLen F K cap i (⟨Δ, hΔ, allAwake⟩ : Env V) + Δ + 2) allAwake (fun _ => rfl) hf cap i hi
    obtain ⟨rho, hpt, hk, hs, hw, he, hs', hp, hpa, ht', -⟩ := healthy_witness_sel key hn hΔ _ ha
      cap i g sel hsel hprog (by linarith) (by linarith) (by linarith)
    exact ⟨i, ⟨_, rho⟩, hw, rfl, ⟨he, hs', hp, ht'⟩, hpa,
      hbad rho hs hk (congrArg EnvPoint.honest hpt)⟩

end Realize

end Consensus.Shape

end
