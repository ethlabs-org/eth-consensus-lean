module
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import ConsensusLean.Lemmas.Model.Causal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GuardIdle
import ConsensusLean.Lemmas.Model.Laws
import ConsensusLean.Lemmas.Model.Adequate
import ConsensusLean.Lemmas.Problem.Facts.Network
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Non-vacuity of continuation after healing (`Continues.realizable`)

`handover_realizable`: for every chain-shape family whose progress requirements are recurrences
fitting its skeleton and whose honest own-signed candidates are conflict-free on every valid run
(`GuardIdleAlways`), at admissible numbers with explicit `θ ≤ ½` and `β ≤ ⅓` premises, and at
least five validators, every
`ΔAC > 1`, `ΔFG > 1` within the FG delay bound and every GST `g` have a valid excuse-free run that
hands over to the sleepy regime at the heal point `T = max g 0 + heal·ΔAC`, with
`⌈n/3⌉ ≥ β·n` validators compromised from `κ = T + 1` on and both continuation claims active
after `κ`. `continues_realizable` is its Goldilocks instance, the `realizable` field of
`Continues` at the headline contract.

The witness point: everyone awake; a set of `⌈n/3⌉ = (n + 2) / 3` validators compromised at `κ`,
nobody before; transaction `42` submitted at `0` to a validator outside that set. The committee
is the one the extremal selection reads at every time (`extremalCommittee`: every validator
without a participation kind, else the fixed set or the first `m` keys of a sized one), and the
compromised set takes the validators outside it first (`exists_handover_faults`): a nonempty
committee of `m` members then has `max 0 (⌈n/3⌉ − (n − m))` of them compromised, fewer than half
of it (`m ≤ n − ⌈n/3⌉`: none; otherwise `m < 2 (n − ⌈n/3⌉)` since `2 ⌈n/3⌉ < n` for `n ≥ 5`). The
run is the canonical causal run from GST `g` under the extremal selection with a validator
outside the compromised set proposing every one-proposer slot (`handoverSel`). Up to `T` nobody
is compromised (healthy, full participation, every nonempty committee healthy); from `T` on the
retained view of every look-ahead has at most `⌈n/3⌉ < n/2` faults and every other validator
ready, so the sleepy bound holds at `θ ≤ ½`, and every nonempty committee keeps more ready
members than compromised ones, so the committee sleepy bound and the cross-boundary bound hold
too. The causal run, whose honest own-signed candidates are conflict-free, convicts nobody on
honest evidence, so no two honest views convict anyone (`ConvictedBelow`). The proposer and a
second validator outside the compromised set are the liveness reader and the two safety readers
after `κ`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The hand-over fault set**: for at least five keys and every committee `C`, a set of
`(N + 2) / 3` keys of which fewer than half of a nonempty `C` are members, and two keys outside it.
It takes the keys outside `C` first: when they are at least `(N + 2) / 3` it misses `C`; otherwise
it takes `(N + 2) / 3 − (N − |C|)` members of `C`, fewer than half of `C` since
`2 · (N + 2) / 3 < N`. -/
private theorem exists_handover_faults {N : Nat} (hn : 5 ≤ N) (C : Finset (Fin N)) :
    ∃ F : Finset (Fin N), F.card = (N + 2) / 3 ∧ (C.Nonempty → 2 * (F ∩ C).card < C.card) ∧
      ∃ q b, q ≠ b ∧ q ∉ F ∧ b ∉ F := by
  classical
  have hD : Cᶜ.card + C.card = N := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := C.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨F, hFc, hFC⟩ : ∃ F : Finset (Fin N), F.card = (N + 2) / 3 ∧
      (C.Nonempty → 2 * (F ∩ C).card < C.card) := by
    rcases le_or_gt ((N + 2) / 3) Cᶜ.card with h | h
    · obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq h
      refine ⟨F, hFc, fun hne => ?_⟩
      have h0 : F ∩ C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
        (Finset.disjoint_of_subset_left hF disjoint_compl_left)
      rw [h0, Finset.card_empty]
      have := hne.card_pos
      omega
    · obtain ⟨G, hG, hGc⟩ := Finset.exists_subset_card_eq (s := C)
        (n := (N + 2) / 3 - Cᶜ.card) (by omega)
      have hdisj : Disjoint Cᶜ G := Finset.disjoint_of_subset_right hG disjoint_compl_left
      refine ⟨Cᶜ ∪ G, by rw [Finset.card_union_of_disjoint hdisj]; omega, fun _ => ?_⟩
      have hGC : (Cᶜ ∪ G) ∩ C = G := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
        constructor
        · rintro ⟨hx | hx, hxC⟩
          · exact absurd hxC hx
          · exact hx
        · intro hx
          exact ⟨Or.inr hx, hG hx⟩
      rw [hGC, hGc]
      omega
  refine ⟨F, hFc, hFC, ?_⟩
  have h2 : 1 < Fᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨q, hq, b, hb, hqb⟩ := Finset.one_lt_card.mp h2
  exact ⟨q, b, hqb, Finset.mem_compl.mp hq, Finset.mem_compl.mp hb⟩

/-- The extremal keys of a specification, with key `q` alone for a one-key specification. -/
private def proposerKeys {N : Nat} (q : Fin N) : Model.SelSpec N → Finset (Fin N)
  | .fixed T => T
  | .sized m => if m = 1 then {q} else extremalKeys (.sized m)

private theorem proposerKeys_admits {N : Nat} (q : Fin N) (s : Model.SelSpec N) :
    s.Admits (proposerKeys q s) := by
  cases s with
  | fixed T => rfl
  | sized m =>
    by_cases hm : m = 1
    · subst hm
      change ({q} : Finset (Fin N)).card = min 1 N
      rw [Finset.card_singleton]
      have := q.pos
      omega
    · change (if m = 1 then {q} else extremalKeys (.sized m)).card = min m N
      rw [ite_eq_right hm]
      exact extremalKeys_admits (.sized m)

/-- The extremal selection with key `q` the proposer of every one-proposer slot. -/
private def handoverSel (F : ChainShapeFamily O Info) (E : Env V) (q : Fin (Fintype.card V)) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => match r with
    | .proposer s => proposerKeys q ((F (pubOf E)).skel.proposerSel s)
    | r => extremalSel F E r

omit [DecidableEq V] in
private theorem handoverSel_admits (F : ChainShapeFamily O Info) (E : Env V)
    (q : Fin (Fintype.card V)) :
    (protoOf (compiled F) E).SelAdmits (handoverSel F E q) := by
  intro r
  cases r with
  | proposer s => exact proposerKeys_admits q ((F (pubOf E)).skel.proposerSel s)
  | poll => exact extremalSel_admits F E .poll
  | duty s k => exact extremalSel_admits F E (.duty s k)

omit [DecidableEq V] in
/-- With one proposer per slot, key `q` is the only proposer of every slot. -/
private theorem handoverSel_proposer_mem (F : ChainShapeFamily O Info) {E : Env V}
    (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1) (q : Fin (Fintype.card V))
    (s : Slot) (k : Fin (Fintype.card V)) :
    k ∈ handoverSel F E q (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔ k = q := by
  change k ∈ proposerKeys q ((F (pubOf E)).skel.proposerSel s) ↔ k = q
  rw [hF]
  exact Finset.mem_singleton

/-- The hand-over witness point: everyone awake, the validators of `Fv` compromised from `κ` on,
transaction `42` submitted to `src` at `0`. -/
private def handoverPoint (Fv : Finset V) (src : V) (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time)
    (hΔF : 0 < ΔF) (H κ : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, ΔF, hΔF, allAwake⟩, fun t => if κ ≤ t then Fv else ∅,
    by
      intro a b hab
      dsimp only
      split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _,
    H, fun v t => if v = src ∧ t = 0 then [42] else []⟩

section Point

variable (Fv : Finset V) (src : V) {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H κ : Time)

omit [Fintype V] in
private theorem handoverPoint_faulty (t : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).faultyAt t = if κ ≤ t then Fv else ∅ := by rfl

omit [Fintype V] in
private theorem handoverPoint_faulty_subset (t : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).faultyAt t ⊆ Fv := by
  rw [handoverPoint_faulty]
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.empty_subset _

omit [Fintype V] in
private theorem handoverPoint_submit (v : V) (t : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).submit v t =
      if v = src ∧ t = 0 then [42] else [] := by rfl

omit [Fintype V] in
private theorem handoverPoint_honest {v : V} (hv : v ∉ Fv) (t : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).HonestAt v t :=
  fun h => hv (handoverPoint_faulty_subset Fv src hΔ hΔF H κ t h)

omit [Fintype V] in
private theorem handoverPoint_ready {v : V} (hv : v ∉ Fv) (c t : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).Ready c v t :=
  ⟨handoverPoint_honest Fv src hΔ hΔF H κ hv t, fun _ _ _ => allAwake_apply _ _⟩

/-- At `θ ≤ ½` the sleepy bound holds everywhere when fewer than half of the validators are
compromised: every retained view has every other validator ready. -/
private theorem handoverPoint_sleepy (hF : 2 * Fv.card + 1 ≤ Fintype.card V) {θ : ℚ}
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2) (c W a b : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).SleepyOn θ c W a b := by
  intro t _ _
  set p := handoverPoint Fv src Δ hΔ ΔF hΔF H κ
  set d := p.lookAhead W t
  have hsub : Finset.univ \ p.faultyAt d ⊆ (p.retain d).readyAt c t := by
    intro v hv
    simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_sdiff.mp hv).2, fun _ _ _ => allAwake_apply _ _⟩
  have hf : (p.faultyAt d).card ≤ Fv.card :=
    Finset.card_le_card (handoverPoint_faulty_subset Fv src hΔ hΔF H κ d)
  have hR := Finset.card_le_card hsub
  rw [Finset.card_univ_sdiff] at hR
  have hRF : Fintype.card V ≤ ((p.retain d).readyAt c t).card + (p.faultyAt d).card := by omega
  have h2 : 2 * (p.faultyAt d).card + 1 ≤ Fintype.card V := by omega
  unfold EnvPoint.ReadyAbove EnvPoint.faultCount
  change θ * (((p.retain d).readyAt c t).card + (p.faultyAt d).card : ℚ) < _
  have hRF' : ((Fintype.card V : ℕ) : ℚ) ≤
      (((p.retain d).readyAt c t).card : ℚ) + ((p.faultyAt d).card : ℚ) := by exact_mod_cast hRF
  have h2' : 2 * ((p.faultyAt d).card : ℚ) + 1 ≤ ((Fintype.card V : ℕ) : ℚ) := by
    exact_mod_cast h2
  linarith only [hRF', h2', mul_le_mul_of_nonneg_right hθ.2
    (by positivity : (0 : ℚ) ≤ (((p.retain d).readyAt c t).card : ℚ) + (p.faultyAt d).card)]

/-- At `θ ≤ ½` the committee sleepy bound holds everywhere when fewer than half of every nonempty
committee is in `Fv`: the members outside the retained faults are ready. -/
private theorem handoverPoint_committeeSleepy (K : Time → Finset V)
    (hK : ∀ t, (K t).Nonempty → 2 * (Fv ∩ K t).card < (K t).card) {θ : ℚ}
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2) (c W a b : Time) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).CommitteeSleepyOn K θ 0 c W a b := by
  intro t _ _ hne
  set p := handoverPoint Fv src Δ hΔ ΔF hΔF H κ
  set d := p.lookAhead W t
  change (if (0 : Time) ≤ 0 then _ else _)
  simp only [le_refl, ↓reduceIte]
  have hR : (p.retain d).readyAt c t ∩ K t = K t \ p.faultyAt d := by
    ext v
    simp only [EnvPoint.readyAt, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hv, -⟩, hvK⟩
      exact ⟨hvK, hv⟩
    · rintro ⟨hvK, hv⟩
      exact ⟨⟨hv, fun _ _ _ => allAwake_apply _ _⟩, hvK⟩
  have hF : 2 * (p.faultyAt d ∩ K t).card < (K t).card :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.inter_subset_inter_right
      (handoverPoint_faulty_subset Fv src hΔ hΔF H κ d)))) (hK t hne)
  have hsplit := Finset.card_sdiff_add_card_inter (K t) (p.faultyAt d)
  rw [Finset.inter_comm (K t) (p.faultyAt d)] at hsplit
  change θ * ((((p.retain d).readyAt c t ∩ K t).card + (p.faultyAt d ∩ K t).card : Nat) : ℚ) <
    (((p.retain d).readyAt c t ∩ K t).card : ℚ)
  rw [hR]
  have hlt : ((p.faultyAt d ∩ K t).card : ℚ) < ((K t \ p.faultyAt d).card : ℚ) := by
    exact_mod_cast (by omega : (p.faultyAt d ∩ K t).card < (K t \ p.faultyAt d).card)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hθ.2 (by positivity :
    (0 : ℚ) ≤ ((K t \ p.faultyAt d).card : ℚ) + ((p.faultyAt d ∩ K t).card : ℚ))]

omit [Fintype V] in
/-- Fewer than half of every nonempty committee is ever compromised. -/
private theorem handoverPoint_committee_half (K : Time → Finset V)
    (hK : ∀ t, (K t).Nonempty → 2 * (Fv ∩ K t).card < (K t).card) (u d : Time)
    (hne : (K u).Nonempty) :
    2 * ((handoverPoint Fv src Δ hΔ ΔF hΔF H κ).faultyAt d ∩ K u).card < (K u).card :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.inter_subset_inter_right
    (handoverPoint_faulty_subset Fv src hΔ hΔF H κ d)))) (hK u hne)

/-- No faults before `κ`: healthy, with full participation, up to any `T < κ`. -/
private theorem handoverPoint_healthy (hn : 0 < Fintype.card V) {β : ℚ} (hβ : 0 < β)
    (g T : Time) (hT : T < κ) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).HealthyOn β g T := by
  refine ⟨?_, fun _ _ _ _ _ => allAwake_apply _ _⟩
  unfold EnvPoint.faultCount
  rw [handoverPoint_faulty, ite_eq_right (not_le.mpr hT), Finset.card_empty, Nat.cast_zero]
  have hn' : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  exact mul_pos hβ hn'

omit [Fintype V] in
/-- No faults before `κ`: every nonempty committee is healthy up to any `T < κ`. -/
private theorem handoverPoint_committeeHealthy (K : Time → Finset V) {β : ℚ} (hβ : 0 < β)
    (a T : Time) (hT : T < κ) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).CommitteeHealthyOn K β a T := by
  intro t _ _ hne
  rw [handoverPoint_faulty, ite_eq_right (not_le.mpr hT), Finset.empty_inter, Finset.card_empty,
    Nat.cast_zero]
  have hc : (0 : ℚ) < (K t).card := by exact_mod_cast hne.card_pos
  exact mul_pos hβ hc

/-- At `κ` at least fraction `β ≤ ⅓` of the validators are compromised. -/
private theorem handoverPoint_beta (hcard : Fv.card = (Fintype.card V + 2) / 3) {β : ℚ}
    (hβ : β ≤ 1 / 3) :
    β * Fintype.card V ≤ ((handoverPoint Fv src Δ hΔ ΔF hΔF H κ).faultCount κ : ℚ) := by
  unfold EnvPoint.faultCount
  rw [handoverPoint_faulty, ite_eq_left le_rfl, hcard]
  have h3 : ((Fintype.card V : ℕ) : ℚ) ≤ 3 * (((Fintype.card V + 2) / 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : Fintype.card V ≤ 3 * ((Fintype.card V + 2) / 3))
  linarith only [h3, mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg (α := ℚ) (Fintype.card V))]

/-- The proposer `key q`, never compromised and always awake, proposes every slot: every fitting
recurrence holds on every window. -/
private theorem handoverPoint_holds (key : Fin (Fintype.card V) ≃ V) (q : Fin (Fintype.card V))
    (hq : key q ∉ Fv) (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (hrec : ∀ cap i, ∃ ρ, K.progress cap i = .recur ρ)
    (cap : Capability) (i : K.Idx) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (handoverPoint Fv src Δ hΔ ΔF hΔF H κ)
      (key, handoverSel F (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).env q) := by
  obtain ⟨ρ, hρ⟩ := hrec cap i
  have hfit := hf cap i (pubOf (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).env)
  rw [hρ] at hfit ⊢
  change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
  apply patternRecurrence_of_all
  intro sl j _
  have hmem := handoverSel_proposer_mem F hfit q (sl + j)
  refine ⟨⟨q, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
  obtain rfl := (hmem k).mp hk
  exact ⟨handoverPoint_ready Fv src hΔ hΔF H κ hq _ _, handoverPoint_honest Fv src hΔ hΔF H κ hq _⟩

omit [Fintype V] in
/-- Liveness is active after `start`: transaction `42`, submitted to `src` at `0`, is owed to `b`
at the horizon. -/
private theorem handoverPoint_txLiveActive {b : V} (hsrc : src ∉ Fv) (hb : b ∉ Fv)
    (hne : b ≠ src) (c start D : Time) (hH : max 0 start + Δ + D ≤ H) :
    (handoverPoint Fv src Δ hΔ ΔF hΔF H κ).TxLiveActive c start D := by
  refine ⟨42, 0, H, src, b, le_rfl, handoverPoint_honest Fv src hΔ hΔF H κ hsrc _,
    allAwake_apply _ _, ?_, hne, ?_, hH, le_rfl,
    handoverPoint_ready Fv src hΔ hΔF H κ hb _ _⟩
  · simp only [handoverPoint_submit, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false]
  · intro τ
    simp only [handoverPoint_submit, hne, false_and, ↓reduceIte, List.not_mem_nil,
      not_false_eq_true]

omit [Fintype V] in
/-- Safety is active after `t₀`: `src` and `b` ready at `t₀ + 1`, `src` again at `t₀ + 2`. -/
private theorem handoverPoint_safeActive {b : V} (hsrc : src ∉ Fv) (hb : b ∉ Fv) (hne : b ≠ src)
    (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (handoverPoint Fv src Δ hΔ ΔF hΔF H κ) :=
  ⟨src, b, t₀ + 1, t₀ + 2, hne.symm, lt_add_one t₀, add_lt_add_right one_lt_two t₀, hH,
    handoverPoint_ready Fv src hΔ hΔF H κ hsrc _ _, handoverPoint_ready Fv src hΔ hΔF H κ hb _ _,
    handoverPoint_ready Fv src hΔ hΔF H κ hsrc _ _⟩

end Point

/-- **Hand-over witness**: for a family whose progress requirements are fitting recurrences and
whose honest own-signed candidates are conflict-free on every valid run (`GuardIdleAlways`), at
admissible numbers with explicit `θ ≤ ½` and `β ≤ ⅓` premises and at least five validators,
every `ΔAC > 1`, `ΔFG > 1` within the FG delay bound and every GST `g` have a valid excuse-free
run that hands over at the heal point `T`, with at least fraction `β` compromised by `κ = T + 1`,
progress from `ready` to the horizon, and liveness and safety active after `κ`.

The committee is the one the extremal selection reads at every time (`extremalCommittee`), and
the compromised validators are a set of `(n + 2) / 3` with fewer than half of a nonempty
committee (`exists_handover_faults`): the selected committees are healthy up to `T` (nobody is
compromised before `κ`), keep a ready majority after it, and keep fewer than half compromised
through every look-ahead. The proposer and the two readers are outside the compromised set. -/
theorem handover_realizable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (ha : K.params.Admissible) (hθ : K.params.θ ≤ 1 / 2)
    (hβ : K.params.β ≤ 1 / 3) (hf : ProgressFits K F) (hg : GuardIdleAlways F)
    (hrec : ∀ cap i, ∃ ρ, K.progress cap i = .recur ρ) (hn : 5 ≤ Fintype.card V)
    (cap : Capability) (i : K.Idx) (Δ ΔF g : Time) (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (hr : ΔF ≤ (K.params.fgDelay : Time) * Δ) :
    ∃ r T κ, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ ((Sys F V).pt r).env.ΔAC = Δ ∧
      ((Sys F V).pt r).env.ΔFG = ΔF ∧ (Sys F V).Handover (shapeProgress F V).toExternal K g T r ∧
      (Sys F V).heal K cap i g r ≤ T ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g r)
        ((Sys F V).pt r).horizon r ∧
      K.params.β * Fintype.card V ≤ (((Sys F V).pt r).faultCount κ : ℚ) ∧
      ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r) κ ((Sys F V).lat K cap i r) ∧
      SafeActive ((Sys F V).cDur K r) κ ((Sys F V).pt r) := by
  have hΔ := zero_lt_one.trans hΔ1
  have hΔF := zero_lt_one.trans hΔF1
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let T := max g 0 + (K.params.heal cap i : Time) * Δ
  let κ := T + 1
  let H := κ + Δ + (K.params.latency cap i : Time) * Δ + 2
  have hheal : 0 ≤ (K.params.heal cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hT0 : 0 ≤ T := add_nonneg (le_max_right _ _) hheal
  have hH : 0 ≤ H := by dsimp only [H, κ]; linarith
  -- the committee read at every time, and the compromised set against it
  let E : Env V := ⟨Δ, hΔ, ΔF, hΔF, allAwake⟩
  obtain ⟨Fi, hFc, hFC, q, b, hqb, hq, hb⟩ := exists_handover_faults hn (extremalCommittee F E)
  let Fv := Fi.map key.toEmbedding
  have hq' : key q ∉ Fv := fun h => hq ((Finset.mem_map' key.toEmbedding).mp h)
  have hb' : key b ∉ Fv := fun h => hb ((Finset.mem_map' key.toEmbedding).mp h)
  have hne : key b ≠ key q := fun h => hqb (key.injective h).symm
  have hFv : Fv.card = (Fintype.card V + 2) / 3 := by rw [Finset.card_map, hFc]
  let p := handoverPoint Fv (key q) Δ hΔ ΔF hΔF H κ
  let sel := handoverSel F p.env q
  have hsel : ∀ t, (shapeProgress F V).selected p.env (key, sel) t =
      (extremalCommittee F E).map key.toEmbedding :=
    selected_of_duty F p.env key sel fun _ _ => rfl
  have hK : ∀ t, ((shapeProgress F V).selected p.env (key, sel) t).Nonempty →
      2 * (Fv ∩ (shapeProgress F V).selected p.env (key, sel) t).card <
        ((shapeProgress F V).selected p.env (key, sel) t).card := by
    intro t hne'
    rw [hsel] at hne' ⊢
    rw [← Finset.map_inter, Finset.card_map, Finset.card_map]
    exact hFC (Finset.map_nonempty.mp hne')
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.faultyAt p.faultyAt_mono H hH key
      sel (handoverSel_admits F p.env q) p.submit hash g
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono H events key
    sel p.submit relay hash
  let r : (Sys F V).Run := ⟨p.env, rho⟩
  have hnc : ¬ rho.HashCollision :=
    Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  have hconv := Model.convicted_honestEvidence_eq_empty (O := O) rho hv
    (rho.not_slashable_of_causal hc (hg V r hv))
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  have hL := Model.sysOf_laws O (compiled F) V
  have hFn : 2 * Fv.card + 1 ≤ Fintype.card V := by rw [hFv]; omega
  refine ⟨r, T, κ, hv, hnc, rfl, rfl,
    ⟨hse.psync le_rfl hΔ1 hΔF1,
      handoverPoint_healthy Fv (key q) hΔ hΔF H κ (by omega) ha.β_range.1 g T (lt_add_one T), hr,
      handoverPoint_sleepy Fv (key q) hΔ hΔF H κ hFn ⟨ha.θ_range.1, hθ⟩ _ _ _ _, ?_,
      handoverPoint_committeeHealthy Fv (key q) hΔ hΔF H κ _ ha.β_range.2 _ T (lt_add_one T),
      handoverPoint_committeeSleepy Fv (key q) hΔ hΔF H κ _ hK ⟨ha.θ_range.1, hθ⟩ _ _ _ _,
      fun u _ _ hne' => handoverPoint_committee_half Fv (key q) hΔ hΔF H κ _ hK u _ hne'⟩,
    le_rfl, handoverPoint_holds Fv (key q) hΔ hΔF H κ key q hq' F K hf hrec cap i _ _ _,
    handoverPoint_beta Fv (key q) hΔ hΔF H κ hFv hβ,
    handoverPoint_txLiveActive Fv (key q) hΔ hΔF H κ hq' hb' hne _ _ _ ?_,
    handoverPoint_safeActive Fv (key q) hΔ hΔF H κ hq' hb' hne _ _ ?_⟩
  · intro u v i j hi hj hu hw
    have hsub : Consensus.convicted ((Sys F V).convicts r) ((Sys F V).view r u i ∪
        (Sys F V).view r v j) ⊆ Consensus.convicted ((Sys F V).convicts r)
          ((Sys F V).honestEvidenceBy r H) := by
      intro x hx
      unfold Consensus.convicted at hx ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine hL.convicts_mono r _ _ x ?_ hx
      rintro o (ho | ho)
      · exact ⟨u, i, hi, (hL.trace r hv).cutTime_le_horizon i hi, hu, ho⟩
      · exact ⟨v, j, hj, (hL.trace r hv).cutTime_le_horizon j hj, hw, ho⟩
    have hempty : Consensus.convicted ((Sys F V).convicts r) ((Sys F V).view r u i ∪
        (Sys F V).view r v j) = ∅ := Finset.subset_empty.mp (hconv ▸ hsub)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hα : 0 < K.params.α := ha.β_range.1.trans_le ha.α_range.1
    have hn' : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    exact mul_pos hα hn'
  · change max 0 κ + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    rw [max_eq_right (by dsimp only [κ]; linarith)]
    dsimp only [H]; linarith
  · dsimp only [H]; linarith

end Consensus.Shape

namespace Consensus.Goldilocks

open AsChainShape
open Blocks Shape

/-- **Continuation is not vacuous** for Goldilocks: the `realizable` field of `Continues` for the
compiled family at the headline contract, from `handover_realizable` (every Goldilocks progress
requirement is a recurrence with one proposer per slot, `β = ⅓`, and its honest own-signed
candidates are conflict-free on every valid run, `GuardIdleAlways` by `Simulation.guardIdle`). -/
theorem continues_realizable (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    5 ≤ Fintype.card V → ∀ cap i (ΔAC ΔFG g : Time), (cap = .available ∨ cap = .stable) →
      1 < ΔAC → 1 < ΔFG → ΔFG ≤ (K.params.fgDelay : Time) * ΔAC → 0 ≤ g →
      ∃ r T κ, Sy.Valid r ∧ ¬ Sy.Excuse r ∧ (Sy.pt r).env.ΔAC = ΔAC ∧
        (Sy.pt r).env.ΔFG = ΔFG ∧ Sy.Handover (shapeProgress (goldilocks S) V).toExternal K g T r ∧
        Sy.heal K cap i g r ≤ T ∧
        Sy.prog (shapeProgress (goldilocks S) V)
          K cap i (Sy.ready K g r) (Sy.pt r).horizon r ∧
        K.params.β * Fintype.card V ≤ ((Sy.pt r).faultCount κ : ℚ) ∧
        (Sy.pt r).TxLiveActive (Sy.cDur K r) κ (Sy.lat K cap i r) ∧
        SafeActive (Sy.cDur K r) κ (Sy.pt r) := by
  intro Sy K hn cap i ΔAC ΔFG g _ hΔ hΔF hr _
  have ha : K.params.Admissible :=
    { catchUp_pos := (contract_coefficients S A).catchUp.pos
      θ_range := by norm_num [K, Params.standard]
      β_range := by norm_num [K, Params.standard]
      α_range := by norm_num [K, Params.standard]
      budget_pos := by have := S.two_le_k; dsimp [K, Params.standard]; omega }
  exact handover_realizable (goldilocks S) K ha
    (by norm_num [K, Params.standard])
    (by norm_num [K, Params.standard]) (fun _ _ _ _ => rfl)
    (fun _ _ _ r hv => Simulation.guardIdle _ r.2 hv)
    (fun _ _ => ⟨_, rfl⟩) hn cap i ΔAC ΔFG g hΔ hΔF hr

end Consensus.Goldilocks

end
