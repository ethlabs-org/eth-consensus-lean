module
public import ConsensusShape.Refinement
public import Mathlib.Tactic

@[expose] public section

/-! # Coverage and joint realizability (layer 1)

Two kinds of non-vacuity, both generic over the shape family.

* `coverage` (fixed selection): any well-formed environment point, with any
  PKI and any admissible selection, that satisfies a premise's environment and
  progress parts is exactly the point, PKI and selection of a valid,
  collision-free, conviction-free compiled run satisfying the whole premise.
  The protocol cannot make a premise harder to meet than its environment and
  progress parts.
* `Contract.Realizable` (D-24): the per-value certificate that every premise of
  every provided capability, for every index, is jointly realizable with a
  faulty validator, no hash collision, no conviction, and *active* service
  (`Witness`, `LiveActive`, `ResilienceActive`). `premise_realizable` produces
  witnesses at the extremal point from projections of the skeleton (proposer
  selection size and grid) only; the values (`Values/*`) apply it.

The extremal selection (`extremalSel`) gives every `.sized m` role (`m` below
the population) the keys `1, …, m`, all honest under the extremal PKI
(`extremalKey`), since only validator `0` is faulty. -/

namespace Consensus.Premise

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- The environment part and every needed progress instance give the
evaluation at a point. -/
theorem evalAt_of_evalEnv {p : EnvPoint V} {c : Time} {σ : Nat → Time}
    {prog : Prog → Time → Time → Prop} {P : Premise Prog} (h : P.evalEnv p c σ)
    (hprog : P.UsesProgress → ∀ π s, prog π c s) : P.evalAt p c σ prog := by
  unfold evalEnv at h
  induction P with
  | progress π s => exact hprog trivial π _
  | conj P Q hP hQ =>
    exact ⟨hP h.1 fun hu => hprog (Or.inl hu), hQ h.2 fun hu => hprog (Or.inr hu)⟩
  | _ => exact h

omit [Fintype V] [DecidableEq V] in
/-- Without a `progress` atom every progress condition holds trivially. -/
theorem progressAll_of_not_usesProgress {p : EnvPoint V} {σ : Nat → Time}
    {q : Prog → Time → Prop} {P : Premise Prog} (h : ¬ P.UsesProgress) :
    P.ProgressAll p σ q := by
  induction P with
  | progress π s => exact absurd trivial h
  | conj P Q hP hQ => exact ⟨hP fun hu => h (Or.inl hu), hQ fun hu => h (Or.inr hu)⟩
  | _ => trivial

end Consensus.Premise

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf modelProfile)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-! ## Fixed-selection coverage -/

/-- Fixed-selection coverage. Inputs are fixed, outputs preserve them: the
point `p`, the PKI `key`, an admissible selection `sel`. If the environment and
progress parts of `P` hold at `p` for that PKI and selection (progress =
`PatternRecurrence p key sel .proposer grid`), some valid, collision-free,
conviction-free compiled run has exactly that point, PKI and selection and
satisfies `P` in full. -/
theorem coverage (F : ShapeFamily O Info) (K : Contract O ProgressReq) (P : Premise ProgressReq)
    {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V) (hp : p.WellFormed)
    (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf (compiled F) p.env).selSpec r).Admits (sel r)) (σ : Nat → Time)
    (h : P.evalAt p (((K.catchUp : Nat) : Time) * p.env.Δ) σ
      (fun π c s => PatternRecurrence (R := ShapeRole (F (pubOf p.env)).skel.Kind) p key sel
        ShapeRole.proposer (F (pubOf p.env)).skel.grid π c s)) :
    ∃ rho : Model.Run (compiled F) p.env, rho.point = p ∧ rho.key = key ∧ rho.sel = sel ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
      (sysOf O (compiled F) V).convicted ⟨p.env, rho⟩
        ((sysOf O (compiled F) V).honestEvidence ⟨p.env, rho⟩) = ∅ ∧
      ShapePremise K P σ rho := by
  let hash : (protoOf (compiled F) p.env).Item → Nat := fun x => Encodable.encode x + 1
  obtain ⟨relay, events, hv, hps, hhp, hc⟩ :=
    Model.canonical_run_causal O (compiled F) V p.env p.honest p.horizon hp key sel hsel
      p.submit hash
  let rho := Model.mkRun (F := compiled F) (E := p.env) p.honest p.horizon key sel p.submit
    relay hash events
  refine ⟨rho, rfl, rfl, rfl, hv, ?_, ?_, ?_⟩
  · apply Model.Run.not_hashCollision_of_injective
    intro a b hab
    exact Encodable.encode_injective (Nat.add_right_cancel hab)
  · exact Model.convicted_honestEvidence_eq_empty rho (rho.not_slashable_of_causal hv hc)
  · exact Consensus.Premise.eval_of_evalAt hps (fun b => hhp b) h

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

/-- At the extremal point, a proposer selection `.sized m` with `1 ≤ m ≤ n`
selects honest, ready keys only, and at least one. -/
theorem extremalSel_proposers (F : ShapeFamily O Info) {n m : Nat} {H g : Time}
    {submit : Fin (n + 1) → Time → List Tx} (hm1 : 1 ≤ m) (hm : m ≤ n)
    (hF : (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.proposerSel = .sized m) :
    ∀ s c t, HonestReadyIn (EnvPoint.extremal n H g submit) (extremalKey n)
      (extremalSel F (EnvPoint.extremal n H g submit).env)
      (ShapeRole.proposer s : ShapeRole (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.Kind)
      c t := by
  intro s c t
  have hN : m < Fintype.card (Fin (n + 1)) := by rw [Fintype.card_fin]; omega
  have hsel : extremalSel F (EnvPoint.extremal n H g submit).env (ShapeRole.proposer s) =
      Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m := by
    change extremalKeys (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.proposerSel = _
    rw [hF]
    simp only [extremalKeys, hN, ↓reduceIte]
  unfold HonestReadyIn
  rw [hsel]
  refine ⟨⟨⟨1, by omega⟩, by simp [hm1]⟩, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k.val := (Finset.mem_filter.mp hk).2.1
  have hh : extremalKey n k ∈ (EnvPoint.extremal n H g submit).honest := by
    simp only [EnvPoint.extremal, Finset.mem_erase, Finset.mem_univ, and_true]
    intro h0
    have : (extremalKey n k).val = k.val := rfl
    rw [h0] at this
    simp at this; omega
  exact ⟨hh, hh, fun _ _ _ => rfl⟩

/-! ## Witnesses -/

/-- Progress activity: every `progress π s` occurrence of `P` has a full
recurrence window inside the horizon, so it tests a selection (D-22). -/
def ProgressActive {V : Type} (G : TimeGrid) (p : EnvPoint V) (σ : Nat → Time)
    (P : Premise ProgressReq) : Prop :=
  P.ProgressAll p σ fun π s => max s 0 + ((π.gap : Nat) : Time) * G.slotLen p.env.Δ ≤ p.horizon

/-- A realizability witness for premise `P` at parameters `σ`: a valid run
with a faulty validator, no collision and no conviction, satisfying `P`, whose
progress atoms are active. -/
structure Witness (F : ShapeFamily O Info) (K : Contract O ProgressReq) (P : Premise ProgressReq)
    (σ : Nat → Time) {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop where
  /-- Some validator is faulty. -/
  faulty : rho.point.faulty.Nonempty
  /-- A valid execution. -/
  valid : rho.ExecutionValid
  /-- No hash collision (the excuse does not hold). -/
  noCollision : ¬ rho.HashCollision
  /-- No validator convicted by honest evidence: no escape `α > 0` and no
  accountability conclusion is satisfied by slashing. -/
  noConviction : (sysOf O (compiled F) V).convicted ⟨E, rho⟩
    ((sysOf O (compiled F) V).honestEvidence ⟨E, rho⟩) = ∅
  /-- The premise holds. -/
  premise : ShapePremise K P σ rho
  /-- Every progress atom has a recurrence window inside the horizon. -/
  progressActive : ProgressActive (F (pubOf E)).skel.grid rho.point σ P

/-- Liveness activity: the antecedent of the advertised `TxLive` is inhabited
with the actual deadline `max t gst + Δ + D·Δ` (L0 `TxLiveActive`). -/
def LiveActive (F : ShapeFamily O Info) (K : Contract O ProgressReq) (start : TimeExpr) (D : Nat)
    (σ : Nat → Time) {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop :=
  ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive (((K.catchUp : Nat) : Time) * E.Δ)
    (start.eval rho.point σ) (((D : Nat) : Time) * E.Δ)

/-- Resilience activity: a nonempty outage inside the horizon and a
continuously eligible reader over it. -/
def ResilienceActive (F : ShapeFamily O Info) (K : Contract O ProgressReq) (σ : Nat → Time)
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E) : Prop :=
  0 ≤ σ 0 ∧ σ 0 < σ 1 ∧ σ 1 < σ 2 ∧ σ 2 ≤ rho.horizon ∧
    ∃ w ∈ rho.honest,
      rho.point.AwakeOnClosed w (max 0 (σ 1 - ((K.catchUp : Nat) : Time) * E.Δ - 1)) (σ 2)

/-- The per-value non-vacuity certificate (D-24). Witnesses are chosen per
capability and per index (one finite run cannot serve unbounded indices). -/
structure _root_.Consensus.Contract.Realizable (F : ShapeFamily O Info)
    (K : Contract O ProgressReq) : Prop where
  /-- Every safety premise has a witness. -/
  safety : ∀ c s, K.spec c = some s →
    ∃ σ n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K s.safety.premise σ rho
  /-- Every liveness premise, at every index, has a witness with active
  liveness. -/
  live : ∀ c s, K.spec c = some s → ∀ i : K.Idx,
    ∃ σ n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K (s.live.premise i) σ rho ∧
        LiveActive F K (s.live.start i) (s.live.latency i) σ rho
  /-- Every resilience premise has a witness with an active outage. -/
  resilience : ∀ c s P, K.spec c = some s → s.resilience = some P →
    ∃ σ n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K P σ rho ∧ ResilienceActive F K σ rho
  /-- Every recovery premise, at every index, has a witness with active
  liveness from the recovery point. -/
  recovery : ∀ c s R, K.spec c = some s → s.recovery = some R → ∀ i : K.Idx,
    ∃ σ n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K (R.premise i) σ rho ∧ LiveActive F K (R.start i) (R.latency i) σ rho

/-! ## Generic realizability at the extremal point -/

/-- Joint realizability of one premise at the extremal point, from
projections of the skeleton only: if `P` uses `progress`, one proposer
selection size `m ≥ 1` for every population. The timing constraints and the
progress windows must hold at the extremal point (they depend on `Δ = 1`, the
GST, the horizon and `σ` only). -/
theorem premise_realizable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (P : Premise ProgressReq) (hP : P.WellFormed)
    (hsel : P.UsesProgress → ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m)
    (σ : Nat → Time) (H g : Time) (hH : 0 ≤ H)
    (ht : ∀ n submit, P.TimesHold (EnvPoint.extremal n H g submit) σ)
    (hact : ∀ n submit, ProgressActive (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.grid
      (EnvPoint.extremal n H g submit) σ P) :
    ∃ N, ∀ n, N ≤ n → ∀ submit,
      ∃ rho : Model.Run (compiled F) (EnvPoint.extremal n H g submit).env,
        rho.point = EnvPoint.extremal n H g submit ∧ Witness F K P σ rho := by
  classical
  obtain ⟨N₀, hN₀⟩ := P.extremal_realizable hP
  let m : Nat := if hu : P.UsesProgress then Classical.choose (hsel hu) else 0
  refine ⟨max N₀ m, fun n hn submit => ?_⟩
  let p := EnvPoint.extremal n H g submit
  have henv := hN₀ n (le_of_max_le_left hn) H g submit σ
    (((K.catchUp : Nat) : Time) * p.env.Δ) (ht n submit)
  have hprog : P.UsesProgress → ∀ π s,
      PatternRecurrence (R := ShapeRole (F (pubOf p.env)).skel.Kind) p (extremalKey n)
        (extremalSel F p.env) ShapeRole.proposer (F (pubOf p.env)).skel.grid π
        (((K.catchUp : Nat) : Time) * p.env.Δ) s := by
    intro hu π s
    have hm : m = Classical.choose (hsel hu) := by simp [m, hu]
    obtain ⟨hm1, hmF⟩ := Classical.choose_spec (hsel hu)
    rw [← hm] at hm1 hmF
    apply patternRecurrence_of_all p.env.Δ_pos
    intro s j _
    exact extremalSel_proposers F hm1 (le_of_max_le_right hn) (hmF _) _ _ _
  obtain ⟨rho, hpt, -, -, hv, hnc, hconv, hprem⟩ :=
    coverage F K P p (show 0 ≤ H from hH) (extremalKey n) (extremalSel F p.env)
      (extremalSel_admits F p.env) σ (Premise.evalAt_of_evalEnv henv hprog)
  refine ⟨rho, hpt, ⟨?_, hv, hnc, hconv, hprem, ?_⟩⟩
  · rw [hpt, EnvPoint.extremal_faulty]; exact Finset.singleton_nonempty _
  · rw [hpt]; exact hact n submit

/-- The extremal submission: transaction `42` to validator `1` at `τ₀`. -/
def submit42 {n : Nat} (τ₀ : Time) : Fin (n + 1) → Time → List Tx :=
  fun v t => if v.val = 1 ∧ t = τ₀ then [42] else []

/-- Activity at the extremal point: submission `42` to validator 1 at `τ₀`,
reader validator 2 (honest, never submitted to), everyone awake. -/
theorem extremal_liveActive (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (start : TimeExpr) (D : Nat) (σ : Nat → Time) {n : Nat} {H g τ₀ : Time} (hn : 2 ≤ n)
    (hτ : start.eval (EnvPoint.extremal n H g (submit42 τ₀)) σ ≤ τ₀) (hτ0 : 0 ≤ τ₀)
    (hD : max τ₀ g + 1 + D ≤ H)
    (rho : Model.Run (compiled F) (EnvPoint.extremal n H g (submit42 τ₀)).env)
    (hp : rho.point = EnvPoint.extremal n H g (submit42 τ₀)) :
    LiveActive F K start D σ rho := by
  unfold LiveActive Trace.TxLiveActive
  change ∃ (x : Tx) (t t' : Time) (u w : Fin (n + 1)), start.eval rho.point σ ≤ t ∧ 0 ≤ t ∧
    u ∈ rho.point.honest ∧ rho.point.env.awake u t = true ∧ x ∈ rho.point.submit u t ∧
    w ∈ rho.point.honest ∧ w ≠ u ∧ (∀ τ, x ∉ rho.point.submit w τ) ∧
    max t rho.point.env.gst + rho.point.env.Δ + ((D : Nat) : Time) * rho.point.env.Δ ≤ t' ∧
    t' ≤ rho.point.horizon ∧ rho.point.Ready (((K.catchUp : Nat) : Time) * rho.point.env.Δ) w t'
  rw [hp]
  have h1 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have h2 : (⟨2, by omega⟩ : Fin (n + 1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hon : ∀ v : Fin (n + 1), v ≠ 0 → v ∈ (EnvPoint.extremal n H g (submit42 τ₀)).honest :=
    fun v hv => Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
  refine ⟨42, τ₀, max τ₀ g + 1 + D, ⟨1, by omega⟩, ⟨2, by omega⟩, hτ, hτ0, hon _ h1, rfl,
    by simp [EnvPoint.extremal, submit42], hon _ h2, ?_, ?_, ?_, hD, hon _ h2, fun _ _ _ => rfl⟩
  · intro h; have := congrArg Fin.val h; simp at this
  · intro τ; simp [EnvPoint.extremal, submit42]
  · simp [EnvPoint.extremal]

/-- Activity of a resilience witness at the extremal point. -/
theorem extremal_resilienceActive (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (σ : Nat → Time) {n : Nat} {H g : Time} {submit : Fin (n + 1) → Time → List Tx} (hn : 1 ≤ n)
    (h : 0 ≤ σ 0 ∧ σ 0 < σ 1 ∧ σ 1 < σ 2 ∧ σ 2 ≤ H)
    (rho : Model.Run (compiled F) (EnvPoint.extremal n H g submit).env)
    (hp : rho.point = EnvPoint.extremal n H g submit) :
    ResilienceActive F K σ rho := by
  have hH : rho.horizon = H := congrArg EnvPoint.horizon hp
  have hh : rho.honest = Finset.univ.erase 0 := congrArg EnvPoint.honest hp
  refine ⟨h.1, h.2.1, h.2.2.1, hH ▸ h.2.2.2, ⟨1, by omega⟩, ?_, fun _ _ _ => rfl⟩
  rw [hh]
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  intro h0; have := congrArg Fin.val h0; simp at this

/-- Realizability of a live (or recovery) premise with active liveness:
`premise_realizable` at the extremal submission `submit42 τ₀`, with a
population of at least three. -/
theorem live_realizable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (P : Premise ProgressReq) (hP : P.WellFormed)
    (hsel : P.UsesProgress → ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m)
    (start : TimeExpr) (D : Nat) (σ : Nat → Time) (H g τ₀ : Time)
    (ht : ∀ n submit, P.TimesHold (EnvPoint.extremal n H g submit) σ)
    (hact : ∀ n submit, ProgressActive (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.grid
      (EnvPoint.extremal n H g submit) σ P)
    (hτ : ∀ n, start.eval (EnvPoint.extremal n H g (submit42 τ₀)) σ ≤ τ₀) (hτ0 : 0 ≤ τ₀)
    (hD : max τ₀ g + 1 + D ≤ H) :
    ∃ σ' n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K P σ' rho ∧ LiveActive F K start D σ' rho := by
  have hH : 0 ≤ H := by
    have := le_max_left τ₀ g
    have : (0 : Time) ≤ (D : Time) := by positivity
    linarith
  obtain ⟨N, hN⟩ := premise_realizable F K P hP hsel σ H g hH ht hact
  obtain ⟨rho, hp, hw⟩ := hN (max N 2) (le_max_left _ _) (submit42 τ₀)
  exact ⟨σ, max N 2, _, rho, hw,
    extremal_liveActive F K start D σ (le_max_right _ _) (hτ _) hτ0 hD rho hp⟩

/-- Realizability of a premise without an activity requirement (safety
premises): `premise_realizable` with no submissions. -/
theorem witness_realizable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (P : Premise ProgressReq) (hP : P.WellFormed)
    (hsel : P.UsesProgress → ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m)
    (σ : Nat → Time) (H g : Time) (hH : 0 ≤ H)
    (ht : ∀ n submit, P.TimesHold (EnvPoint.extremal n H g submit) σ)
    (hact : ∀ n submit, ProgressActive (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.grid
      (EnvPoint.extremal n H g submit) σ P) :
    ∃ σ' n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E), Witness F K P σ' rho := by
  obtain ⟨N, hN⟩ := premise_realizable F K P hP hsel σ H g hH ht hact
  obtain ⟨rho, -, hw⟩ := hN N le_rfl fun _ _ => []
  exact ⟨σ, N, _, rho, hw⟩

/-- Realizability of a resilience premise with an active outage
(`0 ≤ σ 0 < σ 1 < σ 2 ≤ H`). -/
theorem resilience_realizable (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (P : Premise ProgressReq) (hP : P.WellFormed)
    (hsel : P.UsesProgress → ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m)
    (σ : Nat → Time) (H g : Time)
    (ht : ∀ n submit, P.TimesHold (EnvPoint.extremal n H g submit) σ)
    (hact : ∀ n submit, ProgressActive (F (pubOf (EnvPoint.extremal n H g submit).env)).skel.grid
      (EnvPoint.extremal n H g submit) σ P)
    (hσ : 0 ≤ σ 0 ∧ σ 0 < σ 1 ∧ σ 1 < σ 2 ∧ σ 2 ≤ H) :
    ∃ σ' n, ∃ (E : Env (Fin (n + 1))) (rho : Model.Run (compiled F) E),
      Witness F K P σ' rho ∧ ResilienceActive F K σ' rho := by
  have hH : 0 ≤ H := by linarith [hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2]
  obtain ⟨N, hN⟩ := premise_realizable F K P hP hsel σ H g hH ht hact
  obtain ⟨rho, hp, hw⟩ := hN (max N 1) (le_max_left _ _) fun _ _ => []
  exact ⟨σ, max N 1, _, rho, hw,
    extremal_resilienceActive F K σ (le_max_right _ _) hσ rho hp⟩

/-- The relay is exercised: in a partially synchronous run where every
validator is always awake, an active liveness witness has an honest reader
that receives the submitted transaction by relay, never by its own
submission. -/
theorem active_relay {F : ShapeFamily O Info} {K : Contract O ProgressReq} {start : TimeExpr}
    {D : Nat} {σ : Nat → Time} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (rho : Model.Run (compiled F) E) (hs : rho.PartialSynchrony)
    (hawake : ∀ v t, E.awake v t = true) (ha : LiveActive F K start D σ rho) :
    ∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ := by
  obtain ⟨x, t, t', u, w, -, ht0, hu, hua, hx, hw, -, hnw, hdl, hth, -⟩ := ha
  change u ∈ rho.honest at hu
  change w ∈ rho.honest at hw
  change x ∈ rho.submit u t at hx
  change ∀ τ, x ∉ rho.submit w τ at hnw
  change max t E.gst + E.Δ + ((D : Nat) : Time) * E.Δ ≤ t' at hdl
  change t' ≤ rho.horizon at hth
  have hDΔ : 0 ≤ ((D : Nat) : Time) * E.Δ := mul_nonneg (by positivity) E.Δ_pos.le
  have hd : max t E.gst + E.Δ ≤ rho.horizon := by linarith
  obtain ⟨τ, hτ, -, hxτ⟩ := hs.txs u hu x t ht0 hua hx w hw t le_rfl hd hd
    (fun z _ _ => hawake w z)
  refine ⟨x, w, hw, hnw, τ, hτ, ?_⟩
  rcases List.mem_append.mp hxτ with h | h
  · exact absurd h (hnw τ)
  · exact h

end Consensus.Shape

end
