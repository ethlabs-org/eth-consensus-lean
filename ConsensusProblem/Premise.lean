module
public import ConsensusProblem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # The premise language (layer 0)

Claim premises are written in a closed language: times built from `0`, the
GST, the horizon and claim parameters; environment atoms (fault bounds and
participation fractions, evaluated at one time); and three execution atoms
whose meaning is fixed below the protocol: partial synchrony and synchrony up
to a time (fixed by the execution model), and a progress requirement (fixed by
the protocol shape from reviewed building blocks). There is no disjunction or
negation: every well-formed environment atom holds at large enough extremal
points, so the environment part of a well-formed premise holds there whenever
its timing constraints hold (`Premise.extremal_realizable`). Well-formedness
also keeps the horizon and the claim parameters unbounded: timing constraints
never bound them from above by a fixed time (`Premise.TimesHold.shift`), so a
premise cannot restrict its claims to short runs or early times. -/

namespace Consensus

/-- Times in premises. `param i` is the `i`-th claim parameter; `add e d` is
`e + d` units; `addΔ e k` is `e + k·Δ`. -/
inductive TimeExpr where
  | zero
  | gst
  | horizon
  | param (i : Nat)
  | add (e : TimeExpr) (d : Int)
  | addΔ (e : TimeExpr) (k : Int)

namespace TimeExpr

/-- The value of a time expression at an environment point with parameters `σ`. -/
def eval {V : Type} (p : EnvPoint V) (σ : Nat → Time) : TimeExpr → Time
  | zero => 0
  | gst => p.env.gst
  | horizon => p.horizon
  | param i => σ i
  | add e d => e.eval p σ + d
  | addΔ e k => e.eval p σ + k * p.env.Δ

/-- The protected read time `T` of a resilience claim (parameter 0). -/
abbrev protectedAt : TimeExpr := .param 0

/-- The outage start `b₀` of a resilience claim (parameter 1). -/
abbrev outageStart : TimeExpr := .param 1

/-- The outage end `b₁` of a resilience claim (parameter 2); it appears in
premises only. -/
abbrev outageEnd : TimeExpr := .param 2

/-- The horizon does not occur. -/
def HorizonFree : TimeExpr → Prop
  | horizon => False
  | add e _ => e.HorizonFree
  | addΔ e _ => e.HorizonFree
  | _ => True

/-- A fixed time: built on `0` or the GST (no parameter, no horizon). -/
def Fixed : TimeExpr → Prop
  | zero => True
  | gst => True
  | add e _ => e.Fixed
  | addΔ e _ => e.Fixed
  | _ => False

section Shift

variable {V : Type} (p : EnvPoint V) (σ : Nat → Time) {d e : Time}

/-- A fixed time does not move when the parameters move by `d` and the horizon
by `d + e`. -/
theorem eval_shift_fixed {a : TimeExpr} (h : a.Fixed) :
    a.eval { p with horizon := p.horizon + d + e } (fun i => σ i + d) = a.eval p σ := by
  induction a with
  | zero => rfl
  | gst => rfl
  | horizon => exact h.elim
  | param i => exact h.elim
  | add a k ih => simp only [eval]; rw [ih h]
  | addΔ a k ih => simp only [eval]; rw [ih h]

/-- A horizon-free time moves by at most `d`. -/
theorem eval_shift_le (hd : 0 ≤ d) {a : TimeExpr} (h : a.HorizonFree) :
    a.eval { p with horizon := p.horizon + d + e } (fun i => σ i + d) ≤ a.eval p σ + d := by
  induction a with
  | zero => simp [eval, hd]
  | gst => simp [eval, hd]
  | horizon => exact h.elim
  | param i => exact le_rfl
  | add a k ih => have := ih h; simp only [eval]; linarith
  | addΔ a k ih => have := ih h; simp only [eval]; linarith

/-- A time that is not fixed moves by at least `d`. -/
theorem eval_shift_ge (he : 0 ≤ e) {a : TimeExpr} (h : ¬ a.Fixed) :
    a.eval p σ + d ≤ a.eval { p with horizon := p.horizon + d + e } (fun i => σ i + d) := by
  induction a with
  | zero => exact absurd trivial h
  | gst => exact absurd trivial h
  | horizon => simp only [eval]; linarith
  | param i => exact le_rfl
  | add a k ih => have := ih h; simp only [eval]; linarith
  | addΔ a k ih => have := ih h; simp only [eval]; linarith

end Shift

end TimeExpr

/-- Environment atoms, evaluated at one time with catch-up `c`. -/
inductive EnvAtom where
  /-- `|faulty| < β·n` (independent of time). -/
  | faultsBelow (β : ℚ)
  /-- `θ·(|ready| + |faulty|) < |ready|`. -/
  | readyAbove (θ : ℚ)
  /-- `|faulty| ≤ m` (independent of time; an absolute fault bound). -/
  | faultsAtMost (m : Nat)
  /-- `φ·n < |ready|`. -/
  | readyOfAll (φ : ℚ)
  /-- `θ·|awake in [t − η·Δ, t] ∪ faulty| < |ready|` (`η` a Δ-coefficient). -/
  | etaSleepy (θ : ℚ) (η : Nat)
  /-- Every honest validator is awake. -/
  | full
  /-- No honest validator wakes. -/
  | noWake

namespace EnvAtom

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The meaning of an atom at point `p`, catch-up `c` (a duration) and time `t`. -/
def holds (p : EnvPoint V) (c t : Time) : EnvAtom → Prop
  | faultsBelow β => p.FaultsBelow β
  | readyAbove θ => p.ReadyAbove θ c t
  | faultsAtMost m => p.FaultsAtMost m
  | readyOfAll φ => p.ReadyOfAll φ c t
  | etaSleepy θ η => p.EtaSleepy θ ((η : Time) * p.env.Δ) c t
  | full => p.FullAt t
  | noWake => p.NoWakeAt t

/-- Parameter domains: `0 < β ≤ 1`; `1 ≤ m` (so that faults remain possible);
`0 ≤ θ, φ < 1`. -/
def WellFormed : EnvAtom → Prop
  | faultsBelow β => 0 < β ∧ β ≤ 1
  | faultsAtMost m => 1 ≤ m
  | readyAbove θ => 0 ≤ θ ∧ θ < 1
  | readyOfAll φ => 0 ≤ φ ∧ φ < 1
  | etaSleepy θ _ => 0 ≤ θ ∧ θ < 1
  | full => True
  | noWake => True

/-- A counting atom: a fault bound or a participation threshold. `full` and
`noWake` are not: one sleeping honest validator violates them. -/
def Counting : EnvAtom → Prop
  | full => False
  | noWake => False
  | _ => True

end EnvAtom

/-- The closed premise language over progress requirements `Prog`. -/
inductive Premise (Prog : Type) where
  /-- No assumption. -/
  | truth
  /-- A timing constraint `a ≤ b`. -/
  | le (a b : TimeExpr)
  /-- An environment atom at one time. -/
  | atTime (t : TimeExpr) (a : EnvAtom)
  /-- An environment atom at every time `t` with `lo ≤ t ≤ hi`. -/
  | throughout (lo hi : TimeExpr) (a : EnvAtom)
  /-- Partial synchrony (fixed by the execution model). -/
  | sync
  /-- Δ-delivery for deadlines up to `b` (fixed by the execution model). -/
  | syncUntil (b : TimeExpr)
  /-- Progress requirement `π` from `start` (fixed by the protocol shape). -/
  | progress (π : Prog) (start : TimeExpr)
  /-- Both premises. -/
  | conj (P Q : Premise Prog)

/-- Interpretation of the execution atoms: the execution model fixes `sync`
and `syncUntil`, the shape fixes `progress` (arguments: requirement, catch-up
duration, start). -/
structure ExecProfile {V : Type} (S : System V) (Prog : Type) where
  /-- Partial synchrony. -/
  sync : S.Run → Prop
  /-- Synchrony for deadlines up to a time. -/
  syncUntil : Time → S.Run → Prop
  /-- A progress requirement with a catch-up duration from a start. -/
  progress : Prog → Time → Time → S.Run → Prop

namespace Premise

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- Evaluation on a run; `c` is the contract's catch-up coefficient (the
catch-up duration is `c·Δ`). -/
def eval (S : System V) (X : ExecProfile S Prog) (c : Nat) (σ : Nat → Time)
    (r : S.Run) : Premise Prog → Prop
  | truth => True
  | le a b => a.eval (S.trace r).point σ ≤ b.eval (S.trace r).point σ
  | atTime t a => a.holds (S.trace r).point ((c : Time) * (S.trace r).point.env.Δ)
      (t.eval (S.trace r).point σ)
  | throughout lo hi a => ∀ t, lo.eval (S.trace r).point σ ≤ t → t ≤ hi.eval (S.trace r).point σ →
      a.holds (S.trace r).point ((c : Time) * (S.trace r).point.env.Δ) t
  | sync => X.sync r
  | syncUntil b => X.syncUntil (b.eval (S.trace r).point σ) r
  | progress π s => X.progress π ((c : Time) * (S.trace r).point.env.Δ)
      (s.eval (S.trace r).point σ) r
  | conj P Q => P.eval S X c σ r ∧ Q.eval S X c σ r

/-- Evaluation at an environment point with catch-up duration `c` and a given
interpretation `prog` of progress; the synchrony atoms are `True` (used before
a run exists, for example progress over a fixed key assignment). -/
def evalAt (p : EnvPoint V) (c : Time) (σ : Nat → Time)
    (prog : Prog → Time → Time → Prop) : Premise Prog → Prop
  | truth => True
  | le a b => a.eval p σ ≤ b.eval p σ
  | atTime t a => a.holds p c (t.eval p σ)
  | throughout lo hi a => ∀ t, lo.eval p σ ≤ t → t ≤ hi.eval p σ → a.holds p c t
  | sync => True
  | syncUntil _ => True
  | progress π s => prog π c (s.eval p σ)
  | conj P Q => P.evalAt p c σ prog ∧ Q.evalAt p c σ prog

/-- The environment part only (`evalAt` with progress `True`). -/
def evalEnv (p : EnvPoint V) (c : Time) (σ : Nat → Time) (P : Premise Prog) : Prop :=
  P.evalAt p c σ (fun _ _ _ => True)

/-- Assembling a premise: the environment and progress parts at the run's point,
together with both synchrony atoms, give the full evaluation. -/
theorem eval_of_evalAt {S : System V} {X : ExecProfile S Prog} {c : Nat} {σ : Nat → Time}
    {r : S.Run} {P : Premise Prog} (hs : X.sync r) (hu : ∀ b, X.syncUntil b r)
    (h : P.evalAt (S.trace r).point ((c : Time) * (S.trace r).point.env.Δ) σ
      (fun π cd s => X.progress π cd s r)) : P.eval S X c σ r := by
  induction P with
  | sync => exact hs
  | syncUntil b => exact hu _
  | conj P Q hP hQ => exact ⟨hP h.1, hQ h.2⟩
  | _ => exact h

/-- Every `progress π s` occurrence satisfies `q π (s.eval p σ)` (for activity
witnesses). -/
def ProgressAll (p : EnvPoint V) (σ : Nat → Time) (q : Prog → Time → Prop) :
    Premise Prog → Prop
  | progress π s => q π (s.eval p σ)
  | conj P Q => P.ProgressAll p σ q ∧ Q.ProgressAll p σ q
  | _ => True

/-- Only the timing constraints (`le` atoms; every other atom is `True`).
Depends on `p` only through `Δ`, the GST and the horizon. -/
def TimesHold (p : EnvPoint V) (σ : Nat → Time) : Premise Prog → Prop
  | le a b => a.eval p σ ≤ b.eval p σ
  | conj P Q => P.TimesHold p σ ∧ Q.TimesHold p σ
  | _ => True

/-- Some `progress` atom occurs. -/
def UsesProgress : Premise Prog → Prop
  | progress _ _ => True
  | conj P Q => P.UsesProgress ∨ Q.UsesProgress
  | _ => False

/-- `sync` occurs as a conjunct (through `conj` only). -/
def HasSync : Premise Prog → Prop
  | sync => True
  | conj P Q => P.HasSync ∨ Q.HasSync
  | _ => False

/-- A premise with `sync` as a conjunct implies partial synchrony. -/
theorem HasSync.sync_of_eval {S : System V} {X : ExecProfile S Prog} {c : Nat}
    {σ : Nat → Time} {r : S.Run} {P : Premise Prog} (h : P.HasSync)
    (he : P.eval S X c σ r) : X.sync r := by
  induction P with
  | sync => exact he
  | conj P Q hP hQ => exact h.elim (fun h => hP h he.1) (fun h => hQ h he.2)
  | _ => exact h.elim

/-- Well-formedness: every environment atom is well-formed, and the horizon
and the parameters are never bounded from above by a fixed time. The horizon
does not occur on the left of a `le`, in the time of an `atTime`, or in the
lower end of a `throughout`; a `le` whose right side is fixed (built on `0` or
the GST) has a fixed left side. So `le horizon e` (a run-length cap) and
`le protectedAt zero` (a parameter cap) are rejected, and timing constraints
that hold keep holding when the horizon and the parameters move later
(`TimesHold.shift`). -/
def WellFormed : Premise Prog → Prop
  | le a b => a.HorizonFree ∧ (b.Fixed → a.Fixed)
  | atTime t a => t.HorizonFree ∧ a.WellFormed
  | throughout lo _ a => lo.HorizonFree ∧ a.WellFormed
  | conj P Q => P.WellFormed ∧ Q.WellFormed
  | _ => True

/-- Every environment atom satisfies `q`. -/
def AtomsAll (q : EnvAtom → Prop) : Premise Prog → Prop
  | atTime _ a => q a
  | throughout _ _ a => q a
  | conj P Q => P.AtomsAll q ∧ Q.AtomsAll q
  | _ => True

omit [Fintype V] [DecidableEq V] in
/-- No horizon or parameter cap: if the timing constraints of a well-formed
premise hold, they hold with every parameter moved later by `d ≥ 0` and the
horizon moved later by `d + e` (`e ≥ 0`). In particular they hold on every
longer run (`d = 0`). -/
theorem TimesHold.shift {p : EnvPoint V} {σ : Nat → Time} {d e : Time} {P : Premise Prog}
    (hP : P.WellFormed) (hd : 0 ≤ d) (he : 0 ≤ e) (h : P.TimesHold p σ) :
    P.TimesHold { p with horizon := p.horizon + d + e } (fun i => σ i + d) := by
  induction P with
  | le a b =>
    change a.eval p σ ≤ b.eval p σ at h
    change a.eval _ _ ≤ b.eval _ _
    by_cases ha : a.Fixed
    · rw [TimeExpr.eval_shift_fixed p σ ha]
      by_cases hb : b.Fixed
      · rw [TimeExpr.eval_shift_fixed p σ hb]; exact h
      · have := TimeExpr.eval_shift_ge p σ he (d := d) hb; linarith
    · have hb : ¬ b.Fixed := fun hb => ha (hP.2 hb)
      have h1 := TimeExpr.eval_shift_le p σ hd (e := e) hP.1
      have h2 := TimeExpr.eval_shift_ge p σ he (d := d) hb
      linarith
  | conj P Q hP' hQ' => exact ⟨hP' hP.1 h.1, hQ' hP.2 h.2⟩
  | _ => trivial

/-- The environment part holds at a point where every atom satisfying `q` holds
at every time, if every atom of the premise satisfies `q` and the timing
constraints hold. -/
theorem evalEnv_of_atomsAll {p : EnvPoint V} {q : EnvAtom → Prop}
    (hq : ∀ a, q a → ∀ c t, a.holds p c t) {σ : Nat → Time} {c : Time} (P : Premise Prog)
    (hf : P.AtomsAll q) (ht : P.TimesHold p σ) : P.evalEnv p c σ := by
  unfold Premise.evalEnv
  induction P with
  | truth => trivial
  | le a b => exact ht
  | atTime t a => exact hq a hf c _
  | throughout lo hi a => exact fun t _ _ => hq a hf c t
  | sync => trivial
  | syncUntil b => trivial
  | progress π s => trivial
  | conj P Q ihP ihQ => exact ⟨ihP hf.1 ht.1, ihQ hf.2 ht.2⟩

/-! ## Named standard terms -/

/-- `a` at every time of `[0, horizon]`. -/
def always (a : EnvAtom) : Premise Prog := throughout .zero .horizon a

/-- `a` at every time of `[GST, horizon]`. -/
def fromGST (a : EnvAtom) : Premise Prog := throughout .gst .horizon a

/-- `a` at every time of `[b, horizon]`. -/
def after (b : TimeExpr) (a : EnvAtom) : Premise Prog := throughout b .horizon a

/-- `a` at every time of `[0, b)`. -/
def before (b : TimeExpr) (a : EnvAtom) : Premise Prog := throughout .zero (.add b (-1)) a

/-- Synchronous from time 0 (GST ≤ 0), with the ready honest validators above
fraction `θ` of the ready and faulty ones at every time. -/
def sleepy (θ : ℚ) : Premise Prog := conj (le .gst .zero) (conj sync (always (.readyAbove θ)))

/-- The sleepy model with more ready honest validators than faulty ones. -/
def honestMajority : Premise Prog := sleepy (1 / 2)

/-- Fewer than a third of the validators are faulty. -/
def faultsBelowThird : Premise Prog := atTime .zero (.faultsBelow (1 / 3))

/-- The outage parameters: `0 ≤ protectedAt`, `protectedAt + lag·Δ ≤ outageStart
≤ outageEnd ≤ outageStart + budget·Δ`, `outageEnd ≤ horizon`. -/
def outageWindow (lag budget : Nat) : Premise Prog :=
  conj (le .zero .protectedAt)
    (conj (le (.addΔ .protectedAt lag) .outageStart)
      (conj (le .outageStart .outageEnd)
        (conj (le .outageEnd (.addΔ .outageStart budget))
          (le .outageEnd .horizon))))

/-- More than half of all validators are ready at the outage start. With
`EnvPoint.two_mul_card_faulty_union_lt`, if every ready validator is in an
honest set `C`, the faulty validators together with any honest set avoiding
`C` are fewer than half of all validators. -/
def coverMajority : Premise Prog := atTime .outageStart (.readyOfAll (1 / 2))

end Premise

/-! ## The extremal point and the sleeper point -/

/-- The extremal point: `n + 1` validators, validator 0 faulty, every node
awake always, `Δ = 1`, GST `g`, horizon `H`, submissions `submit`. -/
def EnvPoint.extremal (n : Nat) (H g : Time) (submit : Fin (n + 1) → Time → List Tx) :
    EnvPoint (Fin (n + 1)) :=
  ⟨⟨1, by decide, g, fun _ _ => true⟩, Finset.univ.erase 0, H, submit⟩

/-- The sleeper point: the extremal point, except that the honest validator `n`
(the last one) is asleep at time `t₀`. -/
def EnvPoint.sleeper (n : Nat) (H g t₀ : Time) (submit : Fin (n + 1) → Time → List Tx) :
    EnvPoint (Fin (n + 1)) :=
  ⟨⟨1, by decide, g, fun v t => !(decide (v = Fin.last n) && decide (t = t₀))⟩,
    Finset.univ.erase 0, H, submit⟩

namespace EnvPoint

section Extremal

variable (n : Nat) (H g : Time) (submit : Fin (n + 1) → Time → List Tx)

/-- At the extremal point exactly validator 0 is faulty. -/
theorem extremal_faulty : (EnvPoint.extremal n H g submit).faulty = {0} := by
  ext v; simp [EnvPoint.faulty, EnvPoint.extremal]

theorem extremal_readyAt (c t : Time) :
    (EnvPoint.extremal n H g submit).readyAt c t = Finset.univ.erase 0 := by
  ext v
  simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, EnvPoint.extremal]

theorem extremal_awakeIn (a b : Time) (h : a ≤ b) :
    (EnvPoint.extremal n H g submit).awakeIn a b = Finset.univ.erase 0 := by
  classical
  ext v
  unfold EnvPoint.awakeIn
  rw [Finset.mem_filter]
  exact and_iff_left_of_imp fun _ => ⟨b, h, le_rfl, rfl⟩

end Extremal

/-- Every well-formed atom holds at the extremal point with population `n + 1`
when the population is large enough for the atom's fraction. -/
theorem extremal_atom (a : EnvAtom) (ha : a.WellFormed) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ H g submit (c t : Time),
      a.holds (EnvPoint.extremal n H g submit) c t := by
  have frac (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
      ∃ N : Nat, ∀ n : Nat, N ≤ n → θ * ((n : ℚ) + 1) < n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - θ))
    refine ⟨N, fun n hn => ?_⟩
    have hd : 0 < 1 - θ := sub_pos.mpr h1
    have hn' : 1 / (1 - θ) < (n : ℚ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    have := (div_lt_iff₀ hd).mp hn'
    nlinarith
  have card (n : Nat) : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by simp
  cases a with
  | faultsBelow β =>
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / β)
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    change (EnvPoint.extremal n H g submit).FaultsBelow β
    unfold FaultsBelow
    rw [extremal_faulty]
    have hn' : 1 / β < (n : ℚ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    have := (div_lt_iff₀ ha.1).mp hn'
    simp only [Finset.card_singleton, Nat.cast_one, Fintype.card_fin, Nat.cast_add]
    nlinarith [ha.1]
  | faultsAtMost m =>
    refine ⟨0, fun n _ H g submit c t => ?_⟩
    change (EnvPoint.extremal n H g submit).FaultsAtMost m
    unfold FaultsAtMost
    rw [extremal_faulty]
    simpa [EnvAtom.WellFormed] using ha
  | readyAbove θ =>
    obtain ⟨N, hN⟩ := frac θ ha.1 ha.2
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    change (EnvPoint.extremal n H g submit).ReadyAbove θ c t
    unfold ReadyAbove
    rw [extremal_faulty, extremal_readyAt, card]
    simp only [Finset.card_singleton, Nat.cast_one]
    exact hN n hn
  | readyOfAll φ =>
    obtain ⟨N, hN⟩ := frac φ ha.1 ha.2
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    change φ * (Fintype.card (Fin (n + 1)) : ℚ) <
      ((EnvPoint.extremal n H g submit).readyAt c t).card
    rw [extremal_readyAt, card]
    simpa using hN n hn
  | etaSleepy θ η =>
    obtain ⟨N, hN⟩ := frac θ ha.1 ha.2
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    change (EnvPoint.extremal n H g submit).EtaSleepy θ ((η : Time) * _) c t
    unfold EtaSleepy
    have hη : t - (η : Time) * (EnvPoint.extremal n H g submit).env.Δ ≤ t := by
      simp [EnvPoint.extremal]
    rw [extremal_awakeIn _ _ _ _ _ _ hη, extremal_faulty, extremal_readyAt, card]
    have hu : Finset.univ.erase (0 : Fin (n + 1)) ∪ {0} = Finset.univ := by
      ext v; by_cases hv : v = 0 <;> simp [hv]
    rw [hu]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact hN n hn
  | full =>
    exact ⟨0, fun n _ H g submit c t v _ => rfl⟩
  | noWake =>
    refine ⟨0, fun n _ H g submit c t v _ hw => ?_⟩
    have := hw.2
    simp [EnvPoint.extremal] at this

section Sleeper

variable (n : Nat) (H g t₀ : Time) (submit : Fin (n + 1) → Time → List Tx)

/-- At the sleeper point exactly validator 0 is faulty. -/
theorem sleeper_faulty : (EnvPoint.sleeper n H g t₀ submit).faulty = {0} := by
  ext v; simp [EnvPoint.faulty, EnvPoint.sleeper]

/-- Every validator other than the last one is always awake. -/
theorem sleeper_awake {v : Fin (n + 1)} (hv : v ≠ Fin.last n) (t : Time) :
    (EnvPoint.sleeper n H g t₀ submit).env.awake v t = true := by
  simp [EnvPoint.sleeper, hv]

/-- The last validator is asleep at `t₀`. -/
theorem sleeper_asleep : (EnvPoint.sleeper n H g t₀ submit).env.awake (Fin.last n) t₀ = false := by
  simp [EnvPoint.sleeper]

theorem sleeper_honest {v : Fin (n + 1)} (hv : v ≠ 0) :
    v ∈ (EnvPoint.sleeper n H g t₀ submit).honest :=
  Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩

/-- At least `n - 1` validators are ready at every time. -/
theorem sleeper_card_readyAt (hn : 1 ≤ n) (c t : Time) :
    (n : ℚ) ≤ ((EnvPoint.sleeper n H g t₀ submit).readyAt c t).card + 1 := by
  classical
  have hl0 : Fin.last n ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hsub : (Finset.univ.erase (0 : Fin (n + 1))).erase (Fin.last n) ⊆
      (EnvPoint.sleeper n H g t₀ submit).readyAt c t := by
    intro v hv
    obtain ⟨hvl, hv0⟩ := Finset.mem_erase.mp hv
    have hh := sleeper_honest n H g t₀ submit (Finset.mem_erase.mp hv0).1
    unfold readyAt
    exact Finset.mem_filter.mpr ⟨hh, hh, fun u _ _ => sleeper_awake n H g t₀ submit hvl u⟩
  have hc : ((Finset.univ.erase (0 : Fin (n + 1))).erase (Fin.last n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hl0, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have := Finset.card_le_card hsub
  rw [hc] at this
  have h' : n ≤ ((EnvPoint.sleeper n H g t₀ submit).readyAt c t).card + 1 := by omega
  exact_mod_cast h'

end Sleeper

/-- For `θ < 1`, eventually `θ·(n + 1) < n − 1`. -/
theorem eventually_frac (θ : ℚ) (h1 : θ < 1) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → θ * ((n : ℚ) + 1) < (n : ℚ) - 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (1 - θ))
  refine ⟨N, fun n hn => ?_⟩
  have hd : 0 < 1 - θ := sub_pos.mpr h1
  have hn' : 2 / (1 - θ) < (n : ℚ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have := (div_lt_iff₀ hd).mp hn'
  nlinarith

/-- Every well-formed counting atom holds at the sleeper point with population
`n + 1` when the population is large enough for the atom's fraction. -/
theorem sleeper_atom (a : EnvAtom) (ha : a.WellFormed) (hc : a.Counting) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ H g t₀ submit (c t : Time),
      a.holds (EnvPoint.sleeper n H g t₀ submit) c t := by
  cases a with
  | faultsBelow β =>
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / β)
    refine ⟨N, fun n hn H g t₀ submit c t => ?_⟩
    change (EnvPoint.sleeper n H g t₀ submit).FaultsBelow β
    unfold FaultsBelow
    rw [sleeper_faulty]
    have hn' : 1 / β < (n : ℚ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    have := (div_lt_iff₀ ha.1).mp hn'
    simp only [Finset.card_singleton, Nat.cast_one, Fintype.card_fin, Nat.cast_add]
    nlinarith [ha.1]
  | faultsAtMost m =>
    refine ⟨0, fun n _ H g t₀ submit c t => ?_⟩
    change (EnvPoint.sleeper n H g t₀ submit).FaultsAtMost m
    unfold FaultsAtMost
    rw [sleeper_faulty]
    simpa [EnvAtom.WellFormed] using ha
  | readyAbove θ =>
    obtain ⟨N, hN⟩ := eventually_frac θ ha.2
    refine ⟨max N 1, fun n hn H g t₀ submit c t => ?_⟩
    change (EnvPoint.sleeper n H g t₀ submit).ReadyAbove θ c t
    unfold ReadyAbove
    rw [sleeper_faulty]
    have hr := sleeper_card_readyAt n H g t₀ submit (le_of_max_le_right hn) c t
    have h := hN n (le_of_max_le_left hn)
    simp only [Finset.card_singleton, Nat.cast_one]
    nlinarith [ha.1, mul_nonneg (sub_nonneg.2 ha.2.le) (by linarith : (0 : ℚ) ≤
      ((EnvPoint.sleeper n H g t₀ submit).readyAt c t).card + 1 - n)]
  | readyOfAll φ =>
    obtain ⟨N, hN⟩ := eventually_frac φ ha.2
    refine ⟨max N 1, fun n hn H g t₀ submit c t => ?_⟩
    change φ * (Fintype.card (Fin (n + 1)) : ℚ) <
      ((EnvPoint.sleeper n H g t₀ submit).readyAt c t).card
    have hr := sleeper_card_readyAt n H g t₀ submit (le_of_max_le_right hn) c t
    have h := hN n (le_of_max_le_left hn)
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  | etaSleepy θ η =>
    obtain ⟨N, hN⟩ := eventually_frac θ ha.2
    refine ⟨max N 1, fun n hn H g t₀ submit c t => ?_⟩
    change (EnvPoint.sleeper n H g t₀ submit).EtaSleepy θ ((η : Time) * _) c t
    unfold EtaSleepy
    have hr := sleeper_card_readyAt n H g t₀ submit (le_of_max_le_right hn) c t
    have h := hN n (le_of_max_le_left hn)
    have hu : (((EnvPoint.sleeper n H g t₀ submit).awakeIn (t - (η : Time) * 1) t ∪
        (EnvPoint.sleeper n H g t₀ submit).faulty).card : ℚ) ≤ (n : ℚ) + 1 := by
      have := Finset.card_le_univ ((EnvPoint.sleeper n H g t₀ submit).awakeIn
        (t - (η : Time) * 1) t ∪ (EnvPoint.sleeper n H g t₀ submit).faulty)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hθ := mul_le_mul_of_nonneg_left hu ha.1
    change θ * (((EnvPoint.sleeper n H g t₀ submit).awakeIn (t - (η : Time) * 1) t ∪
        (EnvPoint.sleeper n H g t₀ submit).faulty).card : ℚ) < _
    linarith
  | full => exact hc.elim
  | noWake => exact hc.elim

end EnvPoint

/-- The environment part of a well-formed premise whose atoms all satisfy `q`
holds on a family of points `pt n x` (population index `n`) from some `n` on,
whenever its timing constraints hold, if every well-formed atom satisfying `q`
holds there from some `n` on. -/
theorem Premise.eventually_evalEnv {Prog : Type} {A W : Nat → Type} [∀ n, Fintype (W n)]
    [∀ n, DecidableEq (W n)] (pt : ∀ n, A n → EnvPoint (W n)) (q : EnvAtom → Prop)
    (hq : ∀ a, a.WellFormed → q a → ∃ N : Nat, ∀ n, N ≤ n → ∀ x c t, a.holds (pt n x) c t)
    (P : Premise Prog) (hP : P.WellFormed) (hPq : P.AtomsAll q) :
    ∃ N, ∀ n, N ≤ n → ∀ x (σ : Nat → Time) (c : Time),
      P.TimesHold (pt n x) σ → P.evalEnv (pt n x) c σ := by
  unfold Premise.evalEnv
  induction P with
  | truth => exact ⟨0, fun _ _ _ _ _ _ => trivial⟩
  | le a b => exact ⟨0, fun _ _ _ _ _ h => h⟩
  | atTime t a =>
    obtain ⟨N, hN⟩ := hq a hP.2 hPq
    exact ⟨N, fun n hn x σ c _ => hN n hn x c _⟩
  | throughout lo hi a =>
    obtain ⟨N, hN⟩ := hq a hP.2 hPq
    exact ⟨N, fun n hn x σ c _ t _ _ => hN n hn x c t⟩
  | sync => exact ⟨0, fun _ _ _ _ _ _ => trivial⟩
  | syncUntil b => exact ⟨0, fun _ _ _ _ _ _ => trivial⟩
  | progress π s => exact ⟨0, fun _ _ _ _ _ _ => trivial⟩
  | conj P Q ihP ihQ =>
    obtain ⟨N₁, h₁⟩ := ihP hP.1 hPq.1
    obtain ⟨N₂, h₂⟩ := ihQ hP.2 hPq.2
    exact ⟨max N₁ N₂, fun n hn x σ c ht =>
      ⟨h₁ n (le_of_max_le_left hn) x σ c ht.1, h₂ n (le_of_max_le_right hn) x σ c ht.2⟩⟩

/-- Extremal realizability of the environment part: for every well-formed
premise there is a population size from which the extremal point satisfies the
premise's environment part (for every horizon, GST, submissions, parameters and
catch-up) as soon as its timing constraints hold. -/
theorem Premise.extremal_realizable {Prog : Type} (P : Premise Prog) (hP : P.WellFormed) :
    ∃ N, ∀ n, N ≤ n → ∀ H g submit (σ : Nat → Time) (c : Time),
      P.TimesHold (EnvPoint.extremal n H g submit) σ →
      P.evalEnv (EnvPoint.extremal n H g submit) c σ := by
  have hall : P.AtomsAll (fun _ => True) := by
    induction P with
    | conj P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
    | _ => trivial
  obtain ⟨N, hN⟩ := Premise.eventually_evalEnv
    (A := fun n => Time × Time × (Fin (n + 1) → Time → List Tx))
    (fun n x => EnvPoint.extremal n x.1 x.2.1 x.2.2) (fun _ => True)
    (fun a ha _ => by
      obtain ⟨N, hN⟩ := EnvPoint.extremal_atom a ha
      exact ⟨N, fun n hn x c t => hN n hn _ _ _ c t⟩) P hP hall
  exact ⟨N, fun n hn H g submit σ c ht => hN n hn (H, g, submit) σ c ht⟩

/-- Sleeper realizability of the environment part: for every well-formed
premise whose atoms are all counting atoms, there is a population size from
which the sleeper point (one honest validator asleep at `t₀`) satisfies the
premise's environment part as soon as its timing constraints hold. -/
theorem Premise.sleeper_realizable {Prog : Type} (P : Premise Prog) (hP : P.WellFormed)
    (hc : P.AtomsAll EnvAtom.Counting) :
    ∃ N, ∀ n, N ≤ n → ∀ H g t₀ submit (σ : Nat → Time) (c : Time),
      P.TimesHold (EnvPoint.sleeper n H g t₀ submit) σ →
      P.evalEnv (EnvPoint.sleeper n H g t₀ submit) c σ := by
  obtain ⟨N, hN⟩ := Premise.eventually_evalEnv
    (A := fun n => Time × Time × Time × (Fin (n + 1) → Time → List Tx))
    (fun n x => EnvPoint.sleeper n x.1 x.2.1 x.2.2.1 x.2.2.2) EnvAtom.Counting
    (fun a ha hca => by
      obtain ⟨N, hN⟩ := EnvPoint.sleeper_atom a ha hca
      exact ⟨N, fun n hn x c t => hN n hn _ _ _ _ c t⟩) P hP hc
  exact ⟨N, fun n hn H g t₀ submit σ c ht => hN n hn (H, g, t₀, submit) σ c ht⟩

end Consensus

end
