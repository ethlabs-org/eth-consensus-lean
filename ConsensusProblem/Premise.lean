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
its timing constraints hold (`Premise.extremal_realizable`). -/

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

end TimeExpr

/-- Environment atoms, evaluated at one time with catch-up `c`. -/
inductive EnvAtom where
  /-- `|faulty| < β·n` (independent of time). -/
  | faultsBelow (β : ℚ)
  /-- `θ·(|ready| + |faulty|) < |ready|`. -/
  | readyAbove (θ : ℚ)
  /-- `φ·n < |ready|`, or `φ·n ≤ |ready|` if `inclusive`. -/
  | readyOfAll (φ : ℚ) (inclusive : Bool)
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
  | readyOfAll φ false => p.ReadyOfAll φ c t
  | readyOfAll φ true => p.ReadyOfAllAtLeast φ c t
  | etaSleepy θ η => p.EtaSleepy θ ((η : Time) * p.env.Δ) c t
  | full => p.FullAt t
  | noWake => p.NoWakeAt t

/-- Parameter domains: `0 < β ≤ 1`; `0 ≤ θ, φ < 1` (inclusive thresholds too,
so that faults remain possible). -/
def WellFormed : EnvAtom → Prop
  | faultsBelow β => 0 < β ∧ β ≤ 1
  | readyAbove θ => 0 ≤ θ ∧ θ < 1
  | readyOfAll φ _ => 0 ≤ φ ∧ φ < 1
  | etaSleepy θ _ => 0 ≤ θ ∧ θ < 1
  | full => True
  | noWake => True

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

/-- The environment part of an evaluated premise holds. -/
theorem eval_env {S : System V} {X : ExecProfile S Prog} {c : Nat} {σ : Nat → Time}
    {r : S.Run} {P : Premise Prog} (h : P.eval S X c σ r) :
    P.evalEnv (S.trace r).point ((c : Time) * (S.trace r).point.env.Δ) σ := by
  unfold evalEnv
  induction P with
  | sync => trivial
  | syncUntil b => trivial
  | progress π s => trivial
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

/-- Every environment atom is well-formed. -/
def WellFormed : Premise Prog → Prop
  | atTime _ a => a.WellFormed
  | throughout _ _ a => a.WellFormed
  | conj P Q => P.WellFormed ∧ Q.WellFormed
  | _ => True

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

/-- More than half of all validators are ready at the outage start (with
`EnvPoint.two_mul_card_faulty_union_lt` this gives the FG-SA outage bound once
every ready validator is covered). -/
def coverMajority : Premise Prog := atTime .outageStart (.readyOfAll (1 / 2) false)

end Premise

/-! ## The extremal point -/

/-- The extremal point: `n + 1` validators, validator 0 faulty, every node
awake always, `Δ = 1`, GST `g`, horizon `H`, submissions `submit`. -/
def EnvPoint.extremal (n : Nat) (H g : Time) (submit : Fin (n + 1) → Time → List Tx) :
    EnvPoint (Fin (n + 1)) :=
  ⟨⟨1, by decide, g, fun _ _ => true⟩, Finset.univ.erase 0, H, submit⟩

namespace EnvPoint

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
  | readyAbove θ =>
    obtain ⟨N, hN⟩ := frac θ ha.1 ha.2
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    change (EnvPoint.extremal n H g submit).ReadyAbove θ c t
    unfold ReadyAbove
    rw [extremal_faulty, extremal_readyAt, card]
    simp only [Finset.card_singleton, Nat.cast_one]
    exact hN n hn
  | readyOfAll φ inc =>
    obtain ⟨N, hN⟩ := frac φ ha.1 ha.2
    refine ⟨N, fun n hn H g submit c t => ?_⟩
    have h : φ * (Fintype.card (Fin (n + 1)) : ℚ) <
        ((EnvPoint.extremal n H g submit).readyAt c t).card := by
      rw [extremal_readyAt, card]; simpa using hN n hn
    cases inc
    · exact h
    · exact h.le
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

end EnvPoint

/-- Extremal realizability of the environment part: for every well-formed
premise there is a population size from which the extremal point satisfies the
premise's environment part (for every horizon, GST, submissions, parameters and
catch-up) as soon as its timing constraints hold. -/
theorem Premise.extremal_realizable {Prog : Type} (P : Premise Prog) (hP : P.WellFormed) :
    ∃ N, ∀ n, N ≤ n → ∀ H g submit (σ : Nat → Time) (c : Time),
      P.TimesHold (EnvPoint.extremal n H g submit) σ →
      P.evalEnv (EnvPoint.extremal n H g submit) c σ := by
  unfold Premise.evalEnv
  induction P with
  | truth => exact ⟨0, fun _ _ _ _ _ _ _ _ => trivial⟩
  | le a b => exact ⟨0, fun _ _ _ _ _ _ _ h => h⟩
  | atTime t a =>
    obtain ⟨N, hN⟩ := EnvPoint.extremal_atom a hP
    exact ⟨N, fun n hn H g submit σ c _ => hN n hn H g submit c _⟩
  | throughout lo hi a =>
    obtain ⟨N, hN⟩ := EnvPoint.extremal_atom a hP
    exact ⟨N, fun n hn H g submit σ c _ t _ _ => hN n hn H g submit c t⟩
  | sync => exact ⟨0, fun _ _ _ _ _ _ _ _ => trivial⟩
  | syncUntil b => exact ⟨0, fun _ _ _ _ _ _ _ _ => trivial⟩
  | progress π s => exact ⟨0, fun _ _ _ _ _ _ _ _ => trivial⟩
  | conj P Q ihP ihQ =>
    obtain ⟨N₁, h₁⟩ := ihP hP.1
    obtain ⟨N₂, h₂⟩ := ihQ hP.2
    exact ⟨max N₁ N₂, fun n hn H g submit σ c ht =>
      ⟨h₁ n (le_of_max_le_left hn) H g submit σ c ht.1,
        h₂ n (le_of_max_le_right hn) H g submit σ c ht.2⟩⟩

end Consensus

end
