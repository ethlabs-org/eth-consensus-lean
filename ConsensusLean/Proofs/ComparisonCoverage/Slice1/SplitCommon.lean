module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Domain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: shared pieces of the split witnesses

* `planInj`: the injections of a forgery list (`mem_planInj`, `planInj_append`).
* `holdPol_front`: with `ΔAC = 2`, the held split's filter serves everything on the front of a time
  before `b₀` or from `b₁` on.
* `le_of_inject_releases`, `notMem_faulty_of_releases`: nobody releases before the first awake
  time; a validator that releases is honest then.
* `exercised_of_fresh`: an honest content first released at the start of the incident, held by
  origin, exercises the split.
* `preAt`, `postAt`, `moved_sets`: moving the planned forgeries of `exists_plan` (split at `T₁`)
  later, keeping the activity sets. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf Obj Msg)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema}

/-- `omega` on integer times. -/
local macro "tomega" : tactic => `(tactic| (try dsimp only [Time] at *) <;> omega)

section Generic

variable {F : Model.ProtocolFamily O} {E : Env V}

/-- The injections of a forgery list: at `t`, to `u₀`, the forged objects of its entries timed
`t`. -/
def planInj (u₀ : V) (fs : List (Forgery F E)) (t : Time) (v : V) :
    List (protoOf F E).Object :=
  if v = u₀ then (fs.filter fun x => decide (x.time = t)).map Forgery.obj else []

theorem mem_planInj {u₀ : V} {fs : List (Forgery F E)} {t : Time} {v : V}
    {o : (protoOf F E).Object} :
    o ∈ planInj u₀ fs t v ↔ v = u₀ ∧ ∃ x ∈ fs, x.time = t ∧ o = x.obj := by
  unfold planInj
  split_ifs with h
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, h, true_and]
    constructor
    · rintro ⟨x, ⟨hx, ht⟩, rfl⟩; exact ⟨x, hx, ht, rfl⟩
    · rintro ⟨x, hx, ht, rfl⟩; exact ⟨x, ⟨hx, ht⟩, rfl⟩
  · simp [h]

theorem planInj_append {u₀ : V} {fs fs' : List (Forgery F E)} {t : Time}
    (h : ∀ x ∈ fs', t < x.time) : planInj u₀ (fs ++ fs') t = planInj u₀ fs t := by
  funext v
  unfold planInj
  split_ifs
  · have h0 : fs'.filter (fun x => decide (x.time = t)) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx => by simp [(h x hx).ne']
    rw [List.filter_append, h0, List.append_nil]
  · rfl

theorem planInj_eq_nil {u₀ : V} {fs : List (Forgery F E)} {t : Time}
    (h : ∀ x ∈ fs, t < x.time) : planInj u₀ fs t = fun _ => [] := by
  have := planInj_append (u₀ := u₀) (fs := []) (fs' := fs) h
  rw [List.nil_append] at this
  rw [this]
  funext v
  unfold planInj
  split_ifs <;> rfl

/-- With `ΔAC = 2`, the held split's filter serves everything on the front of a time `t` after a
prefix of earlier events, when `t` is before `b₀` or from `b₁` on. -/
theorem holdPol_front_of (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
    (hΔ : E.ΔAC = 2) (es : List (Model.Event V (protoOf F E).Object)) (t : Time)
    (hes : ∀ e ∈ es, e.time < t) (ht : t < b₀ ∨ b₁ ≤ t) (w : V) (o : (protoOf F E).Object) :
    holdPol rho G b₀ b₁ (rho.front es t) w o t = true := by
  rw [holdPol_eq_true]
  rintro ⟨hlt, d, -, k, r, -, -, hheld⟩
  rcases ht with ht | ht
  · obtain ⟨-, ⟨t', ht'⟩, hall⟩ := heldIn_iff.mp hheld
    have hle := rho.front_releases_le _ t hes ht'
    have := hall t' ht'
    rw [hΔ] at this
    tomega
  · exact absurd hlt (not_lt.mpr ht)

/-- With `ΔAC = 2`, the held split's filter serves everything on the front of a time `n` before
`b₀` or from `b₁` on. -/
theorem holdPol_front (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
    (hΔ : E.ΔAC = 2) (delay : Model.Event V (protoOf F E).Object → Time)
    (inj : Time → V → List (protoOf F E).Object)
    (pol : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)
    (n : ℕ) (hn : (n : Time) < b₀ ∨ b₁ ≤ n) (w : V) (o : (protoOf F E).Object) :
    holdPol rho G b₀ b₁ (rho.front (rho.injectStages delay inj pol n) (n : Time)) w o
      (n : Time) = true :=
  holdPol_front_of rho G b₀ b₁ hΔ _ _ (fun _ he => (rho.injectStages_time delay inj pol n he).2)
    hn w o

/-- Nobody releases before the first awake time `T₁`. -/
theorem le_of_inject_releases (rho : Model.Run F E) {T₁ : Time}
    (hT : ∀ v t, E.awake v t = true → T₁ ≤ t) (delay : Model.Event V (protoOf F E).Object → Time)
    (inj : Time → V → List (protoOf F E).Object)
    (pol : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)
    {u : V} {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.injectRun delay inj pol).releases u o t) : T₁ ≤ t := by
  obtain ⟨i, hs, -⟩ := hr
  have hev : ∀ e ∈ (rho.injectRun delay inj pol).events,
      (∀ v τ, e ≠ .restart v τ) → T₁ ≤ e.time := by
    intro e he hne
    rw [Model.Run.withEvents_events, Model.Run.injectEvents_eq] at he
    obtain ⟨k, -, hk⟩ := (rho.mem_injectStages _ inj pol _ _).mp he
    rcases (rho.mem_injectLayer _ inj pol _ _ _).mp hk with
      ⟨v, -, -, -, rfl⟩ | ⟨v, -, haw, rfl⟩ | ⟨v, -, haw, p, -, rfl⟩
    · exact absurd rfl (hne v _)
    · exact hT v _ haw
    · exact hT v _ haw
  rcases hs with he | ⟨o', he⟩
  · exact hev _ (List.mem_of_getElem? he) (fun _ _ h => by cases h)
  · exact hev _ (List.mem_of_getElem? he) (fun _ _ h => by cases h)

/-- In a valid run, a validator that releases is honest then. -/
theorem notMem_faulty_of_releases {W : Model.Run F E} (hv : W.ExecutionValid) {u : V}
    {o : (protoOf F E).Object} {t : Time} (hr : W.releases u o t) : u ∉ W.faultyAt t := by
  obtain ⟨i, hs, -⟩ := hr
  obtain ⟨e, he, hn, ht⟩ := hs.exists_event
  have := hv.honest_only e (List.mem_of_getElem? he)
  rw [hn, ht] at this
  exact this

/-- **A fresh content exercises the split**: in a valid run that holds content by origin, a
content that is not an FG attestation, released by its signer at the start `b₀` of the incident
and by nobody before, is held from every honest node of the other group awake through the incident
until `b₁`. -/
theorem exercised_of_fresh {W : Model.Run F E} {G : V → Bool} {b₀ b₁ : Time}
    (hv : W.ExecutionValid) (hhold : ContentOriginHold W G b₀ b₁)
    (hconst : ∀ t, W.faultyAt t = W.faultyAt 0) (hΔ : 1 < E.ΔAC)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} {d : (protoOf F E).Object}
    (hs : d.auth = .signed k r) (hfg : ¬ (protoOf F E).isFGAtt d)
    (hrel : W.releases (W.key k) d b₀) (hnew : ∀ u t, t < b₀ → ¬ W.releases u d t)
    {w : V} (hwG : G w ≠ G (W.key k)) (hw : ∀ t, w ∉ W.faultyAt t)
    (hwa : ∀ t, b₀ ≤ t → t ≤ b₁ → E.awake w t = true) (hb : b₀ + E.ΔAC ≤ b₁)
    (hT : ∃ u, G u = true ∧ ∀ t, u ∉ W.faultyAt t)
    (hF : ∃ u, G u = false ∧ ∀ t, u ∉ W.faultyAt t) :
    Exercised (sysOf O F V) (.split G) b₀ b₁ ⟨E, W⟩ := by
  have hk : ∀ t, W.key k ∉ W.faultyAt t := fun t => by
    have h0 := notMem_faulty_of_releases hv hrel
    rw [hconst] at h0 ⊢
    exact h0
  have hsig : d.signer? = some k := by simp [Model.Obj.signer?, hs]
  have hb₀₁ : b₀ < b₁ := by linarith
  obtain ⟨uT, huT, huT'⟩ := hT
  obtain ⟨uF, huF, huF'⟩ := hF
  refine ⟨⟨uT, huT, huT' _⟩, ⟨uF, huF, huF' _⟩, W.key k, w, ⟨E, d⟩, b₀, fun h' => hwG h'.symm,
    ⟨d, rfl, hrel⟩, hk b₀, fun h' => hfg ((Model.sysOf_log_fgAtt W d).mp h'), le_rfl, hb, hw b₁,
    fun t h1 h2 => hwa t h1 h2, ?_⟩
  intro d' hd' hheld
  obtain ⟨t', ht'd, hsr, -⟩ := (Model.sysOf_held_iff W w d d').mp hheld
  rcases hsr with hsr | hsr
  · exact hwG (by rw [W.releases_key_of_signer hsr hsig])
  · refine hhold w d t' hsr (hw t') (lt_of_le_of_lt ht'd hd') d (Obj.Contains.refl d) k r hs
      (fun h' => hwG h'.symm)
      ⟨hfg, b₀, ⟨⟨hk b₀, d, hrel, Obj.Contains.refl d⟩, ?_⟩, hb₀₁, by linarith⟩
    rintro t ⟨hh, o', hr', hc'⟩
    obtain ⟨t'', ht'', hr''⟩ := W.part_released hv hr' hc' hs hh
    by_contra hlt
    exact hnew _ t'' (by linarith) hr''

end Generic

/-! ### Moving the plan -/

section Plan

variable {F : Model.ProtocolFamily O} {E : Env V}

/-- The forgeries planned before `T₁`, moved to `τ`. -/
def preAt (T₁ τ : Time) (fs : List (Forgery F E)) : List (Forgery F E) :=
  (fs.filter fun x => decide (x.time < T₁)).map fun x => { x with time := τ }

/-- The forgeries planned from `T₁` on, shifted by `sh`. -/
def postAt (T₁ sh : Time) (fs : List (Forgery F E)) : List (Forgery F E) :=
  (fs.filter fun x => decide (T₁ ≤ x.time)).map fun x => { x with time := x.time + sh }

omit [DecidableEq V] in
theorem mem_preAt {T₁ τ : Time} {fs : List (Forgery F E)} {x : Forgery F E} :
    x ∈ preAt T₁ τ fs ↔ ∃ y ∈ fs, y.time < T₁ ∧ x = { y with time := τ } := by
  unfold preAt
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, ht⟩, rfl⟩; exact ⟨y, hy, ht, rfl⟩
  · rintro ⟨y, hy, ht, rfl⟩; exact ⟨y, ⟨hy, ht⟩, rfl⟩

omit [DecidableEq V] in
theorem mem_postAt {T₁ sh : Time} {fs : List (Forgery F E)} {x : Forgery F E} :
    x ∈ postAt T₁ sh fs ↔ ∃ y ∈ fs, T₁ ≤ y.time ∧ x = { y with time := y.time + sh } := by
  unfold postAt
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, ht⟩, rfl⟩; exact ⟨y, hy, ht, rfl⟩
  · rintro ⟨y, hy, ht, rfl⟩; exact ⟨y, ⟨hy, ht⟩, rfl⟩

omit [DecidableEq V] in
/-- An entry of the moved plan comes from an entry of the plan with the same key, role, message
and tag, at a time no earlier. -/
theorem mem_moved {T₁ τ sh : Time} (hτ : T₁ ≤ τ) (hsh : 0 ≤ sh) {fs : List (Forgery F E)}
    {x : Forgery F E} (hx : x ∈ preAt T₁ τ fs ++ postAt T₁ sh fs) :
    ∃ y ∈ fs, x.key = y.key ∧ x.role = y.role ∧ x.msg = y.msg ∧ x.tag = y.tag ∧
      y.time ≤ x.time ∧ T₁ ≤ x.time := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, ht, rfl⟩ := mem_preAt.mp hx
    exact ⟨y, hy, rfl, rfl, rfl, rfl, by dsimp only; linarith, hτ⟩
  · obtain ⟨y, hy, ht, rfl⟩ := mem_postAt.mp hx
    exact ⟨y, hy, rfl, rfl, rfl, rfl, by dsimp only; linarith, by dsimp only; linarith⟩

omit [DecidableEq V] in
/-- The moved plan injects each forged object at one time only, when the plan does. -/
theorem moved_unique {T₁ τ sh : Time} {fs : List (Forgery F E)}
    (hu : ∀ x ∈ fs, ∀ y ∈ fs, x.key = y.key → x.role = y.role → x.msg = y.msg →
      x.tag = y.tag → x.time = y.time) :
    ∀ x ∈ preAt T₁ τ fs ++ postAt T₁ sh fs, ∀ y ∈ preAt T₁ τ fs ++ postAt T₁ sh fs,
      x.key = y.key → x.role = y.role → x.msg = y.msg → x.tag = y.tag → x.time = y.time := by
  have hside : ∀ z ∈ fs, ∀ z' ∈ fs, z.key = z'.key → z.role = z'.role → z.msg = z'.msg →
      z.tag = z'.tag → z.time < T₁ → z'.time < T₁ := fun z hz z' hz' h1 h2 h3 h4 hzt => by
    rw [← hu z hz z' hz' h1 h2 h3 h4]; exact hzt
  intro x hx y hy hk hr hm' htg
  rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨z, -, -, rfl⟩ := mem_preAt.mp hx
    obtain ⟨z', -, -, rfl⟩ := mem_preAt.mp hy
    rfl
  · obtain ⟨z, hz, hzt, rfl⟩ := mem_preAt.mp hx
    obtain ⟨z', hz', hzt', rfl⟩ := mem_postAt.mp hy
    exact absurd (hside z hz z' hz' hk hr hm' htg hzt) (not_lt.mpr hzt')
  · obtain ⟨z, hz, hzt, rfl⟩ := mem_postAt.mp hx
    obtain ⟨z', hz', hzt', rfl⟩ := mem_preAt.mp hy
    exact absurd (hside z' hz' z hz hk.symm hr.symm hm'.symm htg.symm hzt') (not_lt.mpr hzt)
  · obtain ⟨z, hz, -, rfl⟩ := mem_postAt.mp hx
    obtain ⟨z', hz', -, rfl⟩ := mem_postAt.mp hy
    change z.time + sh = z'.time + sh
    rw [hu z hz z' hz' hk hr hm' htg]

end Plan

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- **The moved plan's activity sets**: forging the plan's entries before `T₁` at `τ < T₁ + sh`
and the others `sh` later, the keys forged on `[0, T₁ + sh)` are those of `Apre`, and those forged
on `[T₁ + sh, H]` are those of `Apost` (for `H ≥ Hp + sh`). -/
theorem moved_sets {F : ChainShapeFamily O Info} {E : Env V}
    {key : Fin (Fintype.card V) ≃ V} {Apre Apost : List V} {T₁ Hp : Time}
    {sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V))}
    {fs : List (Forgery (compiled F) E)} (hP : PlanProps F E key Apre Apost T₁ Hp sel fs)
    {τ sh H : Time} (hτ0 : 0 ≤ τ) (hτ : τ < T₁ + sh) (hH : Hp + sh ≤ H) :
    (((preAt T₁ τ fs ++ postAt T₁ sh fs).filter
        fun x => decide (0 ≤ x.time ∧ x.time < T₁ + sh)).map fun x => key x.key).toFinset =
      Apre.toFinset ∧
    (((preAt T₁ τ fs ++ postAt T₁ sh fs).filter
        fun x => decide (T₁ + sh ≤ x.time ∧ x.time < H + 1)).map fun x => key x.key).toFinset =
      Apost.toFinset := by
  rw [← hP.pre, ← hP.post]
  constructor <;> ext v <;>
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_append,
      decide_eq_true_eq]
  · constructor
    · rintro ⟨x, ⟨hx | hx, hxt⟩, rfl⟩
      · obtain ⟨y, hy, ht, rfl⟩ := mem_preAt.mp hx
        exact ⟨y, ⟨hy, (hP.time_range y hy).1, ht⟩, rfl⟩
      · obtain ⟨y, hy, ht, rfl⟩ := mem_postAt.mp hx
        exact absurd hxt.2 (by dsimp only; linarith)
    · rintro ⟨y, ⟨hy, -, ht⟩, rfl⟩
      exact ⟨{ y with time := τ }, ⟨Or.inl (mem_preAt.mpr ⟨y, hy, ht, rfl⟩), hτ0, hτ⟩, rfl⟩
  · constructor
    · rintro ⟨x, ⟨hx | hx, hxt⟩, rfl⟩
      · obtain ⟨y, hy, ht, rfl⟩ := mem_preAt.mp hx
        exact absurd hxt.1 (by dsimp only; linarith)
      · obtain ⟨y, hy, ht, rfl⟩ := mem_postAt.mp hx
        refine ⟨y, ⟨hy, ht, ?_⟩, rfl⟩
        have := (hP.time_range y hy).2
        linarith
    · rintro ⟨y, ⟨hy, ht, -⟩, rfl⟩
      have := (hP.time_range y hy).2
      exact ⟨{ y with time := y.time + sh }, ⟨Or.inr (mem_postAt.mpr ⟨y, hy, ht, rfl⟩),
        by dsimp only; linarith, by dsimp only; linarith⟩, rfl⟩

theorem bool_of_ne {x y b : Bool} (h₁ : x ≠ y) (h₂ : y ≠ b) : x = b := by
  cases x <;> cases y <;> cases b <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem classGroups_two {a : IncidentClass V} (hs : a.IsSplit) (h : a.TwoGroups) :
    (∃ v, classGroups a v = true) ∧ ∃ v, classGroups a v = false := by
  cases a with
  | any => exact hs.elim
  | split G => rw [classGroups_split]; exact h
  | splitHeld G => rw [classGroups_splitHeld]; exact h

omit [Fintype V] [DecidableEq V] in
theorem exercised_async {S : System V} {a : IncidentClass V} (hs : a.IsSplit)
    {b₀ b₁ : Time} {r : S.Run} (h : Exercised S (.split (classGroups a)) b₀ b₁ r) :
    Exercised S a.async b₀ b₁ r := by
  cases a with
  | any => exact hs.elim
  | split G => rw [classGroups_split] at h; exact h
  | splitHeld G => rw [classGroups_splitHeld] at h; exact h

end Consensus.Comparison

end
