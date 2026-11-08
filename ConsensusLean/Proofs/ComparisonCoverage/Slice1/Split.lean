module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Domain
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Late
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.ForgeryAt
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the exercised split without sleepers

`cov1_split_witness_awake`: at a point of the coverage domain with a split class and no sleepers
(`m ≤ fcap`), a Slice 1 witness that exercises the class.

The construction, on the late witness point `latePoint A T₁ v₀ H` (everyone asleep before
`T₁ = n·slotLen + 1`), with the forgery plan of `exists_plan` for the window split at `T₁`:
* the reference run `R`: the held split's filtered run with incident `[T₁, T₁)` (it serves
  everything), injecting the forgeries planned before `T₁` at `T₁`. Cut at `H₀`, it is healthy
  from `T₁`; healthy liveness gives an honest proposal `m`, first released at `t₀ ≥ T₁`;
* the witness `W`: the held split's filtered run with incident `[t₀, t₀ + 2L)`, injecting the same
  forgeries at `T₁` and the forgeries planned from `T₁` on, shifted past `b₁`. Its filter serves
  everything before `t₀`, so `W` has the stages of `R` before `t₀` (`Run.injectStages_congr`);
* at `t₀`: if the filter of `W` holds back nothing, `W` has the stages of `R` through `t₀` and
  releases `m` at `t₀`; otherwise the held part is a content of the other group first released at
  a tick of `t₀`. Either way an honest content is first released at `t₀`, and the content-origin
  hold keeps it from the other group until `b₁` (`exercised_of_fresh`). -/

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
private def planInj (u₀ : V) (fs : List (Forgery F E)) (t : Time) (v : V) :
    List (protoOf F E).Object :=
  if v = u₀ then (fs.filter fun x => decide (x.time = t)).map Forgery.obj else []

private theorem mem_planInj {u₀ : V} {fs : List (Forgery F E)} {t : Time} {v : V}
    {o : (protoOf F E).Object} :
    o ∈ planInj u₀ fs t v ↔ v = u₀ ∧ ∃ x ∈ fs, x.time = t ∧ o = x.obj := by
  unfold planInj
  split_ifs with h
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, h, true_and]
    constructor
    · rintro ⟨x, ⟨hx, ht⟩, rfl⟩; exact ⟨x, hx, ht, rfl⟩
    · rintro ⟨x, hx, ht, rfl⟩; exact ⟨x, ⟨hx, ht⟩, rfl⟩
  · simp [h]

private theorem planInj_append {u₀ : V} {fs fs' : List (Forgery F E)} {t : Time}
    (h : ∀ x ∈ fs', t < x.time) : planInj u₀ (fs ++ fs') t = planInj u₀ fs t := by
  funext v
  unfold planInj
  split_ifs
  · have h0 : fs'.filter (fun x => decide (x.time = t)) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx => by simp [(h x hx).ne']
    rw [List.filter_append, h0, List.append_nil]
  · rfl

/-- A release at `t ≥ 0` of a scheduled run is one of every scheduled run of the same base with
the same first `t + 1` stages. -/
private theorem releases_of_stages (rho : Model.Run F E)
    {inj inj' : Time → V → List (protoOf F E).Object}
    {pol pol' : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}
    {u : V} {o : (protoOf F E).Object} {t : Time} (ht0 : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hst : rho.injectStages (fun _ => 0) inj pol (t.toNat + 1) =
      rho.injectStages (fun _ => 0) inj' pol' (t.toNat + 1))
    (hr : (rho.injectRun (fun _ => 0) inj pol).releases u o t) :
    (rho.injectRun (fun _ => 0) inj' pol').releases u o t := by
  have hn : t.toNat + 1 ≤ rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hth; omega
  obtain ⟨tail, htail⟩ := rho.injectStages_prefix (fun _ => 0) inj pol hn
  obtain ⟨tail', htail'⟩ := rho.injectStages_prefix (fun _ => 0) inj' pol' hn
  change (rho.withEvents (rho.injectEvents (fun _ => 0) inj' pol')).releases u o t
  rw [Model.Run.injectEvents_eq, htail', ← hst]
  apply rho.releases_append
  change (rho.withEvents (rho.injectEvents (fun _ => 0) inj pol)).releases u o t at hr
  rw [Model.Run.injectEvents_eq, htail] at hr
  have hin : ∀ e ∈ rho.injectStages (fun _ => 0) inj pol (t.toNat + 1) ++ tail, e.node = u →
      e.time = t → e ∈ rho.injectStages (fun _ => 0) inj pol (t.toNat + 1) := by
    intro e he _ het
    rw [← htail] at he
    have h := rho.mem_injectStages_of_time_lt _ inj pol he (a := t + 1)
      (by rw [het]; exact lt_add_one t)
    rwa [show (t + 1).toNat = t.toNat + 1 by rw [Int.toNat_add ht0 zero_le_one]; rfl] at h
  exact rho.releases_restrict _ tail (htail ▸ rho.injectStages_nodup _ inj pol _) hin hr

/-- With `ΔAC = 2`, the held split's filter serves everything on the front of a time `n` before
`b₀` or from `b₁` on. -/
private theorem holdPol_front (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
    (hΔ : E.ΔAC = 2) (inj : Time → V → List (protoOf F E).Object)
    (pol : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)
    (n : ℕ) (hn : (n : Time) < b₀ ∨ b₁ ≤ n) (w : V) (o : (protoOf F E).Object) :
    holdPol rho G b₀ b₁ (rho.front (rho.injectStages (fun _ => 0) inj pol n) (n : Time)) w o
      (n : Time) = true := by
  rw [holdPol_eq_true]
  rintro ⟨hlt, d, -, k, r, -, -, hheld⟩
  rcases hn with hn | hn
  · obtain ⟨-, ⟨t', ht'⟩, hall⟩ := heldIn_iff.mp hheld
    have hle := rho.front_releases_le _ (n : Time)
      (fun e he => (rho.injectStages_time (fun _ => 0) inj pol n he).2) ht'
    have := hall t' ht'
    rw [hΔ] at this
    tomega
  · exact absurd hlt (not_lt.mpr hn)

/-- Nobody releases before the first awake time `T₁`. -/
private theorem le_of_inject_releases (rho : Model.Run F E) {T₁ : Time}
    (hT : ∀ v t, E.awake v t = true → T₁ ≤ t) (inj : Time → V → List (protoOf F E).Object)
    (pol : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)
    {u : V} {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.injectRun (fun _ => 0) inj pol).releases u o t) : T₁ ≤ t := by
  obtain ⟨i, hs, -⟩ := hr
  have hev : ∀ e ∈ (rho.injectRun (fun _ => 0) inj pol).events,
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

/-- A validator that releases is honest then. -/
private theorem notMem_faulty_of_releases (rho : Model.Run F E)
    {inj : Time → V → List (protoOf F E).Object}
    {pol : List (Model.Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}
    (hv : (rho.injectRun (fun _ => 0) inj pol).ExecutionValid) {u : V}
    {o : (protoOf F E).Object} {t : Time}
    (hr : (rho.injectRun (fun _ => 0) inj pol).releases u o t) : u ∉ rho.faultyAt t := by
  obtain ⟨i, hs, -⟩ := hr
  obtain ⟨e, he, hn, ht⟩ := hs.exists_event
  have := hv.honest_only e (List.mem_of_getElem? he)
  rw [Model.Run.withEvents_faultyAt, hn, ht] at this
  exact this

/-- **A held part is a fresh content**: when the held split's filter holds back an object at the
start `b₀` of its incident (with `ΔAC = 2`), a part of it is a content that is not an FG
attestation, released by its signer at `b₀` and by nobody before. -/
private theorem fresh_of_blocked (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
    (inj : Time → V → List (protoOf F E).Object) (hΔ : E.ΔAC = 2) {n₀ : ℕ}
    (hn₀ : (n₀ : Time) = b₀) (hh : b₀ ≤ rho.horizon) {w : V} {o : (protoOf F E).Object}
    (hblk : holdPol rho G b₀ b₁ (rho.front (rho.injectStages (fun _ => 0) inj
      (holdPol rho G b₀ b₁) n₀) (n₀ : Time)) w o (n₀ : Time) = false) :
    ∃ k r d, d.auth = .signed k r ∧ ¬ (protoOf F E).isFGAtt d ∧
      (holdRun rho G b₀ b₁ inj).releases (rho.key k) d b₀ ∧
      ∀ u t, t < b₀ → ¬ (holdRun rho G b₀ b₁ inj).releases u d t := by
  set es := rho.injectStages (fun _ => 0) inj (holdPol rho G b₀ b₁) n₀ with hes
  have hnot : ¬ holdPol rho G b₀ b₁ (rho.front es (n₀ : Time)) w o (n₀ : Time) = true := by
    rw [hblk]; decide
  rw [holdPol_eq_true, not_not] at hnot
  obtain ⟨-, d, -, k, r, hs, -, hheld⟩ := hnot
  obtain ⟨hfg, ⟨t', ht'⟩, hall⟩ := heldIn_iff.mp hheld
  have hesT : ∀ e ∈ es, e.time < (n₀ : Time) := fun e he =>
    (rho.injectStages_time _ inj _ n₀ he).2
  have hle := rho.front_releases_le es (n₀ : Time) hesT ht'
  have hge := hall t' ht'
  rw [hΔ] at hge
  have ht'b : t' = b₀ := by rw [← hn₀] at hge ⊢; tomega
  rw [ht'b] at ht'
  have hN : n₀ < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat (show (n₀ : Time) ≤ rho.horizon by rw [hn₀]; exact hh)
    simp only [Int.toNat_natCast] at this
    omega
  obtain ⟨tail, htail⟩ := rho.injectFront_prefix (fun _ => 0) inj (holdPol rho G b₀ b₁) hN
  refine ⟨k, r, d, hs, hfg, ?_, fun u t ht hr => ?_⟩
  · change (rho.withEvents (rho.injectEvents (fun _ => 0) inj (holdPol rho G b₀ b₁))).releases
      (rho.key k) d b₀
    rw [Model.Run.injectEvents_eq, htail]
    exact rho.releases_append _ tail ht'
  · have hsig : d.signer? = some k := by simp [Model.Obj.signer?, hs]
    have hu : rho.key k = u := by
      have := (holdRun rho G b₀ b₁ inj).releases_key_of_signer hr hsig
      rwa [Model.Run.withEvents_key] at this
    subst hu
    obtain ⟨tail', htail'⟩ := rho.injectStages_prefix (fun _ => 0) inj (holdPol rho G b₀ b₁)
      (show n₀ ≤ rho.horizon.toNat + 1 by omega)
    change (rho.withEvents (rho.injectEvents (fun _ => 0) inj (holdPol rho G b₀ b₁))).releases
      (rho.key k) d t at hr
    rw [Model.Run.injectEvents_eq, htail'] at hr
    have hin : ∀ e ∈ es ++ tail', e.node = rho.key k → e.time = t → e ∈ es := by
      intro e he _ het
      rw [← htail'] at he
      have h := rho.mem_injectStages_of_time_lt _ inj _ he (a := (n₀ : Time))
        (by rw [het, hn₀]; exact ht)
      simpa only [Int.toNat_natCast] using h
    have hr' := rho.releases_restrict _ tail' (htail' ▸ rho.injectStages_nodup _ inj _ _) hin hr
    have := hall t (by
      rw [Model.Run.front_eq, List.append_assoc]
      exact rho.releases_append _ _ hr')
    rw [hΔ] at this
    tomega

/-- **A fresh content exercises the split**: a content that is not an FG attestation, released by
its honest signer at the start `b₀` of the held split's incident and by nobody before, is held from
every honest node of the other group awake through the incident until `b₁`. -/
private theorem exercised_of_fresh {rho : Model.Run F E} {G : V → Bool} {b₀ b₁ : Time}
    {inj : Time → V → List (protoOf F E).Object} (h : HoldPremises rho G b₀ b₁ inj)
    (hv : (holdRun rho G b₀ b₁ inj).ExecutionValid)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} {d : (protoOf F E).Object}
    (hs : d.auth = .signed k r) (hfg : ¬ (protoOf F E).isFGAtt d)
    (hrel : (holdRun rho G b₀ b₁ inj).releases (rho.key k) d b₀)
    (hnew : ∀ u t, t < b₀ → ¬ (holdRun rho G b₀ b₁ inj).releases u d t)
    {w : V} (hwG : G w ≠ G (rho.key k)) (hw : ∀ t, w ∉ rho.faultyAt t)
    (hwa : ∀ t, b₀ ≤ t → t ≤ b₁ → E.awake w t = true) (hb : b₀ + E.ΔAC ≤ b₁)
    (hT : ∃ u, G u = true ∧ ∀ t, u ∉ rho.faultyAt t)
    (hF : ∃ u, G u = false ∧ ∀ t, u ∉ rho.faultyAt t) :
    Exercised (sysOf O F V) (.split G) b₀ b₁ ⟨E, holdRun rho G b₀ b₁ inj⟩ := by
  set W := holdRun rho G b₀ b₁ inj with hW
  have hpt : W.point = rho.point := Model.Run.withEvents_point _ _
  have hkey : W.key = rho.key := Model.Run.withEvents_key _ _
  have hk : ∀ t, rho.key k ∉ rho.faultyAt t := fun t => by
    have h0 := notMem_faulty_of_releases rho hv hrel
    rw [h.constFaults] at h0 ⊢
    exact h0
  have hsig : d.signer? = some k := by simp [Model.Obj.signer?, hs]
  have hΔ := h.ΔAC_gt
  have hb₀₁ : b₀ < b₁ := by linarith
  obtain ⟨uT, huT, huT'⟩ := hT
  obtain ⟨uF, huF, huF'⟩ := hF
  refine ⟨⟨uT, huT, ?_⟩, ⟨uF, huF, ?_⟩, rho.key k, w, ⟨E, d⟩, b₀, fun h' => hwG h'.symm,
    ⟨d, rfl, hrel⟩, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
  · change W.point.HonestAt uT W.point.horizon
    rw [hpt]; exact huT' _
  · change W.point.HonestAt uF W.point.horizon
    rw [hpt]; exact huF' _
  · change W.point.HonestAt (rho.key k) b₀
    rw [hpt]; exact hk b₀
  · exact fun h' => hfg ((Model.sysOf_log_fgAtt W d).mp h')
  · change b₀ + E.ΔAC ≤ b₁
    exact hb
  · change W.point.HonestAt w b₁
    rw [hpt]; exact hw b₁
  · intro t h1 h2
    exact hwa t h1 h2
  · intro d' hd' hheld
    obtain ⟨t', ht'd, hsr, -⟩ := (Model.sysOf_held_iff W w d d').mp hheld
    rcases hsr with hsr | hsr
    · have := W.releases_key_of_signer hsr hsig
      rw [hkey] at this
      exact hwG (by rw [this])
    · refine hold_contentOriginHold h w d t' hsr ?_ (lt_of_le_of_lt ht'd hd') d
        (Obj.Contains.refl d) k r hs (by rw [hkey]; exact fun h' => hwG h'.symm)
        ⟨hfg, b₀, ⟨⟨?_, d, ?_, Obj.Contains.refl d⟩, ?_⟩, hb₀₁, by linarith⟩
      · change W.point.HonestAt w t'
        rw [hpt]; exact hw t'
      · change W.point.HonestAt (W.key k) b₀
        rw [hpt, hkey]; exact hk b₀
      · rw [hkey]; exact hrel
      · rintro t ⟨hh, o', hr', hc'⟩
        obtain ⟨t'', ht'', hr''⟩ := W.part_released hv hr' hc' hs hh
        by_contra hlt
        exact hnew _ t'' (by linarith) hr''

end Generic

/-! ### Moving the plan -/

section Plan

variable {F : Model.ProtocolFamily O} {E : Env V}

/-- The forgeries planned before `T₁`, moved to `T₁`. -/
private def preAt (T₁ : Time) (fs : List (Forgery F E)) : List (Forgery F E) :=
  (fs.filter fun x => decide (x.time < T₁)).map fun x => { x with time := T₁ }

/-- The forgeries planned from `T₁` on, shifted by `sh`. -/
private def postAt (T₁ sh : Time) (fs : List (Forgery F E)) : List (Forgery F E) :=
  (fs.filter fun x => decide (T₁ ≤ x.time)).map fun x => { x with time := x.time + sh }

omit [DecidableEq V] in
private theorem mem_preAt {T₁ : Time} {fs : List (Forgery F E)} {x : Forgery F E} :
    x ∈ preAt T₁ fs ↔ ∃ y ∈ fs, y.time < T₁ ∧ x = { y with time := T₁ } := by
  unfold preAt
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, ht⟩, rfl⟩; exact ⟨y, hy, ht, rfl⟩
  · rintro ⟨y, hy, ht, rfl⟩; exact ⟨y, ⟨hy, ht⟩, rfl⟩

omit [DecidableEq V] in
private theorem mem_postAt {T₁ sh : Time} {fs : List (Forgery F E)} {x : Forgery F E} :
    x ∈ postAt T₁ sh fs ↔ ∃ y ∈ fs, T₁ ≤ y.time ∧ x = { y with time := y.time + sh } := by
  unfold postAt
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, ht⟩, rfl⟩; exact ⟨y, hy, ht, rfl⟩
  · rintro ⟨y, hy, ht, rfl⟩; exact ⟨y, ⟨hy, ht⟩, rfl⟩

omit [DecidableEq V] in
/-- An entry of the moved plan comes from an entry of the plan with the same key, role, message
and tag, at a time no earlier. -/
private theorem mem_moved {T₁ sh : Time} (hsh : 0 ≤ sh) {fs : List (Forgery F E)}
    {x : Forgery F E} (hx : x ∈ preAt T₁ fs ++ postAt T₁ sh fs) :
    ∃ y ∈ fs, x.key = y.key ∧ x.role = y.role ∧ x.msg = y.msg ∧ x.tag = y.tag ∧
      y.time ≤ x.time ∧ T₁ ≤ x.time := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, ht, rfl⟩ := mem_preAt.mp hx
    exact ⟨y, hy, rfl, rfl, rfl, rfl, ht.le, le_rfl⟩
  · obtain ⟨y, hy, ht, rfl⟩ := mem_postAt.mp hx
    exact ⟨y, hy, rfl, rfl, rfl, rfl, by dsimp only; linarith, by dsimp only; linarith⟩

end Plan

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- **The moved plan's activity sets**: forging the plan's entries before `T₁` at `T₁` and the
others `sh > 0` later, the keys forged on `[0, T₁ + sh)` are those of `Apre`, and those forged on
`[T₁ + sh, H]` are those of `Apost` (for `H ≥ Hp + sh`). -/
private theorem moved_sets {F : ChainShapeFamily O Info} {E : Env V}
    {key : Fin (Fintype.card V) ≃ V} {Apre Apost : List V} {T₁ Hp : Time}
    {sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V))}
    {fs : List (Forgery (compiled F) E)} (hP : PlanProps F E key Apre Apost T₁ Hp sel fs)
    (hT : 0 ≤ T₁) {sh H : Time} (hsh : 0 < sh) (hH : Hp + sh ≤ H) :
    (((preAt T₁ fs ++ postAt T₁ sh fs).filter
        fun x => decide (0 ≤ x.time ∧ x.time < T₁ + sh)).map fun x => key x.key).toFinset =
      Apre.toFinset ∧
    (((preAt T₁ fs ++ postAt T₁ sh fs).filter
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
      exact ⟨{ y with time := T₁ }, ⟨Or.inl (mem_preAt.mpr ⟨y, hy, ht, rfl⟩), hT,
        by dsimp only; linarith⟩, rfl⟩
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

private theorem bool_of_ne {x y b : Bool} (h₁ : x ≠ y) (h₂ : y ≠ b) : x = b := by
  cases x <;> cases y <;> cases b <;> simp_all

omit [Fintype V] [DecidableEq V] in
private theorem classGroups_two {a : IncidentClass V} (hs : a.IsSplit) (h : a.TwoGroups) :
    (∃ v, classGroups a v = true) ∧ ∃ v, classGroups a v = false := by
  cases a with
  | any => exact hs.elim
  | split G => rw [classGroups_split]; exact h
  | splitHeld G => rw [classGroups_splitHeld]; exact h

omit [Fintype V] [DecidableEq V] in
private theorem exercised_async {S : System V} {a : IncidentClass V} (hs : a.IsSplit)
    {b₀ b₁ : Time} {r : S.Run} (h : Exercised S (.split (classGroups a)) b₀ b₁ r) :
    Exercised S a.async b₀ b₁ r := by
  cases a with
  | any => exact hs.elim
  | split G => rw [classGroups_split] at h; exact h
  | splitHeld G => rw [classGroups_splitHeld] at h; exact h

/-- **The exercised Slice 1 witness without sleepers** (`m ≤ fcap`) at a point of the coverage
domain with a split class. -/
theorem cov1_split_witness_awake (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hcl : ShapeClaimsAt F K V) (hf : ProgressFits K F) (hnfg : ProposalsNotFGAtt F)
    (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx) (g : O.Id)
    (hg : O.output cap = some g) (q : HealQ V) (hq : q.DomainFeasible) (hsplit : q.a.IsSplit)
    (hadm : AdmitsFaults (K.progress cap i) q.fcap)
    (hforge : 0 < q.hpre ∨ 0 < q.hpost → ForgeableRole F)
    (hβ : (q.fcap : ℚ) < K.params.β * Fintype.card V) (hm : q.m ≤ q.fcap)
    (hsq hlq latq : WithTop ℕ) :
    ∃ (r : (Sys F V).Run) (b₀ b₁ : Time), (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
      HealClass (compiled F) K (shapeRoleFloor F V) q b₀ b₁ r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
        ((Sys F V).pt r).horizon r ∧
      Attains (compiled F) (shapeRoleFloor F V) q b₀ b₁ r ∧
      (∀ c : ℕ, hsq = c → SafeActive (q.readerDur (Sys F V) r) (healAt (Sys F V) b₁ c r)
        ((Sys F V).pt r)) ∧
      (∀ c d : ℕ, hlq = c → latq = d → ((Sys F V).pt r).TxLiveActive (q.readerDur (Sys F V) r)
        (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  classical
  obtain ⟨hpre_le, hpost_le, hn, -, hL1, hTG⟩ := hq
  have hL : 1 ≤ q.L := hL1 hsplit
  have hL2 : (2 : Time) ≤ (q.L : Time) * 2 := by
    have : (1 : Time) ≤ q.L := by exact_mod_cast hL
    linarith
  have h2 : 2 ≤ Fintype.card V := by omega
  /- The validators: `v₁` (key `1`) and `v₀`, in the other group, stay honest. -/
  let G := classGroups q.a
  have hGT : (∃ v, G v = true) ∧ ∃ v, G v = false := classGroups_two hsplit hTG
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let v₁ := key ⟨1, by omega⟩
  obtain ⟨v₀, hv₀G⟩ : ∃ x, G x ≠ G v₁ := by
    cases h : G v₁
    · obtain ⟨x, hx⟩ := hGT.1; exact ⟨x, by rw [hx]; decide⟩
    · obtain ⟨x, hx⟩ := hGT.2; exact ⟨x, by rw [hx]; decide⟩
  have h01 : v₀ ≠ v₁ := fun h => hv₀G (h ▸ rfl)
  obtain ⟨A, hA, hAc⟩ := exists_faulty {v₀, v₁} Finset.card_le_two (f := q.fcap) (by omega)
  have hv₀A : v₀ ∉ A := Finset.disjoint_right.mp hA (by simp)
  have hv₁A : v₁ ∉ A := Finset.disjoint_right.mp hA (by simp)
  have hadmA : AdmitsFaults (K.progress cap i) A.card := hAc ▸ hadm
  let Apre := A.toList.take q.hpre
  let Apost := A.toList.take q.hpost
  have hApre : Apre.length = q.hpre := by simp [Apre, hAc, hpre_le]
  have hApost : Apost.length = q.hpost := by simp [Apost, hAc, hpost_le]
  have hsubA : ∀ v, v ∈ Apre ∨ v ∈ Apost → v ∈ A := fun v hv => by
    rcases hv with hv | hv <;> exact Finset.mem_toList.mp (List.mem_of_mem_take hv)
  have hnodup : ∀ k, (A.toList.take k).Nodup := fun k => (Finset.nodup_toList A).sublist
    (List.take_sublist _ _)
  /- The times. -/
  let SL : Time := (F ⟨Fintype.card V, 2, two_pos, 2, two_pos⟩).skel.grid.slotLen
  have hSL : 0 < SL := (F _).skel.grid.slotLen_pos
  let T₁ : Time := (Fintype.card V : Time) * SL + 1
  have hT₁ : 0 < T₁ := by positivity
  let tR : Time := T₁ + ((K.params.heal cap i + K.params.catchUp : ℕ) : Time) * 2 + 1
  let H₀ : Time := tR + (K.params.latency cap i : Time) * 2
  let Hp : Time := ((T₁.toNat + Fintype.card V : ℕ) : Time) * SL
  let Hc : Time := ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
  let H : Time := H₀ + (q.L : Time) * 2 + Hc + Hp + (q.catchUp : Time) * 2 + 4
  have hx : ∀ y : WithTop ℕ, (0 : Time) ≤ ((y.untopD 0 : ℕ) : Time) := fun _ => by positivity
  have hcoe : ∀ c : ℕ, WithTop.untopD 0 (c : WithTop ℕ) = c := fun _ => rfl
  have hHc : 0 ≤ Hc := by positivity
  have hHp : 0 ≤ Hp := by positivity
  have htR : T₁ + 1 ≤ tR := by
    have : (0 : Time) ≤ ((K.params.heal cap i + K.params.catchUp : ℕ) : Time) * 2 := by
      positivity
    simp only [tR]; linarith
  have hH₀ : tR ≤ H₀ := le_add_of_nonneg_right (by positivity)
  have hH₀H : H₀ + (q.L : Time) * 2 + Hc + Hp + (q.catchUp : Time) * 2 + 4 ≤ H := le_rfl
  have hcu : (0 : Time) ≤ (q.catchUp : Time) * 2 := by positivity
  let p := latePoint A T₁ v₀ H
  let E : Env V := p.env
  have hΔ : E.ΔAC = 2 := latePoint_ΔAC A T₁ v₀ H
  have hΔF : E.ΔFG = 2 := latePoint_ΔFG A T₁ v₀ H
  have hawE : ∀ v t, E.awake v t = decide (T₁ ≤ t) := latePoint_awake A T₁ v₀ H
  have hT : ∀ v t, E.awake v t = true → T₁ ≤ t := fun v t h => by
    rw [hawE, decide_eq_true_iff] at h; exact h
  have hforge' : (Apre = [] ∧ Apost = []) ∨ ForgeableRole F := by
    by_cases hz : q.hpre = 0 ∧ q.hpost = 0
    · left
      exact ⟨List.length_eq_zero_iff.mp (hApre.trans hz.1),
        List.length_eq_zero_iff.mp (hApost.trans hz.2)⟩
    · right
      exact hforge (by omega)
  have hSLE : (F (pubOf E)).skel.grid.slotLen = SL := by
    change (F (pubOf (latePoint A T₁ v₀ H).env)).skel.grid.slotLen = SL
    rw [latePoint_pubOf]
  obtain ⟨sel, fs, hP⟩ := exists_plan F E key Apre Apost (b₁ := T₁) (H := Hp)
    (by rw [hSLE]; simp only [T₁]; linarith) (by rw [hSLE]) hforge'
  have hT₁Hp : T₁ ≤ Hp := by
    have h1 : (T₁.toNat : Time) = T₁ := Int.toNat_of_nonneg hT₁.le
    have h3 : (1 : Time) ≤ SL := hSL
    have h4 : T₁ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) := by
      push_cast; rw [h1]; linarith [show (0 : Time) ≤ (Fintype.card V : Time) by positivity]
    calc T₁ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) := h4
      _ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) * SL :=
        le_mul_of_one_le_right (by positivity) h3
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) E).Item
  let base : Model.Run (compiled F) E := Model.Run.mk p.faultyAt p.faultyAt_mono p.horizon [] key
    sel p.submit (Model.eagerRelay E p.faultyAt p.submit) hash
  have hfA : ∀ t, base.faultyAt t = A := fun t => latePoint_faultyAt A T₁ v₀ H t
  have hbH : base.horizon = H := latePoint_horizon A T₁ v₀ H
  have hH0 : 0 ≤ H := by
    have : (0 : Time) ≤ tR := by linarith
    linarith
  have hbH0 : 0 ≤ base.horizon := hbH ▸ hH0
  have hkeys : ∀ x ∈ fs, key x.key ∈ A := fun x hx => hsubA _ (hP.keys x hx)
  /- Forgery lists drawn from the plan inject only compromised, selected keys. -/
  have hinjF : ∀ l : List (Forgery (compiled F) E), (∀ x ∈ l, key x.key ∈ A) →
      ∀ t v o, o ∈ planInj v₀ l t v → ∀ d, Obj.Contains o d → ∀ u,
        base.signerOf d = some u → u ∈ base.faultyAt t := by
    intro l hl t v o ho d hd u hu
    obtain ⟨-, x, hx, -, rfl⟩ := mem_planInj.mp ho
    rcases parts_forged hd with rfl | hn
    · simp only [Model.Run.signerOf, Obj.signer?, forged_auth, Option.map_some,
        Option.some.injEq] at hu
      subst hu
      rw [hfA]
      exact hl x hx
    · simp [Model.Run.signerOf, Obj.signer?, hn] at hu
  have hinjS : ∀ l : List (Forgery (compiled F) E), (∀ x ∈ l, x.key ∈ sel x.role) →
      ∀ t v o, o ∈ planInj v₀ l t v → ∀ d, Obj.Contains o d → ∀ k r,
        d.auth = .signed k r → k ∈ base.sel r := by
    intro l hl t v o ho d hd k r hkr
    obtain ⟨-, x, hx, -, rfl⟩ := mem_planInj.mp ho
    rcases parts_forged hd with rfl | hn
    · rw [forged_auth] at hkr
      injection hkr with h1 h2
      subst h1 h2
      exact hl x hx
    · rw [hn] at hkr; cases hkr
  have hHPof : ∀ (b₀ b₁ : Time) (l : List (Forgery (compiled F) E)),
      (∀ x ∈ l, key x.key ∈ A) → (∀ x ∈ l, x.key ∈ sel x.role) →
      HoldPremises base G b₀ b₁ (planInj v₀ l) := fun b₀ b₁ l hl hl' =>
    ⟨hbH0, hP.admits, by rw [hΔ]; exact one_lt_two, by rw [hΔ, hΔF],
      Model.eagerRelay_txs (holdRun base G b₀ b₁ (planInj v₀ l))
        (by simp only [Model.Run.withEvents_eq]; rfl), fun t => by rw [hfA, hfA],
      hinjF l hl, hinjS l hl'⟩
  have hvalidOf : ∀ (b₀ b₁ : Time) (l : List (Forgery (compiled F) E)),
      (∀ x ∈ l, key x.key ∈ A) → (∀ x ∈ l, x.key ∈ sel x.role) →
      (holdRun base G b₀ b₁ (planInj v₀ l)).ExecutionValid := fun b₀ b₁ l hl hl' =>
    base.injectEvents_valid _ _ _ hbH0 hP.admits (fun _ => le_rfl) (hinjF l hl) (hinjS l hl')
  have hncOf : ∀ es, ¬ (base.withEvents es).HashCollision := fun es => by
    rw [Model.Run.withEvents_eq]
    exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  /- The reference run `R` and its cut `R'` at `H₀`. -/
  let fsR := preAt T₁ fs
  have hfsR : ∀ x ∈ fsR, key x.key ∈ A ∧ x.key ∈ sel x.role := fun x hx => by
    obtain ⟨y, hy, ht, rfl⟩ := mem_preAt.mp hx
    exact ⟨hkeys y hy, hP.cred y hy⟩
  let injR := planInj v₀ fsR
  let polR := holdPol base G T₁ T₁
  let R := holdRun base G T₁ T₁ injR
  have hHPR : HoldPremises base G T₁ T₁ injR :=
    hHPof T₁ T₁ fsR (fun x hx => (hfsR x hx).1) (fun x hx => (hfsR x hx).2)
  have hvR : R.ExecutionValid :=
    hvalidOf T₁ T₁ fsR (fun x hx => (hfsR x hx).1) (fun x hx => (hfsR x hx).2)
  obtain ⟨ys, hsplitR, hys⟩ := Model.Run.truncate_split hvR.sorted H₀
  let R' : Model.Run (compiled F) E := Model.Run.mk base.faultyAt base.faultyAt_mono H₀
    ((base.injectEvents (fun _ => 0) injR polR).filter (fun e => decide (e.time ≤ H₀))) key sel
    base.submit base.relay hash
  have hR' : R.truncate H₀ = R' := by
    change (base.withEvents (base.injectEvents (fun _ => 0) injR polR)).truncate H₀ = R'
    rw [Model.Run.truncate_eq, Model.Run.withEvents_eq]
  have hH₀0 : 0 ≤ H₀ := by linarith
  have hvR' : R'.ExecutionValid := hR' ▸ Model.Run.truncate_valid hvR hH₀0
    (by change H₀ ≤ (base.withEvents _).horizon; rw [Model.Run.withEvents_horizon, hbH]; linarith)
  have hrelR' : ∀ {u o t}, R'.releases u o t → R.releases u o t := by
    intro u o t hr
    have ht : t ≤ H₀ := by
      obtain ⟨j, hj, -⟩ := hr
      obtain ⟨e, he, -, het⟩ := hj.exists_event
      exact het ▸ (hvR'.in_horizon e (List.mem_of_getElem? he)).2
    rw [← hR'] at hr
    exact (Model.Run.truncate_releases_iff hsplitR hys ht).mp hr
  have hptR' : R'.point = latePoint A T₁ v₀ H₀ := latePoint_withHorizon A T₁ v₀ H H₀
  have hcDur : (Sys F V).cDur K ⟨E, R'⟩ = (K.params.catchUp : Time) * 2 := by
    change (K.params.catchUp : Time) * E.ΔAC = _
    rw [hΔ]
  /- `R'` is healthy from `T₁`, with progress from `T₁ + catchUp·2 + 1`. -/
  have hpsR : ((Sys F V).log ⟨E, R'⟩).PSync ((Sys F V).pt ⟨E, R'⟩) T₁ := by
    obtain ⟨-, -, hag, -⟩ := Model.Run.truncate_prefix hvR H₀
    rw [hR'] at hag
    have h1 := (Model.sysOf_delivers_iff R _ _ _).mpr (hold_psync hHPR)
    have h2 := h1.prefix hag (b := H₀)
      (by change H₀ ≤ (base.withEvents _).horizon; rw [Model.Run.withEvents_horizon, hbH]; linarith)
      (fun a => by
        have := le_max_left a T₁
        change a ≤ max a T₁ + E.ΔAC - 1
        rw [hΔ]; linarith)
      (fun a => by
        have := le_max_left a T₁
        change a ≤ max a T₁ + E.ΔFG - 1
        rw [hΔF]; linarith)
    have h3 := h2.reindex (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (cut' := H₀)
      (by change H₀ ≤ (base.withEvents _).horizon; rw [Model.Run.withEvents_horizon, hbH]; linarith)
    simp only [R, Model.sysOf_point, holdRun, Model.Run.injectRun, Model.Run.withEvents_point]
      at h3
    exact h3
  have hheal : (Sys F V).Healthy K T₁ ⟨E, R'⟩ := by
    refine ⟨hpsR, ?_, ?_⟩
    · change R'.point.HealthyOn K.params.β T₁ R'.point.horizon
      rw [hptR']
      refine ⟨?_, fun v t ht _ _ => latePoint_awake_of_ge (le_trans (le_max_left _ _) ht) v⟩
      rw [latePoint_faultCount, hAc]
      exact hβ
    · change E.ΔFG ≤ (K.params.fgDelay : Time) * E.ΔAC
      rw [hΔ, hΔF]
      have : (1 : Time) ≤ K.params.fgDelay := by exact_mod_cast hfg
      linarith
  have hprogR' : (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K T₁ ⟨E, R'⟩)
      ((Sys F V).pt ⟨E, R'⟩).horizon ⟨E, R'⟩ := by
    change shapeHolds F (K.progress cap i) ((Sys F V).cDur K ⟨E, R'⟩) _ _ R'.point (key, sel)
    refine latePoint_holds F K key h2 hptR' sel hP.proposer hf cap i hadmA hv₁A ?_ _
    change T₁ + _ + 1 ≤ max T₁ 0 + (Sys F V).cDur K ⟨E, R'⟩ + 1
    rw [max_eq_left hT₁.le]
  /- Healthy liveness gives an honest proposal `m` of `v`. -/
  have hlive : ProposalLiveReady R' ((Sys F V).cDur K ⟨E, R'⟩) g
      ((Sys F V).heal K cap i T₁ ⟨E, R'⟩) (K.params.latency cap i) := by
    rcases hcl.healthyLive cap g hg i T₁ ⟨E, R'⟩ hvR' ⟨hheal, hprogR'⟩ with h | h
    · exact h
    · exact absurd h
        (Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj))
  obtain ⟨τ, k, hdr, hτt, -, ⟨-, rl, cs, hrole, hrel⟩, -⟩ := hlive tR
    (by
      change max T₁ 0 + (K.params.heal cap i : Time) * E.ΔAC ≤ tR
      rw [hΔ, max_eq_left hT₁.le]
      have : (0 : Time) ≤ (K.params.catchUp : Time) * 2 := by positivity
      simp only [tR]; push_cast; linarith)
    (by change tR + (K.params.latency cap i : Time) * E.ΔAC ≤ H₀; rw [hΔ])
    ⟨v₁, by
      rw [hptR', hcDur]
      refine latePoint_ready hv₁A ?_
      rw [hΔ]
      have : (0 : Time) ≤ (K.params.latency cap i : Time) * 2 := by positivity
      have : (0 : Time) ≤ (K.params.heal cap i : Time) * 2 := by positivity
      simp only [tR]; push_cast; linarith⟩
  let v : V := key k
  let m : (protoOf (compiled F) E).Object := Model.Obj.mk (.signed k rl) (.item hdr) cs
  have hmfg : ¬ (protoOf (compiled F) E).isFGAtt m := hnfg (pubOf E) k rl hdr cs hrole
  have hτR : R.releases v m τ := hrelR' hrel
  have hτ0 : 0 ≤ τ := le_trans hT₁.le (le_of_inject_releases base hT injR polR hτR)
  have hτH₀ : τ ≤ H₀ := by
    obtain ⟨j, hj, -⟩ := hrel
    obtain ⟨e, he, -, het⟩ := hj.exists_event
    exact het ▸ (hvR'.in_horizon e (List.mem_of_getElem? he)).2
  /- The first release `t₀` of `m` on `R`. -/
  have hsigm : m.signer? = some k := rfl
  have hex : ∃ n : ℕ, R.releases v m n := ⟨τ.toNat, by rwa [Int.toNat_of_nonneg hτ0]⟩
  let n₀ := Nat.find hex
  set t₀ : Time := (n₀ : Time) with ht₀
  have hrel₀ : R.releases v m t₀ := Nat.find_spec hex
  have hmin : ∀ u t', t' < t₀ → ¬ R.releases u m t' := by
    intro u t' ht' hr
    have hu : key k = u := by
      have := R.releases_key_of_signer hr hsigm
      rwa [Model.Run.withEvents_key] at this
    subst hu
    have ht0 : 0 ≤ t' := le_trans hT₁.le (le_of_inject_releases base hT injR polR hr)
    have hlt : t'.toNat < n₀ := (Int.toNat_lt ht0).mpr ht'
    exact Nat.find_min hex hlt (by rwa [Int.toNat_of_nonneg ht0])
  have ht₀τ : t₀ ≤ τ := by
    have h1 : n₀ ≤ τ.toNat := Nat.find_min' hex (by rwa [Int.toNat_of_nonneg hτ0])
    have h2 : (0 : Int) ≤ τ := hτ0
    change (n₀ : Int) ≤ τ
    omega
  have hT₁t₀ : T₁ ≤ t₀ := le_of_inject_releases base hT injR polR hrel₀
  /- The witness `W`: incident `[t₀, b₁)`, the plan's late forgeries shifted past `b₁`. -/
  let b₁ : Time := t₀ + (q.L : Time) * 2
  have hb₀₁ : t₀ ≤ b₁ := by simp only [b₁]; linarith
  have ht₀b₁ : t₀ < b₁ := by simp only [b₁]; linarith
  have hb₁ : 0 ≤ b₁ := by linarith
  let sh : Time := b₁ - T₁
  have hsh : 0 < sh := by simp only [sh, b₁]; linarith
  have hb₁sh : T₁ + sh = b₁ := by simp only [sh]; ring
  let fsW := fsR ++ postAt T₁ sh fs
  have hmovedW : ∀ x ∈ fsW, ∃ y ∈ fs, x.key = y.key ∧ x.role = y.role ∧ x.msg = y.msg ∧
      x.tag = y.tag ∧ y.time ≤ x.time ∧ T₁ ≤ x.time := fun x hx => mem_moved hsh.le hx
  have hfsW : ∀ x ∈ fsW, key x.key ∈ A ∧ x.key ∈ sel x.role := fun x hx => by
    obtain ⟨y, hy, hk, hr, -, -, -, -⟩ := hmovedW x hx
    rw [hk, hr]
    exact ⟨hkeys y hy, hP.cred y hy⟩
  have hpostT : ∀ x ∈ postAt T₁ sh fs, b₁ ≤ x.time := fun x hx => by
    obtain ⟨y, -, ht, rfl⟩ := mem_postAt.mp hx
    dsimp only
    linarith
  let injW := planInj v₀ fsW
  let polW := holdPol base G t₀ b₁
  let W := holdRun base G t₀ b₁ injW
  have hHPW : HoldPremises base G t₀ b₁ injW :=
    hHPof t₀ b₁ fsW (fun x hx => (hfsW x hx).1) (fun x hx => (hfsW x hx).2)
  have hvW : W.ExecutionValid :=
    hvalidOf t₀ b₁ fsW (fun x hx => (hfsW x hx).1) (fun x hx => (hfsW x hx).2)
  have hinjRW : ∀ t, t < b₁ → injR t = injW t := fun t ht =>
    (planInj_append (fun x hx => lt_of_lt_of_le ht (hpostT x hx))).symm
  have hpolR : ∀ (n : ℕ) (w : V) (o : (protoOf (compiled F) E).Object),
      polR (base.front (base.injectStages (fun _ => 0) injR polR n) (n : Time)) w o (n : Time) =
        true := fun n w o => by
    rcases lt_or_ge (n : Time) T₁ with h | h
    · exact holdPol_front base G T₁ T₁ hΔ injR polR n (Or.inl h) w o
    · exact holdPol_front base G T₁ T₁ hΔ injR polR n (Or.inr h) w o
  have hstage : ∀ n ≤ n₀, base.injectStages (fun _ => 0) injR polR n =
      base.injectStages (fun _ => 0) injW polW n :=
    base.injectStages_congr (fun _ => 0) injR polR
      (fun n hn => hinjRW _ (lt_of_lt_of_le
        (show (n : Time) < t₀ by change (n : Int) < (n₀ : Int); omega) hb₀₁))
      (fun n hn w o => by
        rw [hpolR n w o]
        exact (holdPol_front base G t₀ b₁ hΔ injR polR n
          (Or.inl (by change (n : Int) < (n₀ : Int); omega)) w o).symm)
  have ht₀H : t₀ ≤ base.horizon := by rw [hbH]; linarith
  /- A content first released at `t₀` on `W`, by its honest signer. -/
  obtain ⟨k', r', d, hs, hfgd, hrelW, hnew⟩ : ∃ k r d, d.auth = .signed k r ∧
      ¬ (protoOf (compiled F) E).isFGAtt d ∧ W.releases (base.key k) d t₀ ∧
      ∀ u t, t < t₀ → ¬ W.releases u d t := by
    by_cases hblk : ∃ w o, polW (base.front (base.injectStages (fun _ => 0) injR polR n₀)
        (n₀ : Time)) w o (n₀ : Time) = false
    · obtain ⟨w, o, hb⟩ := hblk
      rw [hstage n₀ le_rfl] at hb
      exact fresh_of_blocked base G t₀ b₁ injW hΔ rfl ht₀H hb
    · push Not at hblk
      have hstage' : ∀ n ≤ n₀ + 1, base.injectStages (fun _ => 0) injR polR n =
          base.injectStages (fun _ => 0) injW polW n :=
        base.injectStages_congr (fun _ => 0) injR polR
          (fun n hn => hinjRW _ (lt_of_le_of_lt
            (show (n : Time) ≤ t₀ by change (n : Int) ≤ (n₀ : Int); omega) ht₀b₁))
          (fun n hn w o => by
            rw [hpolR n w o]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
            · exact (holdPol_front base G t₀ b₁ hΔ injR polR n
                (Or.inl (by change (n : Int) < (n₀ : Int); omega)) w o).symm
            · cases h : polW (base.front (base.injectStages (fun _ => 0) injR polR n₀)
                (n₀ : Time)) w o (n₀ : Time)
              · exact absurd h (hblk w o)
              · rfl)
      refine ⟨k, rl, m, rfl, hmfg, ?_, fun u t ht hr => ?_⟩
      · refine releases_of_stages base (by linarith) ht₀H ?_ hrel₀
        rw [ht₀, Int.toNat_natCast]
        exact hstage' _ le_rfl
      · have ht0 : 0 ≤ t := le_trans hT₁.le (le_of_inject_releases base hT injW polW hr)
        refine hmin u t ht (releases_of_stages base ht0 (by linarith) ?_ hr)
        exact (hstage (t.toNat + 1) ((Int.toNat_lt ht0).mpr ht)).symm
  /- The other group's honest node and the exercise. -/
  have hk' : key k' ∉ A := by
    have := notMem_faulty_of_releases base hvW hrelW
    rwa [hfA] at this
  obtain ⟨w, hwG, hwA⟩ : ∃ w, G w ≠ G (key k') ∧ w ∉ A := by
    by_cases h : G v₀ = G (key k')
    · exact ⟨v₁, fun h' => hv₀G (h.trans h'.symm), hv₁A⟩
    · exact ⟨v₀, h, hv₀A⟩
  have hgroups : ∀ b : Bool, ∃ u, G u = b ∧ ∀ t, u ∉ base.faultyAt t := by
    intro b
    by_cases h : G v₁ = b
    · exact ⟨v₁, h, fun t => by rw [hfA]; exact hv₁A⟩
    · refine ⟨v₀, ?_, fun t => by rw [hfA]; exact hv₀A⟩
      exact bool_of_ne hv₀G h
  have hexer : Exercised (Sys F V) q.a.async t₀ b₁ ⟨E, W⟩ :=
    exercised_async hsplit (exercised_of_fresh hHPW hvW hs hfgd hrelW hnew hwG
      (fun t => by rw [hfA]; exact hwA)
      (fun t h1 _ => by rw [hawE, decide_eq_true_iff]; linarith)
      (by rw [hΔ]; simp only [b₁]; linarith) (hgroups true) (hgroups false))
  /- The rest of the witness, as in `cov1_witness`. -/
  have hpt : (Sys F V).pt ⟨E, W⟩ = p := by
    change W.point = p
    simp only [W, holdRun, Model.Run.injectRun, Model.Run.withEvents_point]
    rfl
  have hside : ∀ z ∈ fs, ∀ z' ∈ fs, z.key = z'.key → z.role = z'.role → z.msg = z'.msg →
      z.tag = z'.tag → z.time < T₁ → z'.time < T₁ := fun z hz z' hz' h1 h2 h3 h4 hzt => by
    rw [← hP.unique z hz z' hz' h1 h2 h3 h4]; exact hzt
  have huniqW : ∀ x ∈ fsW, ∀ y ∈ fsW, x.key = y.key → x.role = y.role → x.msg = y.msg →
      x.tag = y.tag → x.time = y.time := by
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
      rw [hP.unique z hz z' hz' hk hr hm' htg]
  have hFP : ForgeryPremisesAt base (shapeRoleFloor F V E) v₀ fsW injW polW :=
    ⟨fun _ _ _ => mem_planInj, hvW, fun t => by rw [hfA, hfA],
      fun x hx => by rw [hfA]; exact (hfsW x hx).1, by rw [hfA]; exact hv₀A,
      fun x hx => by
        obtain ⟨-, -, -, -, -, -, -, hT'⟩ := hmovedW x hx
        rw [hawE, decide_eq_true_iff]; exact hT',
      fun x hx => by
        obtain ⟨-, -, -, -, -, -, -, hT'⟩ := hmovedW x hx
        refine ⟨by linarith, ?_⟩
        rw [hbH]
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨z, -, -, rfl⟩ := mem_preAt.mp hx
          change T₁ ≤ H
          simp only [H]; linarith
        · obtain ⟨z, hz, -, rfl⟩ := mem_postAt.mp hx
          have := (hP.time_range z hz).2
          change z.time + sh ≤ H
          simp only [H, sh, b₁]; linarith,
      fun x hx s hs => by
        obtain ⟨y, hy, -, hr, -, -, hyt, -⟩ := hmovedW x hx
        rw [hr] at hs
        exact le_trans (hP.floor_le y hy s hs) hyt,
      huniqW⟩
  have hact : ∀ a b, activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ a b =
      ((fsW.filter fun x => decide (a ≤ x.time ∧ x.time < b)).map
        fun x => key x.key).toFinset.card := fun a b => by
    change (activeFaulty W (shapeRoleFloor F V E) a b).card = _
    rw [activeFaulty_of_forgeriesAt hFP]
  obtain ⟨hsetPre, hsetPost⟩ := moved_sets hP hT₁.le hsh (H := H)
    (by simp only [H, sh, b₁]; linarith)
  rw [hb₁sh] at hsetPre hsetPost
  have hactpre : activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ 0 (max b₁ 0) = q.hpre := by
    rw [hact, max_eq_left hb₁, hsetPre, List.toFinset_card_of_nodup (hnodup _), hApre]
  have hactpost : activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ (max b₁ 0)
      (((Sys F V).pt ⟨E, W⟩).horizon + 1) = q.hpost := by
    rw [hact, max_eq_left hb₁, hpt, latePoint_horizon, hsetPost,
      List.toFinset_card_of_nodup (hnodup _), hApost]
  have hnah : (notAwakeHonest (Sys F V) t₀ b₁ ⟨E, W⟩).card = max q.m q.fcap := by
    rw [latePoint_notAwakeHonest hpt hT₁t₀, hAc, max_eq_right hm]
  have hready : (Sys F V).ready K b₁ ⟨E, W⟩ = b₁ + (Sys F V).cDur K ⟨E, W⟩ + 1 := by
    simp only [System.ready, max_eq_left hb₁]
  have hhealAt : ∀ c : ℕ, healAt (Sys F V) b₁ c ⟨E, W⟩ = b₁ + (c : Time) * 2 := fun c => by
    change max b₁ 0 + (c : Time) * ((Sys F V).pt ⟨E, W⟩).env.ΔAC = _
    rw [hpt, latePoint_ΔAC, max_eq_left hb₁]
  have hrd : q.readerDur (Sys F V) ⟨E, W⟩ = (q.catchUp : Time) * 2 := by
    change (q.catchUp : Time) * ((Sys F V).pt ⟨E, W⟩).env.ΔAC = _
    rw [hpt, latePoint_ΔAC]
  have hcl' := holdRun_class (rho := base) (b₀ := t₀) (b₁ := b₁) (inj := injW) q.a hHPW
  refine ⟨⟨E, W⟩, t₀, b₁, hvW, hncOf _, ⟨hcl'.1, hcl'.2, hb₀₁, ?_, hactpre.le, hactpost.le, ?_,
    ?_, ?_, ?_⟩, ?_, ⟨?_, hactpre, hactpost, ?_, hnah, hexer⟩, ?_, ?_⟩
  · rw [hpt, latePoint_ΔAC]; simp only [b₁]; linarith
  · rw [hnah]; exact le_max_left _ _
  · rw [hpt, latePoint_faultCount, hAc]
  · intro v t h1 h2 h3
    rw [hpt] at h2 h3 ⊢
    exact latePoint_honestAwakeAfter (by linarith) v t h1 h2 h3
  · rw [hpt, latePoint_ΔAC, latePoint_ΔFG]
    have : (1 : Time) ≤ (K.params.fgDelay : Time) := by exact_mod_cast hfg
    linarith
  · rw [hready]
    change shapeHolds F (K.progress cap i) ((Sys F V).cDur K ⟨E, W⟩) _ _
      ((Sys F V).pt ⟨E, W⟩) (W.key, W.sel)
    rw [show W.key = key from Model.Run.withEvents_key _ _,
      show W.sel = sel from Model.Run.withEvents_sel _ _]
    refine latePoint_holds F K key h2 hpt sel hP.proposer hf cap i hadmA hv₁A ?_ _
    linarith
  · rw [hpt, latePoint_ΔAC]; simp only [b₁]; ring
  · rw [hpt, latePoint_faultCount, hAc]
  · intro c hc
    rw [hhealAt, hpt, hrd]
    have : (c : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 ≤ ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hcoe]
      push_cast
      linarith [hx hlq, hx latq]
    refine latePoint_safeActive hv₀A hv₁A h01 _ _ ?_ ?_
    · simp only [H, b₁]; linarith
    · simp only [H]; linarith
  · intro c d hc hd
    rw [hhealAt, hpt, latePoint_ΔAC, hrd]
    have : (c : Time) * 2 + (d : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 + (d : Time) * 2 ≤
        ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hd, hcoe, hcoe]
      push_cast
      linarith [hx hsq]
    have hc0 : (0 : Time) ≤ (c : Time) * 2 := by positivity
    refine latePoint_txLiveActive hv₀A hv₁A h01.symm hT₁.le _ _ _ ?_ ?_
    · rw [max_eq_right (by simp only [b₁]; linarith)]
      simp only [H, b₁]; linarith
    · simp only [H]; linarith

end Consensus.Comparison

end
