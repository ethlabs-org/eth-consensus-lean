module
public import ConsensusLean.Comparison.HealProfile

@[expose] public section

/-! # Slice 1 rejection tests

Cheap checks that the Slice 1 statements reject what they must: points outside the coverage domain
(a split class, held or not, at `L = 0`; sleepers beyond the cap at `L = 0`; activity above the
cap; fewer than two ready readers), coverage by a system with no valid run, with an excuse on every
run or without the covered output, and coverage of a finite liveness bound by runs that never
exercise liveness. The window guard of `notAwakeHonest`: on an empty incident window it is
`faultyAt horizon`. The class order: `splitHeld G ≤ split G ≤ any`, and `any` is below no split
class. The content-origin hold goes by first origin: prefix stock (first released with its
deadline by `b₀`) and contents first released from `b₁` on are never held, also when re-released
honestly during or after the incident, so a cross-group receipt of them is allowed; a release
shortly before `b₀` whose deadline falls past `b₀` is held. Own signatures nested in a release are
honest. A held-split point of the coverage domain exists. -/

namespace Consensus.Comparison.Test

open Consensus.Comparison Consensus.Model

variable {V : Type}

section Points

variable [Fintype V]

/-- A split class at `L = 0` is outside the coverage domain. -/
theorem heal_split_zero_infeasible (hpre hpost m f c : ℕ) (θ : ℚ) (G : V → Bool) :
    ¬ (⟨0, hpre, hpost, m, f, .split G, θ, c⟩ : HealQ V).DomainFeasible := by
  rintro ⟨-, -, -, -, h, -⟩
  simpa using h trivial

/-- A held split class at `L = 0` is outside the coverage domain. -/
theorem heal_splitHeld_zero_infeasible (hpre hpost m f c : ℕ) (θ : ℚ) (G : V → Bool) :
    ¬ (⟨0, hpre, hpost, m, f, .splitHeld G, θ, c⟩ : HealQ V).DomainFeasible := by
  rintro ⟨-, -, -, -, h, -⟩
  simpa using h trivial

/-- At `L = 0` (empty incident window) a lower bound `m` above the cap is outside the domain. -/
theorem heal_zero_sleepers_infeasible (q : HealQ V) (hL : q.L = 0) (hm : q.fcap < q.m) :
    ¬ q.DomainFeasible :=
  fun hq => absurd (hq.2.2.2.1 hL) (by omega)

/-- Activity above the cap is outside the domain (before or after the incident). -/
theorem heal_activity_gt_infeasible (q : HealQ V) (h : q.fcap < q.hpre ∨ q.fcap < q.hpost) :
    ¬ q.DomainFeasible := by
  rintro ⟨h₁, h₂, -⟩
  omega

/-- Fewer than two validators outside the counted ones is outside the domain. -/
theorem heal_readers_infeasible (q : HealQ V) (h : Fintype.card V < max q.m q.fcap + 2) :
    ¬ q.DomainFeasible :=
  fun hq => absurd hq.2.2.1 (by omega)

/-- A held-split point of the coverage domain: two validators in two groups, one incident delay,
no faults, no activity, no sleepers. -/
theorem splitHeld_feasible_example :
    (⟨1, 0, 0, 0, 0, .splitHeld (fun v : Fin 2 => decide (v = 0)), 1 / 2, 1⟩ :
      HealQ (Fin 2)).DomainFeasible :=
  ⟨le_rfl, le_rfl, by simp, by simp, fun _ => le_rfl, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

end Points

/-- The held split is below the split. -/
theorem splitHeld_le_split (G : V → Bool) : (.splitHeld G : IncidentClass V) ≤ .split G := rfl

/-- The split is below `any`. -/
theorem split_le_any (G : V → Bool) : (.split G : IncidentClass V) ≤ .any := trivial

/-- `any` is below no split class. -/
theorem any_not_le_split (G : V → Bool) : ¬ (.any : IncidentClass V) ≤ .split G := id

section Runs

variable [Fintype V] [DecidableEq V]

/-- The window guard: on an empty incident window (`b₁ ≤ max b₀ 0`) the validators that cannot vote
are exactly those compromised by the horizon. -/
theorem notAwakeHonest_empty_window {S : System V} (b₀ b₁ : Time) (r : S.Run)
    (h : b₁ ≤ max b₀ 0) : notAwakeHonest S b₀ b₁ r = (S.pt r).faultyAt (S.pt r).horizon := by
  ext v
  simp only [notAwakeHonest, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hv | ⟨hlt, -⟩)
    · exact hv
    · exact absurd hlt (not_lt.mpr h)
  · exact Or.inl

variable {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}

/-- **Prefix stock is never held**: a content whose first honest release, at `t₀`, has its
deadline `t₀ + ΔAC − 1` by `b₀` has no held origin, even when its validator re-releases it honestly
during or after the incident (`t' ≥ b₀`). -/
theorem prefix_stock_not_held (rho : Model.Run F E) (k : Fin (Fintype.card V))
    (d : (protoOf F E).Object) (b₀ b₁ t₀ t' : Time) (h₀ : FirstHonestRelease rho k d t₀)
    (hpre : t₀ + E.ΔAC - 1 ≤ b₀) (_hre : HonestReleaseAt rho k d t') (_ht' : b₀ ≤ t') :
    ¬ HeldOrigin rho b₀ b₁ k d := by
  rintro ⟨-, t₁, h₁, -, hdl⟩
  obtain rfl : t₁ = t₀ := le_antisymm (h₁.2 t₀ h₀.1) (h₀.2 t₁ h₁.1)
  exact absurd hdl (not_lt.mpr hpre)

/-- **Contents first released from `b₁` on are never held**, whatever their later releases. -/
theorem post_incident_origin_not_held (rho : Model.Run F E) (k : Fin (Fintype.card V))
    (d : (protoOf F E).Object) (b₀ b₁ t₀ : Time) (h₀ : FirstHonestRelease rho k d t₀)
    (hpost : b₁ ≤ t₀) : ¬ HeldOrigin rho b₀ b₁ k d := by
  rintro ⟨-, t₁, h₁, hlt, -⟩
  exact absurd (lt_of_lt_of_le hlt (hpost.trans (h₀.2 t₁ h₁.1))) (lt_irrefl t₁)

/-- **A cross-group receipt of unheld contents is allowed**: when no content signed by the other
group has a held origin (for example, every such content is prefix stock, re-released or not), the
hold holds, whatever is received before `b₁`. -/
theorem hold_of_no_held_origin (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time)
    (h : ∀ k d, ¬ HeldOrigin rho b₀ b₁ k d) : ContentOriginHold rho G b₀ b₁ :=
  fun _ _ _ _ _ _ d _ k _ _ _ => h k d

/-- **A release shortly before `b₀` whose deadline falls past `b₀` is held**: the hold covers every
first honest release not owed by `SyncUntil b₀`, not only releases inside the incident. -/
theorem prefix_tail_held (rho : Model.Run F E) (k : Fin (Fintype.card V))
    (d : (protoOf F E).Object) (b₀ b₁ t₀ : Time) (hfg : ¬ (protoOf F E).isFGAtt d)
    (h₀ : FirstHonestRelease rho k d t₀) (hbefore : t₀ < b₀) (hdl : b₀ < t₀ + E.ΔAC - 1)
    (hb : b₀ ≤ b₁) : HeldOrigin rho b₀ b₁ k d :=
  ⟨hfg, t₀, h₀, lt_of_lt_of_le hbefore hb, hdl⟩

/-- **Own signatures nested in a release are honest**: a content carried in an object that its
signer's validator released while honest is an honest content of that key. -/
theorem honestMade_of_nested (rho : Model.Run F E) (k : Fin (Fintype.card V))
    (o d : (protoOf F E).Object) (t : Time) (hh : rho.point.HonestAt (rho.key k) t)
    (hrel : rho.releases (rho.key k) o t) (hd : Obj.Contains o d) : HonestMade rho k d :=
  ⟨t, hh, o, hrel, hd⟩

variable {Prog : Type} {X : Progress (sysOf O F V) Prog} {K : Contract Prog}
  {fl : RoleFloor F V}

/-- No valid run: no finite safety bound at a point of the coverage domain is covered. -/
theorem heal_no_valid_not_covered (hS : ∀ r, ¬ (sysOf O F V).Valid r) {cap : Capability}
    {i : K.Idx} {hs hl lat : Bound (HealQ V)} (q : HealQ V) (hq : q.DomainFeasible)
    (hfin : hs q < ⊤) : ¬ HealDomainCoverage F X K fl cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, hv, -⟩ := h.covers q hq (Or.inl hfin)
  exact hS r hv

/-- An excuse on every run: no finite safety bound at a point of the coverage domain is
covered. -/
theorem heal_excuse_not_covered (hS : ∀ r, (sysOf O F V).Excuse r) {cap : Capability}
    {i : K.Idx} {hs hl lat : Bound (HealQ V)} (q : HealQ V) (hq : q.DomainFeasible)
    (hfin : hs q < ⊤) : ¬ HealDomainCoverage F X K fl cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, -, hne, -⟩ := h.covers q hq (Or.inl hfin)
  exact hne (hS r)

/-- **An absent output is never covered**: when `cap`'s output is not provided, no finite claim at
a point of the coverage domain is covered (its claims would be vacuous). -/
theorem heal_absent_output_not_covered {cap : Capability}
    (hcap : (sysOf O F V).schema.output cap = none) {i : K.Idx} {hs hl lat : Bound (HealQ V)}
    (q : HealQ V) (hq : q.DomainFeasible) (hfin : hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) :
    ¬ HealDomainCoverage F X K fl cap i hs hl lat := by
  intro h
  have := (h.covers q hq hfin).1
  simp [hcap] at this

/-- **A safety-only witness does not cover a finite liveness bound**: on a system whose valid runs
have no transaction submissions, finite `hl` and `lat` at a point of the coverage domain are not
covered, whatever `hs` is. -/
theorem heal_safety_only_not_covered
    (hS : ∀ r, (sysOf O F V).Valid r → ∀ v t, ((sysOf O F V).pt r).submit v t = [])
    {cap : Capability} {i : K.Idx} {hs hl lat : Bound (HealQ V)} (q : HealQ V)
    (hq : q.DomainFeasible) (c d : ℕ) (hc : hl q = c) (hd : lat q = d) :
    ¬ HealDomainCoverage F X K fl cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, hv, -, -, -, -, hlive⟩ :=
    h.covers q hq (Or.inr ⟨by simp [hc], by simp [hd]⟩)
  obtain ⟨x, t, t', u, w, -, -, -, hx, -⟩ := hlive c d hc hd
  simp [hS r hv] at hx

end Runs

end Consensus.Comparison.Test

end
