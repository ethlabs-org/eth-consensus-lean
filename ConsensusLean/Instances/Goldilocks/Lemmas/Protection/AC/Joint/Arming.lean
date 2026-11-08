module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Numbers
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.ArmingLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Delivery
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the arming over AC traces: the premise package from the class

**The premise package** (`outagePremisesAC_ofClass`): on an AC trace of the SA with the unlock
given at a write mode of width `k` (`ACRunU wm u`, `wm.width = k`), in Tier A's frozen protection
class at a contract point (`ProtClassAC0`, `ProtPointAC0`) with the lag `T + (4k + 6)Δ ≤ b₀`, a
protected block `P ∈ U` that is genesis or an origin within `b₀` of a label `σ` with `t_σ ≤ T`
gives `OutagePremisesAC`, with `b₀`, `b₁`, the no-sleep window `[a, z]` of the class
(`protStartAC`, `protEndAC`), the cohort `A₀` awake at `a`, the late wakers `W` of `[a, z]`, the
cover label `j₀ = Compose.coverLabel sp b₀` and the first restored label `r`
(`restoredLabelAC`). It is the AC counterpart of `Obligations.outageLockPremises_of_arming` with
the arming of `Obligations.outage_arming`; the read of the source is not part of it.

* the numbers N1–N6 (`cover_numbersAC`) from the class's outage times, the lag `4k + 6`, the
  no-sleep length `4k + 6` of a contract point and the budget `β ≤ 4k − 5`;
* the frontier and the fault bounds from η-sleepiness (`ProtClassAC0.frontier`,
  `ProtClassAC0.faultBound`), the service and the tick duty from the class;
* the cohort from `NoSleepOnAC` and `CohortOnAC`, its restarts by `a + Δ`
  (`restart_le_of_awakeAC`);
* the arming fields from the slow-lock writes of `Joint/ArmingLocks` (`armed_lock_prevAC` at
  `j₀ − 1`, `armed_lock_coverAC` at `j₀`, with `Hold := A₀` and `Opp := Hᶜ ∪ W`);
* the post-GST pool delivery from the service from `b₁` (`vote_pooled_before_earlyAC`). -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-! ### The restored label -/

variable (sp) in
/-- **The first restored label** after the stop `b₁`: the least `r` with `b₁ ≤ t_r + Δ` (`0` if
there is none). -/
noncomputable def restoredLabelAC (b₁ : Time) : Nat := by
  classical
  exact if h : ∃ s : Nat, b₁ ≤ sp.ts s + sp.Δ then Nat.find h else 0

/-- The restored label is the least `r` with `b₁ ≤ t_r + Δ`. -/
theorem restoredLabelAC_spec {b₁ : Time} (h : ∃ s : Nat, b₁ ≤ sp.ts s + sp.Δ) :
    b₁ ≤ sp.ts (restoredLabelAC sp b₁) + sp.Δ ∧
      ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → restoredLabelAC sp b₁ ≤ s := by
  classical
  have he : restoredLabelAC sp b₁ = Nat.find h := dite_eq_left h
  rw [he]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min' h hs⟩

/-! ### The numbers -/

/-- A contract point's no-sleep length is `4k + 6`. -/
theorem ProtPointAC0.noSleep_eq {q : ProtQ} (hq : ProtPointAC0 sp q) :
    q.noSleep = 4 * sp.k + 6 := by
  obtain ⟨-, -, h1, h2, -⟩ := hq
  omega

/-- **The outage numbers** in node units at a contract point of the class under the lag
`4k + 6`: the gates of the cover label `j₀`, the budget, the stop inside `(t_{j₀} + Δ,
t_{j₀+k} + Δ]`, the window `[a, z]` from `0`, by `t_{j₀−k}` (so `a + Δ ≤ t_{j₀}`) and past
`t_{j₀+k} + Δ` and `t_{j₀} + 6Δ`, and `k < j₀`. -/
theorem cover_numbersAC {q : ProtQ} (hq : ProtPointAC0 sp q) {T b₀ b₁ : Time}
    (hcl : ProtClassAC0 q T b₀ b₁ tr H U)
    (hlag : T + ((4 * sp.k + 6 : ℕ) : Time) * sp.Δ ≤ b₀) :
    let j₀ := Compose.coverLabel sp b₀
    sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ ∧
      b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ ∧ b₁ ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ ∧
      sp.ts j₀ + sp.Δ < b₁ ∧ protStartAC sp q b₀ + sp.Δ ≤ sp.ts j₀ ∧
      sp.ts (j₀ + sp.k : Nat) + sp.Δ ≤ protEndAC sp q b₁ ∧ 0 ≤ protStartAC sp q b₀ ∧
      protStartAC sp q b₀ ≤ sp.ts ((j₀ : Int) - sp.k) ∧
      (∀ d ≤ 6 * sp.Δ, sp.ts j₀ + d ≤ protEndAC sp q b₁) ∧ sp.k < j₀ := by
  intro j₀
  obtain ⟨hT, hb01, hβ, -⟩ := hcl
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hlag' : T + (4 * sp.k + 6) * sp.Δ ≤ b₀ := by push_cast at hlag; exact hlag
  have hns := hq.noSleep_eq
  have hk : (0 : Time) ≤ sp.k := by positivity
  have hkΔ := mul_nonneg hk hΔ.le
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := sp) (b₀ := b₀) (by
    have : (0 : Time) ≤ (4 * sp.k + 4) * sp.Δ := by positivity
    linarith)
  obtain ⟨ha0, haj, hzj⟩ := outage_window_coverAC (q := q) (by omega) hT hlag' hb01
  have hkj := (Compose.armed_label_lt (sp := sp) (σ := 0) hT hlag'
    (by simp [SAParams.ts]; exact hT)).2
  have hβ' : (q.β : Time) ≤ 4 * (sp.k : Time) - 5 := by
    have h1 := hq.1
    have h2 : (q.β : ℤ) ≤ 4 * (sp.k : ℤ) - 5 := by omega
    exact h2
  have hmul := mul_le_mul_of_nonneg_right hβ' hΔ.le
  have hnsT : (q.noSleep : Time) = 4 * sp.k + 6 := by rw [hns]; push_cast; ring
  change sp.ts j₀ + 2 * sp.Δ ≤ b₀ at hg₁
  change b₀ < sp.ts j₀ + 6 * sp.Δ at hg₂
  change protStartAC sp q b₀ ≤ sp.ts ((j₀ : Int) - sp.k) at haj
  have hjk : sp.ts (j₀ + sp.k : Nat) = sp.ts j₀ + 4 * sp.k * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hj1 : sp.ts (j₀ + 1 : Nat) = sp.ts j₀ + 4 * sp.Δ := ts_succAC j₀
  have hjk' : sp.ts ((j₀ : Int) - sp.k) = sp.ts j₀ - 4 * sp.k * sp.Δ := by
    simp only [SAParams.ts]; ring
  refine ⟨hg₁, by rw [hj1]; linarith, by linarith, by rw [hjk]; linarith, by linarith, ?_,
    ?_, ha0, haj, hzj, hkj⟩
  · rw [hjk'] at haj
    linarith
  · rw [hjk]
    simp only [protEndAC, hnsT]
    linarith

/-! ### The package -/

open Classical in
/-- **The premise package from Tier A's class**: at a contract point `q` of the class, under the
lag `T + (4k + 6)Δ ≤ b₀`, for a protected block `P ∈ U` that is genesis or an origin within `b₀`
of a label `σ` started by `T`. -/
noncomputable def outagePremisesAC_ofClass (hrun : ACRunU wm u proposer tr H U)
    (hw : wm.width = sp.k) {q : ProtQ} (hq : ProtPointAC0 sp q) {T b₀ b₁ : Time}
    (hcl : ProtClassAC0 q T b₀ b₁ tr H U)
    (hlag : T + ((4 * sp.k + 6 : ℕ) : Time) * sp.Δ ≤ b₀) {P : Blk sp.n FGP} {σ : Nat}
    (hP : P ∈ U ∧ (P.root = sp.genesisRoot ∨ OriginWithinAC tr H P σ b₀))
    (hσT : sp.ts σ ≤ T) : OutagePremisesAC wm u proposer tr H U :=
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hT0 : 0 ≤ T := hcl.1
  have hlag' : T + (4 * sp.k + 6) * sp.Δ ≤ b₀ := by push_cast at hlag; exact hlag
  have hb0 : 0 ≤ b₀ := by
    have : (0 : Time) ≤ (4 * sp.k + 6) * sp.Δ := by positivity
    linarith
  have hnum := cover_numbersAC hq hcl hlag
  have hrl := restoredLabelAC_spec (sp := sp) ⟨_, hnum.2.2.2.1⟩
  have hsl := hq.sleepy
  have hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ b₀ → FaultBound tr H (sp.ts s + sp.Δ) :=
    fun s _ => hcl.faultBound hr hsl.1 hsl.2 (by linarith [ts_nonnegAC (sp := sp) s])
  have hfr : FrontierAC tr H U b₀ := hcl.frontier hrun hsl.1 hsl.2 hb0
  have htick : TickDuty tr H := hcl.2.2.2.2.2.1
  have htriv : TrivialFrames tr H := hcl.2.2.2.2.2.2.2.1
  have hsy : SyncUntilAC tr H U b₀ := hcl.2.2.2.1
  have hns : NoSleepOnAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁) :=
    hcl.2.2.2.2.2.2.2.2.2.1
  have hco : CohortOnAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁) :=
    hcl.2.2.2.2.2.2.2.2.2.2.1
  have haw : ∀ x ∈ awakeAtAC tr H (protStartAC sp q b₀), ∀ t, protStartAC sp q b₀ ≤ t →
      t ≤ protEndAC sp q b₁ → tr.awake x t := fun x hx t hat htz =>
    hns x hx.1 _ le_rfl (hat.trans htz) hx.2 t hat htz
  have hσ : σ + sp.k < Compose.coverLabel sp b₀ := (Compose.armed_label_lt hT0 hlag' hσT).1
  { hrun := hrun
    hw := hw
    htriv := htriv
    htick := htick
    b₀ := b₀
    b₁ := b₁
    a := protStartAC sp q b₀
    z := protEndAC sp q b₁
    P := P
    σ := σ
    j₀ := Compose.coverLabel sp b₀
    r := restoredLabelAC sp b₁
    A₀ := awakeAtAC tr H (protStartAC sp q b₀)
    W := lateWakersAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁)
    hj₀ := ⟨hnum.1, hnum.2.1⟩
    hr := hrl
    hσ := hσ
    hrk := by
      refine ⟨?_, hrl.2 _ hnum.2.2.2.1⟩
      by_contra h
      have := ts_le_tsAC (sp := sp) (show restoredLabelAC sp b₁ ≤ Compose.coverLabel sp b₀ by
        omega)
      linarith [hrl.1, hnum.2.2.2.2.1]
    hgap := hnum.2.2.1
    hb₀ := hcl.2.1
    hP := hP
    hpre := hfr
    hpreSvc := hsy
    hFB := fun s _ => hcl.faultBound hr hsl.1 hsl.2 (by linarith [ts_nonnegAC (sp := sp) s])
    hA₀ := fun _ hx => hx.1
    hW := ⟨fun _ hx => hx.1.1, Set.disjoint_left.2 fun _ h₁ h₂ => h₂.2 h₁⟩
    hcohort := hco
    hawake := fun x hx t hat htz haw => by
      by_cases hxa : tr.awake x (protStartAC sp q b₀)
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨⟨hx, t, hat, htz, haw⟩, fun h => hxa h.2⟩
    hA₀awake := haw
    hA₀join := fun x hx k hk hkz =>
      restart_le_of_awakeAC hr htick hx.1 hnum.2.2.2.2.2.2.2.1 (haw x hx) hk hkz
    ha := hnum.2.2.2.2.2.1
    hz := fun t ht _ => ht.trans hnum.2.2.2.2.2.2.1
    lockPrev := fun x hx hg _ => by
      have hj1 : 1 ≤ Compose.coverLabel sp b₀ := by omega
      have hts := ts_succAC (sp := sp) (Compose.coverLabel sp b₀ - 1)
      rw [Nat.sub_add_cancel hj1] at hts
      obtain ⟨c, ℓ, hu, L, f, hL, hPL, hl⟩ := armed_lock_prevAC hrun hw htriv htick hsy hfr hfb
        (hP.2.resolve_left hg) hg hx.1 (haw x hx) (s := Compose.coverLabel sp b₀ - 1)
        (by omega) (by omega)
        (by
          rw [show ((Compose.coverLabel sp b₀ - 1 : Nat) : Int) - sp.k + 1 =
            (Compose.coverLabel sp b₀ : Int) - sp.k by omega]
          exact hnum.2.2.2.2.2.2.2.2.1)
        (by linarith [hnum.2.2.2.2.2.2.2.2.2.1 (2 * sp.Δ) (by linarith)])
        (by linarith [hnum.1])
      exact ⟨c, ℓ, hu, prevBaseAC_iff.2 ⟨L, f, hL, hPL, hl⟩⟩
    lockCover := fun x hx hg _ => by
      have hjk : sp.ts ((Compose.coverLabel sp b₀ : Int) - sp.k) ≤
          sp.ts ((Compose.coverLabel sp b₀ : Int) - sp.k + 1) := (ts_le_iff sp).2 (by omega)
      obtain ⟨c, ℓ, hu, hfirst, hcond⟩ := armed_lock_coverAC hrun hw htriv htick hsy hfr hfb
        (hP.2.resolve_left hg) hg hx.1 (haw x hx) (s := Compose.coverLabel sp b₀)
        (by omega) (by omega) (hnum.2.2.2.2.2.2.2.2.1.trans hjk)
        (hnum.2.2.2.2.2.2.2.2.2.1 _ le_rfl) hnum.1
        (awakeAtAC tr H (protStartAC sp q b₀))
        (Hᶜ ∪ lateWakersAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁))
        Set.subset_union_left hco.two_mul_lt fun y hy j e hv hes hjt => by
          obtain ⟨hts, -⟩ := ts_le_castAC hr hy hv
          rw [hes] at hts
          have h1 := ts_le_tsAC (sp := sp)
            (show Compose.coverLabel sp b₀ - sp.k ≤ Compose.coverLabel sp b₀ + 1 by omega)
          have h2 : sp.ts ((Compose.coverLabel sp b₀ : Int) - sp.k) ≤
              sp.ts ((Compose.coverLabel sp b₀ + 1 : Nat) : Int) := (ts_le_iff sp).2 (by omega)
          obtain ⟨ℓy, hcy, -⟩ := hv
          have hay := hr.awake_of_call y hy j ℓy hcy
          by_cases hya : tr.awake y (protStartAC sp q b₀)
          · exact Or.inl ⟨hy, hya⟩
          · exact Or.inr (Or.inr ⟨⟨hy, tr.time j,
              by linarith [hnum.2.2.2.2.2.2.2.2.1],
              hjt.trans (hnum.2.2.2.2.2.2.2.2.2.1 _ le_rfl), hay⟩, fun h => hya h.2⟩)
      exact ⟨c, ℓ, hu, hfirst, fun hVA hN => coverBaseAC_iff.2 (hcond hVA hN)⟩
    PG := fun w hw c m ℓ hu hrm x hx i e hv hes => by
      have ht := update_timeAC hu
      rw [ts_succAC] at ht
      exact (vote_pooled_before_earlyAC hrun hcl.2.2.2.2.1 hw hu.1 (by linarith)
        (hrl.1.trans (by linarith [ts_le_tsAC (sp := sp) hrm])) (update_restartsAC hr hw hu)
        hx hv hes).1 }

section Projections

variable {hrun : ACRunU wm u proposer tr H U} {hw : wm.width = sp.k} {q : ProtQ}
  {hq : ProtPointAC0 sp q} {T b₀ b₁ : Time} {hcl : ProtClassAC0 q T b₀ b₁ tr H U}
  {hlag : T + ((4 * sp.k + 6 : ℕ) : Time) * sp.Δ ≤ b₀} {P : Blk sp.n FGP} {σ : Nat}
  {hP : P ∈ U ∧ (P.root = sp.genesisRoot ∨ OriginWithinAC tr H P σ b₀)} {hσT : sp.ts σ ≤ T}

@[simp] theorem outagePremisesAC_ofClass_b₀ :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).b₀ = b₀ := by rfl

@[simp] theorem outagePremisesAC_ofClass_b₁ :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).b₁ = b₁ := by rfl

@[simp] theorem outagePremisesAC_ofClass_a :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).a = protStartAC sp q b₀ := by rfl

@[simp] theorem outagePremisesAC_ofClass_z :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).z = protEndAC sp q b₁ := by rfl

@[simp] theorem outagePremisesAC_ofClass_P :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).P = P := by rfl

@[simp] theorem outagePremisesAC_ofClass_σ :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).σ = σ := by rfl

@[simp] theorem outagePremisesAC_ofClass_j₀ :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).j₀ = Compose.coverLabel sp b₀ := by
  rfl

@[simp] theorem outagePremisesAC_ofClass_r :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).r = restoredLabelAC sp b₁ := by rfl

@[simp] theorem outagePremisesAC_ofClass_A₀ :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).A₀ =
      awakeAtAC tr H (protStartAC sp q b₀) := by rfl

@[simp] theorem outagePremisesAC_ofClass_W :
    (outagePremisesAC_ofClass hrun hw hq hcl hlag hP hσT).W =
      lateWakersAC tr H (protStartAC sp q b₀) (protEndAC sp q b₁) := by rfl

end Projections

end Consensus.Goldilocks.Comparison

end
