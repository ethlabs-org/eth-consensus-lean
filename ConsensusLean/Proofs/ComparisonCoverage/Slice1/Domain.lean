module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Plan
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Point
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Hold
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the witness run

`cov1_witness`: at every point of the coverage domain whose progress requirement admits `fcap`
compromised validators (and, with positive activity, of a family with a forgeable role), a valid,
excuse-free run of the Slice 1 class with the progress premise, attaining every environment
parameter but the class's exercise (exact incident length, exact activity in both windows,
exactly `fcap` compromised, exactly `max m fcap` that cannot vote), with every finite claim active
for the point's readers.

The run: the witness point `cov1Point A Sl b₀ b₁ v₀ H` (`A` of size `fcap`, `Sl` of size
`max m fcap − fcap` asleep on the incident `[b₀, b₁)`, `b₀ = n·slotLen + 1`, `b₁ = b₀ + 2L`), the
selection and forgery plan of `exists_plan` for the first `hpre` and the first `hpost` validators of
`A`, the forgeries injected to `v₀`, and the held split's delivery filter `holdPol` for the groups
of the class (one group for `any`, so the filter serves everything). -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf Obj Msg)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema}

/-- In-group synchrony of a model run is in-group synchrony of its system run. -/
theorem groupSync_sysOf {F : Model.ProtocolFamily O} {E : Env V} (rho : Model.Run F E)
    {G : V → Bool} {b₁ : Time} (h : GroupSync rho.point rho.log G b₁) :
    GroupSync ((sysOf O F V).pt ⟨E, rho⟩) ((sysOf O F V).log ⟨E, rho⟩) G b₁ := by
  refine ⟨?_, ?_, h.txs⟩
  · rintro v m t ⟨o, rfl, hs⟩ hv hnfg hlt w hw a hta hah hwh haw
    exact (Model.sysOf_held_iff rho w o _).mpr (h.msgs v o t hs hv
      (fun h' => hnfg ((Model.sysOf_log_fgAtt rho o).mpr h')) hlt w hw a hta hah hwh haw)
  · rintro v m t ⟨o, rfl, hs⟩ hv hfg hlt w hw a hta hah hwh haw
    exact (Model.sysOf_held_iff rho w o _).mpr (h.fgAtts v o t hs hv
      ((Model.sysOf_log_fgAtt rho o).mp hfg) hlt w hw a hta hah hwh haw)

omit [DecidableEq V] in
/-- A compromised set of exactly `f` validators and a sleeper set of exactly `s`, disjoint and
avoiding a set `R` of at most two, when `f + s + 2 ≤ n`. -/
theorem exists_faulty_sleepers (R : Finset V) (hR : R.card ≤ 2) {f s : ℕ}
    (h : f + s + 2 ≤ Fintype.card V) :
    ∃ A Sl : Finset V, Disjoint A R ∧ Disjoint Sl R ∧ Disjoint A Sl ∧ A.card = f ∧
      Sl.card = s := by
  classical
  obtain ⟨B, hB, hBc⟩ := exists_faulty R hR (f := f + s) (by omega)
  obtain ⟨A, hAB, hAc⟩ := Finset.exists_subset_card_eq (show f ≤ B.card by omega)
  refine ⟨A, B \ A, Finset.disjoint_of_subset_left hAB hB,
    Finset.disjoint_of_subset_left Finset.sdiff_subset hB, Finset.disjoint_sdiff, hAc, ?_⟩
  rw [Finset.card_sdiff_of_subset hAB]
  omega

/-- The groups of a class: one group for `any`. -/
def classGroups : IncidentClass V → V → Bool
  | .any => fun _ => true
  | .split G => G
  | .splitHeld G => G

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- The class premises of a filtered run: the incident network of the class's delivery
guarantee and its hold. -/
theorem holdRun_class {F : Model.ProtocolFamily O} {E : Env V} {rho : Model.Run F E}
    {b₀ b₁ : Time} {inj : Time → V → List (protoOf F E).Object} (a : IncidentClass V)
    (h : HoldPremises rho (classGroups a) b₀ b₁ inj) :
    IncidentNet (sysOf O F V) a.async b₀ b₁ ⟨E, holdRun rho (classGroups a) b₀ b₁ inj⟩ ∧
      HoldOn F a b₀ b₁ ⟨E, holdRun rho (classGroups a) b₀ b₁ inj⟩ := by
  refine ⟨⟨⟨(Model.sysOf_delivers_iff _ _ _ _).mpr (hold_syncUntil h),
    (Model.sysOf_delivers_iff _ _ _ _).mpr (hold_psync h)⟩, ?_⟩, ?_⟩
  · cases a with
    | any => trivial
    | split G => exact groupSync_sysOf _ (hold_groupSync h)
    | splitHeld G => exact groupSync_sysOf _ (hold_groupSync h)
  · cases a with
    | any => trivial
    | split G => trivial
    | splitHeld G => exact hold_contentOriginHold h

/-- The parts of `Attains` other than the class's exercise. -/
def AttainsCore {F : Model.ProtocolFamily O} (fl : RoleFloor F V) (q : HealQ V) (b₀ b₁ : Time)
    (r : (sysOf O F V).Run) : Prop :=
  b₁ - b₀ = (q.L : Time) * ((sysOf O F V).pt r).env.ΔAC ∧
    activity F fl r 0 (max b₁ 0) = q.hpre ∧
    activity F fl r (max b₁ 0) (((sysOf O F V).pt r).horizon + 1) = q.hpost ∧
    ((sysOf O F V).pt r).faultCount ((sysOf O F V).pt r).horizon = q.fcap ∧
    (notAwakeHonest (sysOf O F V) b₀ b₁ r).card = max q.m q.fcap

/-- The core of `Attains` with the class's exercise is `Attains`. -/
theorem attains_of_core {F : Model.ProtocolFamily O} {fl : RoleFloor F V} {q : HealQ V}
    {b₀ b₁ : Time} {r : (sysOf O F V).Run} (h : AttainsCore fl q b₀ b₁ r)
    (he : Exercised (sysOf O F V) q.a.async b₀ b₁ r) : Attains F fl q b₀ b₁ r :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, he⟩

/-- **The Slice 1 witness run** at a point of the coverage domain. -/
theorem cov1_witness (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx)
    (q : HealQ V) (hq : q.DomainFeasible) (hadm : AdmitsFaults (K.progress cap i) q.fcap)
    (hforge : 0 < q.hpre ∨ 0 < q.hpost → ForgeableRole F) (hsq hlq latq : WithTop ℕ) :
    ∃ (r : (Sys F V).Run) (b₀ b₁ : Time), (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
      HealClass (compiled F) K (shapeRoleFloor F V) q b₀ b₁ r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
        ((Sys F V).pt r).horizon r ∧
      AttainsCore (shapeRoleFloor F V) q b₀ b₁ r ∧
      (∀ c : ℕ, hsq = c → SafeActive (q.readerDur (Sys F V) r) (healAt (Sys F V) b₁ c r)
        ((Sys F V).pt r)) ∧
      (∀ c d : ℕ, hlq = c → latq = d → ((Sys F V).pt r).TxLiveActive (q.readerDur (Sys F V) r)
        (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  classical
  obtain ⟨hpre_le, hpost_le, hn, hL0, hLs, -⟩ := hq
  have h2 : 2 ≤ Fintype.card V := by omega
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let v₀ := key ⟨0, by omega⟩
  let v₁ := key ⟨1, by omega⟩
  have h10 : v₁ ≠ v₀ := fun h => Nat.one_ne_zero (congrArg Fin.val (key.injective h))
  obtain ⟨A, Sl, hAR, hSR, hASl, hAc, hSc⟩ := exists_faulty_sleepers {v₀, v₁} Finset.card_le_two
    (f := q.fcap) (s := max q.m q.fcap - q.fcap) (by omega)
  have hv₀A : v₀ ∉ A := Finset.disjoint_right.mp hAR (by simp)
  have hv₁A : v₁ ∉ A := Finset.disjoint_right.mp hAR (by simp)
  have hv₀S : v₀ ∉ Sl := Finset.disjoint_right.mp hSR (by simp)
  have hv₁S : v₁ ∉ Sl := Finset.disjoint_right.mp hSR (by simp)
  let Apre := A.toList.take q.hpre
  let Apost := A.toList.take q.hpost
  have hApre : Apre.length = q.hpre := by simp [Apre, hAc, hpre_le]
  have hApost : Apost.length = q.hpost := by simp [Apost, hAc, hpost_le]
  have hsubA : ∀ v, v ∈ Apre ∨ v ∈ Apost → v ∈ A := fun v hv => by
    rcases hv with hv | hv <;> exact Finset.mem_toList.mp (List.mem_of_mem_take hv)
  let SL : Time := (F ⟨Fintype.card V, 2, two_pos, 2, two_pos⟩).skel.grid.slotLen
  have hSL : 0 < SL := (F _).skel.grid.slotLen_pos
  let b₀ : Time := (Fintype.card V : Time) * SL + 1
  let b₁ : Time := b₀ + (q.L : Time) * 2
  have hb₀ : 0 ≤ b₀ := by positivity
  have hb₀₁ : b₀ ≤ b₁ := le_add_of_nonneg_right (by positivity)
  have hb₁ : 0 ≤ b₁ := le_trans hb₀ hb₀₁
  let Hc : Time := ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
  have hHc : 0 ≤ Hc := by positivity
  let H : Time := b₁ + Hc + 4 + ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL
  have hHf : ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL ≤ H := by
    simp only [H]; linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hHf
  let p := cov1Point A Sl b₀ b₁ v₀ H
  let E : Env V := p.env
  have hforge' : (Apre = [] ∧ Apost = []) ∨ ForgeableRole F := by
    by_cases hz : q.hpre = 0 ∧ q.hpost = 0
    · left
      exact ⟨List.length_eq_zero_iff.mp (hApre.trans hz.1),
        List.length_eq_zero_iff.mp (hApost.trans hz.2)⟩
    · right
      exact hforge (by omega)
  have hSLE : (F (pubOf E)).skel.grid.slotLen = SL := by
    change (F (pubOf (cov1Point A Sl b₀ b₁ v₀ H).env)).skel.grid.slotLen = SL
    rw [cov1Point_pubOf]
  obtain ⟨sel, fs, hP⟩ := exists_plan F E key Apre Apost (b₁ := b₁) (H := H)
    (by rw [hSLE]; simp only [b₁, b₀]; linarith) (by rw [hSLE]; exact hHf) hforge'
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) E).Item
  let base : Model.Run (compiled F) E := Model.Run.mk p.faultyAt p.faultyAt_mono p.horizon [] key
    sel p.submit (Model.eagerRelay E p.faultyAt p.submit) hash
  have hfA : ∀ t, base.faultyAt t = A := fun t => cov1Point_faultyAt A Sl b₀ b₁ v₀ H t
  have hbH : base.horizon = H := cov1Point_horizon A Sl b₀ b₁ v₀ H
  have hbH0 : 0 ≤ base.horizon := hbH ▸ hH0
  let G := classGroups q.a
  let W := holdRun base G b₀ b₁ (forgeInj v₀ fs)
  have hkeyA : ∀ x ∈ fs, key x.key ∈ A := fun x hx => hsubA _ (hP.keys x hx)
  have hinjF : ∀ t v o, o ∈ forgeInj v₀ fs t v → ∀ d, Obj.Contains o d → ∀ u,
      base.signerOf d = some u → u ∈ base.faultyAt t := by
    intro t v o ho d hd u hu
    obtain ⟨-, x, hx, -, rfl⟩ := mem_forgeInj.mp ho
    rcases parts_forged hd with rfl | hn
    · simp only [Model.Run.signerOf, Obj.signer?, forged_auth, Option.map_some,
        Option.some.injEq] at hu
      subst hu
      rw [hfA]
      exact hkeyA x hx
    · simp [Model.Run.signerOf, Obj.signer?, hn] at hu
  have hinjS : ∀ t v o, o ∈ forgeInj v₀ fs t v → ∀ d, Obj.Contains o d → ∀ k r,
      d.auth = .signed k r → k ∈ base.sel r := by
    intro t v o ho d hd k r hkr
    obtain ⟨-, x, hx, -, rfl⟩ := mem_forgeInj.mp ho
    rcases parts_forged hd with rfl | hn
    · rw [forged_auth] at hkr
      injection hkr with h1 h2
      subst h1 h2
      exact hP.cred x hx
    · rw [hn] at hkr; cases hkr
  have hvalid : W.ExecutionValid :=
    base.injectEvents_valid _ _ _ hbH0 hP.admits (fun _ => le_rfl) hinjF hinjS
  have hHP : HoldPremises base G b₀ b₁ (forgeInj v₀ fs) :=
    ⟨hbH0, hP.admits,
      by change 1 < (cov1Point A Sl b₀ b₁ v₀ H).env.ΔAC; rw [cov1Point_ΔAC]; exact one_lt_two,
      by change (cov1Point A Sl b₀ b₁ v₀ H).env.ΔFG = (cov1Point A Sl b₀ b₁ v₀ H).env.ΔAC
         rw [cov1Point_ΔAC, cov1Point_ΔFG],
      Model.eagerRelay_txs W
        (by simp only [W, Model.Run.withEvents_eq]; rfl), fun t => by rw [hfA, hfA], hinjF, hinjS⟩
  have hFP : ForgeryPremises base (shapeRoleFloor F V E) v₀ fs (holdPol base G b₀ b₁) :=
    ⟨hvalid, fun t => by rw [hfA, hfA], fun x hx => by rw [hfA]; exact hkeyA x hx,
      by rw [hfA]; exact hv₀A, fun t => cov1Point_awake_of_not_sleeper hv₀S t,
      fun x hx => by rw [hbH]; exact hP.time_range x hx, hP.floor_le, hP.unique⟩
  have hpt : (Sys F V).pt ⟨E, W⟩ = p := by
    change W.point = p
    simp only [W, holdRun, Model.Run.injectRun, Model.Run.withEvents_point]
    rfl
  have hact : ∀ a b, activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ a b =
      ((fs.filter fun x => decide (a ≤ x.time ∧ x.time < b)).map
        fun x => key x.key).toFinset.card := fun a b => by
    change (activeFaulty W (shapeRoleFloor F V E) a b).card = _
    rw [activeFaulty_of_forgeries hFP]
  have hnodup : ∀ k, (A.toList.take k).Nodup := fun k => (Finset.nodup_toList A).sublist
    (List.take_sublist _ _)
  have hactpre : activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ 0 (max b₁ 0) = q.hpre := by
    rw [hact, max_eq_left hb₁, hP.pre, List.toFinset_card_of_nodup (hnodup _), hApre]
  have hactpost : activity (compiled F) (shapeRoleFloor F V) ⟨E, W⟩ (max b₁ 0)
      (((Sys F V).pt ⟨E, W⟩).horizon + 1) = q.hpost := by
    rw [hact, max_eq_left hb₁, hpt, cov1Point_horizon, hP.post,
      List.toFinset_card_of_nodup (hnodup _), hApost]
  have hnah : (notAwakeHonest (Sys F V) b₀ b₁ ⟨E, W⟩).card = max q.m q.fcap := by
    by_cases hs0 : max q.m q.fcap - q.fcap = 0
    · obtain rfl : Sl = ∅ := Finset.card_eq_zero.mp (hSc.trans hs0)
      rw [cov1Point_notAwakeHonest_empty hpt, hAc]
      omega
    · have hL : 1 ≤ q.L := by
        by_contra h
        have := hL0 (by omega)
        omega
      rw [cov1Point_notAwakeHonest hpt hb₀ (by simp only [b₁]; linarith) hASl,
        hAc, hSc]
      omega
  have hready : (Sys F V).ready K b₁ ⟨E, W⟩ = b₁ + (Sys F V).cDur K ⟨E, W⟩ + 1 := by
    simp only [System.ready, max_eq_left hb₁]
  have hheal : ∀ c : ℕ, healAt (Sys F V) b₁ c ⟨E, W⟩ = b₁ + (c : Time) * 2 := fun c => by
    change max b₁ 0 + (c : Time) * ((Sys F V).pt ⟨E, W⟩).env.ΔAC = _
    rw [hpt, cov1Point_ΔAC, max_eq_left hb₁]
  have hx : ∀ y : WithTop ℕ, (0 : Time) ≤ ((y.untopD 0 : ℕ) : Time) := fun _ => by positivity
  have hcoe : ∀ c : ℕ, WithTop.untopD 0 (c : WithTop ℕ) = c := fun _ => rfl
  have hcl := holdRun_class (rho := base) (b₀ := b₀) (b₁ := b₁) (inj := forgeInj v₀ fs) q.a hHP
  refine ⟨⟨E, W⟩, b₀, b₁, hvalid,
    by change ¬ W.HashCollision
       simp only [W, Model.Run.withEvents_eq]
       exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj),
    ⟨hcl.1, hcl.2, hb₀₁, ?_, hactpre.le, hactpost.le, ?_, ?_, ?_, ?_⟩, ?_,
    ⟨?_, hactpre, hactpost, ?_, hnah⟩, ?_, ?_⟩
  · rw [hpt, cov1Point_ΔAC]; simp only [b₁]; linarith
  · rw [hnah]; exact le_max_left _ _
  · rw [hpt, cov1Point_faultCount, hAc]
  · intro v t h1 h2 h3
    rw [hpt] at h2 h3 ⊢
    exact cov1Point_honestAwakeAfter v t h1 h2 h3
  · rw [hpt, cov1Point_ΔAC, cov1Point_ΔFG]
    have : (1 : Time) ≤ (K.params.fgDelay : Time) := by exact_mod_cast hfg
    linarith
  · rw [hready]
    change shapeHolds F (K.progress cap i) ((Sys F V).cDur K ⟨E, W⟩) _ _
      ((Sys F V).pt ⟨E, W⟩) (W.key, W.sel)
    rw [show W.key = key from Model.Run.withEvents_key _ _,
      show W.sel = sel from Model.Run.withEvents_sel _ _]
    exact cov1Point_holds F K key h2 hpt sel hP.proposer hf cap i (hAc ▸ hadm) hv₁A hv₁S le_rfl _
  · rw [hpt, cov1Point_ΔAC]; simp only [b₁]; ring
  · rw [hpt, cov1Point_faultCount, hAc]
  · intro c hc
    rw [hheal, hpt]
    refine cov1Point_safeActive hv₀A hv₀S hv₁A hv₁S h10.symm _ _ ?_
    have : (c : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 ≤ ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hcoe]
      push_cast
      linarith [hx hlq, hx latq]
    have : (0 : Time) ≤ ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL := by positivity
    change b₁ + (c : Time) * 2 + 2 ≤ b₁ + Hc + 4 + ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL
    linarith
  · intro c d hc hd
    rw [hheal, hpt, cov1Point_ΔAC]
    refine cov1Point_txLiveActive hv₀A hv₀S hv₁A hv₁S h10 _ _ _ ?_
    have : (c : Time) * 2 + (d : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 + (d : Time) * 2 ≤
        ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hd, hcoe, hcoe]
      push_cast
      linarith [hx hsq]
    rw [max_eq_right (by positivity)]
    have : (0 : Time) ≤ ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL := by positivity
    change b₁ + (c : Time) * 2 + 2 + (d : Time) * 2 ≤
      b₁ + Hc + 4 + ((b₁.toNat + Fintype.card V : ℕ) : Time) * SL
    linarith

end Consensus.Comparison

end
