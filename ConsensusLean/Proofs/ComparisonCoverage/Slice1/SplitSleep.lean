module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.SplitCommon
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Hold1
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Sleep
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.ForgeryAt
public import ConsensusLean.Lemmas.Model.Canonical.Twins
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the exercised split with sleepers

`cov1_split_witness_sleepers`: at a point of the coverage domain with a split class and sleepers
(`fcap < m`), a Slice 1 witness that exercises the class.

The sleepers must be asleep exactly on the incident `[t₀, b₁)`, whose start is an honest first
release found on a reference run, so the witness lives in another environment than the reference.
Both runs are held split's runs with a one-step delivery delay (`holdRun1`), on twin bases
(`Model.Run.Twins`: the environments differ only in who is awake):
* the reference `R`: everyone asleep before `T₁ = n·slotLen + 1` and awake from `T₁`, no
  forgery, no hold (`sleepPoint A ∅`). Cut at `H₀`, it is healthy from `T₁`; healthy liveness gives
  an honest proposal `m` of `v`, first released at `t₀ ≥ T₁`;
* the witness `W`: the sleepers `Sl` (avoiding `v` and an honest node `w` of the other group) also
  asleep on `[t₀, b₁)`, `b₁ = t₀ + 2L`; the forgeries planned before `T₁` injected to `v` at
  `t₀ + 1`, those planned from `T₁` on shifted past `b₁`; the hold from `t₀`.
* `W` has the stages of `R` before `t₀` (`Model.Run.injectStages_twins`). At `t₀` the due batch
  holds only releases from before `t₀`, which both filters serve, so `v` has the same events at
  `t₀` in both runs and `W` releases `m` at `t₀` (`Model.Run.releases_twins_layer`). The
  content-origin hold keeps `m` from `w` until `b₁`. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf Obj Msg)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema}

/-- The class premises of the delayed filtered run of a split class. -/
private theorem holdRun1_class {F : Model.ProtocolFamily O} {E : Env V} {rho : Model.Run F E}
    {b₀ b₁ : Time} {inj : Time → V → List (protoOf F E).Object} {G : V → Bool}
    (a : IncidentClass V) (ha : a = .split G ∨ a = .splitHeld G)
    (h : HoldPremises1 rho G b₀ b₁ inj) :
    IncidentNet (sysOf O F V) a.async b₀ b₁ ⟨E, holdRun1 rho G b₀ b₁ inj⟩ ∧
      HoldOn F a b₀ b₁ ⟨E, holdRun1 rho G b₀ b₁ inj⟩ := by
  rcases ha with rfl | rfl
  · exact ⟨⟨⟨(Model.sysOf_delivers_iff _ _ _ _).mpr (hold1_syncUntil h),
      (Model.sysOf_delivers_iff _ _ _ _).mpr (hold1_psync h)⟩,
      groupSync_sysOf _ (hold1_groupSync h)⟩, trivial⟩
  · exact ⟨⟨⟨(Model.sysOf_delivers_iff _ _ _ _).mpr (hold1_syncUntil h),
      (Model.sysOf_delivers_iff _ _ _ _).mpr (hold1_psync h)⟩,
      groupSync_sysOf _ (hold1_groupSync h)⟩, hold1_contentOriginHold h⟩

/-- The eager relay of two environments agrees at a recipient and time where they agree, when
they agree at every submission. -/
private theorem eagerRelay_congr {E E' : Env V} {A : Finset V} {subm : V → Time → List Tx}
    (hsub : ∀ x τ, subm x τ ≠ [] → E'.awake x τ = E.awake x τ) {w : V} {k : Time}
    (hw : E'.awake w k = E.awake w k) :
    Model.eagerRelay E' (fun _ => A) subm w k = Model.eagerRelay E (fun _ => A) subm w k := by
  rw [Model.eagerRelay_apply, Model.eagerRelay_apply]
  have hf : ∀ x τ, (if x ∉ A ∧ E'.awake x τ = true then subm x τ else []) =
      (if x ∉ A ∧ E.awake x τ = true then subm x τ else []) := by
    intro x τ
    by_cases h : subm x τ = []
    · simp [h]
    · simp only [hsub x τ h]
  simp only [hw, hf]

/-- A due object was released at a due event. -/
private theorem releases_of_mem_duePool {F : Model.ProtocolFamily O} {E : Env V}
    (σ : Model.Run F E) (delay : Model.Event V (protoOf F E).Object → Time)
    (es : List (Model.Event V (protoOf F E).Object)) (t : Time) {o : (protoOf F E).Object}
    (ho : o ∈ σ.duePool delay es t) :
    ∃ u τ, (∃ e ∈ es, e.time = τ ∧ τ + delay e ≤ t) ∧ (σ.withEvents es).releases u o τ := by
  obtain ⟨j, e, hje, hdue, hoj⟩ := (σ.mem_duePool delay es t o).mp ho
  cases e with
  | tick u τ =>
    exact ⟨u, τ, ⟨_, List.mem_of_getElem? hje, rfl, hdue⟩, j,
      Or.inl (by rw [Model.Run.withEvents_events]; exact hje), hoj⟩
  | deliver u p τ =>
    exact ⟨u, τ, ⟨_, List.mem_of_getElem? hje, rfl, hdue⟩, j,
      Or.inr ⟨p, by rw [Model.Run.withEvents_events]; exact hje⟩, hoj⟩
  | restart u τ =>
    simp [Model.Run.releasesAt, Model.Run.withEvents_events, hje] at hoj

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- **The exercised Slice 1 witness with sleepers** (`fcap < m`) at a point of the coverage domain
with a split class. -/
theorem cov1_split_witness_sleepers (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hcl : ShapeClaimsAt F K V) (hf : ProgressFits K F) (hnfg : ProposalsNotFGAtt F)
    (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx) (g : O.Id)
    (hg : O.output cap = some g) (q : HealQ V) (hq : q.DomainFeasible) (hsplit : q.a.IsSplit)
    (hadm : AdmitsFaults (K.progress cap i) q.fcap)
    (hforge : 0 < q.hpre ∨ 0 < q.hpost → ForgeableRole F)
    (hβ : (q.fcap : ℚ) < K.params.β * Fintype.card V) (hm : q.fcap < q.m)
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
  have hmax : max q.m q.fcap = q.m := max_eq_left hm.le
  have h2 : 2 ≤ Fintype.card V := by omega
  /- The groups and the two honest validators `v₁` (key `1`) and `v₀` (the other group). -/
  let G := classGroups q.a
  have hGT : (∃ v, G v = true) ∧ ∃ v, G v = false := classGroups_two hsplit hTG
  have ha : q.a = .split G ∨ q.a = .splitHeld G := by
    rcases hqa : q.a with _ | G' | G'
    · rw [hqa] at hsplit; exact hsplit.elim
    · left; congr 1; change G' = classGroups q.a; rw [hqa, classGroups_split]
    · right; congr 1; change G' = classGroups q.a; rw [hqa, classGroups_splitHeld]
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
  let Ts : Time := H₀ + (q.L : Time) * 2 + 1
  let H : Time := Ts + Hc + Hp + H₀ + (q.L : Time) * 2 + (q.catchUp : Time) * 2 + 4
  have hx : ∀ y : WithTop ℕ, (0 : Time) ≤ ((y.untopD 0 : ℕ) : Time) := fun _ => by positivity
  have hcoe : ∀ c : ℕ, WithTop.untopD 0 (c : WithTop ℕ) = c := fun _ => rfl
  have hHc : 0 ≤ Hc := by positivity
  have hHp : 0 ≤ Hp := by positivity
  have htR : T₁ + 1 ≤ tR := by
    have : (0 : Time) ≤ ((K.params.heal cap i + K.params.catchUp : ℕ) : Time) * 2 := by
      positivity
    simp only [tR]; linarith
  have hH₀ : tR ≤ H₀ := le_add_of_nonneg_right (by positivity)
  have hcu : (0 : Time) ≤ (q.catchUp : Time) * 2 := by positivity
  /- The reference environment and base run. -/
  let subm : V → Time → List Tx := fun v t => if v = v₀ ∧ t = Ts then [42] else []
  let aR : V → Time → Bool := fun v t => decide (T₁ ≤ t) && sleepAwake (∅ : Finset V) T₁ T₁ v t
  let ER : Env V := ⟨2, two_pos, 2, two_pos, aR⟩
  have hawR : ∀ v t, ER.awake v t = true ↔ T₁ ≤ t := fun v t => by
    change (decide (T₁ ≤ t) && sleepAwake (∅ : Finset V) T₁ T₁ v t) = true ↔ _
    rw [Bool.and_eq_true, decide_eq_true_iff, sleepAwake_eq_true]
    simp
  have hforge' : (Apre = [] ∧ Apost = []) ∨ ForgeableRole F := by
    by_cases hz : q.hpre = 0 ∧ q.hpost = 0
    · left
      exact ⟨List.length_eq_zero_iff.mp (hApre.trans hz.1),
        List.length_eq_zero_iff.mp (hApost.trans hz.2)⟩
    · right
      exact hforge (by omega)
  obtain ⟨sel, fs, hP⟩ := exists_plan F ER key Apre Apost (b₁ := T₁) (H := Hp)
    (by change (Fintype.card V : Time) * SL < T₁; simp only [T₁]; linarith) le_rfl hforge'
  have hT₁Hp : T₁ ≤ Hp := by
    have h1 : (T₁.toNat : Time) = T₁ := Int.toNat_of_nonneg hT₁.le
    have h3 : (1 : Time) ≤ SL := hSL
    have h4 : T₁ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) := by
      push_cast; rw [h1]; linarith [show (0 : Time) ≤ (Fintype.card V : Time) by positivity]
    calc T₁ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) := h4
      _ ≤ ((T₁.toNat + Fintype.card V : ℕ) : Time) * SL :=
        le_mul_of_one_le_right (by positivity) h3
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) ER).Item
  have hH0 : 0 ≤ H := by
    have : (0 : Time) ≤ tR := by linarith
    simp only [H, Ts]; linarith
  let baseR : Model.Run (compiled F) ER := Model.Run.mk (fun _ => A) monotone_const H [] key sel
    subm (Model.eagerRelay ER (fun _ => A) subm) hash
  have hbH0 : 0 ≤ baseR.horizon := hH0
  let injR : Time → V → List (protoOf (compiled F) ER).Object := fun _ _ => []
  let polR := holdPol baseR G T₁ T₁
  let R := holdRun1 baseR G T₁ T₁ injR
  have hHPR : HoldPremises1 baseR G T₁ T₁ injR :=
    ⟨hbH0, hP.admits, by change (1 : Time) < 2; norm_num, rfl,
      Model.eagerRelay_txs (holdRun1 baseR G T₁ T₁ injR)
        (by simp only [Model.Run.withEvents_eq]; rfl), fun _ => rfl,
      fun _ _ _ ho => absurd ho List.not_mem_nil, fun _ _ _ ho => absurd ho List.not_mem_nil⟩
  have hvR : R.ExecutionValid := hold1_valid hHPR
  /- The reference cut `R'` at `H₀`: healthy from `T₁`. -/
  obtain ⟨ys, hsplitR, hys⟩ := Model.Run.truncate_split hvR.sorted H₀
  let R' : Model.Run (compiled F) ER := Model.Run.mk baseR.faultyAt baseR.faultyAt_mono H₀
    ((baseR.injectEvents (fun _ => 1) injR polR).filter (fun e => decide (e.time ≤ H₀))) key sel
    baseR.submit baseR.relay hash
  have hR' : R.truncate H₀ = R' := by
    change (baseR.withEvents (baseR.injectEvents (fun _ => 1) injR polR)).truncate H₀ = R'
    rw [Model.Run.truncate_eq, Model.Run.withEvents_eq]
  have hH₀0 : 0 ≤ H₀ := by linarith
  have hH₀H : H₀ ≤ H := by simp only [H, Ts]; linarith
  have hRhor : H₀ ≤ R.horizon := by
    change H₀ ≤ (baseR.withEvents _).horizon
    rw [Model.Run.withEvents_horizon]
    exact hH₀H
  have hvR' : R'.ExecutionValid := hR' ▸ Model.Run.truncate_valid hvR hH₀0 hRhor
  have hrelR' : ∀ {u o t}, R'.releases u o t → R.releases u o t := by
    intro u o t hr
    have ht : t ≤ H₀ := by
      obtain ⟨j, hj, -⟩ := hr
      obtain ⟨e, he, -, het⟩ := hj.exists_event
      exact het ▸ (hvR'.in_horizon e (List.mem_of_getElem? he)).2
    rw [← hR'] at hr
    exact (Model.Run.truncate_releases_iff hsplitR hys ht).mp hr
  have hptR' : R'.point = sleepPoint A ∅ T₁ T₁ T₁ v₀ Ts H₀ :=
    (sleepPoint_eq A ∅ T₁ T₁ T₁ v₀ Ts H₀).symm
  have hcDur : (Sys F V).cDur K ⟨ER, R'⟩ = (K.params.catchUp : Time) * 2 := rfl
  have hpsR : ((Sys F V).log ⟨ER, R'⟩).PSync ((Sys F V).pt ⟨ER, R'⟩) T₁ := by
    obtain ⟨-, -, hag, -⟩ := Model.Run.truncate_prefix hvR H₀
    rw [hR'] at hag
    have h1 := (Model.sysOf_delivers_iff R _ _ _).mpr (hold1_psync hHPR)
    have h2 := h1.prefix hag (b := H₀) hRhor
      (fun a => by
        have := le_max_left a T₁
        change a ≤ max a T₁ + 2 - 1
        linarith)
      (fun a => by
        have := le_max_left a T₁
        change a ≤ max a T₁ + 2 - 1
        linarith)
    have h3 := h2.reindex (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (cut' := H₀)
      hRhor
    simp only [R, Model.sysOf_point, holdRun1, Model.Run.injectRun, Model.Run.withEvents_point]
      at h3
    exact h3
  have hheal : (Sys F V).Healthy K T₁ ⟨ER, R'⟩ := by
    refine ⟨hpsR, ?_, ?_⟩
    · change R'.point.HealthyOn K.params.β T₁ R'.point.horizon
      rw [hptR']
      refine ⟨?_, fun v t ht _ _ => sleepPoint_awake (Finset.notMem_empty v)
        (le_trans (le_max_left _ _) ht)⟩
      rw [sleepPoint_faultCount, hAc]
      exact hβ
    · change (2 : Time) ≤ (K.params.fgDelay : Time) * 2
      have : (1 : Time) ≤ K.params.fgDelay := by exact_mod_cast hfg
      linarith
  have hprogR' : (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K T₁ ⟨ER, R'⟩)
      ((Sys F V).pt ⟨ER, R'⟩).horizon ⟨ER, R'⟩ := by
    change shapeHolds F (K.progress cap i) ((Sys F V).cDur K ⟨ER, R'⟩) _ _ R'.point (key, sel)
    refine sleepPoint_holds F K key h2 hptR' sel hP.proposer hf cap i hadmA hv₁A le_rfl ?_ _
    change T₁ + _ + 1 ≤ max T₁ 0 + (Sys F V).cDur K ⟨ER, R'⟩ + 1
    rw [max_eq_left hT₁.le]
  /- Healthy liveness gives an honest proposal `m` of `v`. -/
  have hlive : ProposalLiveReady R' ((Sys F V).cDur K ⟨ER, R'⟩) g
      ((Sys F V).heal K cap i T₁ ⟨ER, R'⟩) (K.params.latency cap i) := by
    rcases hcl.healthyLive cap g hg i T₁ ⟨ER, R'⟩ hvR' ⟨hheal, hprogR'⟩ with h | h
    · exact h
    · exact absurd h
        (Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj))
  obtain ⟨τ, k, hdr, hτt, -, ⟨hhon, rl, cs, hrole, hrel⟩, -⟩ := hlive tR
    (by
      change max T₁ 0 + (K.params.heal cap i : Time) * 2 ≤ tR
      rw [max_eq_left hT₁.le]
      have : (0 : Time) ≤ (K.params.catchUp : Time) * 2 := by positivity
      simp only [tR]; push_cast; linarith)
    (by change tR + (K.params.latency cap i : Time) * 2 ≤ H₀; exact le_rfl)
    ⟨v₁, by
      rw [hptR', hcDur]
      refine sleepPoint_ready hv₁A (Finset.notMem_empty _) ?_
      have : (0 : Time) ≤ (K.params.latency cap i : Time) * 2 := by positivity
      have : (0 : Time) ≤ (K.params.heal cap i : Time) * 2 := by positivity
      change T₁ + (K.params.catchUp : Time) * 2 + 1 ≤ tR + (K.params.latency cap i : Time) * 2
      simp only [tR]; push_cast; linarith⟩
  let v : V := key k
  have hvA : v ∉ A := hhon
  let m : (protoOf (compiled F) ER).Object := Model.Obj.mk (.signed k rl) (.item hdr) cs
  have hmfg : ¬ (protoOf (compiled F) ER).isFGAtt m := hnfg (pubOf ER) k rl hdr cs hrole
  have hτR : R.releases v m τ := hrelR' hrel
  have hTR : ∀ v t, ER.awake v t = true → T₁ ≤ t := fun v t h => (hawR v t).mp h
  have hτ0 : 0 ≤ τ :=
    le_trans hT₁.le (le_of_inject_releases baseR hTR (fun _ => 1) injR polR hτR)
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
    have ht0 : 0 ≤ t' :=
      le_trans hT₁.le (le_of_inject_releases baseR hTR (fun _ => 1) injR polR hr)
    exact Nat.find_min hex ((Int.toNat_lt ht0).mpr ht') (by rwa [Int.toNat_of_nonneg ht0])
  have ht₀τ : t₀ ≤ τ := by
    have h1 : n₀ ≤ τ.toNat := Nat.find_min' hex (by rwa [Int.toNat_of_nonneg hτ0])
    have h2 : (0 : Int) ≤ τ := hτ0
    change (n₀ : Int) ≤ τ
    omega
  have hT₁t₀ : T₁ ≤ t₀ := le_of_inject_releases baseR hTR (fun _ => 1) injR polR hrel₀
  /- The receiver `w` in the other group, and the sleepers `Sl`, avoiding `v` and `w`. -/
  obtain ⟨w, hwG, hwA⟩ : ∃ w, G w ≠ G v ∧ w ∉ A := by
    by_cases h : G v₀ = G v
    · exact ⟨v₁, fun h' => hv₀G (h.trans h'.symm), hv₁A⟩
    · exact ⟨v₀, h, hv₀A⟩
  have hvw : v ≠ w := fun h => hwG (h ▸ rfl)
  obtain ⟨Sl, hSlsub, hSlc⟩ : ∃ Sl ⊆ Finset.univ \ (A ∪ {v, w}), Sl.card = q.m - q.fcap := by
    refine Finset.exists_subset_card_eq ?_
    have h1 := Finset.card_le_card_sdiff_add_card (s := Finset.univ) (t := A ∪ {v, w})
    have h3 : (A ∪ {v, w}).card ≤ A.card + 2 :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_two _)
    rw [Finset.card_univ] at h1
    omega
  have hvS : v ∉ Sl := fun h => (Finset.mem_sdiff.mp (hSlsub h)).2 (by simp)
  have hwS : w ∉ Sl := fun h => (Finset.mem_sdiff.mp (hSlsub h)).2 (by simp)
  have hASl : Disjoint A Sl := Finset.disjoint_right.mpr fun x hx hxA =>
    (Finset.mem_sdiff.mp (hSlsub hx)).2 (Finset.mem_union_left _ hxA)
  /- The witness environment and base run, twins of the reference's. -/
  let b₁ : Time := t₀ + (q.L : Time) * 2
  have hb₀₁ : t₀ ≤ b₁ := by simp only [b₁]; linarith
  have ht₀b₁ : t₀ + 2 ≤ b₁ := by simp only [b₁]; linarith
  have hb₁ : 0 ≤ b₁ := by linarith
  have hb₁H₀ : b₁ ≤ H₀ + (q.L : Time) * 2 := by simp only [b₁]; linarith
  let aW : V → Time → Bool := fun x t => decide (T₁ ≤ t) && sleepAwake Sl t₀ b₁ x t
  let EW : Env V := ⟨2, two_pos, 2, two_pos, aW⟩
  have hagree : ∀ x t, ¬ (x ∈ Sl ∧ t₀ ≤ t ∧ t < b₁) → aW x t = aR x t := by
    intro x t h
    change (decide (T₁ ≤ t) && sleepAwake Sl t₀ b₁ x t) =
      (decide (T₁ ≤ t) && sleepAwake (∅ : Finset V) T₁ T₁ x t)
    rw [sleepAwake_eq_true.mpr h, sleepAwake_eq_true.mpr (by simp)]
  let baseW : Model.Run (compiled F) EW := Model.Run.mk (fun _ => A) monotone_const H [] key sel
    subm (Model.eagerRelay EW (fun _ => A) subm) hash
  have tw : Model.Run.Twins baseR baseW := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsubAw : ∀ x τ, subm x τ ≠ [] → EW.awake x τ = ER.awake x τ := by
    intro x τ h
    have hx : x = v₀ ∧ τ = Ts := by
      by_contra hc
      exact h (by simp only [subm, hc, ↓reduceIte])
    refine hagree x τ fun hc => ?_
    have := hc.2.2
    rw [hx.2] at this
    simp only [b₁, Ts] at this
    linarith
  have hrelay : ∀ x t, aW x t = aR x t → baseW.relay x t = baseR.relay x t :=
    fun x t h => eagerRelay_congr hsubAw h
  have hinbox : ∀ x t, aW x t = aR x t → baseW.inbox x t = baseR.inbox x t := fun x t h => by
    change subm x t ++ baseW.relay x t = subm x t ++ baseR.relay x t
    rw [hrelay x t h]
  have hTA : ∀ x t, (t < t₀ ∨ x ∉ Sl) → Model.Run.TickAgrees baseR baseW (.tick x t) := by
    intro x t hxt u τ he
    cases he
    have hag : ∀ k, k ≤ t → aW x k = aR x k := fun k hk => hagree x k fun hc => by
      rcases hxt with h | h
      · linarith [hc.2.1]
      · exact h hc.1
    exact ⟨hag t le_rfl, Model.Run.mempool_twins fun k hk => hinbox x k (hag k hk)⟩
  /- The witness's forgeries: those planned before `T₁` at `t₀ + 1`, the others past `b₁`. -/
  let sh : Time := b₁ - T₁
  have hsh : 0 < sh := by simp only [sh]; linarith
  have hb₁sh : T₁ + sh = b₁ := by simp only [sh]; ring
  let fsM := preAt T₁ (t₀ + 1) fs ++ postAt T₁ sh fs
  have hmovedM : ∀ x ∈ fsM, ∃ y ∈ fs, x.key = y.key ∧ x.role = y.role ∧ x.msg = y.msg ∧
      x.tag = y.tag ∧ y.time ≤ x.time ∧ T₁ ≤ x.time := fun x hx =>
    mem_moved (by linarith) hsh.le hx
  have hlateM : ∀ x ∈ fsM, t₀ + 1 ≤ x.time := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, -, -, rfl⟩ := mem_preAt.mp hx
      exact le_rfl
    · obtain ⟨y, -, hy, rfl⟩ := mem_postAt.mp hx
      change t₀ + 1 ≤ y.time + sh
      simp only [sh]; linarith
  have hrangeM : ∀ x ∈ fsM, 0 ≤ x.time ∧ x.time ≤ H := by
    intro x hx
    refine ⟨by linarith [hlateM x hx], ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, -, -, rfl⟩ := mem_preAt.mp hx
      change t₀ + 1 ≤ H
      simp only [H, Ts]; linarith
    · obtain ⟨y, hy, -, rfl⟩ := mem_postAt.mp hx
      have := (hP.time_range y hy).2
      change y.time + sh ≤ H
      simp only [H, Ts, sh]; linarith
  have hfsM : ∀ x ∈ fsM, key x.key ∈ A ∧ x.key ∈ sel x.role := fun x hx => by
    obtain ⟨y, hy, hk, hr, -, -, -, -⟩ := hmovedM x hx
    rw [hk, hr]
    exact ⟨hsubA _ (hP.keys y hy), hP.cred y hy⟩
  let toW : Forgery (compiled F) ER → Forgery (compiled F) EW :=
    fun x => ⟨x.key, x.role, x.msg, x.tag, x.time⟩
  let fsW := fsM.map toW
  have hfsW : ∀ x ∈ fsW, key x.key ∈ A ∧ x.key ∈ sel x.role := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hfsM y hy
  have hlateW : ∀ x ∈ fsW, t₀ + 1 ≤ x.time := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hlateM y hy
  let injW := planInj v fsW
  let polW := holdPol baseW G t₀ b₁
  let W := holdRun1 baseW G t₀ b₁ injW
  have hHPW : HoldPremises1 baseW G t₀ b₁ injW := by
    refine ⟨hH0, hP.admits, by change (1 : Time) < 2; norm_num, rfl,
      Model.eagerRelay_txs (holdRun1 baseW G t₀ b₁ injW)
        (by simp only [Model.Run.withEvents_eq]; rfl), fun _ => rfl,
      fun t u o ho d hd x hx => ?_, fun t u o ho d hd k' r hkr => ?_⟩
    · obtain ⟨-, y, hy, -, rfl⟩ := mem_planInj.mp ho
      rcases parts_forged hd with rfl | hn
      · simp only [Model.Run.signerOf, Obj.signer?, forged_auth, Option.map_some,
          Option.some.injEq] at hx
        subst hx
        exact (hfsW y hy).1
      · simp [Model.Run.signerOf, Obj.signer?, hn] at hx
    · obtain ⟨-, y, hy, -, rfl⟩ := mem_planInj.mp ho
      rcases parts_forged hd with rfl | hn
      · rw [forged_auth] at hkr
        injection hkr with h1 h2
        subst h1 h2
        exact (hfsW y hy).2
      · rw [hn] at hkr; cases hkr
  have hvW : W.ExecutionValid := hold1_valid hHPW
  have hΔR : ER.ΔAC = 2 := rfl
  have hΔW : EW.ΔAC = 2 := rfl
  /- `W` has the stages of `R` before `t₀`. -/
  have hinjW : ∀ t, t < t₀ + 1 → injW t = injR t := fun t ht =>
    planInj_eq_nil fun x hx => lt_of_lt_of_le ht (hlateW x hx)
  have hstage : ∀ n ≤ n₀, baseW.injectStages (fun _ => 1) injW polW n =
      baseR.injectStages (fun _ => 1) injR polR n :=
    Model.Run.injectStages_twins tw (fun _ => 1) injR injW polR polW
      (fun x t ht => hagree x t fun hc => by
        have : t < t₀ := ht
        linarith [hc.2.1])
      (fun x t ht => hrelay x t (hagree x t fun hc => by
        have : t < t₀ := ht
        linarith [hc.2.1]))
      (fun n hn => hinjW _ (by
        have : (n : Time) < t₀ := by change (n : Int) < (n₀ : Int); omega
        linarith))
      (fun n hn x o => by
        have hnt : (n : Time) < t₀ := by change (n : Int) < (n₀ : Int); omega
        have hes : ∀ e ∈ baseR.injectStages (fun _ => 1) injR polR n, e.time < (n : Time) :=
          fun e he => (baseR.injectStages_time (fun _ => 1) injR polR n he).2
        have hfr : baseR.front (baseR.injectStages (fun _ => 1) injR polR n) (n : Time) =
            baseW.front (baseR.injectStages (fun _ => 1) injR polR n) (n : Time) := by
          rw [Model.Run.front_eq, Model.Run.front_eq,
            Model.Run.wakeEvents_twins tw (fun y => hagree y _ fun hc => by linarith [hc.2.1])
              (fun y => hagree y _ fun hc => by linarith [hc.2.1]),
            Model.Run.tickEvents_twins tw (fun y => hagree y _ fun hc => by linarith [hc.2.1])]
        have h1 := holdPol_front baseR G T₁ T₁ hΔR (fun _ => 1) injR polR n
          ((lt_or_ge (n : Time) T₁).imp id id) x o
        have h2 : polW (baseR.front (baseR.injectStages (fun _ => 1) injR polR n) (n : Time)) x o
            (n : Time) = true := by
          rw [hfr]
          exact holdPol_front_of baseW G t₀ b₁ hΔW _ _ hes (Or.inl hnt) x o
        exact h2.trans h1.symm)
  have ht₀H : t₀ ≤ baseR.horizon := by change t₀ ≤ H; linarith
  have hn₀ : n₀ = t₀.toNat := by rw [ht₀, Int.toNat_natCast]
  /- `W` releases `m` at `t₀`, and nobody releases it before. -/
  set SR := baseR.injectStages (fun _ => 1) injR polR n₀ with hSR
  have hSRtime : ∀ e ∈ SR, e.time < t₀ := fun e he =>
    (baseR.injectStages_time (fun _ => 1) injR polR n₀ he).2
  have hagSR : ∀ e ∈ SR, Model.Run.TickAgrees baseR baseW e := by
    intro e he x t hxt
    subst hxt
    exact hTA x t (Or.inl (hSRtime _ he)) x t rfl
  have hnotdueR : ∀ e ∈ baseR.wakeEvents t₀ ++ baseR.tickEvents t₀,
      t₀ < e.time + (fun _ => (1 : Time)) e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨_, _, _, _, rfl⟩ := (baseR.mem_wakeEvents _ _).mp he
      change t₀ < t₀ + 1; linarith
    · obtain ⟨_, _, _, rfl⟩ := (baseR.mem_tickEvents _ _).mp he
      change t₀ < t₀ + 1; linarith
  have hnotdueW : ∀ e ∈ baseW.wakeEvents t₀ ++ baseW.tickEvents t₀,
      t₀ < e.time + (fun _ => (1 : Time)) e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨_, _, _, _, rfl⟩ := (baseW.mem_wakeEvents _ _).mp he
      change t₀ < t₀ + 1; linarith
    · obtain ⟨_, _, _, rfl⟩ := (baseW.mem_tickEvents _ _).mp he
      change t₀ < t₀ + 1; linarith
  have hpoolW : baseW.duePool (fun _ => 1) (baseW.front SR t₀) t₀ =
      baseW.duePool (fun _ => 1) SR t₀ := by
    rw [Model.Run.front_eq, List.append_assoc]
    exact Model.Run.duePool_append_of_not_due baseW _ SR _ t₀ hnotdueW
  have hpoolR : baseR.duePool (fun _ => 1) (baseR.front SR t₀) t₀ =
      baseR.duePool (fun _ => 1) SR t₀ := by
    rw [Model.Run.front_eq, List.append_assoc]
    exact Model.Run.duePool_append_of_not_due baseR _ SR _ t₀ hnotdueR
  have hpool : baseW.duePool (fun _ => 1) SR t₀ = baseR.duePool (fun _ => 1) SR t₀ :=
    Model.Run.duePool_twins tw (fun _ => 1) SR t₀ hagSR
  have hWev : ∃ tail, W.events = SR ++ tail := by
    have hN : n₀ ≤ H.toNat + 1 := by
      have := Int.toNat_le_toNat (show t₀ ≤ H by linarith)
      rw [← hn₀] at this
      omega
    obtain ⟨tail, htail⟩ := baseW.injectStages_prefix (fun _ => 1) injW polW hN
    exact ⟨tail, by rw [Model.Run.withEvents_events, Model.Run.injectEvents_eq, htail,
      hstage n₀ le_rfl]⟩
  have hpolWserves : ∀ x o, o ∈ baseW.duePool (fun _ => 1) SR t₀ →
      polW (baseW.front SR t₀) x o t₀ = true := by
    intro x o ho
    obtain ⟨u, τ', ⟨e, he, het, -⟩, hr⟩ := releases_of_mem_duePool baseW _ SR t₀ ho
    obtain ⟨tail, htail⟩ := hWev
    have hrW : W.releases u o τ' := by
      have h := baseW.releases_append SR tail hr
      rw [← htail] at h
      simpa only [W, holdRun1, Model.Run.injectRun, Model.Run.withEvents_eq] using h
    have hτ' : τ' < t₀ := het ▸ hSRtime e he
    have hτ1 := Int.add_one_le_of_lt hτ'
    have := hold1_serves hHPW hrW (w := x) hτ' ht₀H (Or.inr (by rw [hΔW]; linarith))
    rw [← hn₀, hstage n₀ le_rfl] at this
    exact this
  have hbatch : (injW t₀ v ++ (baseW.duePool (fun _ => 1) (baseW.front SR t₀) t₀).filter
        (fun o => polW (baseW.front SR t₀) v o t₀)).dedup =
      (injR t₀ v ++ (baseR.duePool (fun _ => 1) (baseR.front SR t₀) t₀).filter
        (fun o => polR (baseR.front SR t₀) v o t₀)).dedup := by
    rw [hinjW t₀ (lt_add_one _), hpoolW, hpoolR,
      List.filter_eq_self.mpr fun o ho => hpolWserves v o ho, hpool,
      List.filter_eq_self.mpr fun o _ =>
        holdPol_front baseR G T₁ T₁ hΔR (fun _ => 1) injR polR n₀ (Or.inr hT₁t₀) v o]
  have hrelW : W.releases v m t₀ :=
    Model.Run.releases_twins_layer tw (fun _ => 1) injR injW polR polW rfl ht₀H
      (hstage n₀ le_rfl) (fun t => hagree v t fun hc => hvS hc.1)
      (fun t => hinbox v t (hagree v t fun hc => hvS hc.1)) hbatch hrel₀
  have hnew : ∀ u t, t < t₀ → ¬ W.releases u m t := by
    intro u t ht hr
    have ht0 : 0 ≤ t := le_trans hT₁.le (le_of_inject_releases baseW (fun x t h => by
      change (decide (T₁ ≤ t) && sleepAwake Sl t₀ b₁ x t) = true at h
      rw [Bool.and_eq_true, decide_eq_true_iff] at h
      exact h.1) (fun _ => 1) injW polW hr)
    have hlt : t.toNat + 1 ≤ n₀ := (Int.toNat_lt ht0).mpr ht
    have hthH : t ≤ H := by linarith
    have hN : t.toNat + 1 ≤ H.toNat + 1 := by have := Int.toNat_le_toNat hthH; omega
    obtain ⟨tailW, htailW⟩ := baseW.injectStages_prefix (fun _ => 1) injW polW hN
    obtain ⟨tailR, htailR⟩ := baseR.injectStages_prefix (fun _ => 1) injR polR hN
    change (baseW.withEvents (baseW.injectEvents (fun _ => 1) injW polW)).releases u m t at hr
    rw [Model.Run.injectEvents_eq, htailW] at hr
    have hin : ∀ e ∈ baseW.injectStages (fun _ => 1) injW polW (t.toNat + 1) ++ tailW,
        e.node = u → e.time = t →
          e ∈ baseW.injectStages (fun _ => 1) injW polW (t.toNat + 1) := by
      intro e he _ het
      rw [← htailW] at he
      have h := baseW.mem_injectStages_of_time_lt _ injW polW he (a := t + 1)
        (by rw [het]; exact lt_add_one t)
      rwa [show (t + 1).toNat = t.toNat + 1 by rw [Int.toNat_add ht0 zero_le_one]; rfl] at h
    have hr' := baseW.releases_restrict _ tailW
      (htailW ▸ baseW.injectStages_nodup _ injW polW _) hin hr
    rw [hstage _ hlt] at hr'
    have hagL : ∀ e ∈ baseR.injectStages (fun _ => 1) injR polR (t.toNat + 1),
        Model.Run.TickAgrees baseR baseW e := by
      intro e he x τ hx
      subst hx
      have h1 := (baseR.injectStages_time (fun _ => 1) injR polR _ he).2
      have h2 : ((t.toNat + 1 : ℕ) : Time) ≤ t₀ := by
        change ((t.toNat + 1 : ℕ) : Int) ≤ (n₀ : Int); omega
      change τ < ((t.toNat + 1 : ℕ) : Time) at h1
      exact hTA x τ (Or.inl (by linarith)) x τ rfl
    have hrR := (Model.Run.releases_twins tw _ hagL).mp hr'
    refine hmin u t ht ?_
    change (baseR.withEvents (baseR.injectEvents (fun _ => 1) injR polR)).releases u m t
    rw [Model.Run.injectEvents_eq, htailR]
    exact baseR.releases_append _ tailR hrR
  /- The exercise. -/
  have hWkey : W.key = baseW.key := Model.Run.withEvents_key _ _
  have hWfa : W.faultyAt = baseW.faultyAt := Model.Run.withEvents_faultyAt _ _
  have hgroups : ∀ b : Bool, ∃ u, G u = b ∧ ∀ t, u ∉ W.faultyAt t := by
    intro b
    by_cases h : G v₁ = b
    · exact ⟨v₁, h, fun t => by rw [hWfa]; exact hv₁A⟩
    · exact ⟨v₀, bool_of_ne hv₀G h, fun t => by rw [hWfa]; exact hv₀A⟩
  have hexer : Exercised (Sys F V) q.a.async t₀ b₁ ⟨EW, W⟩ :=
    exercised_async hsplit (exercised_of_fresh hvW (hold1_contentOriginHold hHPW)
      (fun t => by rw [hWfa]) (by rw [hΔW]; exact one_lt_two) (k := k) (r := rl) rfl hmfg
      (by rw [hWkey]; exact hrelW) hnew (by rw [hWkey]; exact hwG)
      (fun t => by rw [hWfa]; exact hwA)
      (fun t h1 _ => by
        change (decide (T₁ ≤ t) && sleepAwake Sl t₀ b₁ w t) = true
        rw [Bool.and_eq_true, decide_eq_true_iff, sleepAwake_eq_true]
        exact ⟨by linarith, fun hc => hwS hc.1⟩)
      (by rw [hΔW]; linarith) (hgroups true) (hgroups false))
  /- The rest of the witness. -/
  have hpt : (Sys F V).pt ⟨EW, W⟩ = sleepPoint A Sl T₁ t₀ b₁ v₀ Ts H := by
    change W.point = _
    simp only [W, holdRun1, Model.Run.injectRun, Model.Run.withEvents_point]
    exact (sleepPoint_eq A Sl T₁ t₀ b₁ v₀ Ts H).symm
  have huniqM := moved_unique (T₁ := T₁) (τ := t₀ + 1) (sh := sh) hP.unique
  have hFP : ForgeryPremisesAt baseW (shapeRoleFloor F V EW) v fsW injW (fun _ => 1) polW := by
    refine ⟨fun t u o => mem_planInj, fun _ => zero_le_one, hvW, fun _ => rfl,
      fun x hx => (hfsW x hx).1, hvA, fun x hx => ?_, fun x hx => ?_, fun x hx s hs => ?_,
      fun x hx y hy hk hr hm' htg => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      change aW v y.time = true
      rw [hagree v y.time fun hc => hvS hc.1]
      obtain ⟨-, -, -, -, -, -, -, hT'⟩ := hmovedM y hy
      exact (hawR v y.time).mpr hT'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hrangeM y hy
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, -, hr, -, -, hzt, -⟩ := hmovedM y hy
      change shapeRoleFloor F V ER y.role = some s at hs
      rw [hr] at hs
      exact le_trans (hP.floor_le z hz s hs) hzt
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact huniqM x' hx' y' hy' hk hr hm' htg
  have hact : ∀ a b, activity (compiled F) (shapeRoleFloor F V) ⟨EW, W⟩ a b =
      ((fsM.filter fun x => decide (a ≤ x.time ∧ x.time < b)).map
        fun x => key x.key).toFinset.card := fun a b => by
    change (activeFaulty W (shapeRoleFloor F V EW) a b).card = _
    rw [activeFaulty_of_forgeriesAt hFP, List.filter_map, List.map_map]
    rfl
  obtain ⟨hsetPre, hsetPost⟩ := moved_sets hP (τ := t₀ + 1) (sh := sh) (by linarith)
    (by linarith) (H := H) (by simp only [H, Ts, sh]; linarith)
  rw [hb₁sh] at hsetPre hsetPost
  have hactpre : activity (compiled F) (shapeRoleFloor F V) ⟨EW, W⟩ 0 (max b₁ 0) = q.hpre := by
    rw [hact, max_eq_left hb₁, hsetPre, List.toFinset_card_of_nodup (hnodup _), hApre]
  have hactpost : activity (compiled F) (shapeRoleFloor F V) ⟨EW, W⟩ (max b₁ 0)
      (((Sys F V).pt ⟨EW, W⟩).horizon + 1) = q.hpost := by
    rw [hact, max_eq_left hb₁, hpt, sleepPoint_horizon, hsetPost,
      List.toFinset_card_of_nodup (hnodup _), hApost]
  have hnah : (notAwakeHonest (Sys F V) t₀ b₁ ⟨EW, W⟩).card = max q.m q.fcap := by
    rw [sleepPoint_notAwakeHonest hpt (by linarith) hT₁t₀ (by linarith) hASl, hAc, hSlc, hmax]
    omega
  have hready : (Sys F V).ready K b₁ ⟨EW, W⟩ = b₁ + (Sys F V).cDur K ⟨EW, W⟩ + 1 := by
    simp only [System.ready, max_eq_left hb₁]
  have hhealAt : ∀ c : ℕ, healAt (Sys F V) b₁ c ⟨EW, W⟩ = b₁ + (c : Time) * 2 := fun c => by
    change max b₁ 0 + (c : Time) * ((Sys F V).pt ⟨EW, W⟩).env.ΔAC = _
    rw [hpt, sleepPoint_ΔAC, max_eq_left hb₁]
  have hrd : q.readerDur (Sys F V) ⟨EW, W⟩ = (q.catchUp : Time) * 2 := by
    change (q.catchUp : Time) * ((Sys F V).pt ⟨EW, W⟩).env.ΔAC = _
    rw [hpt, sleepPoint_ΔAC]
  have hcl' := holdRun1_class (rho := baseW) (b₀ := t₀) (b₁ := b₁) (inj := injW) q.a ha hHPW
  have hTb₁ : T₁ ≤ b₁ := by linarith
  refine ⟨⟨EW, W⟩, t₀, b₁, hvW,
    by change ¬ W.HashCollision
       simp only [W, Model.Run.withEvents_eq]
       exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj),
    ⟨hcl'.1, hcl'.2, hb₀₁, ?_, hactpre.le, hactpost.le, ?_, ?_, ?_, ?_⟩, ?_,
    ⟨?_, hactpre, hactpost, ?_, hnah, hexer⟩, ?_, ?_⟩
  · rw [hpt, sleepPoint_ΔAC]; simp only [b₁]; linarith
  · rw [hnah]; exact le_max_left _ _
  · rw [hpt, sleepPoint_faultCount, hAc]
  · intro x t h1 h2' h3
    rw [hpt] at h2' h3 ⊢
    exact sleepPoint_honestAwakeAfter hTb₁ x t h1 h2' h3
  · rw [hpt, sleepPoint_ΔAC, sleepPoint_ΔFG]
    have : (1 : Time) ≤ (K.params.fgDelay : Time) := by exact_mod_cast hfg
    linarith
  · rw [hready]
    change shapeHolds F (K.progress cap i) ((Sys F V).cDur K ⟨EW, W⟩) _ _
      ((Sys F V).pt ⟨EW, W⟩) (W.key, W.sel)
    rw [hWkey, show W.sel = baseW.sel from Model.Run.withEvents_sel _ _]
    have hsel' : ∀ s, sel (.proposer s) = extremalSel F EW (.proposer s) := fun s =>
      (hP.proposer s).trans ((extremalSel_apply F ER _).trans (extremalSel_apply F EW _).symm)
    exact sleepPoint_holds F K key h2 hpt sel hsel' hf cap i hadmA hv₁A hTb₁ le_rfl _
  · rw [hpt, sleepPoint_ΔAC]; simp only [b₁]; ring
  · rw [hpt, sleepPoint_faultCount, hAc]
  · intro c hc
    rw [hhealAt, hpt, hrd]
    have : (c : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 ≤ ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hcoe]
      push_cast
      linarith [hx hlq, hx latq]
    refine sleepPoint_safeActive hvA hwA hvw hTb₁ _ _ ?_ ?_
    · simp only [H, Ts]; linarith
    · simp only [H, Ts]; linarith
  · intro c d hc hd
    rw [hhealAt, hpt, sleepPoint_ΔAC, hrd]
    have : (c : Time) * 2 + (d : Time) * 2 ≤ Hc := by
      change (c : Time) * 2 + (d : Time) * 2 ≤
        ((hsq.untopD 0 + hlq.untopD 0 + latq.untopD 0 : ℕ) : Time) * 2
      rw [hc, hd, hcoe, hcoe]
      push_cast
      linarith [hx hsq]
    have hc0 : (0 : Time) ≤ (c : Time) * 2 := by positivity
    have hd0 : (0 : Time) ≤ (d : Time) * 2 := by positivity
    refine sleepPoint_txLiveActive hv₀A hv₁A h01.symm hTb₁ (by simp only [Ts]; linarith)
      (by simp only [Ts]; linarith) _ _ _ ?_ (by simp only [H, Ts]; linarith)
    have hTsb : b₁ + (c : Time) * 2 ≤ Ts + (c : Time) * 2 := by simp only [Ts]; linarith
    have : max Ts (b₁ + (c : Time) * 2) + (d : Time) * 2 ≤ Ts + Hc := by
      rcases le_total Ts (b₁ + (c : Time) * 2) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    simp only [H]
    linarith

end Consensus.Comparison

end
