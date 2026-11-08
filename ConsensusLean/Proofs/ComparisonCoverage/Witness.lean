module
public import ConsensusLean.Comparison.Coverage
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Lemmas.Model.Canonical.Policy
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 0 coverage: the witness runs

The witness point `covPoint A u H`: `ΔAC = ΔFG = 2`, every validator awake at every time, the
validators of `A` compromised from the start (silent: a compromised validator has no engine
events), horizon `H`, transaction `42` submitted to `u` at time `0`. The PKI is
`Fintype.equivFin`, the selection the extremal one (`.sized 1` proposer roles select key `1`), and
`A` (exactly the fault cap) avoids the validator of key `1` and one other validator the witness
needs honest (`exists_faulty`).

* `covPoint_holds`: a fitting progress requirement that admits `|A|` compromised validators holds
  on every window.
* `covPoint_safeActive`, `covPoint_txLiveActive`, `heal_active`: the claims are active at every
  start whose deadline is within the horizon.
* `txLatencyCoverage0_of`, `proposalLatencyCoverage0_of`: the latency coverages, on the
  synchronous canonical run (`Sync0Class` at exactly `f` compromised validators).
* `healCoverage0_any`: heal coverage at a point of class `any`: the synchronous canonical run is in
  the incident class `[0, L·ΔAC)` (the class allows, and does not require, asynchrony), with the
  exact length `L·ΔAC`.
* `healCoverage0_split`: heal coverage at a point of class `split G`: the canonical scheduler
  under a delivery policy holds an honest proposal across the groups until the incident ends
  (see the section's comment). -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf)

variable {V : Type} [DecidableEq V]

/-! ## The witness point -/

/-- The coverage witness point: `ΔAC = ΔFG = 2`, everyone awake at every time, the validators of
`A` compromised from the start, horizon `H`; transaction `42` submitted to `u` at time `0`. -/
def covPoint (A : Finset V) (u : V) (H : Time) : EnvPoint V :=
  ⟨⟨2, two_pos, 2, two_pos, fun _ _ => true⟩, fun _ => A, monotone_const, H,
    fun v t => if v = u ∧ t = 0 then [42] else []⟩

section Point

variable (A : Finset V) (u : V) (H : Time)

theorem covPoint_eq : covPoint A u H =
    ⟨⟨2, two_pos, 2, two_pos, fun _ _ => true⟩, fun _ => A, monotone_const, H,
      fun v t => if v = u ∧ t = 0 then [42] else []⟩ := by rfl

@[simp] theorem covPoint_ΔAC : (covPoint A u H).env.ΔAC = 2 := by rfl

@[simp] theorem covPoint_ΔFG : (covPoint A u H).env.ΔFG = 2 := by rfl

@[simp] theorem covPoint_awake (v : V) (t : Time) : (covPoint A u H).env.awake v t = true := by rfl

@[simp] theorem covPoint_faultyAt (t : Time) : (covPoint A u H).faultyAt t = A := by rfl

theorem covPoint_faultCount (t : Time) : (covPoint A u H).faultCount t = A.card := by rfl

@[simp] theorem covPoint_horizon : (covPoint A u H).horizon = H := by rfl

theorem covPoint_submit (v : V) (t : Time) :
    (covPoint A u H).submit v t = if v = u ∧ t = 0 then [42] else [] := by rfl

variable {A u H}

theorem covPoint_honest {v : V} (hv : v ∉ A) (t : Time) : (covPoint A u H).HonestAt v t := hv

theorem covPoint_ready {v : V} (hv : v ∉ A) (c t : Time) : (covPoint A u H).Ready c v t :=
  ⟨hv, fun _ _ _ => rfl⟩

theorem covPoint_awakeOn (v : V) (a b : Time) : (covPoint A u H).AwakeOnClosed v a b :=
  fun _ _ _ => rfl

/-- Nobody wakes: everyone is awake at every time. -/
theorem covPoint_not_wakes (v : V) (t : Time) : ¬ Wakes (covPoint A u H).env v t :=
  fun h => absurd h.2 (by simp)

/-- Every honest validator is ready: at most `|A|` are not ready. -/
theorem covPoint_readyAt_card [Fintype V] (c t : Time) :
    Fintype.card V ≤ ((covPoint A u H).readyAt c t).card + A.card := by
  classical
  have hsub : Finset.univ \ A ⊆ (covPoint A u H).readyAt c t := by
    intro v hv
    unfold EnvPoint.readyAt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      covPoint_ready (Finset.mem_sdiff.mp hv).2 c t⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ A
  rw [Finset.univ_inter, Finset.card_univ] at h2
  omega

end Point

omit [DecidableEq V] in
/-- A compromised set of exactly `f` validators avoiding a set `R` of at most two, when
`f + 2 ≤ n`. -/
theorem exists_faulty [Fintype V] (R : Finset V) (hR : R.card ≤ 2) {f : ℕ}
    (hf : f + 2 ≤ Fintype.card V) :
    ∃ A : Finset V, Disjoint A R ∧ A.card = f := by
  classical
  have hc : f ≤ (Finset.univ \ R).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ]
    omega
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨A, Finset.disjoint_left.mpr fun v hv hvR => ?_, hAc⟩
  exact (Finset.mem_sdiff.mp (hA hv)).2 hvR

/-! ## Progress and active claims at the witness point -/

variable [Fintype V] {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A fitting progress requirement that admits `|A|` compromised validators holds on every window
of the witness point under the extremal selection, when key `1` is honest: key `1` proposes every
slot, and at most `|A|` validators are not ready. -/
theorem covPoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (h2 : 2 ≤ Fintype.card V) {A : Finset V} {u : V} {H : Time}
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (hA : AdmitsFaults (K.progress cap i) A.card) (h1 : key ⟨1, by omega⟩ ∉ A) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (covPoint A u H)
      (key, extremalSel F (covPoint A u H).env) := by
  have hfit := hf cap i (pubOf (covPoint A u H).env)
  revert hfit hA
  cases K.progress cap i with
  | recur ρ =>
    intro _ hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit h2 (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    exact ⟨covPoint_ready h1 _ _, covPoint_honest h1 _⟩
  | notReadyAtMost m =>
    intro hA _ t _ _ _
    exact le_trans (covPoint_readyAt_card c t) (Nat.add_le_add_left hA _)

omit [Fintype V] in
/-- Safety is active after `t₀` at the witness point: two honest validators ready at `t₀ + 1`, the
first again at `t₀ + 2`. -/
theorem covPoint_safeActive {A : Finset V} {u : V} {H : Time} {v w : V} (hv : v ∉ A)
    (hw : w ∉ A) (hne : v ≠ w) (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (covPoint A u H) :=
  ⟨v, w, t₀ + 1, t₀ + 2, hne, lt_add_one t₀, by linarith, hH,
    covPoint_ready hv _ _, covPoint_ready hw _ _, covPoint_ready hv _ _⟩

omit [Fintype V] in
/-- Liveness is active from `start` at the witness point: transaction `42`, submitted to the honest
`u` at `0`, is owed to an honest `w ≠ u` ready at the horizon. -/
theorem covPoint_txLiveActive {A : Finset V} {u : V} {H : Time} {w : V} (hu : u ∉ A)
    (hw : w ∉ A) (hne : w ≠ u) (c start D : Time) (hH : max 0 start + 2 + D ≤ H) :
    (covPoint A u H).TxLiveActive c start D := by
  refine ⟨42, 0, H, u, w, le_rfl, covPoint_honest hu 0, rfl, ?_, hne, ?_, ?_, le_rfl,
    covPoint_ready hw c H⟩
  · simp [covPoint_submit]
  · intro τ
    simp [covPoint_submit, hne]
  · simpa only [covPoint_ΔAC] using hH

/-! ## The synchronous witness run -/

/-- The synchronous canonical run at the witness point under PKI `key` and the extremal selection:
valid, no hash collision, log eager from `0`, and a fitting progress requirement that admits `|A|`
compromised validators holds on every window (key `1` honest). -/
theorem covPoint_syncRun (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx) (key : Fin (Fintype.card V) ≃ V)
    (h2 : 2 ≤ Fintype.card V) (A : Finset V) (u : V) {H : Time} (hH : 0 ≤ H)
    (hadm : AdmitsFaults (K.progress cap i) A.card) (h1 : key ⟨1, by omega⟩ ∉ A) :
    ∃ rho : Model.Run (compiled F) (covPoint A u H).env, rho.point = covPoint A u H ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log 0 ∧
      ∀ s e, (Sys F V).prog (shapeProgress F V) K cap i s e ⟨_, rho⟩ := by
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run_sel key F (covPoint A u H) hH 0 _ (extremalSel_admits F _)
  exact ⟨_, rfl, hv, hnc, he, fun s e => covPoint_holds F K key h2 hf cap i hadm h1 _ s e⟩

/-- A run at the witness point has every validator awake: `FullAwake`. -/
theorem fullAwake_of_covPoint (F : ChainShapeFamily O Info) {A : Finset V} {u : V} {H : Time}
    (r : (Sys F V).Run) (hp : (Sys F V).pt r = covPoint A u H) : FullAwake (Sys F V) r := by
  intro v t _ _ _
  rw [hp]
  rfl

/-- The synchronous witness at `f` compromised validators: valid, excuse-free, log eager from `0`
(so synchronous up to every cut), with progress on every window, the given horizon and two honest
validators `v₀ ≠ v₁` (`v₁` of key `1`; transaction `42` submitted to `v₀`). -/
theorem sync_witness (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F)
    (cap : Capability) (i : K.Idx) {f : ℕ} (hfn : f + 2 ≤ Fintype.card V)
    (hadm : AdmitsFaults (K.progress cap i) f) {H : Time} (hH : 0 ≤ H) :
    ∃ (r : (Sys F V).Run) (A : Finset V) (v₀ v₁ : V), (Sys F V).pt r = covPoint A v₀ H ∧
      v₀ ∉ A ∧ v₁ ∉ A ∧ v₁ ≠ v₀ ∧ A.card = f ∧
      (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ ((Sys F V).log r).EagerFrom ((Sys F V).pt r) 0 ∧
      (∀ b, ((Sys F V).log r).SyncUntil ((Sys F V).pt r) b) ∧
      (∀ s e, (Sys F V).prog (shapeProgress F V) K cap i s e r) := by
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have h2 : 2 ≤ Fintype.card V := by omega
  let v₀ := key ⟨0, by omega⟩
  let v₁ := key ⟨1, by omega⟩
  have h10 : v₁ ≠ v₀ := fun h => Nat.one_ne_zero (congrArg Fin.val (key.injective h))
  obtain ⟨A, hA, hAc⟩ := exists_faulty {v₀, v₁} (Finset.card_le_two) hfn
  have hv₀ : v₀ ∉ A := Finset.disjoint_right.mp hA (by simp)
  have hv₁ : v₁ ∉ A := Finset.disjoint_right.mp hA (by simp)
  obtain ⟨rho, hp, hv, hnc, he, hprog⟩ :=
    covPoint_syncRun F K hf cap i key h2 A v₀ hH (hAc ▸ hadm) hv₁
  refine ⟨⟨_, rho⟩, A, v₀, v₁, hp, hv₀, hv₁, h10, hAc, hv, hnc, Model.sysOf_eagerFrom _ he,
    fun b => ?_, hprog⟩
  exact (Model.sysOf_delivers_iff rho _ _ _).mpr (he.syncUntil
    (Model.Run.log_sendsFromZero rho hv) le_rfl (by rw [hp, covPoint_ΔAC]; exact one_lt_two)
    (by rw [hp, covPoint_ΔFG]; exact one_lt_two) b)

/-! ## The latency coverages -/

/-- **Transaction latency coverage** for chain shapes. -/
theorem txLatencyCoverage0_of (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx) (lat : Bound ℕ)
    (ho : (O.output cap).isSome) (hsup : LatencySupport0 V K cap i lat) :
    TxLatencyCoverage0 (Sys F V) (shapeProgress F V) K cap i lat := by
  refine ⟨fun f d hfn hd => ⟨ho, ?_⟩⟩
  have hD : (0 : Time) ≤ (d : Time) * 2 := by positivity
  obtain ⟨r, A, v₀, v₁, hp, hv₀, hv₁, h10, hAc, hv, hnc, he, -, hprog⟩ :=
    sync_witness (V := V) F K hf cap i hfn (hsup f d hfn hd) (H := 2 + (d : Time) * 2)
      (by linarith)
  have hpt : (Sys F V).pt r = covPoint A v₀ (2 + (d : Time) * 2) := hp
  refine ⟨r, hv, hnc, ⟨?_, ?_, fullAwake_of_covPoint F r hp⟩, ?_, hprog _ _, ?_⟩
  · exact he.psync le_rfl (by rw [hpt, covPoint_ΔAC]; exact one_lt_two)
      (by rw [hpt, covPoint_ΔFG]; exact one_lt_two)
  · rw [hpt, covPoint_faultCount, hAc]
  · rw [hpt, covPoint_faultCount, hAc]
  · rw [hpt]
    refine covPoint_txLiveActive hv₀ hv₁ h10 _ 0 _ ?_
    simp only [max_self, zero_add, covPoint_ΔAC, le_refl]

/-- **Proposal latency coverage** for chain shapes. -/
theorem proposalLatencyCoverage0_of (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx) (lat : Bound ℕ)
    (ho : (O.output cap).isSome) (hsup : LatencySupport0 V K cap i lat) :
    ProposalLatencyCoverage0 F K V cap i lat := by
  refine ⟨fun f d hfn hd => ⟨ho, ?_⟩⟩
  have hD : (0 : Time) ≤ (d : Time) * 2 := by positivity
  obtain ⟨r, A, v₀, v₁, hp, hv₀, hv₁, h10, hAc, hv, hnc, he, -, hprog⟩ :=
    sync_witness (V := V) F K hf cap i hfn (hsup f d hfn hd) hD
  have hpt : (Sys F V).pt r = covPoint A v₀ ((d : Time) * 2) := hp
  refine ⟨r, hv, hnc, ⟨?_, ?_, fullAwake_of_covPoint F r hp⟩, ?_, hprog _ _, 0, v₁, le_rfl, ?_, ?_⟩
  · exact he.psync le_rfl (by rw [hpt, covPoint_ΔAC]; exact one_lt_two)
      (by rw [hpt, covPoint_ΔFG]; exact one_lt_two)
  · rw [hpt, covPoint_faultCount, hAc]
  · rw [hpt, covPoint_faultCount, hAc]
  · rw [hpt, covPoint_ΔAC, covPoint_horizon, zero_add]
  · rw [hpt]
    exact covPoint_ready hv₁ _ _

/-! ## Heal coverage: the class `any` -/

/-- The horizon of a heal witness whose incident ends at `b₁`: room for the safety heal point, the
liveness heal point and the latency deadline of the bounds (each `0` when `⊤`). -/
noncomputable def healHorizon (b₁ : Time) (hs hl lat : WithTop ℕ) : Time :=
  b₁ + ((hs.untopD 0 + hl.untopD 0 + lat.untopD 0 : ℕ) : Time) * 2 + 4

theorem healHorizon_eq (b₁ : Time) (hs hl lat : WithTop ℕ) :
    healHorizon b₁ hs hl lat =
      b₁ + ((hs.untopD 0 + hl.untopD 0 + lat.untopD 0 : ℕ) : Time) * 2 + 4 := by rfl

theorem healHorizon_nonneg {b₁ : Time} (hb : 0 ≤ b₁) (hs hl lat : WithTop ℕ) :
    0 ≤ healHorizon b₁ hs hl lat := by
  rw [healHorizon_eq]; positivity

/-- At a witness point whose horizon is at least the heal horizon, every finite heal claim is
active: safety from the safety heal point, liveness from the liveness heal point with the
latency. -/
theorem heal_active (F : ChainShapeFamily O Info) (K : Contract ProgressReq) {A : Finset V}
    {u w : V} {b₁ H : Time} (hb : 0 ≤ b₁) (hu : u ∉ A) (hw : w ∉ A) (hne : w ≠ u)
    (hs hl lat : WithTop ℕ) (hH : healHorizon b₁ hs hl lat ≤ H) (r : (Sys F V).Run)
    (hp : (Sys F V).pt r = covPoint A u H) :
    (∀ c : ℕ, hs = c →
      SafeActive ((Sys F V).cDur K r) (healAt (Sys F V) b₁ c r) ((Sys F V).pt r)) ∧
    (∀ c d : ℕ, hl = c → lat = d → ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r)
      (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  have hx : ∀ x : WithTop ℕ, (0 : Time) ≤ ((x.untopD 0 : ℕ) : Time) := fun _ => by positivity
  have hn : ∀ c : ℕ, WithTop.untopD 0 (c : WithTop ℕ) = c := fun _ => rfl
  have hhe : ∀ c : ℕ, healAt (Sys F V) b₁ c r = b₁ + (c : Time) * 2 := fun c => by
    rw [healAt, hp, covPoint_ΔAC, max_eq_left hb]
  refine ⟨fun c hc => ?_, fun c d hc hd => ?_⟩
  · rw [hhe, hp]
    refine covPoint_safeActive hw hu hne _ _ ?_
    rw [healHorizon_eq, hc, hn] at hH
    push_cast at hH
    linarith [hx hl, hx lat]
  · rw [hhe, hp, covPoint_ΔAC]
    refine covPoint_txLiveActive hu hw hne _ _ _ ?_
    rw [max_eq_right (by positivity)]
    rw [healHorizon_eq, hc, hd, hn, hn] at hH
    push_cast at hH
    linarith [hx hs]

/-- **Heal coverage at a point of class `any`**: the synchronous witness with incident
`[0, L·ΔAC)` (exact length; the class allows asynchrony and does not require it), exactly `f`
validators compromised, the progress premise and every finite claim active. -/
theorem healCoverage0_any (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx)
    (hs hl lat : Bound (Slice0Q V)) (L f : ℕ) (hfn : f + 2 ≤ Fintype.card V)
    (hadm : AdmitsFaults (K.progress cap i) f) :
    let q : Slice0Q V := ⟨L, f, .any⟩
    ∃ r b₀ b₁, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ Slice0Class (Sys F V) K q b₀ b₁ r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
        ((Sys F V).pt r).horizon r ∧
      b₁ - b₀ = (q.L : Time) * ((Sys F V).pt r).env.ΔAC ∧
      ((Sys F V).pt r).faultCount ((Sys F V).pt r).horizon = q.fcap ∧
      Exercised (Sys F V) q.a b₀ b₁ r ∧
      (∀ c : ℕ, hs q = c → SafeActive ((Sys F V).cDur K r) (healAt (Sys F V) b₁ c r)
        ((Sys F V).pt r)) ∧
      (∀ c d : ℕ, hl q = c → lat q = d → ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r)
        (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  intro q
  have hb : (0 : Time) ≤ (L : Time) * 2 := by positivity
  obtain ⟨r, A, v₀, v₁, hp, hv₀, hv₁, h10, hAc, hv, hnc, he, hsync, hprog⟩ :=
    sync_witness (V := V) F K hf cap i hfn hadm (healHorizon_nonneg hb (hs q) (hl q) (lat q))
  have hpt := hp
  refine ⟨r, 0, (L : Time) * 2, hv, hnc, ⟨⟨⟨hsync 0, he.psync hb
      (by rw [hpt, covPoint_ΔAC]; exact one_lt_two) (by rw [hpt, covPoint_ΔFG]; exact one_lt_two)⟩,
      trivial⟩, hb, ?_, ?_, fullAwake_of_covPoint F r hp, ?_⟩, hprog _ _, ?_, ?_, trivial,
    heal_active F K hb hv₀ hv₁ h10 (hs q) (hl q) (lat q) le_rfl r hp⟩
  · rw [hpt, covPoint_ΔAC, sub_zero]
  · rw [hpt, covPoint_faultCount, hAc]
  · rw [hpt, covPoint_ΔAC, covPoint_ΔFG]
    have : (1 : Time) ≤ (K.params.fgDelay : Time) := by exact_mod_cast hfg
    linarith
  · rw [hpt, covPoint_ΔAC, sub_zero]
  · rw [hpt, covPoint_faultCount, hAc]

/-! ## Heal coverage: the class `split G`

The witness holds one honest message across the groups until the end of the incident. The message
is an honest proposal: on the synchronous canonical run at the witness point, cut at `H₀` (healthy
from `0` when `fcap < β·n`), healthy liveness (`ShapeClaimsAt.healthyLive`) gives a proposal `m`
released by an honest key of validator `v`. Let `t₀` be the first release time of `m` on the
synchronous run, and put the incident at `[t₀, b₁)`, `b₁ = t₀ + L·ΔAC`. The witness runs the
canonical scheduler under a delivery policy that serves everything except, from `s₀` to `b₁`, an
object to a validator of the group opposite to `v` when no validator of that group and nobody before
`t₀` released it. `s₀` is `t₀` when the tick of `t₀` releases `m`, and `t₀ + 1` otherwise (then
`m` is released only at a delivery of `t₀`, and the deliveries of `t₀` serve only earlier
releases). The policy serves everything before `s₀`, so the witness releases what the synchronous
run releases there: `m` at `t₀` and nowhere before. Only `v` releases `m` (it is signed with `v`'s
key), so the opposite group receives it only from `b₁` on. In-group delivery stays synchronous, and
delivery is synchronous before `t₀` and from `b₁`. -/

/-- **Heal coverage at a point of class `split G`**: a witness with an incident of exact length
`L·ΔAC` in which an honest proposal is held across the groups until the incident ends, exactly
`f` validators compromised, the progress premise and every finite claim active. -/
theorem healCoverage0_split (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hcl : ShapeClaimsAt F K V) (hf : ProgressFits K F) (hnfg : ProposalsNotFGAtt F)
    (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx) (g : O.Id)
    (hg : O.output cap = some g) (hs hl lat : Bound (Slice0Q V)) (L f : ℕ) (G : V → Bool)
    (hL : 1 ≤ L) (hfn : f + 2 ≤ Fintype.card V) (hT : ∃ v, G v = true) (hF : ∃ v, G v = false)
    (hadm : AdmitsFaults (K.progress cap i) f) (hβ : (f : ℚ) < K.params.β * Fintype.card V) :
    let q : Slice0Q V := ⟨L, f, .split G⟩
    ∃ r b₀ b₁, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ Slice0Class (Sys F V) K q b₀ b₁ r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
        ((Sys F V).pt r).horizon r ∧
      b₁ - b₀ = (q.L : Time) * ((Sys F V).pt r).env.ΔAC ∧
      ((Sys F V).pt r).faultCount ((Sys F V).pt r).horizon = q.fcap ∧
      Exercised (Sys F V) q.a b₀ b₁ r ∧
      (∀ c : ℕ, hs q = c → SafeActive ((Sys F V).cDur K r) (healAt (Sys F V) b₁ c r)
        ((Sys F V).pt r)) ∧
      (∀ c d : ℕ, hl q = c → lat q = d → ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r)
        (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  intro q
  classical
  /- The validators: `v₁` (key `1`, the proposer of every slot) and `x`, in the other group, stay
  honest; `A` (exactly `f` validators) is compromised. -/
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have h2 : 2 ≤ Fintype.card V := by omega
  let v₁ := key ⟨1, by omega⟩
  obtain ⟨x, hx⟩ : ∃ x, G x ≠ G v₁ := by
    cases h : G v₁
    · obtain ⟨x, hx⟩ := hT; exact ⟨x, by rw [hx]; decide⟩
    · obtain ⟨x, hx⟩ := hF; exact ⟨x, by rw [hx]; decide⟩
  have hx1 : v₁ ≠ x := fun h => hx (h ▸ rfl)
  obtain ⟨A, hA, hAc⟩ := exists_faulty {x, v₁} Finset.card_le_two hfn
  have hxA : x ∉ A := Finset.disjoint_right.mp hA (by simp)
  have hv₁A : v₁ ∉ A := Finset.disjoint_right.mp hA (by simp)
  have hadmA : AdmitsFaults (K.progress cap i) A.card := hAc ▸ hadm
  /- The horizons: `H₀` for the proposal of the synchronous run, `H` for the witness. -/
  let H₀ : Time := (K.params.heal cap i : Time) * 2 + (K.params.latency cap i : Time) * 2
  have hH₀ : 0 ≤ H₀ := by positivity
  have hL2 : (2 : Time) ≤ (L : Time) * 2 := by
    have : (1 : Time) ≤ L := by exact_mod_cast hL
    linarith
  let H : Time := healHorizon (H₀ + (L : Time) * 2) (hs q) (hl q) (lat q)
  have hHge : ∀ b : Time, b ≤ H₀ + (L : Time) * 2 → healHorizon b (hs q) (hl q) (lat q) ≤ H :=
    fun b hb => by simp only [H, healHorizon_eq]; linarith
  have hH₀H : H₀ + (L : Time) * 2 ≤ H := by
    have hy : ∀ y : WithTop ℕ, (0 : Time) ≤ ((y.untopD 0 : ℕ) : Time) := fun _ => by positivity
    simp only [H, healHorizon_eq]
    linarith [hy (hs q), hy (hl q), hy (lat q)]
  have hH0 : 0 ≤ H := by linarith
  /- The base run: the witness point, PKI `key`, the extremal selection, eager relay, an injective
  hash. -/
  let E : Env V := (covPoint A x H).env
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) E).Item
  let base : Model.Run (compiled F) E := Model.Run.mk (fun _ => A) monotone_const H [] key
    (extremalSel F E) (covPoint A x H).submit
    (Model.eagerRelay E (fun _ => A) (covPoint A x H).submit) hash
  have hsel : base.SelValid := extremalSel_admits F E
  have hnc : ∀ es, ¬ (base.withEvents es).HashCollision := fun es => by
    rw [Model.Run.withEvents_eq]
    exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  have htimes : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
      (∀ {u o t}, rho.releases u o t → 0 ≤ t ∧ t ≤ rho.horizon) ∧
      (∀ {w o t}, rho.receives w o t → 0 ≤ t ∧ t ≤ rho.horizon) := by
    intro rho hv
    refine ⟨fun ⟨j, hj, _⟩ => ?_, fun ⟨j, hj⟩ => hv.in_horizon _ (List.mem_of_getElem? hj)⟩
    obtain ⟨e, he, -, het⟩ := hj.exists_event
    exact het ▸ hv.in_horizon e (List.mem_of_getElem? he)
  /- The synchronous run `R₀` and its prefix `R₀'` up to `H₀`. -/
  let R₀ := base.withEvents (base.canonicalEvents 0)
  have hv0 : R₀.ExecutionValid := base.canonical_valid hH0 hsel 0
  have hk0 : R₀.key = key := Model.Run.withEvents_key _ _
  obtain ⟨ys, hsplit, hys⟩ := Model.Run.truncate_split hv0.sorted H₀
  have hv0t : (R₀.truncate H₀).ExecutionValid :=
    Model.Run.truncate_valid hv0 hH₀
      (by rw [Model.Run.withEvents_horizon]; change H₀ ≤ H; linarith)
  let R₀' : Model.Run (compiled F) E := Model.Run.mk (fun _ => A) monotone_const H₀
    ((base.canonicalEvents 0).filter (fun e => decide (e.time ≤ H₀))) key (extremalSel F E)
    (covPoint A x H).submit (Model.eagerRelay E (fun _ => A) (covPoint A x H).submit) hash
  have hR₀' : R₀.truncate H₀ = R₀' := by
    change (base.withEvents (base.canonicalEvents 0)).truncate H₀ = R₀'
    rw [Model.Run.truncate_eq, Model.Run.withEvents_eq]
  have hv0' : R₀'.ExecutionValid := hR₀' ▸ hv0t
  have hrel0' : ∀ {u o t}, R₀'.releases u o t → R₀.releases u o t := by
    intro u o t hr
    have ht : t ≤ H₀ := ((htimes R₀' hv0').1 hr).2
    rw [← hR₀'] at hr
    exact (Model.Run.truncate_releases_iff hsplit hys ht).mp hr
  have he0' : CommLog.EagerFrom R₀'.point R₀'.log 0 := by
    refine ⟨fun u o t hs hu w a hta hah hw haw => ?_, fun w o t hr => ?_,
      Model.Run.eagerTxDelivery_iff.mp (Model.eagerRelay_txs R₀' rfl)⟩
    · have hr := base.canonical_eagerFrom 0 hH0 u o t (hrel0' hs) hu w a hta
        (le_trans (show a ≤ H₀ from hah) (by linarith)) hw haw
      rw [← hR₀']
      exact (Model.Run.truncate_receives_iff hsplit hys (show a ≤ H₀ from hah)).mpr hr
    · have ht : t ≤ H₀ := ((htimes R₀' hv0').2 hr).2
      rw [← hR₀'] at hr
      exact base.canonical_quiet 0 w o t ((Model.Run.truncate_receives_iff hsplit hys ht).mp hr)
  /- Healthy liveness on `R₀'` gives an honest proposal `m` of `v`. -/
  have hheal : (Sys F V).Healthy K 0 ⟨E, R₀'⟩ := by
    refine ⟨(Model.sysOf_eagerFrom R₀' he0').psync le_rfl (by exact one_lt_two)
      (by exact one_lt_two), ⟨?_, fun _ _ _ _ _ => rfl⟩, ?_⟩
    · change ((A.card : ℕ) : ℚ) < _
      rw [hAc]; exact hβ
    · change (2 : Time) ≤ (K.params.fgDelay : Time) * 2
      have : (1 : Time) ≤ K.params.fgDelay := by exact_mod_cast hfg
      linarith
  have hlive : ProposalLiveReady R₀' ((Sys F V).cDur K ⟨E, R₀'⟩) g
      ((Sys F V).heal K cap i 0 ⟨E, R₀'⟩) (K.params.latency cap i) := by
    rcases hcl.healthyLive cap g hg i 0 ⟨E, R₀'⟩ hv0'
      ⟨hheal, covPoint_holds (u := x) (H := H₀) F K key h2 hf cap i hadmA hv₁A _ _ _⟩ with h | h
    · exact h
    · exact absurd h
        (Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj))
  obtain ⟨τ, k, hdr, -, -, ⟨hhon, rl, cs, hrole, hrel⟩, -⟩ :=
    hlive _ le_rfl (by change max (0 : Time) 0 + _ * 2 + _ * 2 ≤ H₀; rw [max_self, zero_add])
      ⟨v₁, covPoint_ready (A := A) (u := x) (H := H₀) hv₁A _ _⟩
  let v : V := key k
  let m : (protoOf (compiled F) E).Object := Model.Obj.mk (.signed k rl) (.item hdr) cs
  have hvA : v ∉ A := hhon
  have honly : ∀ (rho : Model.Run (compiled F) E), rho.key = key → ∀ {u t'},
      rho.releases u m t' → u = v := fun rho hk u t' hr => by
    have h := rho.releases_key_of_signer hr rfl
    rw [hk] at h
    exact h.symm
  have hτ : R₀.releases v m τ := hrel0' hrel
  have hτ0 : 0 ≤ τ := ((htimes R₀' hv0').1 hrel).1
  have hτH₀ : τ ≤ H₀ := ((htimes R₀' hv0').1 hrel).2
  /- The first release time `t₀` of `m` on the synchronous run. -/
  have hex : ∃ n : ℕ, R₀.releases v m n := ⟨τ.toNat, by rwa [Int.toNat_of_nonneg hτ0]⟩
  let n₀ := Nat.find hex
  let t₀ : Time := n₀
  have ht₀def : t₀ = (n₀ : Time) := rfl
  have hrel₀ : R₀.releases v m t₀ := Nat.find_spec hex
  have hmin : ∀ u t', t' < t₀ → ¬ R₀.releases u m t' := by
    intro u t' ht' hr
    have hu := honly R₀ hk0 hr
    subst hu
    have ht0 : 0 ≤ t' := ((htimes R₀ hv0).1 hr).1
    have ht'' : t' < (n₀ : Time) := ht'
    have hlt : t'.toNat < n₀ := (Int.toNat_lt ht0).mpr ht''
    exact Nat.find_min hex hlt (by rwa [Int.toNat_of_nonneg ht0])
  have ht₀τ : t₀ ≤ τ := by
    have := Nat.find_min' hex (show R₀.releases v m ((τ.toNat : ℕ) : Time) by
      rwa [Int.toNat_of_nonneg hτ0])
    have h1 : n₀ ≤ τ.toNat := this
    have h2 : (0 : Int) ≤ τ := hτ0
    have h3 : ((n₀ : ℕ) : Int) ≤ τ := by omega
    exact h3
  have ht₀0 : 0 ≤ t₀ := Int.natCast_nonneg n₀
  /- The witness, for a start `s₀` of the held window: `t₀` when the tick of `t₀` releases `m`,
  `t₀ + 1` otherwise. -/
  have main : ∀ s₀ : Time,
      (s₀ = t₀ ∧ (base.withEvents (base.front (base.stages 0 n₀) t₀)).releases v m t₀) ∨
      (s₀ = t₀ + 1 ∧ ¬ (base.withEvents (base.front (base.stages 0 n₀) t₀)).releases v m t₀) →
      ∃ r b₀ b₁, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ Slice0Class (Sys F V) K q b₀ b₁ r ∧
        (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
          ((Sys F V).pt r).horizon r ∧
        b₁ - b₀ = (q.L : Time) * ((Sys F V).pt r).env.ΔAC ∧
        ((Sys F V).pt r).faultCount ((Sys F V).pt r).horizon = q.fcap ∧
        Exercised (Sys F V) q.a b₀ b₁ r ∧
        (∀ c : ℕ, hs q = c → SafeActive ((Sys F V).cDur K r) (healAt (Sys F V) b₁ c r)
          ((Sys F V).pt r)) ∧
        (∀ c d : ℕ, hl q = c → lat q = d → ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r)
          (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
    intro s₀ hs₀
    have hs₀l : t₀ ≤ s₀ := by rcases hs₀ with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
    have hs₀u : s₀ ≤ t₀ + 1 := by rcases hs₀ with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
    let b₁ : Time := t₀ + (L : Time) * 2
    let pol : List (Model.Event V (protoOf (compiled F) E).Object) → V →
        (protoOf (compiled F) E).Object → Time → Bool := fun es y o a =>
      decide (¬ (G y ≠ G v ∧ s₀ ≤ a ∧ a < b₁) ∨
        ∃ u t', (base.withEvents es).releases u o t' ∧ (t' < t₀ ∨ G u ≠ G v))
    have hpolT : ∀ es y o a, pol es y o a = true ↔ (¬ (G y ≠ G v ∧ s₀ ≤ a ∧ a < b₁) ∨
        ∃ u t', (base.withEvents es).releases u o t' ∧ (t' < t₀ ∨ G u ≠ G v)) :=
      fun _ _ _ _ => decide_eq_true_iff
    have hpre : ∀ es y o (a : Time), 0 ≤ a → a < s₀ → pol es y o a = true :=
      fun es y o a _ ha => (hpolT es y o a).mpr (Or.inl fun h => absurd h.2.1 (not_le.mpr ha))
    let R₁ := base.withEvents (base.policyEvents pol)
    have hv1 : R₁.ExecutionValid := base.policy_valid pol hH0 hsel
    have hk1 : R₁.key = key := Model.Run.withEvents_key _ _
    have hpt1 : R₁.point = covPoint A x H := Model.Run.withEvents_point _ _
    have hH1 : R₁.horizon = H := Model.Run.withEvents_horizon _ _
    have htx1 : R₁.EagerTxDelivery := by
      change (base.withEvents (base.policyEvents pol)).EagerTxDelivery
      rw [Model.Run.withEvents_eq]
      exact Model.eagerRelay_txs _ rfl
    have hagree : ∀ n : ℕ, (n : Time) ≤ s₀ → base.policyStages pol n = base.stages 0 n :=
      base.policyStages_eq_stages pol hpre
    have hiff : ∀ {u o t}, t + 1 ≤ s₀ → t ≤ H → (R₁.releases u o t ↔ R₀.releases u o t) :=
      fun ht htH => base.policy_releases_iff pol hpre hH0 ht htH
    /- `m` is released at `t₀` and nowhere before. -/
    have hmin1 : ∀ u t', t' < t₀ → ¬ R₁.releases u m t' := fun u t' ht' hr =>
      hmin u t' ht' ((hiff (Int.add_one_le_of_lt (lt_of_lt_of_le ht' hs₀l)) (by linarith)).mp hr)
    have hrel1 : R₁.releases v m t₀ := by
      rcases hs₀ with ⟨hs, htick⟩ | ⟨hs, -⟩
      · have hn₀ : n₀ < H.toNat + 1 := by
          have := Int.toNat_le_toNat (show t₀ ≤ H by linarith)
          rw [ht₀def, Int.toNat_natCast] at this
          omega
        obtain ⟨tail, htail⟩ := base.policy_front_prefix pol hn₀
        rw [hagree n₀ (le_of_eq hs.symm)] at htail
        change (base.withEvents (base.policyEvents pol)).releases v m t₀
        rw [Model.Run.policyEvents_eq, htail]
        exact base.releases_append _ tail htick
      · exact (hiff (le_of_eq hs.symm) (by linarith)).mpr hrel₀
    /- The opposite group does not receive `m` before `b₁`. -/
    have hnorecv : ∀ w, G w ≠ G v → ∀ a, a < b₁ → ¬ R₁.receives w m a := by
      intro w hw a ha hr
      obtain ⟨ha0, haH⟩ := (htimes R₁ hv1).2 hr
      rw [hH1] at haH
      obtain ⟨-, hpool, hp⟩ := base.policy_receives_inv pol hr
      have hext : ∀ u t', (base.withEvents (base.front (base.policyStages pol a.toNat)
          (a.toNat : Time))).releases u m t' → R₁.releases u m t' := by
        intro u t' h'
        have han : a.toNat < H.toNat + 1 := by have := Int.toNat_le_toNat haH; omega
        obtain ⟨tail, htail⟩ := base.policy_front_prefix pol han
        change (base.withEvents (base.policyEvents pol)).releases u m t'
        rw [Model.Run.policyEvents_eq, htail]
        exact base.releases_append _ tail h'
      rcases (hpolT _ _ _ _).mp hp with h1 | ⟨u, t', hu, ht'⟩
      · have has₀ : a < s₀ := by
          by_contra hc
          exact h1 ⟨hw, not_lt.mp hc, ha⟩
        obtain ⟨u, t', hu⟩ := (base.mem_pool _ m).mp hpool
        have hut := honly R₁ hk1 (hext u t' hu)
        subst hut
        have ht'a : t' ≤ a := by
          have := base.front_releases_le _ (a.toNat : Time)
            (fun e he => (base.policyStages_time pol _ he).2) hu
          rwa [Int.toNat_of_nonneg ha0] at this
        have ht't₀ : t₀ ≤ t' := not_lt.mp fun h => hmin1 _ t' h (hext _ t' hu)
        rcases hs₀ with ⟨hs, -⟩ | ⟨hs, htick⟩
        · linarith
        · have hat : a = t₀ := le_antisymm (Int.lt_add_one_iff.mp (hs ▸ has₀)) (by linarith)
          have hnat : a.toNat = n₀ := by rw [hat, ht₀def]; exact Int.toNat_natCast n₀
          have ht't : t' = t₀ := le_antisymm (by linarith) ht't₀
          rw [hnat, hagree n₀ (by rw [hs, ← ht₀def]; linarith), ht't] at hu
          exact htick hu
      · have hut := honly R₁ hk1 (hext u t' hu)
        subst hut
        rcases ht' with ht' | ht'
        · exact hmin1 _ t' ht' (hext _ t' hu)
        · exact ht' rfl
    /- Receipts: a release at `t` is received at `ρ > t` when the policy serves it then. -/
    have hrecv : ∀ u o t, R₁.releases u o t → ∀ w ρ, t < ρ → ρ ≤ H → w ∉ A →
        (b₁ ≤ ρ ∨ G w = G v ∨ t < t₀ ∨ G u ≠ G v) → R₁.receives w o ρ := by
      intro u o t hr w ρ htρ hρH hw hc
      refine base.policy_receives pol hH0 hr htρ hρH hw rfl ((hpolT _ _ _ _).mpr ?_)
      rcases hc with hc | hc | hc
      · exact Or.inl fun h => absurd h.2.2 (not_lt.mpr hc)
      · exact Or.inl fun h => h.1 hc
      · exact Or.inr ⟨u, t, base.policy_releases_front pol hr htρ hρH, hc⟩
    have hheld : ∀ w o ρ d, R₁.receives w o ρ → ρ ≤ d → CommLog.Held R₁.point R₁.log w o d :=
      fun w o ρ d hr hd =>
        ⟨ρ, hd, Or.inr hr, fun t _ _ => by rw [hpt1]; exact covPoint_not_wakes w t⟩
    /- Delivery with deadline `dl` up to `cut`, from a receipt rule. -/
    have hdeliv : ∀ (dl : Time → Time) (cut : Time), (∀ a, a ≤ dl a) →
        (∀ u o t, R₁.releases u o t → u ∉ A → ∀ w a, t ≤ a → dl a ≤ cut → dl a ≤ H → w ∉ A →
          ∃ ρ, ρ ≤ dl a ∧ R₁.receives w o ρ) →
        CommLog.Delivers R₁.point R₁.log dl dl cut := by
      intro dl cut hdl hrule
      have hmsg : ∀ u o t, R₁.log.sent u o t → R₁.point.HonestAt u t → ∀ w a, t ≤ a →
          dl a ≤ cut → dl a ≤ R₁.point.horizon → R₁.point.HonestAt w (dl a) →
          CommLog.Held R₁.point R₁.log w o (dl a) := by
        intro u o t hs hu w a hta hc hh hw
        rw [hpt1] at hu hh hw
        obtain ⟨ρ, hρ, hr⟩ := hrule u o t hs hu w a hta hc hh hw
        exact hheld w o ρ _ hr hρ
      refine ⟨fun u o t hs hu _ w a hta hc hh hw _ => hmsg u o t hs hu w a hta hc hh hw,
        fun u o t hs hu _ w a hta hc hh hw _ => hmsg u o t hs hu w a hta hc hh hw, ?_⟩
      intro u y τ' hτ' hu hau hy w a hτa _ _ hw haw
      exact ⟨dl a, le_trans hτ' (le_trans hτa (hdl a)), le_rfl,
        Model.Run.eagerTxDelivery_iff.mp htx1 u y τ' hτ' hu hau hy w (dl a)
          (le_trans hτa (hdl a)) hw (haw (dl a) (hdl a) le_rfl)⟩
    /- The incident network: synchronous up to `t₀`, partially synchronous from `b₁`. -/
    have hsync : CommLog.SyncUntil R₁.point R₁.log t₀ := by
      change CommLog.Delivers R₁.point R₁.log (fun a => a + 2 - 1) (fun a => a + 2 - 1) t₀
      refine hdeliv _ _ (fun a => by linarith) fun u o t hr _ w a hta hc hH' hw => ?_
      refine ⟨t + 1, by linarith, hrecv u o t hr w (t + 1) (by linarith) (by linarith) hw ?_⟩
      exact Or.inr (Or.inr (Or.inl (by linarith)))
    have hpsync : CommLog.PSync R₁.point R₁.log b₁ := by
      change CommLog.Delivers R₁.point R₁.log (fun a => max a b₁ + 2 - 1)
        (fun a => max a b₁ + 2 - 1) R₁.point.horizon
      refine hdeliv _ _ (fun a => by linarith [le_max_left a b₁]) fun u o t hr _ w a hta _ hH' hw =>
        ⟨max (t + 1) b₁, ?_, hrecv u o t hr w _ ?_ ?_ hw (Or.inl (le_max_right _ _))⟩
      · exact max_le (by linarith [le_max_left a b₁]) (by linarith [le_max_right a b₁])
      · exact lt_of_lt_of_le (lt_add_one t) (le_max_left _ _)
      · exact le_trans (max_le (by linarith [le_max_left a b₁]) (by linarith [le_max_right a b₁]))
          hH'
    /- In-group synchrony before `b₁`. -/
    have hgroup : GroupSync ((Sys F V).pt ⟨E, R₁⟩) ((Sys F V).log ⟨E, R₁⟩) G b₁ := by
      have hin : ∀ u o t, R₁.releases u o t → u ∉ A → ∀ w, G w = G u → ∀ a, t ≤ a →
          a + 2 - 1 ≤ H → w ∉ A → CommLog.Held R₁.point R₁.log w o (a + 2 - 1) := by
        intro u o t hr hu w hw a hta hah hwA
        refine hheld w o (t + 1) _ (hrecv u o t hr w (t + 1) (by linarith) (by linarith) hwA ?_)
          (by linarith)
        by_cases hwv : G w = G v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (Or.inr fun h => hwv (hw.trans h)))
      refine ⟨?_, ?_, ?_⟩
      · rintro u mm t ⟨o, rfl, hs⟩ hu - - w hw a hta hah hwh -
        rw [show ((Sys F V).pt ⟨E, R₁⟩) = covPoint A x H from hpt1] at hu hah hwh
        exact (Model.sysOf_held_iff R₁ w o _).mpr (by
          rw [show ((Sys F V).pt ⟨E, R₁⟩) = covPoint A x H from hpt1] at *
          exact hin u o t hs hu w hw a hta hah hwh)
      · rintro u mm t ⟨o, rfl, hs⟩ hu - - w hw a hta hah hwh -
        rw [show ((Sys F V).pt ⟨E, R₁⟩) = covPoint A x H from hpt1] at hu hah hwh
        exact (Model.sysOf_held_iff R₁ w o _).mpr (hin u o t hs hu w hw a hta hah hwh)
      · intro u y τ' hτ' _ hu hau hy w _ a hτa _ hw haw
        exact ⟨a + 2 - 1, by linarith, le_rfl,
          Model.Run.eagerTxDelivery_iff.mp htx1 u y τ' hτ' hu hau hy w (a + 2 - 1)
            (by linarith) hw (haw _ (by linarith) le_rfl)⟩
    /- The cross-group message held to `b₁`. -/
    obtain ⟨w, hwA, hwG⟩ : ∃ w, w ∉ A ∧ G w ≠ G v := by
      by_cases h : G v = G v₁
      · exact ⟨x, hxA, fun h' => hx (h'.trans h)⟩
      · exact ⟨v₁, hv₁A, fun h' => h h'.symm⟩
    have hhonH : ∀ u, u ∉ A →
        ((Sys F V).pt ⟨E, R₁⟩).HonestAt u ((Sys F V).pt ⟨E, R₁⟩).horizon := fun u hu => by
      change R₁.point.HonestAt u R₁.point.horizon
      rw [hpt1]; exact hu
    have hexer : Exercised (Sys F V) q.a t₀ b₁ ⟨E, R₁⟩ := by
      refine ⟨?_, ?_, v, w, ⟨E, m⟩, t₀, fun h => hwG h.symm, ⟨m, rfl, hrel1⟩, ?_, ?_, le_rfl, ?_,
        ?_, ?_, ?_⟩
      · cases hb : G v₁
        · exact ⟨x, by simpa [hb] using hx, hhonH x hxA⟩
        · exact ⟨v₁, hb, hhonH v₁ hv₁A⟩
      · cases hb : G v₁
        · exact ⟨v₁, hb, hhonH v₁ hv₁A⟩
        · exact ⟨x, by simpa [hb] using hx, hhonH x hxA⟩
      · change R₁.point.HonestAt v t₀
        rw [hpt1]; exact hvA
      · intro h
        exact hnfg (pubOf E) k rl hdr cs hrole ((Model.sysOf_log_fgAtt R₁ m).mp h)
      · change t₀ + 2 ≤ b₁
        linarith
      · change R₁.point.HonestAt w b₁
        rw [hpt1]; exact hwA
      · intro u _ _
        rfl
      · intro d hd h
        obtain ⟨t', ht'd, hsr, -⟩ := (Model.sysOf_held_iff R₁ w m d).mp h
        rcases hsr with hsr | hsr
        · exact hwG (by rw [honly R₁ hk1 hsr])
        · exact hnorecv w hwG t' (lt_of_le_of_lt ht'd hd) hsr
    have hprog1 : ∀ s e, (Sys F V).prog (shapeProgress F V) K cap i s e ⟨E, R₁⟩ := by
      intro s e
      change (Sys F V).prog (shapeProgress F V) K cap i s e
        ⟨E, base.withEvents (base.policyEvents pol)⟩
      rw [Model.Run.withEvents_eq]
      exact covPoint_holds (u := x) (H := H) F K key h2 hf cap i hadmA hv₁A _ s e
    have hb₁ : 0 ≤ b₁ := by linarith
    refine ⟨⟨E, R₁⟩, t₀, b₁, hv1, hnc _, ⟨⟨⟨(Model.sysOf_delivers_iff R₁ _ _ _).mpr hsync,
      (Model.sysOf_delivers_iff R₁ _ _ _).mpr hpsync⟩, hgroup⟩, by linarith, ?_, ?_,
      fullAwake_of_covPoint F ⟨E, R₁⟩ hpt1, ?_⟩, hprog1 _ _, ?_, ?_, hexer,
      heal_active F K hb₁ hxA hv₁A hx1 (hs q) (hl q) (lat q) (hHge b₁ (by linarith))
        ⟨E, R₁⟩ hpt1⟩
    · change b₁ - t₀ ≤ (L : Time) * 2
      linarith
    · change R₁.point.faultCount R₁.point.horizon ≤ f
      rw [hpt1, covPoint_faultCount, hAc]
    · change (2 : Time) ≤ (K.params.fgDelay : Time) * 2
      have : (1 : Time) ≤ K.params.fgDelay := by exact_mod_cast hfg
      linarith
    · change b₁ - t₀ = (L : Time) * 2
      ring
    · change R₁.point.faultCount R₁.point.horizon = f
      rw [hpt1, covPoint_faultCount, hAc]
  by_cases htick : (base.withEvents (base.front (base.stages 0 n₀) t₀)).releases v m t₀
  · exact main t₀ (Or.inl ⟨rfl, htick⟩)
  · exact main (t₀ + 1) (Or.inr ⟨rfl, htick⟩)

end Consensus.Comparison

end
