module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.ArmingRows
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Viable
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the arming over AC traces: the slow locks of the cohort

The arming of `Obligations/OutageArmingSteps` (`armed_first_update`, `armed_lock_formed`,
`armed_lock_cover`) over an AC trace of the SA with the unlock given at a write mode of width `k`
(`ACRunU wm u`, `wm.width = k`), under trivial frames, the tick duty, the deadline-cut service
before `b` and the pre-`b` frontier:

* `OriginWithinAC.ts_le`: an origin within `T` of label `σ` started by `T`;
* the restarts of a node awake on `[a, z]` up to `z` are at or before every public time of
  `[a, z]` (`restart_le_publicAC`), hence by `a + Δ` (`restart_le_of_awakeAC`, the composite
  `restart_le_of_awake`), and the node runs the update of every slot it is awake for
  (`update_of_awakeOnAC`);
* **the first armed update** (`armed_first_updateAC`): its result extends the origin `C`, which
  is in its frame, and every saved attestation of its slow test names a frame block above `C`
  (Lemma P at each slot of the window, `update_result_extends_preAC`);
* **no live lock conflicts with `C`** at an update whose node's lock origins are compatible with
  `C` (`not_conflicts_of_originsAC`): every stored lock sits below an origin of its slot
  (`lock_below_originU`), and under trivial frames every lock block is its own viable ancestor;
* **the label-`(j₀ − 1)` lock** (`armed_lock_prevAC`, after `armed_lock_formed`): an update within
  `b` reads only locks of origins within `b`, compatible with `C` by the frontier;
* **the label-`j₀` lock** (`armed_lock_coverAC`, after `armed_lock_cover`): an update after `b`
  whose votes are delivered by `t_s + 2Δ ≤ b`. A lock origin after `b` before the first update is
  an optimistic selection of slot `s` (an honest seat's slot-`s` vote, cast within `b`, extends
  `C` by the frontier) or of slot `s + 1` (a seat outside `Opp` is in `Hold`, whose votes extend
  `C` by (N)); a result is excluded by the first update. So `C` itself conflicts with no live lock,
  and the slow lock is written whether or not the result is vetoed. The composite's veto analysis
  of the result (`cover_gate_veto_above`) is not needed. -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-- (A2) **An origin within `T` started by `T`**: its label's start `t_σ` is at or before `T`. -/
theorem OriginWithinAC.ts_le (hr : ACLocalRunU wm u H U tr) {C : Blk sp.n FGP} {σ : Nat}
    {T : Time} (h : OriginWithinAC tr H C σ T) : sp.ts σ ≤ T := by
  obtain ⟨x, -, i, CV, hi, ⟨ℓ, hu, -⟩ | ⟨ℓ, A, -, hs, -⟩⟩ := originWithinAC_iff.1 h
  · have ht : tr.time i = sp.ts σ + 6 * sp.Δ := hu.2.2.1
    have := sp.toParams.hΔ
    linarith
  · exact ((ts_le_iff_le_slot sp (hr.time_nonneg i) σ).2 (by rw [hs])).trans hi

/-! ### Trivial frames -/

/-- Under trivial frames the frames of a node's calls grow. -/
theorem trivial_tree_subsetAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    {y : Fin sp.n} (hy : y ∈ H) {c c' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (hc' : tr.CallAt y c' ℓ') (hcc : c ≤ c') :
    ℓ.frame.tree ⊆ ℓ'.frame.tree := by
  obtain ⟨-, -, -, ht⟩ := htriv y hy c ℓ hc
  obtain ⟨-, -, -, ht'⟩ := htriv y hy c' ℓ' hc'
  rw [ht, ht', trivial_F_eqAC hr htriv hy hy hc hc']
  exact Set.insert_subset_insert fun B ⟨k, hk, hB⟩ => ⟨k, hk.trans hcc, hB⟩

/-- Under trivial frames every block of an honest call's frame is viable, and its own viable
ancestor. -/
theorem trivial_viable_selfAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree) :
    B ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ ℓ.frame.viableAncestor B = B := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hy hc
  obtain ⟨-, hfc, hvh, -⟩ := htriv y hy k ℓ hc
  have hv : B ∈ ℓ.frame.viableTree ℓ.frame.tree := by
    refine ⟨hB, ?_, B, hB, ?_, Relation.ReflTransGen.refl⟩
    · rw [hfc]; exact hΦ.rooted.2 B hB
    · rw [hvh]; exact hB
  exact ⟨hv, viableAncestor_self hΦ hB (Or.inl hv)⟩

/-! ### Restarts and updates of a node awake on a window -/

/-- **(R1) Awake on `[a, z]`**: every restart up to `z` is at or before every public
`τ ∈ [a, z]`, `τ ≥ 0`: the node ticks at `τ`, and a later restart would follow a sleep after
the tick, inside the window. -/
theorem restart_le_publicAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {y : Fin sp.n} (hy : y ∈ H) {a z τ : Time} (haw : ∀ t, a ≤ t → t ≤ z → tr.awake y t)
    (haτ : a ≤ τ) (hτz : τ ≤ z) (hτ0 : 0 ≤ τ) (hpub : sp.toParams.IsPublic τ) {k : Nat}
    (hk : tr.RestartAt y k) (hkz : tr.time k ≤ z) : tr.time k ≤ τ := by
  by_contra hgt
  push Not at hgt
  obtain ⟨ℓk, hck, hrk⟩ := hk
  obtain ⟨v, -, hvk, hs, hb⟩ := hr.sleep_of_restart y hy k ℓk hck hrk
  obtain ⟨j, ℓj, hcj, -, htj⟩ := htick y hy τ hτ0 hpub (haw τ haτ hτz)
  have hjk : j < k := by
    by_contra hkj
    have := hr.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk ℓj hcj
  exact hs (haw v (by linarith) (by linarith))

/-- **A restart of a node awake on `[a, z]`** at a time `≤ z` is by `a + Δ` (the composite
`restart_le_of_awake`): the node ticks at the first public time from `a`. -/
theorem restart_le_of_awakeAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {y : Fin sp.n} (hy : y ∈ H) {a z : Time} (ha0 : 0 ≤ a)
    (haw : ∀ t, a ≤ t → t ≤ z → tr.awake y t) {k : Nat} (hk : tr.RestartAt y k)
    (hkz : tr.time k ≤ z) : tr.time k ≤ a + sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hlt
  push Not at hlt
  set p := a + (-a) % sp.Δ with hp
  have hm0 : 0 ≤ (-a) % sp.Δ := Int.emod_nonneg _ hΔ.ne'
  have hm1 : (-a) % sp.Δ < sp.Δ := Int.emod_lt_of_pos _ hΔ
  have hpub : sp.toParams.IsPublic p :=
    ⟨-((-a) / sp.Δ), by rw [hp, Int.emod_def]; ring⟩
  have := restart_le_publicAC hr htick hy haw (τ := p) (by linarith) (by linarith) (by linarith)
    hpub hk hkz
  linarith

/-- The slot of an update's time is the next slot. -/
theorem slot_updateAC {x : Fin sp.n} {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hu : UpdateAt tr x c s ℓ) : sp.slot (tr.time c) = s + 1 := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h6 := update_timeAC hu
  exact slot_of_mem sp (s + 1) (by rw [h6]; linarith) (by rw [h6, ts_succ (s + 1)]; linarith)

/-- **A node awake on `[a, z]` with `a ≤ t_r` runs the update of every slot `q ≥ r`** whose update
is by `z`: it ticks there, joined (its restarts up to `z` are at or before `t_r`). -/
theorem update_of_awakeOnAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {w : Fin sp.n} (hw : w ∈ H) {a z : Time} (haw : ∀ t, a ≤ t → t ≤ z → tr.awake w t)
    {r q : Nat} (ha : a ≤ sp.ts r) (hrq : r ≤ q) (hqz : sp.ts q + 6 * sp.Δ ≤ z) :
    ∃ c ℓ, UpdateAt tr w c q ℓ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hrq' := ts_le_tsAC (sp := sp) hrq
  have h0 := ts_nonnegAC (sp := sp) r
  obtain ⟨c, ℓ, hc, hcall, htc⟩ := htick w hw (sp.ts q + 6 * sp.Δ) (by linarith)
    (Dvd.intro (4 * (q : Int) + 6) (by simp only [SAParams.ts]; ring))
    (haw _ (by linarith) hqz)
  refine ⟨c, ℓ, hc, hcall, htc, ?_⟩
  have hsl : sp.slot (tr.time c) = q + 1 := by
    rw [htc]
    exact slot_of_mem sp (q + 1) (by rw [ts_succ]; linarith)
      (by rw [ts_succ (q + 1), ts_succ]; linarith)
  change (tr.state w c).restartTime ≤
    ((sp.ts ((sp.slot (tr.time c) : Int) - 1) : Time) : WithBot Time)
  rw [hsl, show (((q + 1 : Nat) : Int) - 1) = (q : Int) by push_cast; ring]
  rcases restartTime_stateU hr hw c with h | ⟨k, hk, hrk, h⟩
  · rw [h]; exact bot_le
  · rw [h]
    refine WithBot.coe_le_coe.2 ((restart_le_publicAC hr htick hw haw ha (by linarith) h0
      (Dvd.intro (4 * (r : Int)) (by simp only [SAParams.ts]; ring)) hrk
      ((hr.time_mono hk.le).trans (htc ▸ hqz))).trans hrq')

/-! ### The first armed update -/

/-- **The first armed update** of slot `s` of a node `w` awake on `[a, z]`, with
`a ≤ t_{s−k+1}`, `t_s + 6Δ ≤ z` and the slot's votes delivered by `t_s + 2Δ ≤ b`: it exists; the
origin `C` (within `b`, of a label `σ ≤ s − k`) is in its frame below its result; and every saved
attestation of the slow test names a block of the frame above `C`. -/
theorem armed_first_updateAC (hrun : ACRunU wm u proposer tr H U) (htriv : TrivialFrames tr H)
    (htick : TickDuty tr H) (hsy : SyncUntilAC tr H U b) (hfr : FrontierAC tr H U b)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → FaultBound tr H (sp.ts q + sp.Δ))
    {C : Blk sp.n FGP} {σ : Nat} (hC : OriginWithinAC tr H C σ b) {w : Fin sp.n} (hw : w ∈ H)
    {a z : Time} (haw : ∀ t, a ≤ t → t ≤ z → tr.awake w t) {s : Nat} (hks : sp.k ≤ s)
    (hσs : σ + sp.k ≤ s) (ha : a ≤ sp.ts ((s : Int) - sp.k + 1))
    (hsz : sp.ts s + 6 * sp.Δ ≤ z) (hsb : sp.ts s + 2 * sp.Δ ≤ b) :
    ∃ c ℓ, UpdateAt tr w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ UpdateAt tr w k s ℓ') ∧
      C ∈ ℓ.frame.tree ∧
      (∃ D, getConfirmation sp (tr.state w c) ℓ.frame s = some D ∧ ℓ.frame.Anc C D) ∧
      ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ ℓ.frame.tree,
        (tr.state w c).saved j = some S.root ∧ ℓ.frame.Anc C S := by
  classical
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hrI : ((s - sp.k + 1 : Nat) : Int) = (s : Int) - sp.k + 1 := by omega
  have ha' : a ≤ sp.ts (s - sp.k + 1 : Nat) := by rw [hrI]; exact ha
  have hτs : sp.ts (s - sp.k + 1 : Nat) ≤ sp.ts s := ts_le_tsAC (by omega)
  have h0 := ts_nonnegAC (sp := sp) (s - sp.k + 1)
  have hpub : sp.toParams.IsPublic (sp.ts (s - sp.k + 1 : Nat)) :=
    Dvd.intro (4 * ((s - sp.k + 1 : Nat) : Int)) (by simp only [SAParams.ts]; ring)
  -- the restarts of `w` up to `z` are at or before `t_{s−k+1}`
  have hnr : ∀ k, tr.RestartAt w k → tr.time k ≤ z → tr.time k ≤ sp.ts (s - sp.k + 1 : Nat) :=
    fun k hk hkz => restart_le_publicAC hr htick hw haw ha' (by linarith) h0 hpub hk hkz
  have hex₀ : ∃ c, ∃ ℓ, UpdateAt tr w c s ℓ :=
    update_of_awakeOnAC hr htick hw haw ha' (by omega) hsz
  obtain ⟨ℓ, hu⟩ := Nat.find_spec hex₀
  have hfirst : ∀ k < Nat.find hex₀, ∀ ℓ', ¬ UpdateAt tr w k s ℓ' :=
    fun k hk ℓ' h => Nat.find_min hex₀ hk ⟨ℓ', h⟩
  have htc : tr.time (Nat.find hex₀) = sp.ts s + 6 * sp.Δ := hu.2.2.1
  -- Lemma P at every update of a slot in `(σ, s]`
  have hP : ∀ q, σ < q → q ≤ s → ∀ k ℓ', UpdateAt tr w k q ℓ' → C ∈ ℓ'.frame.tree ∧
      ∃ R, getConfirmation sp (tr.state w k) ℓ'.frame q = some R ∧ ℓ'.frame.Anc C R :=
    fun q hq hqs k ℓ' hu' => by
      have := ts_le_tsAC (sp := sp) hqs
      exact update_result_extends_preAC hrun htriv htick hsy hfr hC hw hq hu' (by linarith)
        (hfb q (by linarith))
  obtain ⟨hCt, hD⟩ := hP s (by omega) le_rfl _ ℓ hu
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hu.1
  refine ⟨Nat.find hex₀, ℓ, hu, hfirst, hCt, hD, fun j hj₁ hj₂ => ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q : Nat, j = q := ⟨j.toNat, by omega⟩
  have hq₂ : q < s := by exact_mod_cast hj₂
  have hqk : s - sp.k + 1 ≤ q := by omega
  have hqs : sp.ts q + 4 * sp.Δ ≤ sp.ts s := by
    have := ts_le_tsAC (sp := sp) (show q + 1 ≤ s by omega)
    rw [ts_succAC] at this
    linarith
  -- the update of slot `q`, before the first update of slot `s`
  obtain ⟨k₀, ℓ₀, hu₀⟩ := update_of_awakeOnAC hr htick hw haw ha' hqk (by linarith)
  have hk₀t : tr.time k₀ = sp.ts q + 6 * sp.Δ := hu₀.2.2.1
  have hk₀ : k₀ < Nat.find hex₀ := by
    by_contra h
    have := hr.time_mono (not_lt.1 h)
    linarith
  -- no restart of `w` after `k₀` up to the update
  have hlow : sp.ts (s - sp.k + 1 : Nat) ≤ sp.ts q := ts_le_tsAC hqk
  have hnr' : ∀ i, k₀ < i → i ≤ Nat.find hex₀ → ¬ tr.RestartAt w i := by
    intro i hi hic hri
    have h1 := hnr i hri ((hr.time_mono hic).trans (by linarith))
    have h2 := hr.time_mono hi.le
    linarith
  -- `saved[q]` stays set from the update `k₀` on
  have hsome : ∀ i, k₀ + 1 ≤ i → i ≤ Nat.find hex₀ → ((tr.state w i).saved q).isSome := by
    intro i hi hic
    induction i, hi using Nat.le_induction with
    | base =>
      rw [saved_after_updateAC hr hw hu₀, Function.update_self]
      obtain ⟨-, R, hR, -⟩ := hP q (by omega) hq₂.le k₀ ℓ₀ hu₀
      rw [hR]
      rfl
    | succ i hi ih =>
      rcases saved_step_of_not_restartAC hr hw i q (hnr' i (by omega) (by omega)) with
        h | ⟨ℓ', hu', h⟩
      · rw [h]; exact ih (by omega)
      · obtain ⟨-, R, hR, -⟩ := hP q (by omega) hq₂.le i ℓ' hu'
        rw [h, hR]
        rfl
  obtain ⟨r, hrs⟩ := Option.isSome_iff_exists.1 (hsome _ hk₀ le_rfl)
  obtain ⟨k', hk', C', CV, ⟨ℓ', hu', hC', -⟩, hC'r⟩ := saved_resultU hr hw _ q hrs
  obtain ⟨-, R, hR, hCR⟩ := hP q (by omega) hq₂.le k' ℓ' hu'
  rw [hR] at hC'
  obtain rfl : R = C' := Option.some.inj hC'
  have hRt : R ∈ ℓ.frame.tree :=
    trivial_tree_subsetAC hr htriv hw hu'.1 hu.1 hk'.le (deepest_mem hR).1.1
  obtain ⟨-, hΦU'⟩ := frameIn_of_callAtU hr hw hu'.1
  refine ⟨R, hRt, ?_, anc_tree_of_anc_U hU hΦ hΦU hCt (hCR.mono hΦU') hRt⟩
  rw [hrs, hC'r]

/-! ### No live lock conflicts with the origin -/

/-- **`C` conflicts with no live lock** at an honest call whose node's lock origins (the results
and optimistic selections of the node at earlier cuts) are compatible with `C`, under trivial
frames: every stored lock sits below an origin of its slot, and every lock block is its own
viable ancestor. -/
theorem not_conflicts_of_originsAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    {w : Fin sp.n} (hw : w ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt w c ℓ) {t : Time} {C : Blk sp.n FGP} (hCt : C ∈ ℓ.frame.tree)
    (hO : ∀ m O, ∀ k < c, ∀ CV, (ResultAt tr w k m O CV ∨ OptimisticLockAt tr w k m O CV) →
      Compatible U O C) :
    ¬ conflictsWithLock sp (tr.state w c).locks ℓ.frame t C := by
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hc
  rintro ⟨W, hW, hCW⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := mem_liveLockBlocks hΦ hW
  rw [(trivial_viable_selfAC hr htriv hw hc hB₀).2] at hCW
  obtain ⟨L, hL, hLr, O, hLO, k, hk, CV, hO'⟩ := lock_below_originU hr hw c l hl
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  rcases compatible_of_ancAC hU hLO (hO l.slot O k hk CV hO') with h | h
  · exact hCW (Or.inr (anc_tree_of_anc_U hU hΦ hΦU hB₀ h hCt))
  · exact hCW (Or.inl (anc_tree_of_anc_U hU hΦ hΦU hCt h hB₀))

/-! ### The two locks -/

/-- **The label-`s` lock at an update within `b`** (the composite `armed_lock_formed`, for the
label `j₀ − 1`): the first update of slot `s` of a node awake on `[a, z]`, at a time
`t_s + 6Δ ≤ b`, stores a lock of slot `s` and expiry `s + k` on a block of its frame above the
origin `C` (not genesis). Its node's lock origins are within `b`, so compatible with `C`. -/
theorem armed_lock_prevAC (hrun : ACRunU wm u proposer tr H U) (hwk : wm.width = sp.k)
    (htriv : TrivialFrames tr H) (htick : TickDuty tr H) (hsy : SyncUntilAC tr H U b)
    (hfr : FrontierAC tr H U b)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → FaultBound tr H (sp.ts q + sp.Δ))
    {C : Blk sp.n FGP} {σ : Nat} (hC : OriginWithinAC tr H C σ b)
    (hCg : C.root ≠ sp.genesisRoot) {w : Fin sp.n} (hw : w ∈ H) {a z : Time}
    (haw : ∀ t, a ≤ t → t ≤ z → tr.awake w t) {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 6 * sp.Δ ≤ b) :
    ∃ c ℓ, UpdateAt tr w c s ℓ ∧ ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc C L ∧
      (⟨L.root, s, f, s + sp.k⟩ : Lock) ∈ (tr.state w (c + 1)).locks := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  obtain ⟨c, ℓ, hu, -, hCt, ⟨D, hD, hCD⟩, hrows⟩ :=
    armed_first_updateAC hrun htriv htick hsy hfr hfb hC hw haw hks hσs ha hsz (by linarith)
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hw hu.1
  have hnvC := not_conflicts_of_originsAC hr htriv hw hu.1 (t := tr.time c) hCt
    fun m O k hk CV hO' => hfr.origins_compatible O m C σ
      (originWithinAC_iff.2 ⟨w, hw, k, CV, (hr.time_mono hk.le).trans (htc ▸ hsb), hO'⟩) hC
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by rw [slot_updateAC hu]; omega
  obtain ⟨L, hL, hCL, hl⟩ := updateConfirmationM_slow_lock_effective hwk hΦ hD hnvC hCt hCg hCD
    hrows hlive (Or.inr (trivial_viable_selfAC hr htriv hw hu.1 hCt).1)
  exact ⟨c, ℓ, hu, L, false, hL, hCL, by rw [state_after_updateAC hr hw hu]; exact hl⟩

/-- **The label-`s` lock at the cover gate** (the composite `armed_lock_cover`, for the label
`j₀`): the first update of slot `s` of a node awake on `[a, z]`, whose slot's votes are
delivered by `t_s + 2Δ ≤ b` but which may itself be after `b`. Given (VA) `C` a candidate and (N)
the `Hold` votes of slot `s + 1` before it extending `C`, it stores a lock of slot `s` and expiry
`s + k` above the origin `C` (not genesis). `Opp` contains the faulty validators, `2·|Opp| < n`,
and every honest slot-`(s + 1)` voter by `t_s + 6Δ` is in `Hold` or `Opp`. -/
theorem armed_lock_coverAC (hrun : ACRunU wm u proposer tr H U) (hwk : wm.width = sp.k)
    (htriv : TrivialFrames tr H) (htick : TickDuty tr H) (hsy : SyncUntilAC tr H U b)
    (hfr : FrontierAC tr H U b)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → FaultBound tr H (sp.ts q + sp.Δ))
    {C : Blk sp.n FGP} {σ : Nat} (hC : OriginWithinAC tr H C σ b)
    (hCg : C.root ≠ sp.genesisRoot) {w : Fin sp.n} (hw : w ∈ H) {a z : Time}
    (haw : ∀ t, a ≤ t → t ≤ z → tr.awake w t) {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b) (Hold Opp : Set (Fin sp.n)) (hF : Hᶜ ⊆ Opp)
    (hopp : 2 * Opp.ncard < sp.n)
    (hcast : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = s + 1 →
      tr.time j ≤ sp.ts s + 6 * sp.Δ → x ∈ Hold ∨ x ∈ Opp) :
    ∃ c ℓ, UpdateAt tr w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ UpdateAt tr w k s ℓ') ∧
      (ℓ.frame.AncestorCandidate C →
        (∀ x ∈ Hold, ∀ j e, VoteAt tr x j e → e.msg.slot = s + 1 → j < c →
          VoteExtends U e.msg C) →
        ∃ L f, ℓ.frame.Anc C L ∧
          (⟨L.root, s, f, s + sp.k⟩ : Lock) ∈ (tr.state w (c + 1)).locks) := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hf : 2 * Hᶜ.ncard < sp.n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hF (Set.toFinite _))) hopp
  obtain ⟨c, ℓ, hu, hfirst, hCt, ⟨D, hD, hCD⟩, hrows⟩ :=
    armed_first_updateAC hrun htriv htick hsy hfr hfb hC hw haw hks hσs ha hsz hsb
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  refine ⟨c, ℓ, hu, hfirst, fun hcand hN => ?_⟩
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hw hu.1
  -- the node's lock origins before the update are compatible with `C`
  have hOC : ∀ m O, ∀ k < c, ∀ CV, (ResultAt tr w k m O CV ∨ OptimisticLockAt tr w k m O CV) →
      Compatible U O C := by
    intro m O k hk CV hO'
    have hkc := hr.time_mono hk.le
    by_cases hkb : tr.time k ≤ b
    · exact hfr.origins_compatible O m C σ (originWithinAC_iff.2 ⟨w, hw, k, CV, hkb, hO'⟩) hC
    push Not at hkb
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · -- a result after `b` before the update is of slot `s`, excluded by the first update
      exfalso
      have hk' : tr.time k = sp.ts m + 6 * sp.Δ := hu'.2.2.1
      have e1 : sp.ts ((s : Int) - 1) = sp.ts s - 4 * sp.Δ := by simp only [SAParams.ts]; ring
      have h1 := (ts_lt_iff sp).1 (show sp.ts ((s : Int) - 1) < sp.ts m by rw [e1]; linarith)
      have h2 := (ts_le_iff sp).1 (show sp.ts m ≤ sp.ts s by linarith)
      obtain rfl : m = s := by omega
      exact hfirst k hk ℓ' hu'
    -- an optimistic selection after `b`: of slot `s` or `s + 1`
    obtain ⟨ℓo, A, hpt, hΦoU, h34, -⟩ := optimistic_sideU hrun hw hopt
    obtain ⟨-, -, -, hsl, -⟩ := hopt
    have hms : s ≤ m := by
      rw [← hsl]
      exact_mod_cast (ts_le_iff_le_slot sp (hr.time_nonneg k) s).1 (by linarith)
    have hm1 : m ≤ s + 1 := by
      by_contra h
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k) ((s + 2 : Nat) : Int)).2
        (by rw [hsl]; push_cast; omega)
      rw [ts_succ₂AC] at this
      linarith
    rcases Nat.lt_or_ge m (s + 1) with hm | hm
    · -- slot `s`: an honest seat's vote is cast within `b`, so it extends `C`
      obtain rfl : m = s := by omega
      obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hOR⟩, hxH⟩ :=
        Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
          (t := optimisticVoters sp A ℓo.frame m O) (by omega)
      have hxH : v.val ∈ H := not_not.1 hxH
      obtain ⟨hvs, j, -, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hw hpt hv hxH
      obtain ⟨-, hte⟩ := ts_le_castAC hr hxH hve
      rw [hvs] at hte
      obtain ⟨Hd, hHdU, hHdr, hCHd⟩ := hfr.vote_extends C σ hC _ hxH j e hve (by linarith)
        (by rw [hvs]; omega)
      obtain rfl : R = Hd := hU.1 (hΦoU hR) hHdU (hRr.trans hHdr.symm)
      exact anc_total hU (hOR.mono hΦoU) hCHd
    · -- slot `s + 1`: a seat outside `Opp` is in `Hold`, whose votes extend `C`
      obtain rfl : m = s + 1 := by omega
      obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hOR⟩, hxO⟩ :=
        Set.exists_mem_notMem_of_ncard_lt_ncard (s := Opp)
          (t := optimisticVoters sp A ℓo.frame (s + 1) O) (by omega)
      have hxH : v.val ∈ H := by
        by_contra h
        exact hxO (hF h)
      obtain ⟨hvs, j, hjk, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hw hpt hv hxH
      have hjt : tr.time j ≤ sp.ts s + 6 * sp.Δ := (hr.time_mono hjk).trans (htc ▸ hkc)
      rcases hcast _ hxH j e hve hvs hjt with hH | hO
      · obtain ⟨Hd, hHdU, hHdr, hCHd⟩ := hN _ hH j e hve hvs (by omega)
        obtain rfl : R = Hd := hU.1 (hΦoU hR) hHdU (hRr.trans hHdr.symm)
        exact anc_total hU (hOR.mono hΦoU) hCHd
      · exact absurd hO hxO
  have hnvC := not_conflicts_of_originsAC hr htriv hw hu.1 (t := tr.time c) hCt hOC
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by rw [slot_updateAC hu]; omega
  obtain ⟨L, -, hCL, hl⟩ := updateConfirmationM_slow_lock_effective hwk hΦ hD hnvC hCt hCg hCD
    hrows hlive hcand
  exact ⟨L, false, hCL, by rw [state_after_updateAC hr hw hu]; exact hl⟩

end Consensus.Goldilocks.Comparison

end
