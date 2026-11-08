module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: the outage counts over AC traces

The restatable count rows of the outage lock-safety argument (`Obligations/OutageLockSafety`,
`Compose/Regimes/OutageMajority`, `Obligations/OutageS5`), read on an AC trace of the SA with the
unlock given at a write mode (`ACLocalRunU wm u`, `ACRunU wm u`), with ancestry inside `U` and
each premise an explicit hypothesis. No lemma reads the write width.

* compatibility through a vote head inside a coherent `U`, for any FG payload type
  (`compatible_of_head_ancAC`, `compatible_of_voteCompatAC`, `compatible_of_ancAC`);
* N6 from the cohort margin (`two_mul_ltAC`; `CohortOnAC.two_mul_lt` at the window's cohort and
  late wakers);
* an honest cast lies in `[t_s, t_s + Δ]` of its slot (`ts_le_castAC`);
* a result's counted validators meet a participant set (`exists_counted_of_participantsAC`); a
  counted honest vote was cast before the update, of its slot, with a head above the result
  (`counted_honest_voteAC`); the result is in `U` (`result_memAC`);
* a cohort member is awake and joined at `t_m + Δ` for `m ∈ [j₀ + 1, j₀ + k]`
  (`cohort_readyAC`);
* a held honest vote across a call was cast (`held_vote_castAC`), and so was a counted honest vote
  of a fast lock, at a cut no later than the lock's (`fastLock_honest_voteAC`);
* the extending majority at a label (`ExtendingCastersAC`, `OpponentsAC`, `ExtendingMajorityAC`,
  their characterisations, `ExtendingMajorityAC.anti`), from unanimity and the fault bound (L4,
  `extendingMajorityAC_of_all`), and at the first restored label `r` from the cohort
  (`restored_majority_at_rAC`, with the cohort's slot-`r` votes extending `P` as a hypothesis). -/

namespace Consensus.Goldilocks.Comparison

open SA
open Compose (VoteCompat voteCompat_iff)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-! ### Compatibility through a vote head -/

/-- A block below a block compatible with `B` is compatible with `B`. -/
theorem compatible_of_head_ancAC (hU : Coherent U) {C R B : Blk sp.n FGP} (hCR : Anc U C R)
    (hR : Compatible U R B) : Compatible U C B := by
  rcases hR with h | h
  · exact Or.inl (hCR.trans h)
  · exact Anc.total hU hCR h

/-- A vote compatible with `B` whose head extends `C` makes `C` compatible with `B`. -/
theorem compatible_of_voteCompatAC (hU : Coherent U) {v : Vote sp.n} {C R B : Blk sp.n FGP}
    (hR : R ∈ U) (hRr : R.root = v.head) (hCR : Anc U C R) (hv : VoteCompat U v B) :
    Compatible U C B := by
  obtain ⟨Hd, hHd, hHdr, hHdB⟩ := voteCompat_iff.1 hv
  obtain rfl : Hd = R := hU.1 hHd hR (hHdr.trans hRr.symm)
  exact compatible_of_head_ancAC hU hCR hHdB

/-- An ancestor of a block compatible with `B` is compatible with `B`. -/
theorem compatible_of_ancAC (hU : Coherent U) {L C B : Blk sp.n FGP} (hLC : Anc U L C)
    (hC : Compatible U C B) : Compatible U L B :=
  compatible_of_head_ancAC hU hLC hC

/-! ### N6 from the cohort margin -/

/-- **N6**: a set `A` of honest validators disjoint from `W` and outnumbering `Hᶜ ∪ W` gives
`2·|Hᶜ ∪ W| < n`. -/
theorem two_mul_ltAC {A W : Set (Fin sp.n)} (hA : A ⊆ H) (hAW : Disjoint A W)
    (hc : (Hᶜ ∪ W).ncard < A.ncard) : 2 * (Hᶜ ∪ W).ncard < sp.n := by
  have hdisj : Disjoint A (Hᶜ ∪ W) := by
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (hA hx), hAW⟩
  have h1 := Set.ncard_union_eq hdisj
  have h2 : (A ∪ (Hᶜ ∪ W)).ncard ≤ sp.n := by
    calc (A ∪ (Hᶜ ∪ W)).ncard ≤ (Set.univ : Set (Fin sp.n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = sp.n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- N6 at the cohort margin of a window: the cohort awake at `a` and the late wakers of `[a, b]`
are disjoint honest sets. -/
theorem CohortOnAC.two_mul_lt {a b : Time} (h : CohortOnAC tr H a b) :
    2 * (Hᶜ ∪ lateWakersAC tr H a b).ncard < sp.n :=
  two_mul_ltAC (A := awakeAtAC tr H a) (fun _ hy => hy.1)
    (Set.disjoint_left.2 fun _ hy hw => hw.2 hy) h

/-! ### Casts, results and counted votes -/

/-- The cast of an honest vote is in `[t_s, t_s + Δ]` of its slot `s`. -/
theorem ts_le_castAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e : Em sp FGP} (hv : VoteAt tr x k e) :
    sp.ts e.msg.slot ≤ tr.time k ∧ tr.time k ≤ sp.ts e.msg.slot + sp.Δ := by
  obtain ⟨ℓ, hc, he⟩ := hv
  have hsl := (castAt_specU hr hx ⟨hc, he⟩).2.1
  refine ⟨(ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [hsl]), ?_⟩
  have := vote_time_leU hr hx ⟨ℓ, hc, he⟩
  rw [hsl]
  exact this

/-- **A result's counted validators meet a participant set.** At an update with result `C`, if
`T` are voters of the update's pool and `|Q| < |T|`, some counted vote is of a validator in `T` or
outside `Q`. -/
theorem exists_counted_of_participantsAC {X : Fin sp.n} {i₀ s : Nat} {C : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hR : ResultAt tr X i₀ s C CV) {T Q : Set (Fin sp.n)}
    (hT : T ⊆ voters {v | v ∈ (tr.state X i₀).pool s}) (hQT : Q.ncard < T.ncard) :
    ∃ v ∈ CV, v.val ∈ T ∨ v.val ∉ Q := by
  by_contra hno
  push Not at hno
  have hmaj := result_majority hR
  obtain ⟨ℓ, -, -, hCV⟩ := hR
  have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ voters {v | v ∈ (tr.state X i₀).pool s} := by
    rintro w ⟨v, hv, rfl⟩
    rw [hCV] at hv
    exact ⟨v, hv.1, rfl⟩
  have hdisj : Disjoint T {w | ∃ v ∈ CV, v.val = w} :=
    Set.disjoint_left.2 fun w hwT ⟨v, hv, hvw⟩ => (hno v hv).1 (hvw ▸ hwT)
  have h1 := Set.ncard_union_eq hdisj
  have h2 := Set.ncard_le_ncard (Set.union_subset hT hSV)
  have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Q.ncard :=
    Set.ncard_le_ncard fun w ⟨v, hv, hvw⟩ => hvw ▸ (hno v hv).2
  omega

/-- A counted vote of an honest validator at an honest update was cast at an earlier cut, of the
update's slot, and its head extends the result inside `U`. -/
theorem counted_honest_voteAC (hrun : ACRunU wm u proposer tr H U) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr X i₀ s C CV)
    {v : Vote sp.n} (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j < i₀, ∃ e, VoteAt tr v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ U, R.root = v.head ∧ Anc U C R := by
  have hr := hrun.localRun
  obtain ⟨ℓ, hu, -, hCV⟩ := hR
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, hj, e, hve, he⟩ := hrun.honest.pool_vote X hX i₀ s v hvp hvH
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hX hu.1
  exact ⟨j, hj, e, hve, he, state_pool_slotU sp hr hX i₀ s v hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- The result of an honest update is in `U`. -/
theorem result_memAC (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr X i₀ s C CV) : C ∈ U := by
  obtain ⟨ℓ, hu, hC, -⟩ := hR
  exact (frameIn_of_callAtU hr hX hu.1).2 (deepest_mem hC).1.1

/-- **The cohort is ready at the labels it protects**: a member of `A₀` is awake and joined at
`t_m + Δ` for a label `m ∈ [j₀ + 1, j₀ + k]` whose slot point some honest call reaches, when `A₀`
is awake throughout `[a, z]`, restarts up to `z` only by `a + Δ ≤ t_{j₀}`, and `z` is at least
every time up to `t_{j₀+k} + Δ` that an honest call reaches. -/
theorem cohort_readyAC {A₀ : Set (Fin sp.n)} {a z : Time} {j₀ : Nat}
    (hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t)
    (hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ)
    (ha : a + sp.Δ ≤ sp.ts j₀)
    (hz : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ →
      (∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ t ≤ tr.time i) → t ≤ z)
    {x : Fin sp.n} (hx : x ∈ A₀) {m : Nat} (hm : j₀ + 1 ≤ m) (hmK : m ≤ j₀ + sp.k)
    (hcall : ∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ sp.ts m + sp.Δ ≤ tr.time i) :
    tr.awake x (sp.ts m + sp.Δ) ∧ JoinedAt tr x (sp.ts m + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj := ts_le_tsAC (sp := sp) (show j₀ ≤ m - 1 by omega)
  have hjm := ts_le_tsAC (sp := sp) (show j₀ ≤ m by omega)
  have hmK' := ts_le_tsAC (sp := sp) hmK
  have hz' := hz (sp.ts m + sp.Δ) (by linarith) hcall
  refine ⟨hA₀awake x hx _ (by linarith) hz', fun k hk hkt => ?_⟩
  rw [slot_ts_deltaAC m]
  have hm1 : sp.ts ((m : Int) - 1) = sp.ts ((m - 1 : Nat) : Int) := by congr 1; omega
  rw [hm1]
  have := (hA₀join x hx k hk (hkt.trans hz')).trans ha
  linarith

/-- A held honest vote across an honest call was cast by its validator: a vote of the pools
before or after the call, or carried by a block of the call's frame. -/
theorem held_vote_castAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {v : Vote sp.n}
    (hv : v ∈ heldVotes (tr.state y j) (tr.state y (j + 1)) ℓ.frame) (hvH : v.val ∈ H) :
    ∃ k e, VoteAt tr v.val k e ∧ e.msg = v := by
  rcases mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
  · obtain ⟨k, -, e, he, hm⟩ := hrun.honest.pool_vote y hy j τ v hv hvH
    exact ⟨k, e, he, hm⟩
  · obtain ⟨k, -, e, he, hm⟩ := hrun.honest.pool_vote y hy (j + 1) τ v hv hvH
    exact ⟨k, e, he, hm⟩
  · have hvB : v ∈ blockVotes C :=
      hv.elim id fun h => (frame_validPayloadU sp hrun.localRun hy hc C hC).2 v h
    obtain ⟨k, -, e, he, hm⟩ := hrun.honest.carried_vote y hy j ℓ hc C hC v hvB hvH
    exact ⟨k, e, he, hm⟩

/-- A counted vote of an honest validator at an honest fast lock was cast at a cut no later than
the lock's. -/
theorem fastLock_honest_voteAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {j s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr y j s B CV)
    {v : Vote sp.n} (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j' ≤ j, ∃ e, VoteAt tr v.val j' e ∧ e.msg = v := by
  rcases hfl with ⟨ℓ, C, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, -, -, rfl⟩
  · obtain ⟨j', hj', e, hve, he⟩ := hrun.honest.pool_vote y hy j s v hv.1 hvH
    exact ⟨j', hj'.le, e, hve, he⟩
  · obtain ⟨-, j', hj', e, hve, he⟩ := optimisticPoint_pool_voteU hrun hy hpt hv.1 hvH
    exact ⟨j', hj', e, hve, he⟩

/-! ### The extending majority at a label -/

/-- The honest slot-`q` casters whose vote extends `B` inside `U`. -/
def ExtendingCastersAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Set (Fin sp.n) :=
  {x | x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ VoteExtends U e.msg B}

/-- The faulty validators and the honest slot-`q` casters whose vote does not extend `B`. -/
def OpponentsAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Set (Fin sp.n) :=
  Hᶜ ∪ {x | x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ ¬ VoteExtends U e.msg B}

/-- The extending majority: the extending casters of label `q` outnumber its opponents. -/
def ExtendingMajorityAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Prop :=
  (OpponentsAC tr H U B q).ncard < (ExtendingCastersAC tr H U B q).ncard

theorem extendingCastersAC_iff {B : Blk sp.n FGP} {q : Nat} {x : Fin sp.n} :
    x ∈ ExtendingCastersAC tr H U B q ↔
      x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ VoteExtends U e.msg B :=
  Iff.rfl

theorem opponentsAC_iff {B : Blk sp.n FGP} {q : Nat} {x : Fin sp.n} :
    x ∈ OpponentsAC tr H U B q ↔ x ∈ Hᶜ ∨
      (x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ ¬ VoteExtends U e.msg B) :=
  Iff.rfl

theorem extendingMajorityAC_iff {B : Blk sp.n FGP} {q : Nat} :
    ExtendingMajorityAC tr H U B q ↔
      (OpponentsAC tr H U B q).ncard < (ExtendingCastersAC tr H U B q).ncard :=
  Iff.rfl

/-- A vote extending `B` extends every block below `B`. -/
private theorem voteExtends_anti {B B' : Blk sp.n FGP} {v : Vote sp.n} (hBB' : Anc U B' B)
    (h : VoteExtends U v B) : VoteExtends U v B' := by
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := h
  exact ⟨Hd, hHd, hHdr, hBB'.trans hBHd⟩

/-- **Downward monotonicity**: the majority for `B` is a majority for every block below `B`. -/
theorem ExtendingMajorityAC.anti {B B' : Blk sp.n FGP} {q : Nat} (hBB' : Anc U B' B)
    (h : ExtendingMajorityAC tr H U B q) : ExtendingMajorityAC tr H U B' q := by
  rw [extendingMajorityAC_iff] at h ⊢
  have hO : OpponentsAC tr H U B' q ⊆ OpponentsAC tr H U B q := by
    intro x hx
    rcases opponentsAC_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact opponentsAC_iff.2 (Or.inl hx)
    · exact opponentsAC_iff.2 (Or.inr ⟨hx, k, e, hv, hs, fun h => hne (voteExtends_anti hBB' h)⟩)
  have hE : ExtendingCastersAC tr H U B q ⊆ ExtendingCastersAC tr H U B' q := by
    intro x hx
    obtain ⟨hx, k, e, hv, hs, hext⟩ := extendingCastersAC_iff.1 hx
    exact extendingCastersAC_iff.2 ⟨hx, k, e, hv, hs, voteExtends_anti hBB' hext⟩
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (h.trans_le (Set.ncard_le_ncard hE (Set.toFinite _)))

/-- **L4**: when every honest slot-`q` vote extends `B`, the opponents are the faulty validators
and the extending casters hold every honest validator awake and joined at `t_q + Δ` (the tick
duty, `vote_of_awake_joinedAC`), so the fault bound there gives the majority. -/
theorem extendingMajorityAC_of_all (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {B : Blk sp.n FGP} {q : Nat}
    (hall : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = q → VoteExtends U e.msg B)
    (hfb : FaultBound tr H (sp.ts q + sp.Δ)) : ExtendingMajorityAC tr H U B q := by
  rw [extendingMajorityAC_iff]
  have hO : OpponentsAC tr H U B q ⊆ Hᶜ := by
    intro x hx
    rcases opponentsAC_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact hx
    · exact absurd (hall x hx k e hv hs) hne
  have hE : {y | y ∈ H ∧ tr.awake y (sp.ts q + sp.Δ) ∧ JoinedAt tr y (sp.ts q + sp.Δ)} ⊆
      ExtendingCastersAC tr H U B q := by
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joinedAC hr htick hx hw hj
    exact extendingCastersAC_iff.2 ⟨hx, k, e, hv, hs, hall x hx k e hv hs⟩
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (lt_of_lt_of_le hfb (Set.ncard_le_ncard hE (Set.toFinite _)))

/-- **The extending majority at the first restored label `r`**: the cohort `A₀` casts in slot `r`
(it is ready at `t_r + Δ`, `cohort_readyAC`, and votes there, `vote_of_awake_joinedAC`) and its
slot-`r` votes extend `P` (`hvotes`); an honest slot-`r` caster that does not extend `P` casts
within the no-sleep window, so it is in `A₀ ∪ W` and not in `A₀`; hence the opponents lie in
`Hᶜ ∪ W`, fewer than `A₀`. -/
theorem restored_majority_at_rAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {P : Blk sp.n FGP} {A₀ W : Set (Fin sp.n)} {a z : Time} {j₀ r : Nat}
    (hrk : j₀ + 1 ≤ r ∧ r ≤ j₀ + sp.k) (hA₀ : A₀ ⊆ H) (hcohort : (Hᶜ ∪ W).ncard < A₀.ncard)
    (hawake : ∀ x ∈ H, ∀ t, a ≤ t → t ≤ z → tr.awake x t → x ∈ A₀ ∪ W)
    (hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t)
    (hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ)
    (ha : a + sp.Δ ≤ sp.ts j₀)
    (hz : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ →
      (∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ t ≤ tr.time i) → t ≤ z)
    (hvotes : ∀ x ∈ A₀, ∀ k e, VoteAt tr x k e → e.msg.slot = r → VoteExtends U e.msg P)
    (hcall : ∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ sp.ts r + sp.Δ ≤ tr.time i) :
    ExtendingMajorityAC tr H U P r := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rw [extendingMajorityAC_iff]
  have hA : A₀ ⊆ ExtendingCastersAC tr H U P r := by
    intro x hx
    obtain ⟨haw, hjn⟩ := cohort_readyAC hA₀awake hA₀join ha hz hx hrk.1 hrk.2 hcall
    obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joinedAC hr htick (hA₀ hx) haw hjn
    exact extendingCastersAC_iff.2 ⟨hA₀ hx, k, e, hv, hs, hvotes x hx k e hv hs⟩
  have hO : OpponentsAC tr H U P r ⊆ Hᶜ ∪ W := by
    intro x hx
    rcases opponentsAC_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact Or.inl hx
    refine Or.inr ?_
    obtain ⟨hts, hte⟩ := ts_le_castAC hr hx hv
    rw [hs] at hts hte
    obtain ⟨ℓ, hc, -⟩ := id hv
    have hrK := ts_le_tsAC (sp := sp) hrk.2
    have hjr := ts_le_tsAC (sp := sp) (show j₀ ≤ r by omega)
    have hzk := hz (tr.time k) (by linarith) ⟨x, hx, k, ℓ, hc, le_rfl⟩
    rcases hawake x hx (tr.time k) (by linarith) hzk (hr.awake_of_call x hx k ℓ hc)
      with hA₀' | hW
    · exact absurd (hvotes x hA₀' k e hv hs) hne
    · exact hW
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (hcohort.trans_le (Set.ncard_le_ncard hA (Set.toFinite _)))

end Consensus.Goldilocks.Comparison

end
