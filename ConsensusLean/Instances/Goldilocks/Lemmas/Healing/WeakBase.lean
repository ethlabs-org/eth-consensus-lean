module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Weak
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Goldilocks milestone Regimes: R.6's base for the Sleepy invariant from `s₀`

This module lives in Healing because the base uses the reset and acceptance projection lemmas;
the Compose layer is below Healing in the import matrix.

`healed_safe_until` (R.6, `Lemmas/Compose/Regimes/Weak`) goes through the Sleepy record invariant
started at a label `s₀` after the reset (`Compose.sleepy_invariant_from`, over `SleepyFrom` and
`SleepyBase`). This file derives both from `WeakPremises` (the healing premises of R.3 cut at the
heal point `T`) for a start label `s₀` with `a + T_b ≤ t_{s₀}` (the reset `a`, `T_b` of H.3 (c)'s
bridge), early enough before `T` (`t_{s₀+k} ≤ T`, `t_{s₀+2} + 6Δ ≤ T`), split by owner
(consensus-lean#17, 2026-10-31):

* `weak_sleepyFrom`: `Sync` and `f < h_t` from `t_{s₀}` (`GST(g)` from `ḡ`; every honest node
  awake on `[ḡ, T]` and joined from `t_{s₀}`, the ready ones from `T`) (proved);
* `weak_base_locks`, `weak_base_sources`, `weak_base_old_blocks`: `SleepyBase`'s (1) (a read-point
  lock of a slot `< s₀` is live only at votes of slots `< s₀ + k`, so before `T`, under `Healthy`
  and H.2's drain), (3b) (A1.5: a source is below the stored block of a recent fast lock) and (6)
  (`Catch(2Δ)` for the acceptances before `ḡ`, `GST(g)`'s relay for those in `[ḡ, t_{s₀})`, the
  voter joined). Sources and old blocks are proved; locks remain open;
* `weak_base_until`: the facts (2), (3a), (5) and (5′) at the cuts up to `T` (`BaseFacts` at
  `· ≤ T`), the paper obligation of the T3 orb (open);
* `weak_base_extend`: the same facts at every cut (`BaseFacts` at every time), from those up to
  `T` and the run after `T` (amp-orbs service; open). Not by monotonicity alone: a `Σ.F` that moves
  past `T` needs a covering origin, and a row first held after `T` is not covered by the facts up
  to `T`.

`weak_sleepyBase` assembles `SleepyBase` from them. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **`SleepyBase`'s facts (2), (3a), (5), (5′) at the cuts whose time satisfies `P`** (the
fields of `SleepyBase` with the guard `P (tr.time i)`): at every time (`P := fun _ => True`) they
are `SleepyBase`'s fields; up to `T` (`P := (· ≤ T)`) they are what the healed configuration
and `Healthy` up to `T` can give. -/
structure BaseFacts (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s₀ : Nat)
    (P : Time → Prop) : Prop where
  /-- (2) Records (RecRet). -/
  records : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts s₀ + 6 * sp.Δ ≤ tr.time i →
    ∀ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed →
      (∃ s < s₀, Origin tr H C s) →
        OnOriginChainFrom tr H C s₀ ∨ Anc (tr.HonestBlocks H) C (tr.state y i).fg.F
  /-- (3a) Caches. -/
  caches : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    OnOriginChainFrom tr H (tr.state y i).fg.F s₀ ∧ OnOriginChainFrom tr H (tr.state y i).fg.J s₀
  /-- (5) Rows at votes of slots `> s₀`. -/
  vote_rows : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → P (tr.time i) →
    ∀ s, e.msg.slot = s + 1 → s₀ ≤ s → ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload,
      a.val ∈ H → (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧ l ≤ s ∧
          Anc (tr.HonestBlocks H) D C
  /-- (5′) Rows at the cuts from `t_{s₀}`. -/
  event_rows : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts s₀ ≤ tr.time i →
    ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧
          Anc (tr.HonestBlocks H) D C

section Base

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a Tb T : Time} {s₀ : Nat}

/-- **(1) Old live locks** (open; acbase): a read-point lock of a slot `< s₀` is live at a vote
of a slot `> s₀` only before `t_{s₀+k} ≤ T`, where `Healthy` and H.2's drain hold. -/
theorem weak_base_locks (hrun : GoldilocksRun dg H tr) (hw : WeakPremises tr H dg g ΔF Gp a Tb T)
    (hs₀ : a + Tb ≤ sp.ts s₀) (hk : sp.ts (s₀ + sp.k : Nat) ≤ T) :
    ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s₀ < e.msg.slot →
      ∀ L ∈ SA.liveLockBlocks sp {l ∈ e.readPoint.locks | l.slot < s₀} ℓ.frame (tr.time i),
        ∀ C j, OriginFrom tr H C j s₀ → j < e.msg.slot → Compatible (tr.HonestBlocks H) L C := by
  sorry

/-- **(3b) Sources**: the two-slot age bound puts the supporting lock's origin after `s₀`. -/
theorem weak_base_sources (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (_hs₀ : a + Tb ≤ sp.ts s₀) :
    ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
      (∃ C' l, Origin tr H C' l ∧ l < s₀ ∧ Anc (tr.HonestBlocks H) C C') →
        OnOriginChainFrom tr H C s₀ := by
  intro y hy i ℓ C hto hi _
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hw.noColl).localRun
  obtain ⟨hpc, -, hC⟩ := hto
  have hCand : C ∈ SA.toFGCandidates sp (tr.projAC.state y i) ℓ.frame (tr.time i) := by
    unfold SA.acToFG at hC
    dsimp only at hC
    split_ifs at hC
    split at hC
    · cases hC
    · rename_i C' hC'
      split_ifs at hC
      cases hC
      exact (SA.deepest_mem hC').1
  obtain ⟨hCv, l, hl, hlC, -, hls⟩ := hCand
  rw [projAC_state hrun.toLocalRun hy i] at hl
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hpc
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : C = ℓ.frame.viableAncestor B := hΦ.coherent.1 hCv.1 hvt hlC.symm
  obtain ⟨L, hL, hLr, C', hC', hLC'⟩ := lock_origin hrun hw.noColl hy i l₀ hl₀
  obtain rfl : B = L := hr.coherent.1 (hΦU hB) ⟨y, hy, i, hL⟩ (hBr.trans hLr.symm)
  have hslot := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) (s₀ + 2 : Nat)).1 hi
  have hl : s₀ ≤ l₀.slot := by
    change sp.slot (tr.time i) ≤ l₀.slot + 2 at hls
    exact_mod_cast (show (s₀ : Int) ≤ l₀.slot by omega)
  exact onOriginChainFrom_iff.2
    (Or.inr ⟨C', l₀.slot, originFrom_iff.2 ⟨hC'.origin, hl⟩, (hva.mono hΦU).trans hLC'⟩)

/-- The reset is after `c_z`; post-`T` readiness supplies a cut after `c_z` without
assuming full participation after `T`. -/
private theorem weak_cutZ_lt_reset (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) : Healing.cutZ sp.toParams g < a := by
  classical
  let t := max T (max 0 (Healing.cutZ sp.toParams g + 1))
  have ht0 : 0 ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero
    (Nat.ne_of_gt ((Nat.zero_le _).trans_lt (hw.sleepyAfter t (le_max_left _ _))))
  obtain ⟨m, -, hm⟩ := hrun.awake_in_horizon z hz.1 t
    (hz.2 t (max_le ht0 (by have := sp.toParams.hΔ; simp only [catchUp]; linarith)) le_rfl)
  have hex : ∃ j, Healing.cutZ sp.toParams g < tr.time j :=
    ⟨m, by
      have := le_max_right T (max 0 (Healing.cutZ sp.toParams g + 1))
      have := le_max_right 0 (Healing.cutZ sp.toParams g + 1)
      dsimp [t] at hm
      linarith⟩
  have hj : Healing.FirstCutAfter tr (Nat.find hex) (Healing.cutZ sp.toParams g) :=
    ⟨fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩
  obtain ⟨⟨y, hy, k, att, hs, hatt, hka⟩, -⟩ := hw.reset
  by_contra h
  have hkj : k ≤ Nat.find hex := by
    by_contra h'
    have := hrun.time_mono (le_of_not_ge h')
    linarith [hj.2]
  have := (Healing.signAt_h_le hrun hy hs).trans
    ((Healing.hmax_mono hrun.toLocalRun hy hkj).trans (Healing.hmax_le_HZ hy hj))
  omega

/-- **`Sync` and `f < h_t` from `t_{s₀}`** under `Weak`: full participation up to `T`,
and the ready honest validators thereafter. -/
theorem weak_sleepyFrom (hrun : GoldilocksRun dg H tr) (hw : WeakPremises tr H dg g ΔF Gp a Tb T)
    (hs₀ : a + Tb ≤ sp.ts s₀) : SleepyFrom tr H ΔF s₀ := by
  have hΔ := sp.toParams.hΔ
  have hstart : gbar g + 8 * sp.Δ < sp.ts s₀ := by
    have := Healing.lt_cutZ sp g
    have := weak_cutZ_lt_reset hrun hw
    have := hw.offset
    linarith
  have hg : g ≤ sp.ts s₀ := by have := Healing.le_gbar g; linarith
  refine sleepyFrom_iff.2 ⟨⟨hw.gst.deltaF, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx i m hm hi
    simpa only [max_eq_left (hg.trans hi), id_eq] using hw.gst.message x hx i m hm trivial
  · intro x hx i B hB hi
    simpa only [max_eq_left (hg.trans hi), id_eq] using hw.gst.block x hx i B hB trivial
  · intro x hx i B hB hi
    simpa only [max_eq_left (hg.trans hi), id_eq] using hw.gst.relay x hx i B hB (hg.trans hi)
  · intro x hx i att hatt hi
    simpa only [max_eq_left (hg.trans hi), id_eq] using
      hw.gst.attestation x hx i att hatt trivial
  · intro s hs d hd
    have hss : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs)
    have hd0 : 0 ≤ d := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl <;> linarith
    have ht0 : 0 ≤ sp.ts s + d := by have := Healing.gbar_nonneg g; linarith
    by_cases ht : sp.ts s + d ≤ T
    · have hsub : H ⊆ {y | y ∈ H ∧ tr.awake y (sp.ts s + d) ∧
          tr.JoinedAt y (sp.ts s + d)} := by
        intro y hy
        refine ⟨hy, ready_implies_joined sp ro dg H tr hrun y hy _ (8 * sp.Δ - 1)
          ht0 (by linarith) ?_⟩
        intro u hu hut
        exact hw.awake y hy u (by
          have := le_max_right 0 (sp.ts s + d - (8 * sp.Δ - 1) - 1)
          linarith)
          (hut.trans ht)
      have hle : H.ncard ≤ tr.honestAwakeJoined H (sp.ts s + d) := Set.ncard_le_ncard hsub
      have hn : H.ncard + Hᶜ.ncard = sp.n := by
        rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
      have hf := hw.faults
      have hpos := sp.toParams.hn
      change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts s + d)
      change 0 < sp.n at hpos
      omega
    · have hsub : {y | ReadyAt tr H (catchUp sp) y (sp.ts s + d)} ⊆
          {y | y ∈ H ∧ tr.awake y (sp.ts s + d) ∧ tr.JoinedAt y (sp.ts s + d)} := by
        intro y hy
        exact ⟨hy.1, ready_implies_joined sp ro dg H tr hrun y hy.1 _ (catchUp sp)
          ht0 (by simp only [catchUp]; linarith) hy.2⟩
      exact (hw.sleepyAfter _ (not_le.1 ht).le).trans_le (Set.ncard_le_ncard hsub)

/-- **(6) Old blocks caught up**: `Catch(2Δ)` and `GST(g)`'s relay. -/
theorem weak_base_old_blocks (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀) :
    ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → ∀ s, e.msg.slot = s + 1 →
      s₀ ≤ s → ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
        Anc (tr.HonestBlocks H) ℓ.frame.F B →
          SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ) := by
  classical
  intro y hy i ℓ e hc s hs hs₀' x hx m B hacc hm hF
  have hΔ := sp.toParams.hΔ
  have hss : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀')
  have hgs : gbar g + 2 * sp.Δ < sp.ts s₀ := by
    have := Healing.lt_cutZ sp g
    have := weak_cutZ_lt_reset hrun hw
    have := hw.offset
    linarith
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hw.noColl hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s :=
    fun c hci ⟨ℓr, hcr, hrr⟩ => hrs c hci ⟨ℓr, projAC_callAt.2 hcr, hrr⟩
  have hFy : Anc (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    rw [frame_of_projAC hrun hy hc.1] at hF
    exact hF
  by_cases hmg : tr.time m < gbar g
  · have hex : ∃ j, gbar g + 2 * sp.Δ ≤ tr.time j := ⟨i, by linarith⟩
    have hj : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
      ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
    have hji : Nat.find hex ≤ i := Nat.find_min' hex (by linarith)
    obtain ⟨k, hk, hAk⟩ := hw.catchPremise x hx m B hacc hmg y hy _ hj
      ((Healing.run_F_mono hrun.toLocalRun hy hji).trans hFy)
    obtain ⟨hAk', htk, -⟩ := Healing.ac_block_after hrun.toLocalRun hy hAk
    exact Or.inr ⟨k + 1, hAk', by
      change tr.time (k + 1) < _
      rw [htk]
      have := hj.2 k hk
      linarith⟩
  · have hdl : ∀ c ≤ i, tr.deadline y c (tr.time m) sp.Δ ≤ sp.ts s + sp.Δ := by
      intro c hci
      have := deadline_le_of_restarts (fun k hk hr => hrs' k (hk.trans hci) hr)
        (tr.time m) sp.Δ
      have := max_le (hm.le.trans hss) (le_refl (sp.ts s))
      linarith
    have hmax : max (tr.time m) g = tr.time m :=
      max_eq_left ((Healing.le_gbar g).trans (not_lt.1 hmg))
    obtain ⟨k, hki, hAk, hkt⟩ := hw.gst.relay x hx m B hacc
      ((Healing.le_gbar g).trans (not_lt.1 hmg)) y hy i ⟨_, projAC_callAt.1 hc.1⟩
      (by rw [hmax]; have := hdl i le_rfl; linarith)
      hFy
    rw [hmax] at hkt
    obtain ⟨hAk', htk, -⟩ := Healing.ac_block_after hrun.toLocalRun hy hAk
    exact Or.inr ⟨k + 1, hAk', by
      change tr.time (k + 1) < _
      rw [htk]
      have := hdl k hki
      linarith⟩

/-- **(2), (3a), (5), (5′) up to `T`** (open; the T3 orb's paper obligation). -/
theorem weak_base_until (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) :
    BaseFacts tr H s₀ (· ≤ T) := by
  sorry

/-- **(2), (3a), (5), (5′) at every cut** from those up to `T` (open; amp-orbs service). -/
theorem weak_base_extend (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) (hbase : BaseFacts tr H s₀ (· ≤ T)) :
    BaseFacts tr H s₀ fun _ => True := by
  sorry

/-- **`SleepyBase` at `s₀` under `Weak`**, assembled. -/
theorem weak_sleepyBase (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hk : sp.ts (s₀ + sp.k : Nat) ≤ T) (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) :
    SleepyBase tr H s₀ := by
  have hb := weak_base_extend hrun hw hs₀ hT (weak_base_until hrun hw hs₀ hT)
  exact ⟨weak_base_locks hrun hw hs₀ hk,
    fun y hy i hi => hb.records y hy i trivial hi,
    fun y hy i hi => hb.caches y hy i trivial hi,
    weak_base_sources hrun hw hs₀,
    fun y hy i ℓ e hc => hb.vote_rows y hy i ℓ e hc trivial,
    fun y hy i hi => hb.event_rows y hy i trivial hi,
    weak_base_old_blocks hrun hw hs₀⟩

end Base

end Consensus.Goldilocks.Regimes

end
