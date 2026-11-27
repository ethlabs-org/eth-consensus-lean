module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo

public section

/-! # A left replay entry has an origin honest at its own write

Count signers at the later of the reader's observation and `c_z`. Those signers were honest at
delivery, at signing and at `c_z`, even if other historical holders have since been compromised.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g : Time}

/-- A high entry left by a held chain was named by an earlier signer honest at it and at `c_z`;
the quorum budget is read at the later of the observation and `c_z`. The source origin's
honesty is at its write and at `c_z`, not the reader's later observation. -/
theorem left_entry_origin_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q)
    {E C : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hqt : ∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H t,
      ∃ d < k, tr.SignAt v d att ∧ att.T = E.root ∧
        ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
          Anc (tr.HonestBlocksAt H) E O := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨W, hW, att, ha, haT, haHz⟩ := Healing.honest_att_of_left
    (fg_reachable_at hrun ht hle hy) hq hET hEC hlt
  have haH := hrun.antitone (le_max_right _ _) haHz
  have he := Trace.upTo_state tr y hle
  have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i att
    (hrun.antitone (hle i hik) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hle i hik) haH)
  have hdk : d < k := hdi.trans hik
  have hv := hrun.antitone (hle d hdk) haH
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
    (hrun.upTo (hrun.time_nonneg d)) hv hs'
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hE' hE'h
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  have hEq : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
  subst E'
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
  obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
    high_row_source_at hrun hnc (hrun.antitone (max_le_max le_rfl (hle d hdk)) haHz) hs
      (by rw [← hE'h, hσ]; exact hEh) hsnap fun D hD => (hle d hdk).trans (hqt D hD)
  have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
      fun q hq => hrun.time_mono hq.le, hrun.antitone (le_max_right _ _) ho.1, h⟩
  have hEq₀ : E₀ = E := hU.1 (hsub₀ hE₀) (hsub hE) (hE₀r.trans haT)
  subst E₀
  exact ⟨W, hW, att, ha, att.val, haH, d, hdk, hs, haT, r, hrd, l, O, ho,
    hE₀O.mono hsub₀⟩

/-- **The deep quarantine or the high-source cover**, at a time `t ≤ b` of the reset premises:
either `t` is inside the deep quarantine `c_z + 4DΔ` (or deep sources are off), or the bundle
carries the high-source cover. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo.quarantine_or_cover_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {ΔF a b hold : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {t : Time} (htb : t ≤ b) :
    (∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
  cases hdd : sp.deepDepth with
  | none => exact Or.inl fun D hD => by cases hD
  | some D =>
    rcases hp.deepCover D hdd with hb | hc
    · refine Or.inl fun D' hD' => ?_
      cases hD'
      exact htb.trans hb
    · exact Or.inr hc

/-- **A high signed row below the signer's own lock write**, under the high-source cover: the
row's entry is below a member `C` of the healed family that is below a lock write, fast or slow,
of label `s` by the signer itself at a cut `r` before the signing: its high origin inside the
quarantine, or, after the drain, its own stored lock above its source report. The writer and the
cut sharpen the member's label against later slots. -/
theorem signed_row_lock_member_before_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧ ∃ r < d, ∃ s C D,
      HealedMemberBefore tr H g a b C s d ∧
      Anc (tr.HonestBlocksAt H) E C ∧ Anc (tr.HonestBlocksAt H) C D ∧ v ∈ H (tr.time r) ∧
      ((∃ CV, AC.FastLockAt tr.projAC v r s D CV) ∨ AC.SlowLockAt tr.projAC v r s D) := by
  have hv := hrun.antitone (le_max_right _ _) hvz
  by_cases hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ
  · obtain ⟨r, hrd, l, O, ho, E, hE, hEO, hEr, -⟩ := high_row_source_at hrun hnc hvz hs hh hsnap hq
    have hO := hrun.antitone (le_max_right _ _) ho.1
    have hr0 := hrun.time_nonneg r
    have hler : ∀ q < r, tr.time q ≤ tr.time r := fun q hq => hrun.time_mono hq.le
    obtain ⟨CV, ell, D', hcl, hfl, hOD⟩ := ho.2.2.1
    have hOD' : Anc (tr.HonestBlocksAt H) O D' := by
      rw [hOD]
      exact Anc.mono (Compose.Growing.frameIn_at hrun hnc hO hcl).2 (AC.anc_viableAncestor _ D')
    exact ⟨E, ⟨v, r, tr.time r, hr0, hler, hO, hE⟩, hEr, r, hrd, l, O, D',
      healedMemberBefore_iff.2
        (Or.inr (Or.inr ⟨v, r, hrd, (hrun.time_mono hrd.le).trans hdb, ho⟩)),
      honest_anc_of_store_anc_at hr0 hler hO hEO, hOD', hO, Or.inl ⟨CV, hfl⟩⟩
  push Not at hq
  obtain ⟨Dd, hD, hlt⟩ := hq
  have hdrain := hc.drain_le Dd hD
  have hΔ := sp.toParams.hΔ
  obtain ⟨src, hcall⟩ := hs
  obtain ⟨d', rfl, ℓ, hc', hto, htd, hC, hfgeq⟩ := Compose.Growing.attest_source hrun hv hcall
  have hv' : v ∈ H (tr.time d') := htd ▸ hv
  have hrep : AC.ToFGAt tr.projAC v d' ℓ src :=
    ⟨Compose.projAC_callAt.mpr hc', hto, by
      rw [Compose.Growing.projAC_state_at hrun hv']; exact hC⟩
  have hdt : drainTime sp a ≤ tr.time d' := by rw [htd]; linarith
  have hdb' : tr.time d' ≤ b := htd ▸ hdb
  -- the source report is below the block of one of the signer's live locks, fast or slow
  have hk0 := hrun.time_nonneg d'
  have hleR : ∀ q < d', tr.time q ≤ tr.time d' := fun _ hq => hrun.time_mono hq.le
  obtain ⟨-, A, ⟨hAt, l, hl, hlA⟩, hCA⟩ := AC.toFG_source_below_lock hrep.2.2
  have hU' := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hk0
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo hk0) (hnc.upTo _)).localRun
  have hst : (tr.upTo (tr.time d')).projAC.state v d' = tr.projAC.state v d' := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC v hleR
  have hck : (tr.upTo (tr.time d')).projAC.CallAt v d' ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hrep.1
  have hwf := AC.locksWF_stateU (hr := hr.toU) hrun.vstart hv' d'
  rw [hst] at hwf
  have hlab : healedLockFloor sp a ≤ l.slot := Healing.drain_live_locks (a := a) hwf hdt l hl
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  change healedLockFloor sp a ≤ l₀.slot at hlab
  have hl₀' : l₀ ∈ ((tr.upTo (tr.time d')).projAC.state v d').locks := by rw [hst]; exact hl₀
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hv' hck
  have hvB := AC.viableAncestor_anc hPhi hB₀
  obtain rfl : A = ℓ.frame.viableAncestor B₀ :=
    hr.coherent.1 (hPhiU hAt) (hPhiU hvB.1) hlA.symm
  obtain ⟨r', hrk, D, hsrc, hXD⟩ : ∃ r' < d', ∃ D,
      ((∃ CV, AC.FastLockAt tr.projAC v r' l₀.slot D CV) ∨
        AC.SlowLockAt tr.projAC v r' l₀.slot D) ∧
      Anc (tr.HonestBlocksAt H) (ℓ.frame.viableAncestor B₀) D := by
    cases hlf : l₀.fast
    · obtain ⟨r', hrk, D, ⟨ℓu, C', hu, hC', hD'⟩, L, hL, hLr, hLD⟩ :=
        AC.slow_lock_provenance hr hrun.vstart hv' d' l₀ hl₀' hlf
      rw [hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)] at hLD
      rw [RunTrace.upTo_projAC] at hu hC' hD'
      obtain ⟨hrt, hu⟩ := (AC.upTo_updateAt hrun.time_mono).1 hu
      have hs' : (tr.projAC.upTo (tr.time d')).state v r' = tr.projAC.state v r' :=
        Trace.upTo_state _ v fun _ hq => (hrun.time_mono hq.le).trans hrt
      rw [hs'] at hC' hD'
      rw [Trace.upTo_time] at hD'
      exact ⟨r', hrk, D, Or.inr ⟨ℓu, C', hu, hC', hD'⟩,
        Anc.mono hU' ((hvB.2.mono hPhiU).trans hLD)⟩
    · obtain ⟨r', hrk, CV, ℓ', D, hcr, hfl, L, hL, hLr, hLD⟩ :=
        Healing.stored_fast_lock_provenance hr hrun.vstart hv' d' l₀ hl₀' hlf
      rw [hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)] at hLD
      obtain ⟨ell', hc'', hD⟩ := Healing.fastLock_mem hfl
      obtain rfl : ell' = ℓ' := Option.some.inj (hc''.2.symm.trans hcr.2)
      obtain ⟨hPhi', hPhiU'⟩ := AC.frameIn_of_callAt hr hv' hc''
      have hrt : tr.time r' ≤ tr.time d' := hrun.time_mono hrk.le
      exact ⟨r', hrk, D,
        Or.inl ⟨CV, (fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl⟩,
        Anc.mono hU' ((hvB.2.mono hPhiU).trans
          (hLD.trans ((AC.viableAncestor_anc hPhi' hD).2.mono hPhiU')))⟩
  have hvr : v ∈ H (tr.time r') := hrun.antitone (hrun.time_mono hrk.le) hv'
  -- the signed entry, below the source
  have hd0 := hrun.time_nonneg (d' + 1)
  have hle1 : ∀ q < d' + 1, tr.time q ≤ tr.time (d' + 1) := fun q hq => hrun.time_mono hq.le
  have hreach := fg_reachable_at hrun hd0 hle1 hv
  set st := (tr.state v (d' + 1)).fg with hst'
  have hCst : src ∈ st.tree := by
    rw [hfgeq]; exact toFG_mem_tree_at hrun hv' hrep
  have hcut := (hrun.cutLaw v (d' + 1) _ hcall hv).1
  obtain ⟨-, haT⟩ := Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, -, hETh⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach _ hCst
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  have hED : Anc (tr.HonestBlocksAt H) E D :=
    (honest_anc_of_store_anc_at hd0 hle1 hv hEC).trans
      ((Anc.mono hU' (hCA.mono hPhiU)).trans hXD)
  exact ⟨E, ⟨v, d' + 1, _, hd0, hle1, hv, hE⟩, hEr', r', by omega, l₀.slot, D, D,
    healedMemberBefore_iff.2
      (Or.inr (Or.inl ⟨hlab, v, r', by omega, hvr, (hrun.time_mono hrk.le).trans hdb', hsrc⟩)),
    hED, .refl, hvr, hsrc⟩

/-- `signed_row_lock_member_before_at`, with the member read in the healed family. -/
theorem signed_row_lock_member_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧ ∃ r < d, ∃ s C D,
      Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b ∧
      Anc (tr.HonestBlocksAt H) E C ∧ Anc (tr.HonestBlocksAt H) C D ∧ v ∈ H (tr.time r) ∧
      ((∃ CV, AC.FastLockAt tr.projAC v r s D CV) ∨ AC.SlowLockAt tr.projAC v r s D) :=
  let ⟨E, hE, hEr, r, hrd, s, C, D, hC, h⟩ :=
    signed_row_lock_member_before_at hrun hnc hvz hs hh hsnap hc hdb
  ⟨E, hE, hEr, r, hrd, s, C, D, hC.healedOrigin, h⟩

/-- **A high signed row is covered before its signing under the high-source cover**: the row's
entry is below a member of the healed family written before the signing
(`signed_row_lock_member_before_at`), of label at most the signing's slot. -/
theorem signed_row_covered_before_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧
      CoveredBefore tr H g a b (sp.slot (tr.time d)) d E := by
  obtain ⟨E, hE, hEr, r, hrd, s, C, D, hC, hEC, -, hvr, hlock⟩ :=
    signed_row_lock_member_before_at hrun hnc hvz hs hh hsnap hc hdb
  exact ⟨E, hE, hEr, coveredBefore_iff.2 ⟨hc, C, s, hC,
    (Compose.Growing.LockWithin.label_le_slot hrun
      (Compose.Growing.lockWithin_iff.2 ⟨v, r, hvr, le_rfl, hlock⟩)).trans
      (AC.slot_mono sp (hrun.time_nonneg r) (hrun.time_mono hrd.le)), hEC⟩⟩

/-- **A high signed row is covered under the high-source cover**: the row's entry is below a
member of the healed family of label at most the signing's slot
(`signed_row_covered_before_at`). -/
theorem signed_row_covered_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧
      CoveredUpTo tr H g a b (sp.slot (tr.time d)) E :=
  let ⟨E, hE, hEr, h⟩ := signed_row_covered_before_at hrun hnc hvz hs hh hsnap hc hdb
  ⟨E, hE, hEr, h.coveredUpTo⟩

/-- `left_entry_origin_at` under the high-source cover: the left entry is the target of a held
attestation whose signer is honest at the observation and at `c_z`, and it is covered up to the
slot of the observation time. -/
theorem left_entry_covered_before_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q)
    {E C : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (htb : t ≤ b) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H (max (cutZ sp.toParams g) t),
      ∃ d < k, tr.SignAt v d att ∧ att.T = E.root ∧ CoveredBefore tr H g a b (sp.slot t) k E := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨W, hW, att, ha, haT, haHz⟩ := Healing.honest_att_of_left
    (fg_reachable_at hrun ht hle hy) hq hET hEC hlt
  have haH := hrun.antitone (le_max_right _ _) haHz
  have he := Trace.upTo_state tr y hle
  have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i att
    (hrun.antitone (hle i hik) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hle i hik) haH)
  have hdk : d < k := hdi.trans hik
  have hv := hrun.antitone (hle d hdk) haH
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
    (hrun.upTo (hrun.time_nonneg d)) hv hs'
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hE' hE'h
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
  obtain ⟨E₀, hE₀, hE₀r, hch⟩ := signed_row_covered_before_at hrun hnc
    (hrun.antitone (max_le_max le_rfl (hle d hdk)) haHz) hs
    (by rw [← hE'h, hσ]; exact hEh) hsnap hc ((hle d hdk).trans htb)
  obtain rfl : E₀ = E' := hU.1 hE₀ (hsub hE) (hE₀r.trans haT)
  exact ⟨W, hW, att, ha, att.val, haHz, d, hdk, hs, haT,
    hch.mono (AC.slot_mono sp (hrun.time_nonneg d) (hle d hdk)) hdk.le⟩

/-- `left_entry_covered_before_at`, with the cover read up to the label only. -/
theorem left_entry_covered_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q)
    {E C : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (htb : t ≤ b) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H (max (cutZ sp.toParams g) t),
      ∃ d < k, tr.SignAt v d att ∧ att.T = E.root ∧ CoveredUpTo tr H g a b (sp.slot t) E :=
  let ⟨W, hW, att, ha, v, hv, d, hdk, hs, haT, h⟩ :=
    left_entry_covered_before_at hrun hnc ht hle hy hq hE hET hEh hEC hlt hsnap hc htb
  ⟨W, hW, att, ha, v, hv, d, hdk, hs, haT, h.coveredUpTo⟩

end Consensus.Goldilocks.Healing.Growing.Outcome

end
