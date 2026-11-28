module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ViableEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The voter's height floor is bounded by its old-origin upper bound -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- An older fast-lock label written by the late-vote deadline was written before the slot. -/
theorem fastLock_time_lt_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {r m u : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hfl : AC.FastLockAt tr.projAC x r m D CV)
    (hmu : m < u) (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  rcases hfl with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
  · change tr.time r = sp.ts m + 6 * sp.Δ at ht
    have htwo : (m : Int) + 2 ≤ u := by
      have := Compose.ts_add_two_le (ht ▸ htr)
      exact_mod_cast this
    have hDelta := sp.toParams.hΔ
    rw [ht]
    simp only [ACParams.ts] at htr ⊢
    linarith only [mul_le_mul_of_nonneg_left htwo (show (0 : Time) ≤ 4 * sp.Δ by linarith), hDelta]
  · change sp.slot (tr.time r) = m at hsl
    by_contra h
    have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg r) u).mp (not_lt.mp h)
    omega

/-- An older lock written by the late-vote deadline was written before the slot, whether the
write was fast or slow. Slow locks use their update time, never a supporter count. -/
theorem lock_time_lt_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {r m u : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlock : (∃ CV, AC.FastLockAt tr.projAC x r m D CV) ∨ AC.SlowLockAt tr.projAC x r m D)
    (hmu : m < u) (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  rcases hlock with ⟨CV, hf⟩ | ⟨ell, C, ⟨_, _, ht, _⟩, _⟩
  · exact fastLock_time_lt_at hrun hf hmu htr
  · change tr.time r = sp.ts m + 6 * sp.Δ at ht
    have htwo : (m : Int) + 2 ≤ u := by
      exact_mod_cast Compose.ts_add_two_le (ht ▸ htr)
    have hDelta := sp.toParams.hΔ
    rw [ht]
    simp only [ACParams.ts]
    linarith only [mul_le_mul_of_nonneg_left htwo
      (show (0 : Time) ≤ 4 * sp.Δ by linarith), hDelta]

/-- A signer's lock written before a held row was signed has label below the cast slot.
The optimistic case uses the row's causal exclusion; slow and fast updates use their time. -/
theorem row_lock_label_lt_at
    {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlock : (∃ CV, AC.FastLockAt tr.projAC v r l D CV) ∨ AC.SlowLockAt tr.projAC v r l D) :
    l < e.msg.slot := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg k)).localRun
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hk : e.msg.slot = sp.slot (tr.time k) := (AC.castAt_specU hr.toU hy hc').2.1
  have htr : tr.time r ≤ tr.time k := hp.run.time_mono (by omega)
  have hup (ht : tr.time r = sp.ts l + 6 * sp.Δ) : l < e.msg.slot := by
    have h₁ : sp.ts (l + 1 : Nat) ≤ tr.time k := by
      have heq : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      rw [heq]
      linarith [sp.toParams.hΔ]
    have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mp h₁
    omega
  rcases hlock with ⟨CV, hf⟩ | ⟨ell', C, hu, _⟩
  · rcases hf with ⟨ell', C, hu, _⟩ | hopt
    · exact hup hu.2.2.1
    · have hl : l ≤ e.msg.slot := by
        obtain ⟨_, _, _, hsl, _⟩ := hopt
        rw [hk, ← hsl]
        exact AC.slot_mono sp (hp.run.time_nonneg r) htr
      rcases hl.lt_or_eq with hl | rfl
      · exact hl
      · exact absurd hopt (KernelProof.row_origin_not_current_at hp hy hc hW ha hv hs hrd)
  · exact hup hu.2.2.1

/-- A high entry named by a held signed row is below a healed member strictly before the cast
slot. The signer's own lock provenance excludes a same-slot optimistic write. -/
theorem row_entry_member_before_cast_at
    {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (hs : tr.SignAt v d att) (hdk : d < k)
    {E : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hT : att.T = E.root) (hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hcover : HighSourceCover tr H g a b) :
    ∃ C s, HealedMemberBefore tr H g a b C s k ∧
      s < e.msg.slot ∧ Anc (tr.HonestBlocksAt H) E C := by
  have ht := hp.run.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono hq.le
  have hvd := hp.run.antitone ((hp.run.time_mono hdk.le).trans (le_max_right _ _)) hvz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain ⟨E', hE', hEr, hEh⟩ := Healing.signAt_entry (hp.run.upTo (hp.run.time_nonneg d)) hvd
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  rw [RunTrace.upTo_state_of_le hp.run.time_mono le_rfl] at hE' hEh
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨y, k, tr.time k, ht, hle, hy, h⟩
  have hsub' : (tr.state v d).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨v, d, tr.time d, hp.run.time_nonneg d, fun _ hq => hp.run.time_mono hq.le, hvd, h⟩
  have he : E' = E := hU.1 (hsub' hE') (hsub hE) (hEr.trans hT)
  subst E'
  have hσ := σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg d)
    (fun _ hq => hp.run.time_mono hq.le) hvd ht hle hy hE' hE
  obtain ⟨E₀, hE₀, hE₀r, r, hrd, s, C, D, hC, hEC, _, _, hlock⟩ :=
    signed_row_lock_member_before_at hp.run hp.noColl
      (hp.run.antitone (max_le_max le_rfl (hp.run.time_mono hdk.le)) hvz) hs
      (by rw [← hEh, hσ]; exact hh) (hp.snapshot.imp fun _ h => h.1) hcover
      ((hp.run.time_mono hdk.le).trans hkb)
  have he₀ : E₀ = E := hU.1 hE₀ (hsub hE) (hE₀r.trans hT)
  subst E₀
  exact ⟨C, s, hC.mono hdk.le,
    row_lock_label_lt_at hp hy hc hW ha hvd hs hdk hrd hlock, hEC⟩

end Outcome

namespace ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- A left entry of the voter's store below a higher block lies below every block above the
pre-slot origins and the label-bounded covers. -/
private theorem reset_left_entry_below_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B)
    (hcovered : HighSourceCover tr H g a b → ∀ C s,
      HealedMemberBefore tr H g a b C s j → s < u → Anc (tr.HonestBlocksAt H) C B)
    (hE : E ∈ (tr.state y j).fg.tree) (hET : ((tr.state y j).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y j).fg.σ E.root).h)
    (hEC : (tr.state y j).fg.Anc E C)
    (hlt : ((tr.state y j).fg.σ E.root).h < ((tr.state y j).fg.σ C.root).h) :
    Anc (tr.HonestBlocksAt H) E B := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hp.run.time_mono hq.le
  obtain ⟨W, hW, att, ha, v, d, hv, hdj, hs, hT, hsource⟩ :=
    hp.left_entry_origin_or_covered_at ht hj hy hjb hE hET hEh hEC hlt
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hr := (Compose.goldilocks_ac_projection_from (hp.run.upTo ht) (hp.noColl.upTo _)).localRun
  have htupper : tr.time j ≤ sp.ts u + sp.Δ :=
    hes ▸ (Compose.cast_head_fcRoot hr (hp.run.upTo ht).vstart hy ⟨hc', hc.2⟩).2
  have hEB : Anc (tr.HonestBlocksAt H) E B := by
    rcases hsource with ⟨r, hrd, l, O, ho, hEO⟩ | ⟨_, hcov⟩
    · have hlu : l < u := hes ▸ KernelProof.row_origin_label_lt_at hp hy hc hW ha
        (hp.run.antitone (hp.run.time_mono hdj.le) hv) hs hdj hrd ho
      obtain ⟨CV, ellw, D, _, hf, _⟩ := ho.2.2.1
      have hrj := hp.run.time_mono (show r ≤ j by omega)
      have hrt := Outcome.fastLock_time_lt_at hp.run hf hlu (hrj.trans htupper)
      exact hEO.trans (hBold v r l O ho hrt (hrj.trans hjb))
    · obtain ⟨hcov, _⟩ := coveredUpTo_iff.1 hcov
      obtain ⟨C, s, hC, hsu, hEC⟩ := Outcome.row_entry_member_before_cast_at hp hy hjb hc hW ha
        ‹v ∈ H (max (cutZ sp.toParams g) (tr.time j))› hs hdj hE hT (by omega) hcov
      exact hEC.trans (hcovered hcov C s hC (hes ▸ hsu))
  exact hEB

/-- A pre-slot origin bound and a label-bounded cover bound make a held block viable at the voter
(P-U viability): it is above every high left entry of the store. -/
theorem reset_vote_viable_above_old_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B)
    (hcovered : HighSourceCover tr H g a b → ∀ C s,
      HealedMemberBefore tr H g a b C s j → s < u → Anc (tr.HonestBlocksAt H) C B) :
    (tr.state y j).fg.IsViable B := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hp.run.time_mono hq.le
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  refine isViable_of_entries_below (fg_reachable_at hp.run ht hj hy) hB
    (Outcome.high_of_anc_at hp.run hp.noColl ho₀ ht hj hy hB
      (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb))
    fun E hE C hET hEh hEC hlt => ?_
  exact store_anc_of_honest_anc_at hp.run hp.noColl ht hj hy
    (reset_left_entry_below_at hp hy hc hes hjb hBold hcovered hE hET hEh hEC hlt) hB

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
