module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.StaticCoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reset seeds before a post-drain slot in the P-U run -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The reset signing supplies a high origin strictly before every post-drain slot. -/
theorem ResetPremisesUpTo.reset_seed_before_slot_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u := by
  obtain ⟨⟨v, d, att, hvz, hs, hh, hda⟩, -⟩ := hp.reset
  have ha : 0 ≤ a := hda ▸ hp.run.time_nonneg d
  have hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ := by
    intro D hD
    rw [hda]
    rcases hp.deepCover D hD with hbq | hc
    · exact hp.reset_le.trans hbq
    · have := Healing.lt_drainTime (sp := sp) ha
      have := hc.drain_le D hD
      have := sp.toParams.hΔ
      linarith
  obtain ⟨r, hrd, l, O, ho, -⟩ := ShadowLeft.high_row_source_at hp.run hp.noColl hvz hs
    (by omega) (hp.snapshot.imp fun _ h => h.1) hq
  have hra : tr.time r ≤ a := (hp.run.time_mono hrd.le).trans hda.le
  have hrt : tr.time r < sp.ts u :=
    hra.trans_lt ((Healing.lt_drainTime (sp := sp) ha).trans_le hR)
  have htime : sp.ts l ≤ tr.time r := by
    obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
    rcases hfl with ⟨ell', C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell', A, -, hsl, -⟩
    · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
      rw [ht']
      have := sp.toParams.hΔ
      linarith
    · change sp.slot (tr.time r) = l at hsl
      exact (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l).mpr (by omega)
  have hlu : l < u := by
    have := (AC.ts_lt_iff sp).mp (htime.trans_lt hrt)
    exact_mod_cast this
  exact ⟨v, r, l, O, ho, hra.trans hp.reset_le, hlu, hrt⟩

namespace Outcome

/-- A held signed row's lock is older than the cast, including optimistic writes. -/
private theorem row_lock_label_lt_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlock : (∃ CV, AC.FastLockAt tr.projAC v r l D CV) ∨ AC.SlowLockAt tr.projAC v r l D) :
    l < e.msg.slot := by
  have hac := hp.run.toCore.acRun_upTo hp.noColl (hp.run.time_nonneg k)
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hk : e.msg.slot = sp.slot (tr.time k) :=
    (AC.castAt_specU hac.localRun.toU hy hc').2.1
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

/-- A high signed entry is below a healed member strictly before the cast's slot. -/
theorem row_entry_member_before_cast_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (hs : tr.SignAt v d att) (hdk : d < k)
    {E : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hT : att.T = E.root) (hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hcover : HighSourceCover tr H g a b) :
    ∃ C s, HealedMemberBefore tr H g a b C s k ∧
      s < e.msg.slot ∧ Anc (tr.HonestBlocksAt H) E C := by
  have hvd := hp.run.antitone ((hp.run.time_mono hdk.le).trans (le_max_right _ _)) hvz
  have rc := hp.run.toCore
  have hU := rc.coherent hp.noColl
  obtain ⟨E', hE', hEr, hEh⟩ := rc.signAt_entry hvd hs
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨y, k, tr.time k, hp.run.time_nonneg k, fun _ hq => hp.run.time_mono hq.le, hy, h⟩
  have hsub' : (tr.state v d).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨v, d, tr.time d, hp.run.time_nonneg d, fun _ hq => hp.run.time_mono hq.le, hvd, h⟩
  have he : E' = E := hU.1 (hsub' hE') (hsub hE) (hEr.trans hT)
  subst E'
  have hσ := rc.σ_eq_honest_at hp.noColl (hp.run.time_nonneg d)
    (fun _ hq => hp.run.time_mono hq.le) hvd (hp.run.time_nonneg k)
    (fun _ hq => hp.run.time_mono hq.le) hy hE' hE
  obtain ⟨E₀, hE₀, hE₀r, r, hrd, s, C, D, hC, hEC, _, _, hlock⟩ :=
    ShadowLeft.signed_row_lock_member hp.run hp.noColl
      (hp.run.antitone (max_le_max le_rfl (hp.run.time_mono hdk.le)) hvz) hs
      (by rw [← hEh, hσ]; exact hh) (hp.snapshot.imp fun _ h => h.1) hcover
      ((hp.run.time_mono hdk.le).trans hkb)
  have he₀ : E₀ = E := hU.1 hE₀ (hsub hE) (hE₀r.trans hT)
  subst E₀
  exact ⟨C, s, hC.mono hdk.le,
    row_lock_label_lt_at hp hy hc hW ha hvd hs hdk hrd hlock, hEC⟩

end Outcome

end Consensus.Goldilocks.Healing.Growing

end
