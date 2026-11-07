module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Foundation
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A raw writer's block in a later voter's frozen tree, under growing faults

The growing form of `Healing.raw_writer_voterBlockTree_window_before` (`Healing/Retention/Relay`):
the writer is honest at its write, and its counted head is genesis or accepted by it while
honest (`Healing.Growing.raw_writer_relay_source_at`); the voter is honest at its cast. An
accepted head reaches the voter before its slot's freeze through the window service or, for an
acceptance before the window, the catch-up, each owed from the writer's acceptance alone. The
rest is the voter's own frozen domain, read on the prefix through its cast. -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)}

/-- An ancestor of a raw writer's block, for a writer honest at its write, is available in the
frozen block tree of a later voter honest at its cast. -/
theorem raw_writer_voterBlockTree_window_before_at
    (hr : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b κ : Time} (hsync : ServiceWindowBefore H U a b tr)
    (hcatch : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < a →
      ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → a + κ ≤ tr.time j → tr.time j ≤ b →
        Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < a + κ)
    {x y : Fin sp.n} {j i s : Nat} (hx : x ∈ H (tr.time j)) (hy : y ∈ H (tr.time i))
    {B C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : ResultAt tr x j s C CV ∨ FastLockAt tr x j s C CV)
    (hBC : Anc U B C) {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : tr.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F B) : B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  have hm := hr.time_mono
  have hi0 := hr.time_nonneg i
  have hri := hr.upTo hi0
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hc' : CastAt (tr.upTo (tr.time i)) y i ℓ e := upTo_castAt.mpr ⟨le_rfl, hc⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hri hy hc'.1
  obtain ⟨-, hys, hyj, -⟩ := castAt_spec hri hy hc'
  have hm' : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ tr.time i :=
    (ts_le_iff_le_slot sp hi0 _).2 (by rw [hys]; rfl)
  have hfz : freeze sp e.msg.slot ≤ tr.time i := by unfold freeze; linarith only [hΔ, hm', hti]
  have hrsy : ∀ k ≤ i, ACTrace.RestartAt (tr.upTo (tr.time i)) y k →
      tr.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : joined sp ((tr.upTo (tr.time i)).post i) (tr.time i) := by
      unfold joined; rw [restartTime_of_castAt hri hy hc']; exact hyj
    intro k hk hrk
    have := ((joined_awake sp) FGP ro _ U _ hri y hy i ℓ hc'.1 hj').2 k hk hrk
    rwa [← hys] at this
  obtain ⟨v, -, D, hDU, -, hBD, hsource⟩ :=
    Healing.Growing.raw_writer_relay_source_at hr hx hwriter hBC
  have hFD := hF.trans hBD
  -- the voter holds `D` in its frame, stamped before its slot's freeze
  have hDt : D ∈ ℓ.frame.tree ∧
      e.readPoint.blockStamp D.root < ETime.of (freeze sp e.msg.slot) := by
    rcases hsource with hgen | ⟨q, hxq, hq, hqt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hri hy _ _ hc'.1
      obtain rfl : D = G := hU.1 hDU hGU (hgen.trans hGr.symm)
      have hDt : D ∈ ℓ.frame.tree := by
        obtain heq | ⟨c, _, hp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFD
        · exact heq ▸ hΦ.rooted.1
        · exact absurd (hp.2.2.symm.trans hGp) (Option.some_ne_none _)
      have hfz' : freeze sp e.msg.slot < tr.time i := by
        unfold freeze SAParams.ts at hti ⊢
        linarith only [hΔ, hti]
      have hbs := blockStamp_lt_of_acceptedBefore sp hri hy hc'.1 hDt (Or.inl hGr)
        (fun k hk hrk => lt_of_le_of_lt (hrsy k hk hrk) (by unfold freeze; linarith only [hΔ]))
        (Or.inl hfz'.le)
      have hne : ∀ X, ℓ.call = .block X → D.root ≠ X.root := by
        intro X hcall heq
        exact accept_ne_genesis sp hri hy ⟨ℓ, hc'.1, hcall⟩ (heq.symm.trans hGr)
      rw [← readPoint_blockStamp hri hy hc' hne] at hbs
      exact ⟨hDt, hbs⟩
    have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (ts_le_iff sp).2 (by omega)
    have hdl : ∀ k ≤ i, tr.deadline y k (tr.time q) <
        sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
      intro k hk
      have h₁ := Compose.ac_deadline_le_of_restarts (T := tr)
        (fun k' hk' hr' => hrsy k' (hk'.trans hk)
          ((ACTrace.upTo_restartAt).mpr ⟨hm (hk'.trans hk), hr'⟩)) (tr.time q)
      have h₂ := max_lt (show tr.time q < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
          linarith only [hqt, hsm])
        (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
          linarith only [hΔ])
      change tr.deadline y k (tr.time q) ≤ max (tr.time q) (sp.ts ((e.msg.slot : Int) - 1)) +
        sp.Δ at h₁
      linarith only [h₂, h₁]
    obtain ⟨ky, hky, hacc, hkyt⟩ : ∃ ky ≤ i, tr.AcceptAt y ky D ∧
        tr.time ky < freeze sp e.msg.slot := by
      by_cases ha : a ≤ tr.time q
      · obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.relay x q D hxq hq ha y i ℓ hy hc.1
          (by linarith only [hi, hΔ, hm', hti, hdl i le_rfl])
          (by linarith only [hΔ, hm', hti, hdl i le_rfl]) hFD
        refine ⟨ky, hky, hacc, ?_⟩
        have := hdl ky hky
        unfold freeze
        linarith only [hkyt, this]
      · obtain ⟨ky, hky, hacc, hkyt⟩ := hcatch x q D hxq hq (lt_of_not_ge ha) y i ℓ hy hc.1
          (by linarith only [hcatchTime, hΔ, hti, hm']) hi hFD
        refine ⟨ky, hky, hacc, ?_⟩
        unfold freeze
        linarith only [hcatchTime, hkyt]
    have hacc' :
        ACTrace.AcceptAt (A := goldilocksSA sp FGP ro) (tr.upTo (tr.time i)) y ky D :=
      (ACTrace.upTo_acceptAt).mpr ⟨hm hky, hacc⟩
    have hWt := mem_tree_of_acceptAt sp hri hy hacc' hky hc'.1 hFD
    have hbs := blockStamp_lt_of_acceptedBefore sp hri hy hc'.1 hWt (Or.inr ⟨ky, hacc', hkyt⟩)
      (fun k hk hrk => lt_of_le_of_lt (hrsy k hk hrk) (by unfold freeze; linarith only [hΔ]))
      (Or.inl hfz)
    have hne : ∀ X, ℓ.call = .block X → D.root ≠ X.root := by
      intro X hcall hX
      have hX₀ := (accept_new sp hri hy ⟨ℓ, hc'.1, hcall⟩).1 ℓ hc'.1
      obtain rfl : X = D := hU.1 (hΦU hX₀) (hΦU hWt) hX.symm
      have heq := accept_unique sp hri hy hacc' ⟨ℓ, hc'.1, hcall⟩
      rw [heq] at hkyt
      linarith only [hkyt, hfz]
    rw [← readPoint_blockStamp hri hy hc' hne] at hbs
    exact ⟨hWt, hbs⟩
  have hBt := frame_mem_of_between sp hU hΦ hΦU hDt.1 hBD hF
  exact voterBlockTree_anc hri hy hc' D ⟨hDt.1, Or.inl hDt.2⟩ B
    (anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt.1)

end Consensus.Goldilocks.SA.Growing

end
