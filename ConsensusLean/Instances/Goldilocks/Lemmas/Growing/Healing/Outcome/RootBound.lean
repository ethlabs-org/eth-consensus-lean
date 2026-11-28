module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Bounded historical origins bound an honest cast's root -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- An honest cast's actual frame root is below its store's analysis root. -/
theorem cast_root_anc_analysis_root_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) :
    Anc (tr.HonestBlocksAt H) ell.frame.fcRoot (tr.state y j).fg.fcRoot := by
  rw [Outcome.frame_of_call hp.run hy hc.1]
  have hr := fg_reachable_at hp.run (hp.run.time_nonneg j)
    (fun _ hq => hp.run.time_mono hq.le) hy
  have hFJ := (Store.cache_invariants _ _ _ _ hr).2.2.1.mono
    (fun X hX => (⟨y, j, tr.time j, hp.run.time_nonneg j,
      fun _ hq => hp.run.time_mono hq.le, hy, hX⟩ : X ∈ tr.HonestBlocksAt H))
  change Anc _ (tr.state y j).fg.F _
  unfold Store.fcRoot
  split_ifs
  · exact hFJ
  · exact .refl

/-- The post-drain cast finality is genesis, below a pre-slot origin, or below a healed member
whose label is strictly below the cast slot. -/
theorem reset_vote_finality_source_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    (tr.state y j).fg.F.root = sp.genesisRoot ∨
      (∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F O) ∨
      (HighSourceCover tr H g a b ∧ ∃ C s,
        HealedMemberBefore tr H g a b C s j ∧ s < u ∧
          Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F C) := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun _ hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := fg_reachable_at hp.run ht hj hy
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨y, j, tr.time j, ht, hj, hy, hX⟩
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have htupper : tr.time j ≤ sp.ts u + sp.Δ := by
    have h := (Compose.cast_head_fcRoot (hac.localRun.upTo ht) hac.vstart hy hc').2
    change tr.time j ≤ sp.ts e.msg.slot + sp.Δ at h
    rwa [hes] at h
  obtain ⟨hFm, hJm, hFJ, ⟨C, hCm, hCJ, hChj⟩, hmax, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hCm
  obtain rfl : E = (tr.state y j).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hCJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    rw [← hg] at hJF
    have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
    exact congrArg (·.root) (he.trans hg)
  right
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y j).fg.hj
  · obtain ⟨W, hW, att, ha, v, d, hv, hdj, hs, hT, hor⟩ :=
      hp.left_entry_origin_or_covered_at ht hj hy hjb hJm hJT (by omega) hEC
        (by have := Store.hj_lt_h hr hCm; omega)
    have below {B} (hJB : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.J B) :
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B := (hFJ.mono hsub).trans hJB
    rcases hor with ⟨r, hrd, l, O, ho, hJO⟩ | ⟨hvz, hcov⟩
    swap
    · obtain ⟨hcov, _⟩ := coveredUpTo_iff.1 hcov
      obtain ⟨C, s, hC, hsu, hJC⟩ := Outcome.row_entry_member_before_cast_at hp hy hjb hc
        hW ha hvz hs hdj hJm hT (by omega) hcov
      exact Or.inr ⟨hcov, C, s, hC, hes ▸ hsu, below hJC⟩
    have hlu : l < u := hes ▸ KernelProof.row_origin_label_lt_at hp hy hc hW ha
      (hp.run.antitone (hp.run.time_mono hdj.le) hv) hs hdj hrd ho
    obtain ⟨CV, ellw, D, _, hfl, _⟩ := ho.2.2.1
    have hrj : tr.time r ≤ tr.time j := hp.run.time_mono (by omega)
    have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (hrj.trans htupper)
    exact Or.inl ⟨v, r, l, O, ho, hrt, hrj.trans hjb, below hJO⟩
  obtain ⟨v, r, l, O, ho, hrb, hlu, hrt⟩ := hp.reset_seed_before_slot_at hR
  exact Or.inl ⟨v, r, l, O, ho, hrt, hrb,
    hp.low_finalized_below_origin_at ht hj hy hjb (by omega) ho hrb⟩

/-- Every bounded pre-slot high origin below a target bounds the cast finality. -/
theorem reset_vote_finality_below_bound_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u j : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) B P)
    (hcovered : HighSourceCover tr H g a b → ∀ C s,
      HealedMemberBefore tr H g a b C s j → s < u → Anc (tr.HonestBlocksAt H) C P)
    {y : Fin sp.n} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hs : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P := by
  rcases hp.reset_vote_finality_source_or_covered_at hR hy hc hs hjb with
    hg | ⟨x, r, l, B, ho, ht, hrb, hroot⟩ | ⟨hcover, C, s, hC, hsu, hroot⟩
  · have hr := fg_reachable_at hp.run (hp.run.time_nonneg j)
      (fun _ h => hp.run.time_mono h.le) hy
    exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl
      ⟨y, j, tr.time j, hp.run.time_nonneg j, fun _ h => hp.run.time_mono h.le, hy,
        (Store.cache_invariants _ _ _ _ hr).1⟩ hg hP
  · exact hroot.trans (hbound x r l B ho ht hrb)
  · exact hroot.trans (hcovered hcover C s hC hsu)

/-- Pre-slot high origins and healed members strictly below the cast slot bound its root. -/
theorem reset_vote_root_below_bound_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) B P)
    (hcovered : ∀ C s, Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) C s b → s < u → Anc (tr.HonestBlocksAt H) C P)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.fcRoot P := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun _ hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hr := fg_reachable_at hp.run ht hj hy
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨y, j, tr.time j, ht, hj, hy, hX⟩
  have hfr := Outcome.frame_of_call hp.run hy hc.1
  obtain ⟨hFm, hJm, hFJ, ⟨C, hCm, hCJ, _⟩, hmax, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hCm
  obtain rfl : E = (tr.state y j).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hCJ)
  have hroot : (tr.state y j).fg.fcRoot = (tr.state y j).fg.J ∨
      (tr.state y j).fg.fcRoot = (tr.state y j).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · have hgen : (tr.state y j).fg.fcRoot.root = sp.genesisRoot := by
      rcases hroot with h | h
      · exact congrArg (·.root) (h.trans hg)
      · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
        rw [← hg] at hJF
        have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
        exact congrArg (·.root) (h.trans (he.trans hg))
    have hmem : (tr.state y j).fg.fcRoot ∈ (tr.state y j).fg.tree := by
      rcases hroot with h | h <;> rw [h]
      · exact hJm
      · exact hFm
    exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hsub hmem) hgen hP
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y j).fg.hj
  · obtain ⟨W, hW, att, ha, v, d, hv, hdj, hs, hT, hsource⟩ :=
      hp.left_entry_origin_or_covered_at ht hj hy hjb hJm hJT (by omega) hEC
        (by have := Store.hj_lt_h hr hCm; omega)
    have hJP : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.J P := by
      rcases hsource with ⟨r, hrd, l, O, ho, hJO⟩ | ⟨hvz, hcov⟩
      · have hlu : l < u := hes ▸ KernelProof.row_origin_label_lt_at hp hy hc hW ha
          (hp.run.antitone (hp.run.time_mono hdj.le) hv) hs hdj hrd ho
        obtain ⟨CV, ellw, D, _, hfl, _⟩ := ho.2.2.1
        have hrj : tr.time r ≤ tr.time j := hp.run.time_mono (by omega)
        have htupper := (Compose.Growing.cast_head_fcRoot_at hp.run hp.noColl hy hc).2
        have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (hrj.trans (hes ▸ htupper))
        exact hJO.trans (hbound v r l O ho hrt (hrj.trans hjb))
      · obtain ⟨hcov, _⟩ := coveredUpTo_iff.1 hcov
        obtain ⟨C', s, hC', hsu, hJC'⟩ := Outcome.row_entry_member_before_cast_at hp hy hjb hc
          hW ha hvz hs hdj hJm hT (by omega) hcov
        exact hJC'.trans (hcovered C' s hC'.healedOrigin (hes ▸ hsu))
    rcases hroot with h | h
    · rw [h]; exact hJP
    · rw [h]; exact (hFJ.mono hsub).trans hJP
  obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hFO := hp.low_finalized_below_origin_at ht hj hy hjb (by omega) ho hrb
  have hFO' : Anc (tr.HonestBlocksAt H) ell.frame.F O := by rw [hfr]; exact hFO
  have hOf := (hp.high_origin_held_at_vote_at ho hrb hy hc hjb (by omega) hFO').1
  have hOt := (frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hOf
  have hOh := Outcome.high_of_anc_at hp.run hp.noColl ho ht hj hy hOt .refl
  have hOm := hmax O hOt
  have hOP := hbound v r l O ho hrt hrb
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hJO : (tr.state y j).fg.Anc (tr.state y j).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt,
        store_anc_of_honest_anc_at hp.run hp.noColl ht hj hy hFO hOt, by omega, hn⟩
    exact (hJO.mono hsub).trans hOP
  · exact hFO.trans hOP

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
