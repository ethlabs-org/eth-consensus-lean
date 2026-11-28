module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Continuation.LiveWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finalized ancestry and viability after a hand-over

For a reader honest at `t ∈ [t_{r+k}, t_s + Δ]` whose high rows have sources below members of
labels below `s` (the classification of each row, `hlab`):

* `old_cover`: a member of a label below `s` written before `t_s + 2Δ` is below a member of the
  old family `SeededOld s` (itself, or the optimistic origin of label `s − 1` at its cut);
* `seeded_reader_old`: `F` is below a member of the old family. A held block above the whole
  family is viable: the crossing at `hmax - 1` bounds its height, and it either extends the
  high `J` or is strictly higher than the low `hj` by extending the held reset seed. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {K : AC.CommitteeDict sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}
  {T : Time} {r σ : Nat} {t₁ b : Time}

/-- **A member of a label below `s` written before `t_s + 2Δ` is below a member of the old
family**: itself for a label `≤ s − 2`; for the label `s − 1`, the origin of its label at its cut
(`HealedOrigin.below_origin`) is not a result (written at `t_s + 2Δ`), so an optimistic origin. -/
theorem old_cover (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {s : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {l : Nat} {τ : Time}
    (hC : HealedOrigin tr H g r (r + sp.k - 1) C l τ) (hl : l + 1 ≤ s)
    (hτ : τ < sp.ts s + 2 * sp.Δ) (hτb : τ ≤ b) :
    ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) C O := by
  rcases Nat.lt_or_ge (l + 1) s with hlt | hge
  · exact ⟨C, seededOld_iff.2 (Or.inl ⟨l, hC.mono hτb, by omega⟩), .refl⟩
  obtain rfl : l = s - 1 := by omega
  obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
  obtain ⟨x, k, CV, hx, hkτ, hR | hOp⟩ := originWithin_iff.1 hO
  · obtain ⟨ℓ, hu, _⟩ := hR
    have ht : tr.time k = sp.ts (s - 1 : Nat) + 6 * sp.Δ := hu.2.2.1
    have : sp.ts (s - 1 : Nat) + 4 * sp.Δ = sp.ts s := by
      simp only [ACParams.ts]; push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
    linarith
  · exact ⟨O, seededOld_iff.2 (Or.inr ⟨x, k, CV, hx, hOp⟩), hCO⟩

/-- **A seeded reader's finalized ancestry and viability for slot `s`**, for a reader honest
at `t ∈ [t_{r+k}, t_s + Δ]` (earlier cuts at times `≤ t`) that has called from `t_{r−k−3}` on,
whose high rows have sources below members of labels below `s` (`hlab`): `F` is below a member
of `SeededOld s`, and every held block above all members of `SeededOld s` is viable. -/
theorem seeded_reader_old
    (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b K (cm := cm) (βK := βK) (ini := ini))
    {s : Nat}
    (hs : σ + 1 ≤ s) {y : Fin sp.n} {i : Nat} {t : Time} (hdt : sp.ts (r + sp.k : Nat) ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hts : t ≤ sp.ts s + sp.Δ) (htb : t ≤ b) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    (hlab : ∀ m < i, ∀ X, tr.AcceptAt y m X → ∀ a ∈ X.fgPayload, a.val ∈ H t →
      ∀ k < m, tr.SignAt a.val k a → ∀ c < k, ∀ C l O OV,
        HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) →
        (AC.ResultAt tr.projAC a.val c l O OV ∨ AC.OptimisticLockAt tr.projAC a.val c l O OV) →
        l + 1 ≤ s) :
    (∃ O, SeededOld tr H g r b s O ∧
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F O) ∧
      ∀ B ∈ (tr.state y i).fg.tree, (∀ O, SeededOld tr H g r b s O →
          Anc (tr.HonestBlocksAt H) O B) →
        (tr.state y i).fg.IsViable B := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hrσ := hS.seed.timing.2.1
  have hrun := hS.run
  have hnc := hS.noColl
  have ht0 : (0 : Time) ≤ t := (ts_natCast_nonneg _).trans hdt
  have hf : 2 * (H t)ᶜ.ncard < sp.n := hS.bounds.two t ht0 htb
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  have hst := Trace.upTo_state tr y hi
  have hrun' := hrun.upTo ht0
  have hnc' := hnc.upTo t
  have hsub := upTo_subset hrun ht0
  -- the high rows, sourced below members of the old family
  have hzt : Healing.cutZ sp.toParams g ≤ t := by
    have := ts_le_ts (sp := sp) (show r ≤ r + sp.k by omega)
    linarith [Healing.cutZ_le sp g, hS.seed.timing.2.2]
  have hsrc := rowsAbove_of hrun hnc hS.seed.toHandoverCore ht0 hzt hi hy
    (Q := fun C _ => ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) C O)
    fun m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO => by
      have hct' : tr.time c ≤ t := (hrun.time_mono (show c ≤ m by omega)).trans (hi m hm)
      exact old_cover hrun hnc hC (hlab m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO)
        (by linarith) (hct'.trans htb)
  set G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D => ∃ C l,
    (∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) C O) ∧
      C ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D C with hG
  have hGO : ∀ D, G D → ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) D O := by
    rintro D ⟨C, l, ⟨O, hO, hCO⟩, -, hDC⟩
    exact ⟨O, hO, (hDC.mono hsub).trans hCO⟩
  -- the reset seed of a low reader is a member of the old family
  have hseedOld : ∀ {x q l} {S : AC.Blk sp.n (List (FG.Att sp.n))},
      Healing.Growing.HighOrigin tr H g x q l S → tr.time q ≤ T → l < r →
      SeededOld tr H g r b s S := fun hS' hqT hl =>
    seededOld_iff.2 (Or.inl ⟨_, .of_high (hqT.trans hS.horizon) hS', by omega⟩)
  -- below a block above the old family, every source of `G` is below it, inside the prefix
  have hbelow : ∀ {B}, B ∈ (tr.state y i).fg.tree →
      (∀ O, SeededOld tr H g r b s O → Anc (tr.HonestBlocksAt H) O B) →
      ∀ D, G D → Anc ((tr.upTo t).HonestBlocks (H t)) D B := by
    intro B hB hOB D hD
    obtain ⟨O, hO, hDO⟩ := hGO D hD
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 ⟨y, hy, i, by rw [hst]; exact hB⟩
      (hDO.trans (hOB O hO))
  refine ⟨?_, fun B hB hOB => ?_⟩
  · -- Finalized ancestry, through the held seed or the high justified entry.
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
    · obtain ⟨x, q, l, S, hS', hqT, hl, hFS, -⟩ :=
        low_seed_held hrun hnc hS.conv hS.seed.toHandoverCore ht0 hi hy hcall hlow
      exact ⟨S, hseedOld hS' hqT hl, hFS⟩
    obtain ⟨-, hJm, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
    have hFJ' := Healing.Growing.honest_anc_of_store_anc_at ht0 hi hy hFJ
    have hJ : ∃ O, SeededOld tr H g r b s O ∧
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J O := by
      have hsrc' := rowsAbove_height_mono hsrc
        (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo t).state y i).fg.hj by rw [hst]; omega)
      obtain ⟨-, -, D, hD, hDs⟩ := Compose.justified_honest_source_of hrun' hnc' hf hy hsrc'
        (by rw [hst]; omega)
      rw [hst] at hDs
      have hJP : (tr.state y i).fg.J ∈ (tr.upTo t).HonestBlocks (H t) :=
        ⟨y, hy, i, by rw [hst]; exact hJm⟩
      obtain ⟨x', hx', k', -, -, hJD, -, -⟩ :=
        Compose.honest_source_entry hrun' hnc' hDs hJP rfl
      obtain ⟨O, hO, hDO⟩ := hGO D hD
      exact ⟨O, hO, (Anc.mono (fun Z hZ => hsub ⟨x', hx', k', hZ⟩) hJD).trans hDO⟩
    obtain ⟨O, hO, hJO⟩ := hJ
    exact ⟨O, hO, hFJ'.trans hJO⟩
  · -- Viability at the maximum or its predecessor.
    have hGB := hbelow hB hOB
    have finish : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h →
        (tr.state y i).fg.IsViable B := by
      intro hpred
      change _ ∨ (_ ∧ _)
      by_cases hh : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ B.root).h
      · exact Or.inl hh
      refine Or.inr ⟨by omega, ?_⟩
      by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
      · left
        obtain ⟨x, q, l, S, hS', hqT, hl, _, hSy, _⟩ :=
          low_seed_held hrun hnc hS.conv hS.seed.toHandoverCore ht0 hi hy hcall hlow
        have hSB := hOB S (hseedOld hS' hqT hl)
        have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
          rw [Healing.Growing.σ_eq_honest_at hrun hnc ht0 hi hy (hrun.time_nonneg q)
            (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hS'.1) hSy
            (HighOrigin.mem_tree hrun hnc hS')]
          exact hS'.2.2.2
        have := Healing.h_le_of_store_anc hreach (held_anc_at hrun hnc ht0 hy hi hSB hB)
        omega
      · right
        have hsrc' := rowsAbove_height_mono hsrc
          (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo t).state y i).fg.hj by rw [hst]; omega)
        obtain ⟨_, _, D, hD, hDs⟩ := Compose.justified_honest_source_of hrun' hnc' hf hy hsrc'
          (by rw [hst]; omega)
        have hJm := (Goldilocks.Store.cache_invariants _ _ _ _ hreach).2.1
        obtain ⟨x', hx', k', _, _, hJD, _, _⟩ := Compose.honest_source_entry hrun' hnc' hDs
          ⟨y, hy, i, by rw [hst]; exact hJm⟩ rfl
        have hJB := (hJD.mono (Compose.fg_tree_subset_honest hx' k')).trans (hGB D hD)
        have hheld := Compose.honest_held_anc hrun' hnc' hy hJB (by rw [hst]; exact hB)
        rwa [hst] at hheld
    apply finish
    by_contra hlt
    have hh : ((tr.state y i).fg.σ B.root).h < (tr.state y i).fg.hmax - 1 := by omega
    have hhigh : Healing.Growing.HZ tr H g + 1 ≤ (tr.state y i).fg.hmax - 1 := by
      by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
      · obtain ⟨x, q, l, S, hS', hqT, hl, _, hSy, -⟩ :=
          low_seed_held hrun hnc hS.conv hS.seed.toHandoverCore ht0 hi hy hcall hlow
        have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
          rw [Healing.Growing.σ_eq_honest_at hrun hnc ht0 hi hy (hrun.time_nonneg q)
            (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hS'.1) hSy
            (HighOrigin.mem_tree hrun hnc hS')]
          exact hS'.2.2.2
        have hSB := hOB S (hseedOld hS' hqT hl)
        exact (hSh.trans (Healing.h_le_of_store_anc hreach
          (held_anc_at hrun hnc ht0 hy hi hSB hB))).trans hh.le
      · have := Healing.Store.hj_lt_hmax_of_reachable hreach
        omega
    obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, -, hEh, -, D, hD, hDs⟩ := Compose.frame_crossing_source_of hrun' hnc' hf hy
      hsrc (W := X) (j := (tr.state y i).fg.hmax - 1) (by rw [hst]; exact hX) hhigh
      (by omega) (by rw [hst, hXh]; omega)
    obtain ⟨x', hx', k', -, -, hED, -, -⟩ :=
      Compose.honest_source_entry hrun' hnc' hDs ⟨y, hy, i, hE⟩ rfl
    have hEB : Anc ((tr.upTo t).HonestBlocks (H t)) E B :=
      (hED.mono (Compose.fg_tree_subset_honest hx' k')).trans (hGB D hD)
    have hle := Healing.h_le_of_store_anc hreach
      (held_anc_at hrun hnc ht0 hy hi (hEB.mono hsub) hB)
    rw [hst] at hEh
    omega

end Consensus.Goldilocks.Compose.Growing

end
