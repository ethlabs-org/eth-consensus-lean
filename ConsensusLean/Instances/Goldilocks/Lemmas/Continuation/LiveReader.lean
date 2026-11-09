module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.LiveWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A reader's caches and floor below the old family after a hand-over

For a reader honest at `t ∈ [t_{r+k}, t_s + Δ]` whose high rows have sources below members of
labels below `s` (the classification of each row, `hlab`):

* `old_cover`: a member of a label below `s` written before `t_s + 2Δ` is below a member of the
  old family `SeededOld s` (itself, or the optimistic origin of label `s − 1` at its cut);
* `seeded_reader_old`: the reader's `fc_root` is below a member of the old family, and its head
  height floor is at most the height of every block of its tree above the whole old family. High
  reader: the justified entry and the floor crossings are below the sources of high rows
  (`rowsAbove_of`, the store geometry). Low reader: `fc_root` is below the held reset seed,
  a member of a label `< r` (`low_seed_held`); when the floor is above the seed's height
  there is no contest, and the floor crossing is a high row. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}
  {T : Time} {r σ : Nat} {t₁ b : Time}

/-- **A member of a label below `s` written before `t_s + 2Δ` is below a member of the old
family**: itself for a label `≤ s − 2`; for the label `s − 1`, the origin of its label at its cut
(`HealedOrigin.below_origin`) is not a result (written at `t_s + 2Δ`), so an optimistic origin. -/
theorem old_cover (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {l : Nat} {τ : Time}
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
      simp only [SAParams.ts]; push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
    linarith
  · exact ⟨O, seededOld_iff.2 (Or.inr ⟨x, k, CV, hx, hOp⟩), hCO⟩

/-- **A seeded reader's `fc_root` and floor below the old family of slot `s`**, for a reader honest
at `t ∈ [t_{r+k}, t_s + Δ]` (earlier cuts at times `≤ t`) that has called from `t_{r−k−3}` on,
whose high rows have sources below members of labels below `s` (`hlab`): `fc_root` is below a
member of `SeededOld s`, and the head height floor is at most the height of every block of the
tree above every member of `SeededOld s`. -/
theorem seeded_reader_old (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {s : Nat}
    (hs : σ + 1 ≤ s) {y : Fin sp.n} {i : Nat} {t : Time} (hdt : sp.ts (r + sp.k : Nat) ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hts : t ≤ sp.ts s + sp.Δ) (htb : t ≤ b) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    (hlab : ∀ m < i, ∀ X, tr.AcceptAt y m X → ∀ a ∈ X.fgPayload, a.val ∈ H t →
      ∀ k < m, tr.SignAt a.val k a → ∀ c < k, ∀ C l O OV,
        HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) →
        (SA.ResultAt tr.projAC a.val c l O OV ∨ SA.OptimisticLockAt tr.projAC a.val c l O OV) →
        l + 1 ≤ s) :
    (∃ O, SeededOld tr H g r b s O ∧
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot O) ∧
      ∀ B ∈ (tr.state y i).fg.tree, (∀ O, SeededOld tr H g r b s O →
          Anc (tr.HonestBlocksAt H) O B) →
        (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h := by
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
  have hUP := (Compose.projFG_localRun hrun' hnc').coherent
  have hsub := upTo_subset hrun ht0
  -- the high rows, sourced below members of the old family
  have hsrc := rowsAbove_of hrun hnc hS.seed ht0 hi hy
    (Q := fun C _ => ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) C O)
    fun m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO => by
      have hct' : tr.time c ≤ t := (hrun.time_mono (show c ≤ m by omega)).trans (hi m hm)
      exact old_cover hrun hnc hC (hlab m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO)
        (by linarith) (hct'.trans htb)
  set G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D => ∃ C l,
    (∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) C O) ∧
      C ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D C with hG
  have hGO : ∀ D, G D → ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) D O := by
    rintro D ⟨C, l, ⟨O, hO, hCO⟩, -, hDC⟩
    exact ⟨O, hO, (hDC.mono hsub).trans hCO⟩
  -- the reset seed of a low reader is a member of the old family
  have hseedOld : ∀ {x q l} {S : SA.Blk sp.n (List (FG.Att sp.n))},
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
  · -- `fc_root`
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
    · obtain ⟨x, q, l, S, hS', hqT, hl, hFS, hSy, -⟩ :=
        low_seed_held hrun hnc hS.conv hS.seed ht0 hi hy hcall hlow
      exact ⟨S, hseedOld hS' hqT hl,
        low_fcRoot_below hrun hnc ht0 hi hy hlow hS' hSy hFS⟩
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
    refine ⟨O, hO, ?_⟩
    rw [Goldilocks.Store.fcRoot]
    split_ifs
    · exact hJO
    · exact hFJ'.trans hJO
  · -- the floor
    have hGB := hbelow hB hOB
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
    · obtain ⟨x, q, l, S, hS', hqT, hl, hFS, hSy, -⟩ :=
        low_seed_held hrun hnc hS.conv hS.seed ht0 hi hy hcall hlow
      have hSB : Anc (tr.HonestBlocksAt H) S B := hOB S (hseedOld hS' hqT hl)
      have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
        rw [Healing.Growing.σ_eq_honest_at hrun hnc ht0 hi hy (hrun.time_nonneg q)
          (fun _ h => hrun.time_mono h.le) hS'.1 hSy (HighOrigin.mem_tree hrun hnc hS')]
        exact hS'.2.2.2
      have hSBh := Healing.h_le_of_store_anc hreach (held_anc_at hrun hnc ht0 hy hi hSB hB)
      by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h
      · omega
      have hcon : ¬ (tr.state y i).fg.Contest := fun hc => hSf (by
        simp only [Goldilocks.Store.headHeightFloor, hc, ↓reduceIte]
        have := hc.1
        omega)
      have hfl' : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
        simp only [Goldilocks.Store.headHeightFloor, hcon, ↓reduceIte]
      by_contra hlt
      obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
      obtain ⟨E, hE, -, hEh, -, D, hD, hDs⟩ := Compose.frame_crossing_source_of hrun' hnc' hf hy
        hsrc (W := X) (j := (tr.state y i).fg.hmax - 1) (by rw [hst]; exact hX) (by omega)
        (by omega) (by rw [hst, hXh]; omega)
      rw [hst] at hE hEh
      have hBE := held_below_entry hrun' hnc' hy (by rw [hst]; exact hB) (by rw [hst]; exact hE)
        hDs (Or.inl (hGB D hD)) (by rw [hst, hEh]; omega)
      rw [hst] at hBE
      obtain ⟨x', hx', k', -, -, hED, -, -⟩ :=
        Compose.honest_source_entry hrun' hnc' hDs ⟨y, hy, i, by rw [hst]; exact hE⟩ rfl
      have hEB : Anc ((tr.upTo t).HonestBlocks (H t)) E B :=
        (Anc.mono (Compose.fg_tree_subset_honest hx' k') hED).trans (hGB D hD)
      obtain rfl : B = E := Anc.antisymm hUP
        (Anc.mono (fun Z hZ => ⟨y, hy, i, by rw [hst]; exact hZ⟩) hBE) hEB
      omega
    · have hsrc' := rowsAbove_height_mono hsrc
        (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo t).state y i).fg.hj by rw [hst]; omega)
      rcases Compose.floor_or_crossing_of hrun' hnc' hf hy hsrc'
          (fun D D' hD hD' => Anc.total hUP (hGB D hD) (hGB D' hD'))
          (fun D hD => Or.inl (hGB D hD)) (by rw [hst]; exact hB) with
        hle | ⟨D, E, -, hD, hDs, hE, hBE, hEh, -⟩
      · rwa [hst] at hle
      obtain ⟨x', hx', k', -, -, hED, -, -⟩ :=
        Compose.honest_source_entry hrun' hnc' hDs ⟨y, hy, i, hE⟩ rfl
      have hEB : Anc ((tr.upTo t).HonestBlocks (H t)) E B :=
        (Anc.mono (Compose.fg_tree_subset_honest hx' k') hED).trans (hGB D hD)
      obtain rfl : B = E := Anc.antisymm hUP
        (Anc.mono (Compose.fg_tree_subset_honest hy i) hBE) hEB
      rw [hst] at hEh
      omega

end Consensus.Goldilocks.Compose.Growing

end
