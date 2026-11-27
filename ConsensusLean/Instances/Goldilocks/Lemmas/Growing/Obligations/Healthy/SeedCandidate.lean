module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A guarded high seed supplies current candidacy, under growing faults

`guarded_seed_ancestor_candidate_at_state_covered_at`, the growing form of
The guarded seed ancestor candidate: at a state of a reader honest at an
observation `t ≤ b`, every earlier cut at a time `≤ t`, a target held in the reader's frame,
compatible with a bounded high seed that is held whenever it is above finalization, and compatible
with every earlier high origin, is an ancestor candidate of the frame.

The store argument is `Store.guarded_seed_ancestor_candidate`. The fork-choice root compares
with the target by the state-level forms of the call-level root lemmas
`high_J_root_of_held_at_call_before_covered_at` and `low_root_of_held_seed_at_call_at` (the same
arguments, with the reader's honesty read at `t`); a seed below the head-height floor leaves an
entry at or past it below an earlier high origin, from a high floor's signed source
(`high_floor_signed_source_or_covered_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- With a high justified height, the fork-choice root of a state of a reader honest at `t ≤ b`
is compatible with every block it holds that is compatible with the earlier high origins, when `t`
is inside the deep quarantine. -/
private theorem high_J_root_at_state_quarantine {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hpre : ∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _ hreach).2.2.2 B hBy).mono hsub
  have hcz := hp.cutZ_le_of_high_hj_at ht hle hy hhigh
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocksAt H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H t := by
    intro E hE hEh _ hncE W hW att ha haT haH
    have he := Trace.upTo_state tr y hle
    have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
    rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
    · cases ha
    have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
    obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
      (hrun.antitone (hle i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
      (hrun.antitone (hle i' hi') haH)
    have hdk : d < k := hdi.trans hi'
    have hv := hrun.antitone (hle d hdk) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
      (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
    rw [he'] at hE' hE'h
    have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
        fun q hq => hrun.time_mono hq.le, hv, h⟩
    obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
      (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
    obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      Outcome.high_row_source_at hrun hnc (hrun.antitone (max_le hcz (hle d hdk)) haH) hs
        (by rw [← hE'h, hσ]; exact hEh) (hp.snapshot.imp fun _ h => h.1)
        fun D hD => (hle d hdk).trans (hpre D hD)
    have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
        fun q hq => hrun.time_mono hq.le, hrun.antitone (le_max_right _ _) ho.1, h⟩
    obtain rfl : E₀ = E' := hU.1 (hsub₀ hE₀) (hsub' hE') (hE₀r.trans hE'r.symm)
    have hEO : Anc (tr.HonestBlocksAt H) E₀ O := hE₀O.mono hsub₀
    rcases hcompare _ r l O (by clear * - hi' hrd hdi; omega) ho with hBO | hOB
    · exact hncE (AC.anc_total hU hEO hBO)
    · exact hncE (Or.inl (hEO.trans hOB))
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults t ht htb
    have hn := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  have hJ := Store.J_compatible_of_rows hreach hq hU hsub hgB hrow hhigh
  have hF : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
    obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hreach
    rcases hJ with hJB | hBJ
    · exact Or.inl ((hFJ.mono hsub).trans hJB)
    · exact AC.anc_total hU (hFJ.mono hsub) hBJ
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- The same for a block compatible with the earlier high origins and, under the high-source cover,
the healed members up to the slot of `t`. -/
private theorem high_J_root_at_state_covered {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : CompatibleWithOrigins tr H g a b k (sp.slot t) B) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.fcRoot B := by
  rcases hp.quarantine_or_cover_at htb with hpre | hc
  · exact high_J_root_at_state_quarantine hp ht hle hy htb hBy hhigh hpre
      (compatibleWithOrigins_iff.1 hcompare).1
  · exact hp.high_J_root_of_held_cover_at ht hle hy htb ht hle hy hBy hhigh hc
      ((compatibleWithOrigins_iff.1 hcompare).2 hc)

/-- With a low justified height and a held high seed, the fork-choice root of a state of a reader
honest at `t ≤ b` is compatible with every block compatible with the seed that the reader holds
once it is above `Σ.F`. -/
private theorem low_root_at_state {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (hSy : S ∈ (tr.state y i).fg.tree) (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B → B ∈ (tr.state y i).fg.tree) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hFS := hp.low_finalized_below_origin_at ht hle hy htb hlow hS hqb
  have hSh := Outcome.high_of_anc_at hrun hnc hS ht hle hy hSy .refl
  have hJ : ∀ D ∈ (tr.state y i).fg.tree,
      (tr.state y i).fg.Anc (tr.state y i).fg.F D →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ D.root).h →
      (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬ (tr.state y i).fg.Contest → Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D := by
    intro D hD hFD hDh he hn
    have hle' := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 D hD
    have hJD : (tr.state y i).fg.Anc (tr.state y i).fg.J D := by
      by_contra h
      exact hn ⟨he, D, hD, hFD, by clear * - hlow hDh he hle'; omega, h⟩
    exact hJD.mono fun X hX => ⟨y, i, t, ht, hle, hy, hX⟩
  unfold Store.fcRoot
  split_ifs with hactive
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU
        (hJ S hSy (store_anc_of_honest_anc_at hrun hnc ht hle hy hFS hSy) hSh
          hactive.1 hactive.2) hBS
    · have hFB := hFS.trans hSB
      have hBy := hheld hFB
      have hBhy := Outcome.high_of_anc_at hrun hnc hS ht hle hy hBy hSB
      exact Or.inl (hJ B hBy (store_anc_of_honest_anc_at hrun hnc ht hle hy hFB hBy) hBhy
        hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU hFS hBS
    · exact Or.inl (hFS.trans hSB)

/-- The row labels of the signings read by a reader at `t` are below the slot after `t`. -/
private theorem guarded_row_bound {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t) :
    ∀ W ∈ (tr.state y i).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ z d, z ∈ H (tr.time d) → tr.SignAt z d att → d < i → ∀ r' l O,
        r' < d → HighOrigin tr H g z r' l O → l < sp.slot t + 1 := by
  intro W hW att ha z d hz hs hdi r' l O hrd ho
  obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
  have htl : sp.ts l ≤ tr.time r' := by
    rcases hfl with ⟨ell, C, ⟨-, -, htu, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
    · change tr.time r' = sp.ts l + 6 * sp.Δ at htu
      linarith [sp.toParams.hΔ]
    · change sp.slot (tr.time r') = l at hsl
      exact (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r') l).2 (by omega)
  have := (AC.ts_le_iff_le_slot sp ht l).1 (htl.trans (hle r' (by omega)))
  omega

/-- The candidacy argument, given the high-height root comparison and a source for the floor. -/
private theorem guarded_seed_ancestor_candidate_of_root
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b)
    (hhold : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S → S ∈ (tr.state y i).fg.tree)
    (hPS : Compatible (tr.HonestBlocksAt H) P S)
    {Origin : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hcompare : ∀ O, Origin O → Compatible (tr.HonestBlocksAt H) P O)
    (hsource : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor →
      ∃ O, Origin O ∧ ∃ E ∈ (tr.state y i).fg.tree, Anc (tr.HonestBlocksAt H) E O ∧
        (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ E.root).h)
    (hhighroot : ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hreach := fg_reachable_at hrun ht hle hy
  have hPy := hPt.1
  have hSs := Outcome.high_origin_mem_at hrun hnc hseed
  refine Store.guarded_seed_ancestor_candidate hreach
    (Compose.Growing.honest_blocks_coherent hrun hnc) (fun X hX => ⟨y, i, t, ht, hle, hy, hX⟩)
    (Healing.h_le_of_store_anc hreach) hPt
    (fun hSy => congrArg (·.h) (σ_eq_honest_at hrun hnc (hrun.time_nonneg q)
      (fun r hr => hrun.time_mono hr.le) (hrun.antitone (le_max_right _ _) hseed.1) ht hle hy
      hSs hSy).symm)
    hhold hPS ?_ hcompare hsource
  by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
  · have hSy := hhold (hp.low_finalized_below_origin_at ht hle hy htb hlow hseed hqb)
    exact low_root_at_state hp ht hle hy htb hseed hqb hSy hlow hPS (fun _ => hPy)
  · exact hhighroot hlow

/-- **A comparable bounded high seed, held whenever it is above finalization, supplies current
candidacy**, at a state of a reader honest at a read time `t ≤ b`, every earlier cut at a time
`≤ t`, for a target compatible with the earlier high origins and, under the high-source cover, the
healed members up to the slot of `t`. A local signed entry witnesses any higher floor. -/
theorem guarded_seed_ancestor_candidate_at_state_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b)
    (hhold : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S → S ∈ (tr.state y i).fg.tree)
    (hPS : Compatible (tr.HonestBlocksAt H) P S)
    (hcompare : CompatibleWithOrigins tr H g a b i (sp.slot t) P) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  obtain ⟨hcomp1, hcomp2⟩ := compatibleWithOrigins_iff.1 hcompare
  refine guarded_seed_ancestor_candidate_of_root hp ht hle hy htb hPt hseed hqb hhold hPS
    (Origin := fun B => (∃ x r l, r < i ∧ HighOrigin tr H g x r l B) ∨
      (HighSourceCover tr H g a b ∧ ∃ s, HealedMemberBefore tr H g a b B s i ∧ s ≤ sp.slot t))
    (fun B hB => hB.elim (fun ⟨x, r, l, hri, ho⟩ => hcomp1 x r l B hri ho)
      (fun ⟨hc, s, hs, hsm⟩ => hcomp2 hc B s hs hsm))
    (fun hSf => ?_)
    fun hlow => high_J_root_at_state_covered hp ht hle hy htb hPt.1 (by omega) hcompare
  rcases hp.high_floor_signed_source_or_covered_before_at hseed ht hle hy htb
      (u := sp.slot t + 1)
      (guarded_row_bound hp ht hle)
      (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible_at ho
        ((hle r hri).trans htb) ho' ((hle r' hr'i).trans htb))
      (fun x r l B hri ho => hp.origins_compatible_at hseed hqb ho
        ((hle r hri).trans htb)) hSf with
    ⟨x, r, l, O, E, hri, ho, -, hE, hEO, -, hEf, -⟩ | ⟨E, hE, hcov, hEf, -⟩
  · exact ⟨O, Or.inl ⟨x, r, l, hri, ho⟩, E, hE, hEO, hEf⟩
  · obtain ⟨hc, C, s, hC, hsm, hEC⟩ := coveredBefore_iff.1 hcov
    exact ⟨C, Or.inr ⟨hc, s, hC, hsm⟩, E, hE, hEC, hEf⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
