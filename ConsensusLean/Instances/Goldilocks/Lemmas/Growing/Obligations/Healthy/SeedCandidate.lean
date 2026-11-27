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

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

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
    (hsource : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.hmax - 1 →
      ∃ O, Origin O ∧ ∃ E ∈ (tr.state y i).fg.tree, Anc (tr.HonestBlocksAt H) E O ∧
        (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ E.root).h)
    (hhighroot : (tr.state y i).fg.hmax ≤ (tr.state y i).fg.hj + 1 →
      ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J P) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hreach := fg_reachable_at hrun ht hle hy
  have hPy := hPt.1
  have hSs := Outcome.high_origin_mem_at hrun hnc hseed
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, i, t, ht, hle, hy, hX⟩
  have hanc : ∀ {A C : AC.Blk sp.n (List (FG.Att sp.n))},
      Anc (tr.HonestBlocksAt H) A C → C ∈ (tr.state y i).fg.tree →
      (tr.state y i).fg.Anc A C :=
    fun h hC => Store.anc_of_anc_universe hreach hU hsub h hC
  have hSy : S ∈ (tr.state y i).fg.tree := by
    rcases hPS with hPS | hSP
    · exact hhold ((hPt.2.mono hsub).trans hPS)
    · by_cases he : S = P
      · exact he ▸ hPy
      · exact (Anc.mem (hanc hSP hPy) he).1
  have hcomp : ∀ A B, Compatible (tr.HonestBlocksAt H) A B →
      A ∈ (tr.state y i).fg.tree → B ∈ (tr.state y i).fg.tree →
      Compatible (tr.state y i).fg.tree A B := by
    intro A B hc hA hB
    exact hc.elim (fun h => Or.inl (hanc h hB)) (fun h => Or.inr (hanc h hA))
  refine Store.guarded_seed_ancestor_candidate hreach hPt
    (fun hSy => congrArg (·.h) (σ_eq_honest_at hrun hnc (hrun.time_nonneg q)
      (fun r hr => hrun.time_mono hr.le) (hrun.antitone (le_max_right _ _) hseed.1) ht hle hy
      hSs hSy).symm)
    (Outcome.high_of_anc_at hrun hnc hseed (hrun.time_nonneg q)
      (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hseed.1) hSs .refl)
    (fun h => hhold (h.mono hsub)) ?_ (hcomp P S hPS hPy hSy) ?_
    (Origin := fun E => E ∈ (tr.state y i).fg.tree ∧
      ∃ O, Origin O ∧ Anc (tr.HonestBlocksAt H) E O) ?_ ?_
  · intro hlow
    have hFS := hp.low_finalized_below_origin_at ht hle hy htb hlow hseed hqb
    exact hanc hFS (hhold hFS)
  · intro htop hhigh
    exact hcomp _ _ (hhighroot htop hhigh)
      (Store.cache_invariants _ _ _ _ hreach).2.1 hPy
  · rintro E ⟨hE, O, ho, hEO⟩
    apply hcomp P E _ hPy hE
    rcases hcompare O ho with hPO | hOP
    · exact Anc.total hU hPO hEO
    · exact Or.inr (hEO.trans hOP)
  · intro hf
    obtain ⟨O, ho, E, hE, hEO, hEf⟩ := hsource hf
    exact ⟨E, ⟨hE, O, ho, hEO⟩, E, hE, .refl, hEf⟩

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
    fun _ hlow => hp.high_J_root_J_compatible_covered_at ht hle hy htb hPt.1 (by omega) hcompare
  have hpred : (tr.state y i).fg.hmax - 1 ≤ (tr.state y i).fg.headHeightFloor := by
    unfold Store.headHeightFloor
    split_ifs <;> omega
  rcases hp.high_floor_signed_source_or_covered_before_at hseed ht hle hy htb
      (u := sp.slot t + 1)
      (guarded_row_bound hp ht hle)
      (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible_at ho
        ((hle r hri).trans htb) ho' ((hle r' hr'i).trans htb))
      (fun x r l B hri ho => hp.origins_compatible_at hseed hqb ho
        ((hle r hri).trans htb)) (hSf.trans_le hpred) with
    ⟨x, r, l, O, E, hri, ho, -, hE, hEO, -, hEf, -⟩ | ⟨E, hE, hcov, hEf, -⟩
  · exact ⟨O, Or.inl ⟨x, r, l, hri, ho⟩, E, hE, hEO, hpred.trans hEf⟩
  · obtain ⟨hc, C, s, hC, hsm, hEC⟩ := coveredBefore_iff.1 hcov
    exact ⟨C, Or.inr ⟨hc, s, hC, hsm⟩, E, hE, hEC, hpred.trans hEf⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
