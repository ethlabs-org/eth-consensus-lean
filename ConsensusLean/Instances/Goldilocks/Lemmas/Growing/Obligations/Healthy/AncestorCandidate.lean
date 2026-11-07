module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.RetainedPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RetentionPending
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A held target is an ancestor candidate, under growing faults

`held_target_ancestor_candidate_at_state_at`, the growing form of
`Obligations.UpTo.held_target_ancestor_candidate_at_state`: at a state of a reader honest at an
observation `t ≤ b`, every earlier cut at a time `≤ t`, a held target above a bounded high seed
and compatible with every earlier high origin is an ancestor candidate of the reader's frame.

The fork-choice root compares with the target by the state-level forms of the call-level root
lemmas `high_J_root_of_held_at_call_before_at` and `low_root_of_held_seed_at_call_at` (the same
arguments, with the reader's honesty read at `t`); an entry at or past the head-height floor
above the target comes from a high floor's signed source
(`high_floor_signed_source_of_row_bound_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- With a high justified height, the fork-choice root of a state of a reader honest at `t ≤ b`
is compatible with every block it holds that is compatible with the earlier high origins. -/
private theorem high_J_root_at_state (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
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
      Outcome.high_row_source_at hrun hnc hv hs (by rw [← hE'h, hσ]; exact hEh)
    have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
        fun q hq => hrun.time_mono hq.le, ho.1, h⟩
    obtain rfl : E₀ = E' := hU.1 (hsub₀ hE₀) (hsub' hE') (hE₀r.trans hE'r.symm)
    have hEO : Anc (tr.HonestBlocksAt H) E₀ O := hE₀O.mono hsub₀
    rcases hcompare _ r l O (by clear * - hi' hrd hdi; omega) ho with hBO | hOB
    · exact hncE (SA.anc_total hU hEO hBO)
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
    · exact SA.anc_total hU (hFJ.mono hsub) hBJ
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- With a low justified height and a held high seed, the fork-choice root of a state of a reader
honest at `t ≤ b` is compatible with every block compatible with the seed that the reader holds
once it is above `Σ.F`. -/
private theorem low_root_at_state (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B S : SA.Blk sp.n (List (FG.Att sp.n))}
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
    · exact SA.anc_total hU
        (hJ S hSy (store_anc_of_honest_anc_at hrun hnc ht hle hy hFS hSy) hSh
          hactive.1 hactive.2) hBS
    · have hFB := hFS.trans hSB
      have hBy := hheld hFB
      have hBhy := Outcome.high_of_anc_at hrun hnc hS ht hle hy hBy hSB
      exact Or.inl (hJ B hBy (store_anc_of_honest_anc_at hrun hnc ht hle hy hFB hBy) hBhy
        hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact SA.anc_total hU hFS hBS
    · exact Or.inl (hFS.trans hSB)

/-- **A held target is an ancestor candidate.** At a state of a reader honest at `t ≤ b`, every
earlier cut at a time `≤ t`, a target held in the reader's frame above a bounded high seed and
compatible with every earlier high origin is an ancestor candidate of the frame. -/
theorem held_target_ancestor_candidate_at_state_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) P B) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hPhi := (Store.frame_realization _ _ _ _ hreach).1
  have hPhiU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, i, t, ht, hle, hy, hX.1⟩
  have hPy := hPt.1
  have hSy := mem_of_honest_anc_at hrun hnc ht hle hy hSP hPy
  have hroot : Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot P := by
    change Compatible _ (tr.state y i).fg.fcRoot P
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact low_root_at_state hp ht hle hy htb hseed hqb hSy hlow (Or.inr hSP) (fun _ => hPy)
    · exact high_J_root_at_state hp ht hle hy htb hPy (by omega)
        (fun x r l B hri ho => hcompare x r l B hri ho)
  rcases hroot with hroot | hroot
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hPhiU hPt hroot hPhi.fcRoot_mem)
  have hrootf := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hroot hPt
  have witness : ∃ E ∈ (tr.state y i).fg.tree,
      Anc (tr.HonestBlocksAt H) P E ∧
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ E.root).h := by
    by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · exact ⟨P, hPy, .refl, hfloor⟩
    have hSs := Outcome.high_origin_mem_at hrun hnc hseed
    have hSh := Healing.σ_h_le_of_anc hreach
      (store_anc_of_honest_anc_at hrun hnc ht hle hy hSP hPy)
    have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
      rw [σ_eq_honest_at hrun hnc (hrun.time_nonneg q) (fun r hr => hrun.time_mono hr.le)
        hseed.1 ht hle hy hSs hSy]
      omega
    obtain ⟨x, r, l, O, E, hri, ho, -, hE, hEO, -, hEf, -⟩ :=
      hp.high_floor_signed_source_of_row_bound_at hseed ht hle hy htb
        (u := sp.slot t + 1)
        (fun W hW att ha z d hz hs hdi r' l O hrd ho => by
          obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
          have htl : sp.ts l ≤ tr.time r' := by
            rcases hfl with ⟨ell, C, ⟨-, -, htu, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
            · change tr.time r' = sp.ts l + 6 * sp.Δ at htu
              linarith [sp.toParams.hΔ]
            · change sp.slot (tr.time r') = l at hsl
              exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r') l).2 (by omega)
          have := (SA.ts_le_iff_le_slot sp ht l).1 (htl.trans (hle r' (by omega)))
          omega)
        (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible_at ho
          ((hle r hri).trans htb) ho' ((hle r' hr'i).trans htb))
        (fun x r l B hri ho => hp.origins_compatible_at hseed hqb ho
          ((hle r hri).trans htb)) hSf
    have hPE : Compatible (tr.HonestBlocksAt H) P E := by
      rcases hcompare x r l O hri ho with h | h
      · exact SA.anc_total hU h hEO
      · exact Or.inr (hEO.trans h)
    rcases hPE with hPE | hEP
    · exact ⟨E, hE, hPE, hEf⟩
    · have := Healing.σ_h_le_of_anc hreach
        (store_anc_of_honest_anc_at hrun hnc ht hle hy hEP hPy)
      omega
  obtain ⟨E, hE, hPE, hEf⟩ := witness
  have hPEs := store_anc_of_honest_anc_at hrun hnc ht hle hy hPE hE
  have hEt : E ∈ (Node.frame (tr.state y i)).tree := ⟨hE, hPt.2.trans hPEs⟩
  have hPEf := SA.anc_tree_of_anc_U hU hPhi hPhiU hPt hPE hEt
  refine Or.inr ⟨hPt, hrootf, E, hEt, ?_, hPEf⟩
  have hRE := hrootf.trans hPEf
  exact ⟨hE, hPt.2.trans hPEs, Anc.mono (fun _ h => h.1) hRE, hEf⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
