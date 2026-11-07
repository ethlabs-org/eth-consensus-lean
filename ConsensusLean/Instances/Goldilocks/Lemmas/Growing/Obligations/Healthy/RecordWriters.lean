module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordWritersPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.RetainedPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RetentionPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentSourcesPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Actual local writers and their retained optimistic locks, under growing faults

The growing forms of `Lemmas/Obligations/HealthyRecordWriters`: a writer is honest at its own cut,
a reader honest at a read time `t` with every earlier cut at a time `≤ t`; ancestry is in the
blocks held while honest. The node-local writer facts are the static ones on the prefix through
the cut or read time, where the node is honest throughout. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

variable {g ΔF a b : Time}

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

private theorem guarded_seed_ancestor_candidate_at_state_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b)
    (hhold : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S → S ∈ (tr.state y i).fg.tree)
    (hPS : Compatible (tr.HonestBlocksAt H) P S)
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
  have hroot : Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot P := by
    change Compatible _ (tr.state y i).fg.fcRoot P
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · have hSy := hhold (hp.low_finalized_below_origin_at ht hle hy htb hlow hseed hqb)
      exact low_root_at_state hp ht hle hy htb hseed hqb hSy hlow hPS (fun _ => hPy)
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
    have hσS : S ∈ (tr.state y i).fg.tree →
        (tr.state v q).fg.σ S.root = (tr.state y i).fg.σ S.root := fun hSy =>
      σ_eq_honest_at hrun hnc (hrun.time_nonneg q) (fun r hr => hrun.time_mono hr.le)
        hseed.1 ht hle hy hSs hSy
    by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hPS' : Anc (tr.HonestBlocksAt H) P S := by
        rcases hPS with h | h
        · exact h
        · have hSy := mem_of_honest_anc_at hrun hnc ht hle hy h hPy
          have hSh := Healing.σ_h_le_of_anc hreach
            (store_anc_of_honest_anc_at hrun hnc ht hle hy h hPy)
          rw [hσS hSy] at hSf
          omega
      have hFS : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S :=
        (hPt.2.mono (fun X hX => (⟨y, i, t, ht, hle, hy, hX⟩ : X ∈ tr.HonestBlocksAt H))).trans
          hPS'
      have hSy := hhold hFS
      rw [hσS hSy] at hSf
      exact ⟨S, hSy, hPS', hSf⟩
    replace hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
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

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The writer shape of a cut of the prefix through `d`, read back on the run. -/
private theorem writer_shape_of_upTo
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {d : Time}
    {y : Fin sp.n} {q : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hle : ∀ k < q + 1, tr.time k ≤ d)
    (h : (∃ s CV, SA.ResultAt (tr.upTo d).projAC y q s R CV) ∨
      ((∃ CV, SA.OptimisticLockAt (tr.upTo d).projAC y q (sp.slot ((tr.upTo d).time q)) R CV) ∧
        ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot ((tr.upTo d).time q), true, e⟩ :
          SA.Lock) ∈ ((tr.upTo d).state y (q + 1)).ac.locks)) :
    (∃ s CV, SA.ResultAt tr.projAC y q s R CV) ∨
      ((∃ CV, SA.OptimisticLockAt tr.projAC y q (sp.slot (tr.time q)) R CV) ∧
        ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot (tr.time q), true, e⟩ : SA.Lock) ∈
          (tr.state y (q + 1)).ac.locks) := by
  have hm := hrun.time_mono
  rw [RunTrace.upTo_projAC, Trace.upTo_state tr y hle] at h
  rcases h with ⟨s, CV, hR⟩ | ⟨⟨CV, hO⟩, e, hl⟩
  · exact Or.inl ⟨s, CV, ((Compose.Growing.sa_resultAt_upTo hm).mp hR).2⟩
  · exact Or.inr ⟨⟨CV, ((Compose.Growing.sa_optimisticLockAt_upTo hm).mp hO).2⟩, e, hl⟩

/-- A changed own record identifies its actual call, selected block and, for an optimistic
selection, the normalized lock left by that same call. -/
theorem record_changed_writer_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {q : Nat} (hy : y ∈ H (tr.time q))
    (hne : (tr.state y (q + 1)).ac.latestConfirmed ≠ (tr.state y q).ac.latestConfirmed) :
    ∃ ell, tr.projAC.CallAt y q ell ∧
      ∃ R ∈ ell.frame.tree, (tr.state y (q + 1)).ac.latestConfirmed = R.root ∧
        ((∃ s CV, SA.ResultAt tr.projAC y q s R CV) ∨
          ((∃ CV, SA.OptimisticLockAt tr.projAC y q (sp.slot (tr.time q)) R CV) ∧
            ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot (tr.time q), true, e⟩ : SA.Lock) ∈
              (tr.state y (q + 1)).ac.locks)) := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg q
  have hle : ∀ k < q + 1, tr.time k ≤ tr.time q := fun k hk => hm (Nat.le_of_lt_succ hk)
  have hle' : ∀ k < q, tr.time k ≤ tr.time q := fun k hk => hm hk.le
  obtain ⟨ell, hcall, R, hR, hroot, hshape⟩ := Obligations.record_changed_writer
    (hrun.upTo hd) (hnc.upTo _) hy (q := q)
    (by rw [Trace.upTo_state tr y hle, Trace.upTo_state tr y hle']; exact hne)
  rw [Trace.upTo_state tr y hle] at hroot
  have hcall' : tr.projAC.CallAt y q ell := by
    rw [RunTrace.upTo_projAC] at hcall
    exact ((Trace.upTo_callAt _).mp hcall).2
  exact ⟨ell, hcall', R, hR, hroot, writer_shape_of_upTo hrun hle hshape⟩

/-- A non-genesis current record of a reader honest at `t` has a last own writer, with unchanged
record roots thereafter and the actual creation lock in the optimistic case. -/
theorem last_record_writer_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hnt : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed = some R)
    (hgen : R.root ≠ sp.genesisRoot) :
    ∃ q < n, ∃ ell, tr.projAC.CallAt y q ell ∧ R ∈ ell.frame.tree ∧
      (∀ m, q < m → m ≤ n → (tr.state y m).ac.latestConfirmed = R.root) ∧
      ((∃ s CV, SA.ResultAt tr.projAC y q s R CV) ∨
        ((∃ CV, SA.OptimisticLockAt tr.projAC y q (sp.slot (tr.time q)) R CV) ∧
          ∃ e, (⟨(ell.frame.viableAncestor R).root, sp.slot (tr.time q), true, e⟩ : SA.Lock) ∈
            (tr.state y (q + 1)).ac.locks)) := by
  have hst : ∀ m ≤ n, (tr.upTo t).state y m = tr.state y m :=
    fun m hm => Trace.upTo_state tr y fun k hk => hnt k (by omega)
  obtain ⟨q, hqn, ell, hcall, hRq, hrest, hshape⟩ := Obligations.last_record_writer
    (hrun.upTo ht0) (hnc.upTo _) hy (n := n) (R := R) (by rw [hst n le_rfl]; exact hR) hgen
  have hcall' : tr.projAC.CallAt y q ell := by
    rw [RunTrace.upTo_projAC] at hcall
    exact ((Trace.upTo_callAt _).mp hcall).2
  refine ⟨q, hqn, ell, hcall', hRq, fun m hqm hmn => ?_,
    writer_shape_of_upTo hrun (fun k hk => hnt k (by omega)) hshape⟩
  rw [← hst m hmn]
  exact hrest m hqm hmn

/-- Creation-time holding plus a later finalized-floor guard keeps the writer's block in every
intervening filtered frame of a reader honest at `t`. -/
theorem writer_mem_frame_between_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {q e n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hnt : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) (hqe : q ≤ e) (hen : e ≤ n)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hRq : R ∈ (tr.state y q).fg.tree) (hRn : R ∈ (Node.frame (tr.state y n)).tree) :
    R ∈ (Node.frame (tr.state y e)).tree := by
  have hst : ∀ m ≤ n, (tr.upTo t).state y m = tr.state y m :=
    fun m hm => Trace.upTo_state tr y fun k hk => hnt k (by omega)
  have h := Obligations.writer_mem_frame_between (hrun.upTo ht0) (hnc.upTo _) hy hqe hen
    (by rw [hst q (by omega)]; exact hRq) (by rw [hst n le_rfl]; exact hRn)
  rwa [hst e hen] at h

section Reset

variable {g ΔF a b : Time}

open Healing.Growing in
/-- A clean optimistic writer, honest at its write, that remains in the final frame of a reader
honest at `t ≤ b` is an ancestor candidate at creation and every intervening cut, including the
terminal cut. -/
theorem clean_optimistic_writer_candidate_interval_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} {q s n : Nat} {t : Time} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (ht0 : 0 ≤ t) (hnt : ∀ j < n, tr.time j ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (hop : SA.OptimisticLockAt tr.projAC y q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqn : q < n)
    (hRn : R ∈ (Node.frame (tr.state y n)).tree) :
    ∀ e, q ≤ e → e ≤ n → (Node.frame (tr.state y e)).AncestorCandidate R := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hm := hrun.time_mono
  have hqt := hnt q hqn
  have hqb := hqt.trans htb
  have hyq : y ∈ H (tr.time q) := hrun.antitone hqt hy
  have hst : ∀ m ≤ n, (tr.upTo t).state y m = tr.state y m :=
    fun m hm' => Trace.upTo_state tr y fun k hk => hnt k (by omega)
  have hr := Compose.Growing.acRun_upTo hrun hnc ht0
  obtain ⟨_, _, ell, _, hpoint, hRq, _, _⟩ := SA.optimisticLockAt_spec hr hy
    ((Compose.Growing.sa_optimisticLockAt_upTo hm).mpr ⟨hqt, hop⟩)
  have hcallq : tr.projAC.CallAt y q ell := ((Trace.upTo_callAt _).mp hpoint.1).2
  have hframe := Compose.Growing.frame_of_projAC_at hrun hyq hcallq
  have hRq' : R ∈ (tr.state y q).fg.tree := (hframe ▸ hRq).1
  obtain ⟨v, r, l, S, hseed, hra, hrb, hdeliver⟩ := hp.reset_seed_held_at_call_at hc
  have haq : a + sp.Δ ≤ tr.time q := by
    have ha0 := (hrun.time_nonneg r).trans hra
    have hnext : a < sp.ts (sp.slot a + 1 : Nat) :=
      not_le.mp ((SA.ts_le_iff_le_slot sp ha0 ((sp.slot a + 1 : Nat) : Int)).not.mpr
        (by push_cast; omega))
    have hclean : sp.ts (sp.slot a + 2 : Nat) ≤ sp.ts s := by
      apply (SA.ts_le_iff sp).mpr
      rw [Healing.cleanLabel_eq] at hs
      exact_mod_cast (show sp.slot a + 2 ≤ s by omega)
    have htime : sp.ts s ≤ tr.time q := by
      obtain ⟨_, _, _, hslot, _⟩ := hop
      exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) s).mpr (by
        change sp.slot (tr.time q) = s at hslot
        omega)
    have hΔ := sp.toParams.hΔ
    simp only [SA.SAParams.ts] at hnext hclean htime
    push_cast at hnext hclean htime
    linarith
  intro e hqe hen
  have hRe := writer_mem_frame_between_at hrun hnc ht0 hnt hy hqe hen hRq' hRn
  apply hp.guarded_seed_ancestor_candidate_at_state_at ht0
    (fun j hj => hnt j (lt_of_lt_of_le hj hen)) hy htb hRe hseed hrb
  · intro hFS
    have hFq : Anc (tr.HonestBlocksAt H) ell.frame.F S := by
      rw [hframe]
      have h := Healing.run_F_mono (hrun.upTo ht0).toLocalRun hy hqe
      rw [hst q (by omega), hst e hen] at h
      exact (h.mono (RunTrace.honestBlocks_upTo_subset hm ht0)).trans hFS
    have hSq := hdeliver y q ell hyq hcallq haq hqb hFq
    have h := Compose.tree_mono (hrun.upTo ht0).toLocalRun hy hqe
    rw [hst q (by omega), hst e hen] at h
    exact h (hframe ▸ hSq).1
  · exact hp.clean_source_compatible_high_origin_at hc hyq (Or.inr hop) hs hqb hseed hrb
  · intro x j u B hje ho
    exact hp.clean_source_compatible_high_origin_at hc hyq (Or.inr hop) hs hqb ho
      ((hnt j (lt_of_lt_of_le hje hen)).trans htb)

end Reset

end Consensus.Goldilocks.Obligations.Growing

end
