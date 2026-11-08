module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SourceOrigin
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.OptimisticResult
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FinalizedSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepHonest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
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

open Healing.Growing in
/-- Even a retained writer before the repair update was created no earlier than the opening slot:
its held block extends the operational proposal. A writer after the update satisfies the same
bound directly by time monotonicity. -/
theorem retained_writer_slot_after_update_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j n q : Nat} {t : Time}
    {ell ellq : ACLabel (goldilocksNode sp ro)} (ht0 : 0 ≤ t) (hnt : ∀ k < n, tr.time k ≤ t)
    (hy : y ∈ H t) (hup : SA.UpdateAt tr.projAC y j u ell) (hjn : j < n)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed = some R)
    (hcall : tr.projAC.CallAt y q ellq) (hRq : R ∈ ellq.frame.tree)
    (hrest : ∀ m, q < m → m ≤ n → (tr.state y m).ac.latestConfirmed = R.root) :
    u ≤ sp.slot (tr.time q) := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  by_cases hqj : q < j
  · have hyj : y ∈ H (tr.time j) := hrun.antitone (hnt j hjn) hy
    have hyq : y ∈ H (tr.time q) := hrun.antitone (hnt q (by omega)) hy
    have hcallj := Compose.projAC_callAt.mp hup.1
    have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
      obtain ⟨hfr, _, hfg, _⟩ := hrun.cutLaw y j _ hcallj hyj
      rw [tr.state_succ_of_call hcallj, hfr]
      exact congrArg Store.toFrame hfg
    have hpost : tr.projAC.post j = (tr.state y (j + 1)).ac := by
      have h := Compose.projAC_state (hrun.upTo ht0).toLocalRun hy (j + 1)
      rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => hnt k (by omega)),
        Trace.upTo_state tr y (fun k hk => hnt k (by omega)),
        tr.projAC.state_succ_of_call hup.1] at h
      exact h
    have hRj := writer_mem_frame_between_at hrun hnc ht0 hnt hy (by omega : q ≤ j + 1)
      (by omega : j + 1 ≤ n)
      ((Compose.Growing.frame_of_projAC_at hrun hyq hcall ▸ hRq).1)
      (SA.lookup_eq_some hlookup).1
    have hlook : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed = some R := by
      rw [hpost, hrest (j + 1) (by omega) (by omega)]
      rw [hframe] at hRj
      cases he : SA.lookup ell.frame R.root with
      | none => exact False.elim (SA.lookup_eq_none he ⟨R, hRj, rfl⟩)
      | some B =>
        obtain ⟨hB, hBr⟩ := SA.lookup_eq_some he
        have heq : B = R :=
          (Compose.Growing.frameIn_at hrun hnc hyj hup.1).1.coherent.1 hB hRj hBr
        exact congrArg some heq
    obtain ⟨hPt, -, -, -, -, hrecord⟩ :=
      operational_update_selection_at hp hc hhold hdesignated hactual hPs hR hgu hTb hyj hup
    obtain ⟨hΦj, hΦjU⟩ := Compose.Growing.frameIn_at hrun hnc hyj hup.1
    have hPR : Anc (tr.HonestBlocksAt H) P
        ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) := by
      rw [hrecord]
      exact (Obligations.effective_record_update_slot_growth (sp := sp) hΦj hPt).1.mono hΦjU
    rw [hlook] at hPR
    simp only [Option.getD_some] at hPR
    have hslots := Anc.slot_le hU hPR
    rw [hPs] at hslots
    exact hslots.1.trans (Compose.Growing.frame_slot_le_at hrun hnc hyq hcall R hRq)
  · have htime : sp.ts u ≤ tr.time q := by
      have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
      have hmono := hm (show j ≤ q by omega)
      linarith [sp.toParams.hΔ]
    exact_mod_cast (SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) u).1 htime

open Healing.Growing in
/-- At slot `s + 2`, on the prefix through a read time `t ≤ b` of a reader honest at `t`, the votes
of the actual unlock view held from validators honest at `t` extend a clean optimistic source of
slot `s` by a writer honest at its write; only validators faulty at `t` can oppose it. -/
private theorem optimistic_unlock_keeps_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q s j : Nat} {t : Time} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hx : x ∈ H (tr.time q))
    (hop : SA.OptimisticLockAt tr.projAC x q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqb : tr.time q ≤ b)
    (ht0 : 0 ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hjt : tr.time j ≤ t)
    (hslot : sp.slot (tr.time j) = s + 2)
    (hR : R ∈ (Node.frame ((tr.upTo t).state y j)).tree) :
    Compose.UnlockKeeps (tr.upTo t) y j R := by
  intro ell hcall
  have hrun := hp.run
  have hnc := hp.noColl
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hrT := hrun.upTo ht0
  have hncT := hnc.upTo t
  have hrunT := Compose.goldilocks_ac_projection sp ro dg (H t) (tr.upTo t) proposer hrT hncT
  have hr := hrunT.localRun
  have hcallA := Compose.projAC_callAt.2 hcall
  obtain ⟨hfr, hst, _, _⟩ := hrT.cutLaw y hy j _ hcall
  rw [hfr] at hst
  have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y ((tr.upTo t).state y j).ac
      (Node.frame ((tr.upTo t).state y j)) ((tr.upTo t).time j) ell.call).1 =
        ((tr.upTo t).state y (j + 1)).ac := by
    rw [(tr.upTo t).state_succ_of_call hcall, hst]
  have hpool : ∀ m τ, ∀ v ∈ ((tr.upTo t).state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
    rw [← Compose.projAC_state hrT.toLocalRun hy] at hv
    exact (Compose.state_pool_cap hrT hy m τ).1 v hv
  have hpay : ∀ C ∈ (Node.frame ((tr.upTo t).state y j)).tree, SA.validPayload C := by
    rw [← hfr]
    exact SA.frame_validPayload sp hr hy hcallA
  have hf : 2 * (H t)ᶜ.ncard < sp.n := by
    have hfault := hp.faults t ht0 htb
    have hn : 0 < sp.n := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.n - 1 at hfault
    omega
  have hΦ := Compose.frameOK_state hrT.toLocalRun hy j
  have hPhiU : (Node.frame ((tr.upTo t).state y j)).tree ⊆ tr.HonestBlocksAt H :=
    fun B hB => RunTrace.honestBlocks_upTo_subset hm ht0 ⟨y, hy, j, hB.1⟩
  apply SA.unlockTarget_unlockView_held_of_honest_slot y ell.call hA' hΦ _ hR (hpool j)
    (hpool (j + 1)) hpay
    (fun v hv w hw hvH hval hsl =>
      Compose.heldVotes_honest_unique hrT hncT hy hcall hv hw hvH hval hsl) ?_ hf
  intro v hv hvH hvs Hd hHd hHdr
  obtain ⟨k, e, ⟨ell', hcast⟩, hmsg⟩ :
      ∃ k e, SA.VoteAt (tr.upTo t).projAC v.val k e ∧ e.msg = v := by
    rcases SA.mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
    · rw [← Compose.projAC_state hrT.toLocalRun hy] at hv
      obtain ⟨k, _, e, he, hm⟩ := hrunT.honest.pool_vote y hy j τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · rw [← Compose.projAC_state hrT.toLocalRun hy] at hv
      obtain ⟨k, _, e, he, hm⟩ := hrunT.honest.pool_vote y hy (j + 1) τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · have hvB : v ∈ SA.blockVotes C := hv.elim id fun hv => (hpay C hC).2 v hv
      obtain ⟨k, _, e, he, hm⟩ := hrunT.honest.carried_vote y hy j ell hcallA C
        (hfr.symm ▸ hC) v hvB hvH
      exact ⟨k, e, he, hm⟩
  have hkj : k < j :=
    Compose.cast_lt_of_slot hrT hncT hvH hcast (by simpa [hmsg] using hvs)
  have hcastR : SA.CastAt tr.projAC v.val k ell' e := by
    rw [RunTrace.upTo_projAC] at hcast
    exact (Compose.Growing.sa_castAt_upTo.mp hcast).2
  have hkt : tr.time k ≤ t := (hm hkj.le).trans hjt
  obtain ⟨Hd', hHd', hHd'r, hRHd⟩ := hp.fast_source_votes_before_at hc hx (Or.inr hop)
    (by have := sp.two_le_k; omega) hqb k (hkt.trans htb) v.val (hrun.antitone hkt hvH) ell' e
    hcastR (by
      rw [hmsg]
      change (v.slot : Int) = (sp.slot (tr.time j) : Int) - 1 at hvs
      omega)
  have heq : Hd' = Hd := hU.1 hHd' (hPhiU hHd)
    (hHd'r.trans ((congrArg Vote.head hmsg).trans hHdr.symm))
  subst Hd'
  exact Or.inr (SA.anc_tree_of_anc_U hU hΦ hPhiU hR hRHd hHd)

open Healing.Growing in
/-- The actual slot-`s` fast lock, of expiry at least `s + 2`, survives at a reader honest at
`t ≤ b` until the next-result deadline, provided the held source remains a candidate. -/
theorem young_optimistic_lock_persists_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q s i n : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} {e : Nat}
    (hx : x ∈ H (tr.time q)) (hop : SA.OptimisticLockAt tr.projAC x q s R CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hqb : tr.time q ≤ b)
    (hin : i ≤ n) (hread : ∀ j < n, tr.time j ≤ t) (htb : t ≤ b) (ht0 : 0 ≤ t)
    (hy : y ∈ H t) (hyoung : t < sp.ts (s + 1 : Nat) + 6 * sp.Δ)
    (he : s + 2 ≤ e) (hl : (⟨R.root, s, true, e⟩ : SA.Lock) ∈ (tr.state y i).ac.locks)
    (hframe : ∀ j, i ≤ j → j < n → R ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).AncestorCandidate R) :
    (⟨R.root, s, true, e⟩ : SA.Lock) ∈ (tr.state y n).ac.locks := by
  have hrun := hp.run
  have hrT := hrun.upTo ht0
  have hst : ∀ m ≤ n, (tr.upTo t).state y m = tr.state y m :=
    fun m hm' => Trace.upTo_state tr y fun k hk => hread k (by omega)
  have h := Compose.lock_keep_interval_view hrT hy hin
    (by rw [hst i hin]; exact hl) (B := R) rfl (fun j hij hjn => by
      obtain ⟨hR, hcandidate⟩ := hframe j hij hjn
      have hR' : R ∈ (Node.frame ((tr.upTo t).state y j)).tree := by rw [hst j hjn.le]; exact hR
      have hslot : sp.slot (tr.time j) ≤ s + 2 := by
        have htime := hread j hjn
        have hfloor := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j)
          (sp.slot (tr.time j))).2 le_rfl
        have hΔ := sp.toParams.hΔ
        simp only [SA.SAParams.ts] at hyoung hfloor
        push_cast at hyoung hfloor
        by_contra h
        have : (s : Int) + 3 ≤ sp.slot (tr.time j) := by omega
        linarith [mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_four hΔ.le)]
      refine ⟨show sp.slot (tr.time j) ≤ e by omega, hR', ?_, ?_⟩
      · have hΦ := Compose.frameOK_state hrT.toLocalRun hy j
        rw [hst j hjn.le] at hΦ ⊢
        exact SA.viableAncestor_self hΦ hR hcandidate.symm
      · intro ell hcall
        by_cases hshort : sp.slot (tr.time j) ≤ s + 1
        · left; change (sp.slot (tr.time j) : Int) - 1 ≤ (s : Int); omega
        · right
          exact optimistic_unlock_keeps_at hp hc hx hop hs hqb ht0 htb hy (hread j hjn)
            (by omega) hR' ell hcall)
  rwa [hst n le_rfl] at h

open Healing.Growing in
/-- The next-result alternative at a specified update, so engine callers may choose the tick
known to precede their stored-clock observation. -/
theorem optimistic_result_or_finalized_at_update_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} {ell : ACLabel (goldilocksNode sp ro)}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time j))
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    (hu : SA.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hR : Healing.drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat)) :
    Anc (tr.HonestBlocksAt H) B (tr.state y j).fg.F ∨
      ∃ D DV, SA.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocksAt H) B D := by
  have hrun := hp.run
  rcases hp.finalized_compatible_clean_source_at hc hx (Or.inr hop) hs hrb
      (hrun.time_nonneg j) (fun q hq => hrun.time_mono hq.le) hy hjb with hFB | hBF
  · right
    have hcut := hp.clean_window_timing_at
      (show Healing.cleanLabel sp a + sp.k + 2 ≤ s by have := sp.two_le_k; omega)
      (s + 1) (by omega)
    have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by
      have := Healing.lt_cutZ sp g
      linarith [sp.toParams.hΔ]
    apply optimistic_next_result_of_floor_at hp hc hx hy hop hs hrb hu hjb hgu hR
    rw [Compose.Growing.frame_of_projAC_at hrun hy hu.1]
    exact hFB
  · exact Or.inl hBF

end Reset

section Engine

open Healing.Growing Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A healthy update no later than the stored clock has actually completed, before the read point
after the node's last own event. The equality case uses the engine tick's position, not trace-time
comparison. Honesty is at the stored clock only, which is within the reset premises' bound. -/
theorem update_before_stored_clock_at (hvalid : rho.ExecutionValid) {g ΔF a b : Time}
    (hp : ResetPremisesUpTo (simTraceAt S rho hn) (honestKeysAt S rho)
      (runProposer S rho hn) (digestOf S rho) g ΔF a b) (hbh : b ≤ rho.horizon)
    {v : V} {i u : Nat} (hv : v ∉ rho.faultyAt (stateAt S rho hn v i).now)
    (hslot : (S.params (Model.pubOf E) hn).ts
      ((S.params (Model.pubOf E) hn).slot (SA.gbar g) + 1 : Nat) ≤
        (S.params (Model.pubOf E) hn).ts u)
    (ht : (S.params (Model.pubOf E) hn).ts u + 6 * (S.params (Model.pubOf E) hn).Δ ≤
      (stateAt S rho hn v i).now)
    (htb : (stateAt S rho hn v i).now ≤ b) :
    ∃ j ell, SA.UpdateAt (simTraceAt S rho hn).projAC (rho.ownKey v) j u ell ∧
      j < cutMap S rho hn (lastOwn S rho v i) := by
  let sp := S.params (Model.pubOf E) hn
  let T := sp.ts u + 6 * sp.Δ
  have hDelta := sp.toParams.hΔ
  have hT0 : 0 < T := by
    dsimp [T, SA.SAParams.ts]
    positivity
  have hTb : T ≤ b := ht.trans htb
  have hTh : T ≤ rho.horizon := hTb.trans hbh
  have hslot' : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := hslot
  have hgu : SA.gbar g ≤ sp.ts u := by
    have hnext := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (SA.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hslot'
  have hvT : v ∉ rho.faultyAt T := fun h => hv (rho.faultyAt_mono ht h)
  have hpub : sp.toParams.IsPublic T :=
    ⟨4 * (u : Int) + 6, by dsimp [T, SA.SAParams.ts]; ring⟩
  have hy : rho.ownKey v ∈ honestKeysAt S rho T := honest_ownKey_at S rho hvT hTh
  have hawake := hp.awake _ T hy (by dsimp [T]; linarith) hTb
  have hawake' : E.awake v T = true := by
    simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using
      ((simTraceAt_awake_bounds S rho hn _ T).mp hawake).1
  obtain ⟨p, he⟩ := List.mem_iff_getElem?.mp (hvalid.tick_total v T hT0.le hTh hvT hawake')
  have hm := hp.run.time_mono
  have hnr : ∀ q < i, rho.events[q]? ≠ some (.restart v T) := by
    intro q _ hrestart
    obtain ⟨_, rec, hrec, hnode, htime, ell, hlabel, hcall⟩ :=
      restart_getElem? S rho hn hrestart
    have hrs : (simTraceAt S rho hn).RestartAt (rho.ownKey v) (cutMap S rho hn q) := by
      refine ⟨ell, ⟨?_, ?_⟩, hcall⟩
      · rw [simTraceAt_eq, simTrace_node, hrec]; exact hnode
      · rw [simTraceAt_eq, simTrace_label, hrec, Option.map_some, hlabel]
    have htime' : (simTraceAt S rho hn).time (cutMap S rho hn q) = T := by
      rw [simTraceAt_eq, simTrace_time, hrec]; exact htime
    have hbound := hp.restart_le_before_at (htime' ▸ hy) hrs (htime' ▸ hTb)
    rw [htime'] at hbound
    have hbound' : sp.ts u + 6 * sp.Δ ≤ sp.ts (sp.slot (SA.gbar g) + 1 : Nat) := hbound
    linarith
  have hpi := tick_before_stored_clock S rho hn hvalid he hT0 ht hnr
  have hpl : p + 1 ≤ lastOwn S rho v i := by
    rw [lastOwn_eq]
    exact Nat.le_findGreatest (by omega) (Or.inr ⟨_, by simpa using he, rfl⟩)
  obtain ⟨hgroup, hlen⟩ := simTraceAt_tick_public_group S rho hn hvalid he hpub
  have hlen0 := List.length_pos_iff.mpr hgroup.1
  obtain ⟨hnode, htime, -, -, hlabel⟩ := hgroup.2.1 0 hlen0
  have hcall : (simTraceAt S rho hn).CallAt (rho.ownKey v) (cutMap S rho hn p)
      (Node.acCall (rho.ownKey v) ((simTraceAt S rho hn).state (rho.ownKey v)
        (cutMap S rho hn p)) T .tick).2 := by
    have hget : (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn p)) T
        (.tick (Blocks.encodeTxs (Model.mempool rho.inbox v T)))).2[0]'hlen0 =
        (Node.acCall (rho.ownKey v) ((simTraceAt S rho hn).state (rho.ownKey v)
          (cutMap S rho hn p)) T .tick).2 := rfl
    exact ⟨by simpa only [Nat.add_zero] using hnode,
      by simpa only [Nat.add_zero, hget] using hlabel⟩
  have htime : (simTraceAt S rho hn).time (cutMap S rho hn p) = T := by
    simpa only [Nat.add_zero] using htime
  obtain ⟨ell, hcallA, hcalltick⟩ : ∃ ell,
      (simTraceAt S rho hn).projAC.CallAt (rho.ownKey v) (cutMap S rho hn p) ell ∧
        ell.call = .tick := ⟨_, Compose.projAC_callAt.2 hcall, rfl⟩
  refine ⟨cutMap S rho hn p, ell, ⟨hcallA, hcalltick, htime, ?_⟩, ?_⟩
  · have hr := hp.run.upTo hT0.le
    have hac := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hr (hp.noColl.upTo T)).localRun
    have hj : SA.joined sp (((simTraceAt S rho hn).upTo T).projAC.state (rho.ownKey v)
        (cutMap S rho hn p)) ((simTraceAt S rho hn).time (cutMap S rho hn p)) := by
      unfold SA.joined
      rcases SA.restartTime_state hac hy (cutMap S rho hn p) with h | ⟨r, hri, hrs, h⟩
      · rw [h]; exact bot_le
      · rw [h]
        apply WithBot.coe_le_coe.mpr
        have hrs' : (simTraceAt S rho hn).RestartAt (rho.ownKey v) r :=
          ((RunTrace.upTo_restartAt _).mp (Compose.projAC_restartAt.mp hrs)).2
        have hrd : (simTraceAt S rho hn).time r ≤ T := (hm hri.le).trans htime.le
        have hrestart := hp.restart_le_before_at (hp.run.antitone hrd hy) hrs' (hrd.trans hTb)
        have hsl : sp.slot T = u + 1 :=
          SA.slot_of_mem sp (u + 1)
            (by dsimp [T]; simp only [SA.SAParams.ts]; linarith)
            (by dsimp [T]; simp only [SA.SAParams.ts]; linarith)
        change (simTraceAt S rho hn).time r ≤
          sp.ts ((sp.slot ((simTraceAt S rho hn).time (cutMap S rho hn p)) : Int) - 1)
        rw [htime, hsl]
        simpa using hrestart.trans hslot'
    have hstate : ((simTraceAt S rho hn).projAC.upTo T).state (rho.ownKey v)
        (cutMap S rho hn p) = (simTraceAt S rho hn).projAC.state (rho.ownKey v)
          (cutMap S rho hn p) :=
      Trace.upTo_state _ _ (fun q hq => (hm hq.le).trans htime.le)
    rw [RunTrace.upTo_projAC, hstate] at hj
    exact hj
  · have hmono := cutMap_mono S rho hn hpl
    omega

end Engine

end Consensus.Goldilocks.Obligations.Growing

end
