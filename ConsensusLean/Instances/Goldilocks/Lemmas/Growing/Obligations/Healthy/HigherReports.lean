module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ViableSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Strictly higher reports above a held target, under growing faults

These are growing-fault forms of the report lemmas of `Healing/Retention/Records` and
`Healing/Outcome/SupplierFrames`, with each node honest at its own cut and a held-state reader
honest at an observation time after the state's cuts. Each higher report is by a node
honest at it and at `c_z`, so that its high descendant has a high origin (`high_source_cover_at`):

* `ResetPremisesUpTo.higher_report_of_signed_entry_at`: an attestation, signed while honest and
  honest at `c_z`, naming a held entry strictly above the target yields a strictly higher report
  of its signer;
* `ResetPremisesUpTo.finality_below_or_higher_report_at`: finality compatible with the target is
  below it, or an earlier strictly higher report extends it;
* `ResetPremisesUpTo.held_target_high_pred_report_before_covered_at`: a held target strictly below
  `hmax − 1` yields an earlier strictly higher report.

The finalization quorum of a held chain meets the validators honest at the later of the reader's
cut and `c_z`; each signature is then read on the prefix through its own signing. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

namespace ResetPremisesUpTo
variable {hold : Time}

/-- Read back the report immediately preceding the signing of a strictly higher entry. -/
private theorem higher_report_before_signing_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y z : Fin sp.n} {i d : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    {P E : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    {att : FG.Att sp.n} (hs : tr.SignAt z d att)
    (hT : att.T = E.root) (hPE : Anc (tr.HonestBlocksAt H) P E)
    (hlt : ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ E.root).h) :
    ∃ r ell C, z ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < d ∧
      AC.ToFGAt tr.projAC z r ell C ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hd := hrun.time_nonneg d
  have hz := hrun.antitone (le_max_right _ _) hzz
  obtain ⟨r, hrd, hrt, ell, C, E', hto, hC, hE', hE'r, hEC, -, -, hEh, -⟩ :=
    Healing.signAt_report_entry (hrun.upTo hd) hz ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  subst hrd
  have hrt' : tr.time r = tr.time (r + 1) := hrt
  have hrr : tr.time r ≤ tr.time (r + 1) := hrt'.le
  have hst : (tr.upTo (tr.time (r + 1))).state z r = tr.state z r :=
    RunTrace.upTo_state_of_le hm hrr
  rw [hst] at hC hE' hEC hEh
  have hzr : z ∈ H (tr.time r) := hrt' ▸ hz
  have hzle : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hm hq.le
  have hr0 := hrun.time_nonneg r
  obtain rfl : E' = E := hU.1 ⟨z, r, tr.time r, hr0, hzle, hzr, hE'⟩
    ⟨y, i, t, ht, hle, hy, hE⟩ (hE'r.trans hT)
  have hPC := hPE.trans (honest_anc_of_store_anc_at hr0 hzle hzr hEC)
  have hPr := mem_of_honest_anc_at hrun hp.noColl hr0 hzle hzr hPC hC
  refine ⟨r, ell, C, by rwa [hrt'], by omega, (toFGAt_upTo_iff hm hrr).mp hto, hPC, ?_⟩
  rw [← hEh, σ_eq_honest_at hrun hp.noColl hr0 hzle hzr ht hle hy hPr hP,
    σ_eq_honest_at hrun hp.noColl hr0 hzle hzr ht hle hy hE' hE]
  exact hlt

/-- **A signed entry above the target yields a strictly higher report**: an attestation signed at
`d < i` by a node honest at its signing and at `c_z`, naming an entry held at `i` strictly above a
held target, is preceded by a report of its signer, honest at it and at `c_z`, extending the
target, at a strictly higher height. -/
theorem higher_report_of_signed_entry_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y z : Fin sp.n} {i d : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    {P E : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    {att : FG.Att sp.n} (hs : tr.SignAt z d att) (hdi : d < i)
    (hT : att.T = E.root) (hPE : Anc (tr.HonestBlocksAt H) P E)
    (hlt : ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ E.root).h) :
    ∃ r ell C, z ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
      AC.ToFGAt tr.projAC z r ell C ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  obtain ⟨r, ell, C, hz, hrd, hto, hPC, hh⟩ :=
    higher_report_before_signing_at hp ht hle hy hzz hP hE hs hT hPE hlt
  exact ⟨r, ell, C, hz, hrd.trans hdi, hto, hPC, hh⟩

/-- **A finalized descendant yields a strictly higher report**: a finalized block `X` of a held
chain, strictly above a target `P`, of a node honest at its cut `k ≤ b`, is the finalization
entry signed by a validator honest at `k` and at `c_z` (the quorum is read at the later of the
two), whose report extends `P` at a strictly higher height. -/
private theorem finalized_descendant_report_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {W X P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) (hX : X ∈ (tr.state y k).fg.tree)
    (hXr : X.root = ((tr.state y k).fg.σ W.root).F)
    (hPX : Anc (tr.HonestBlocksAt H) P X) (hne : P ≠ X) :
    ∃ z r ell C, z ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < k ∧
      AC.ToFGAt tr.projAC z r ell C ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hk0 := hrun.time_nonneg k
  have hkle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hm hq.le
  have hr := fg_reachable_at hrun hk0 hkle hy
  have hsub : ∀ {z : Fin sp.n} {m : Nat} {t : Time}, 0 ≤ t → (∀ q < m, tr.time q ≤ t) →
      z ∈ H t → (tr.state z m).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun ht hle hz _ hB => ⟨_, _, _, ht, hle, hz, hB⟩
  obtain ⟨c, hc, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr W hW
  have hpos : 1 ≤ ((tr.state y k).fg.σ W.root).hF := by
    by_contra hn
    have hg := (FG.chain_invariants _ _ _ hcs).2.2.2.2.1 (by omega)
    have he := (hU.mono (hsub hk0 hkle hy)).1 hX (Store.genesis_mem hr) (hXr.trans hg)
    rw [he] at hPX
    rcases Relation.ReflTransGen.cases_tail hPX with heq | ⟨Y, _, hY⟩
    · exact hne (heq.symm.trans he.symm)
    · exact absurd hY.2.2 (by simp [Params.genesisBlock])
  obtain ⟨Q, hQ, hrows⟩ := FG.FGParams.finalized_quorum _ hcs hpos
  change Finset (Fin sp.n) at Q
  have hex : ∃ v ∈ Q, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) := by
    by_contra hn
    have hqsub : (↑Q : Set (Fin sp.n)) ⊆ (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ :=
      fun v hv hvH => hn ⟨v, hv, hvH⟩
    have hh := Set.ncard_le_ncard hqsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hh
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have hf := hp.faults _ (hk0.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) hkb)
    have hn : 0 < sp.n := sp.toParams.hn
    change (2 * sp.n + 2) / 3 ≤ Q.card at hQ
    omega
  obtain ⟨v, hvQ, hv⟩ := hex
  obtain ⟨att, hatt, hav, hfin⟩ := hrows v hvQ
  simp only [FG.FGParams.chainAtts, List.mem_flatMap] at hatt
  obtain ⟨Z', hZ', hatt⟩ := hatt
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
  have haHz : att.val ∈ H (max (cutZ sp.toParams g) (tr.time k)) := hav ▸ hv
  obtain ⟨m, hmk, -, s, hsm, hs, has⟩ :=
    Compose.Growing.honest_row_signed_before_at hrun hp.noColl hy (hc Z hZ) hatt
      (hrun.antitone (le_max_right _ _) haHz)
  have hs0 := hrun.time_nonneg s
  have hsle : ∀ q < s, tr.time q ≤ tr.time s := fun _ hq => hm hq.le
  have hst : (tr.upTo (tr.time s)).state att.val s = tr.state att.val s :=
    RunTrace.upTo_state_of_le hm le_rfl
  obtain ⟨J, hJ, E, hE, hEr, hJE, hJr, -, hJT⟩ := Healing.signed_fin_pair_entry_of_run
    (hrun.upTo hs0) has ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩) hfin
  rw [hst] at hJ hE hJE hJT
  obtain rfl : J = X := hU.1 (hsub hs0 hsle has hJ) (hsub hk0 hkle hy hX) (hJr.trans hXr.symm)
  have hPXs := store_anc_of_honest_anc_at hrun hp.noColl hs0 hsle has hPX hJ
  have hPs := (Anc.mem hPXs hne).1
  have hrs := fg_reachable_at hrun hs0 hsle has
  -- The finalized block is its own entry, so a strict ancestor has smaller height.
  have hlt : ((tr.state att.val s).fg.σ P.root).h < ((tr.state att.val s).fg.σ J.root).h := by
    apply lt_of_le_of_ne (Healing.h_le_of_store_anc hrs hPXs)
    intro heq
    obtain ⟨⟨A, hA, hAr, hAP, -, _⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hrs P hPs
    have hAJ : A = J := hU.1 (hsub hs0 hsle has hA) (hsub hs0 hsle has hJ)
      (hAr.trans ((Healing.Th_eq_of_anc hrs hPXs heq.symm).symm.trans hJT))
    exact hne (hPXs.antisymm (hU.mono (hsub hs0 hsle has)) (hAJ ▸ hAP))
  have hsZ := hrun.antitone (max_le_max le_rfl (hm (hsm.trans hmk).le)) haHz
  obtain ⟨r, ell, C, hz, hrs, hto, hPC, hh⟩ := higher_report_before_signing_at hp hs0 hsle has
    hsZ hPs hE hs hEr.symm (honest_anc_of_store_anc_at hs0 hsle has (hPXs.trans hJE))
    (hlt.trans_le (Healing.h_le_of_store_anc hrs hJE))
  exact ⟨att.val, r, ell, C, hz, hrs.trans (hsm.trans hmk), hto, hPC, hh⟩

/-- **Finality compatible with a target is below it, or an earlier strictly higher report
extends the target**, at a cut `k ≤ b` of a node honest at it; the reporter is honest at its
report and at `c_z`. -/
theorem finality_below_or_higher_report_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcompat : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P) :
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F P ∨
      ∃ z r ell C, z ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < k ∧
        AC.ToFGAt tr.projAC z r ell C ∧
        Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hcompat with h | h
  · exact Or.inl h
  by_cases he : P = (tr.state y k).fg.F
  · exact Or.inl (he ▸ Relation.ReflTransGen.refl)
  have hr := fg_reachable_at hp.run (hp.run.time_nonneg k) (fun _ hq => hp.run.time_mono hq.le) hy
  obtain ⟨hF, -, -, -, -, -, W, hW, hWF⟩ := Store.cache_invariants _ _ _ _ hr
  exact Or.inr (finalized_descendant_report_at hp hy hkb hW hF hWF.symm h he)

/-- **A held target strictly below `hmax − 1` yields an earlier strictly higher report**, at a
cut `i ≤ b` of a node honest at it, when the target is above a high seed and compatible with every
earlier high origin, and the seed is compatible with the earlier high origins; under the
high-source cover, the target is also compatible with healed members of labels at most
the cut's slot (`CompatibleWithOrigins`). -/
theorem held_target_high_pred_report_before_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    {P S : AC.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ (tr.state y i).fg.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hseedcomp : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) S B)
    (hcompare : CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P)
    (hfloor : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.hmax - 1) :
    ∃ x r ell C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
      AC.ToFGAt tr.projAC x r ell C ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hd := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hrun.time_mono hk.le
  have hr := fg_reachable_at hrun hd hle hy
  have hSy := mem_of_honest_anc_at hrun hp.noColl hd hle hy hSP hPy
  have hSs := highOrigin_mem_at hrun hp.noColl hseed
  have hSh := Healing.h_le_of_store_anc hr
    (store_anc_of_honest_anc_at hrun hp.noColl hd hle hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.hmax - 1 := by
    rw [σ_eq_honest_at hrun hp.noColl (hrun.time_nonneg q) (fun _ hk => hrun.time_mono hk.le)
      (hrun.antitone (le_max_right _ _) hseed.1) hd hle hy hSs hSy]
    omega
  have finish {E B : AC.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {d : Nat}
      {att : FG.Att sp.n} (hE : E ∈ (tr.state y i).fg.tree)
      (hEf : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ E.root).h)
      (hEB : Anc (tr.HonestBlocksAt H) E B) (hPB : Compatible (tr.HonestBlocksAt H) P B)
      (hdi : d < i) (hxz : x ∈ H (max (cutZ sp.toParams g) (tr.time d)))
      (hs : tr.SignAt x d att) (hT : att.T = E.root) := by
    have hPE : Anc (tr.HonestBlocksAt H) P E := by
      rcases Compose.Growing.compatible_of_anc_left hU hEB hPB.symm with h | h
      · have := Healing.h_le_of_store_anc hr
          (store_anc_of_honest_anc_at hrun hp.noColl hd hle hy h hPy)
        omega
      · exact h
    exact hp.higher_report_of_signed_entry_at hd hle hy hxz hPy hE hs hdi hT hPE (by omega)
  rcases hp.high_pred_signed_source_or_covered_before_at hseed hd hle hy hib
      (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z d hz hd' hdi r' l O hrd ho => by
        obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
        have hlabel := (AC.ts_le_iff_le_slot sp hd l).1
          ((ProposalImpl.ts_le_of_fastLock_at hrun hfl).trans
            (hrun.time_mono (hrd.trans hdi).le))
        omega) hseedcomp hSf with
    ⟨x, r, l, B, E, hri, ho, -, hE, hEB, -, hEf, d, att, -, hdi, hxd, hs, hT⟩ |
      ⟨E, hE, hcov, hEf, x, d, att, hdi, hxz, hs, hT⟩
  · have hxdz : x ∈ H (max (cutZ sp.toParams g) (tr.time d)) := by
      rcases le_total (cutZ sp.toParams g) (tr.time d) with h | h
      · rwa [max_eq_right h]
      · rw [max_eq_left h]; exact hrun.antitone (le_max_left _ _) ho.1
    exact ⟨x, finish hE hEf hEB ((compatibleWithOrigins_iff.1 hcompare).1 x r l B hri ho)
      hdi hxdz hs hT⟩
  · -- The member above `E` is compatible with `P` under the cover.
    obtain ⟨hc, C, s, hC, hsl, hEC⟩ := coveredBefore_iff.1 hcov
    exact ⟨x, finish hE hEf hEC ((compatibleWithOrigins_iff.1 hcompare).2 hc C s hC hsl) hdi
      (hrun.antitone (max_le_max le_rfl (hle d hdi)) hxz) hs hT⟩

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
