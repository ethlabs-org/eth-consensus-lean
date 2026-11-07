module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Strictly higher reports above a held target, under growing faults

The growing forms of the report lemmas of `Healing/Retention/Records` and the held-target floor
report of `Healing/Outcome/SupplierFrames`, with each node honest at its own cut and a held-state
reader honest at an observation time after the state's cuts:

* `ResetPremisesUpTo.higher_report_of_signed_entry_at`: an attestation, signed while honest,
  naming a held entry strictly above the target yields a strictly higher report of its signer;
* `ResetPremisesUpTo.finality_below_or_higher_report_at`: finality compatible with the target is
  below it, or an earlier strictly higher report extends it;
* `ResetPremisesUpTo.held_target_high_floor_report_before_at`: a held target below the head-height
  floor yields an earlier strictly higher report.

The finalization quorum of a held chain meets the validators honest at the reader's cut; each
signature is then read on the prefix through its own signing. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

namespace ResetPremisesUpTo

/-- **A signed entry above the target yields a strictly higher report**: an attestation signed at
`d < i` by a node honest at its signing, naming an entry held at `i` strictly above a held target,
is preceded by a report of its signer extending the target, at a strictly higher height. -/
theorem higher_report_of_signed_entry_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y z : Fin sp.n} {i d : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (hz : z ∈ H (tr.time d)) {P E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    {att : FG.Att sp.n} (hs : tr.SignAt z d att) (hdi : d < i)
    (hT : att.T = E.root) (hPE : Anc (tr.HonestBlocksAt H) P E)
    (hlt : ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ E.root).h) :
    ∃ r ell C, z ∈ H (tr.time r) ∧ r < i ∧ SA.ToFGAt tr.projAC z r ell C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hd := hrun.time_nonneg d
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
  refine ⟨r, ell, C, hzr, by omega, (toFGAt_upTo_iff hm hrr).mp hto, hPC, ?_⟩
  rw [← hEh, σ_eq_honest_at hrun hp.noColl hr0 hzle hzr ht hle hy hPr hP,
    σ_eq_honest_at hrun hp.noColl hr0 hzle hzr ht hle hy hE' hE]
  exact hlt

/-- **A finalized descendant yields a strictly higher report**: a finalized block `X` of a held
chain, strictly above a target `P`, of a node honest at its cut `k ≤ b`, is the finalization
entry signed by a validator honest at `k`, whose report extends `P` at a strictly higher height. -/
private theorem finalized_descendant_report_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {W X P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) (hX : X ∈ (tr.state y k).fg.tree)
    (hXr : X.root = ((tr.state y k).fg.σ W.root).F)
    (hPX : Anc (tr.HonestBlocksAt H) P X) (hne : P ≠ X) :
    ∃ z r ell C, z ∈ H (tr.time r) ∧ r < k ∧ SA.ToFGAt tr.projAC z r ell C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
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
  have hex : ∃ v ∈ Q, v ∈ H (tr.time k) := by
    by_contra hn
    have hqsub : (↑Q : Set (Fin sp.n)) ⊆ (H (tr.time k))ᶜ := fun v hv hvH => hn ⟨v, hv, hvH⟩
    have hh := Set.ncard_le_ncard hqsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hh
    have hf := hp.faults _ hk0 hkb
    have hn : 0 < sp.n := sp.toParams.hn
    change (2 * sp.n + 2) / 3 ≤ Q.card at hQ
    omega
  obtain ⟨v, hvQ, hv⟩ := hex
  obtain ⟨att, hatt, hav, hfin⟩ := hrows v hvQ
  simp only [FG.FGParams.chainAtts, List.mem_flatMap] at hatt
  obtain ⟨Z', hZ', hatt⟩ := hatt
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
  have haH : att.val ∈ H (tr.time k) := hav ▸ hv
  -- the row was signed while honest, before its block's acceptance at `y`
  have hstk : (tr.upTo (tr.time k)).state y k = tr.state y k :=
    RunTrace.upTo_state_of_le hm le_rfl
  obtain ⟨m, hmk, _, s, hsm, hs⟩ := Compose.honest_row_signed_before (hrun.upTo hk0)
    (hp.noColl.upTo _) hy (by rw [hstk]; exact hc Z hZ) hatt haH
  obtain ⟨hsk, hs⟩ := (RunTrace.upTo_signAt tr).mp hs
  have hs0 := hrun.time_nonneg s
  have has : att.val ∈ H (tr.time s) := hrun.antitone hsk haH
  have hsle : ∀ q < s, tr.time q ≤ tr.time s := fun _ hq => hm hq.le
  -- its finalization entry and its report, at the signing
  have hst : (tr.upTo (tr.time s)).state att.val s = tr.state att.val s :=
    RunTrace.upTo_state_of_le hm le_rfl
  obtain ⟨J, hJ, E, hE, hEr, hJE, hJr, -, -⟩ := Healing.signed_fin_pair_entry_of_run
    (hrun.upTo hs0) has ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩) hfin
  rw [hst] at hJ hE hJE
  obtain rfl : J = X := hU.1 (hsub hs0 hsle has hJ) (hsub hk0 hkle hy hX) (hJr.trans hXr.symm)
  obtain ⟨⟨r, ell, C, hzr, hrs, hto, hPC, hlt⟩⟩ : Nonempty (∃ r ell C,
      att.val ∈ H (tr.time r) ∧ r < s ∧ SA.ToFGAt tr.projAC att.val r ell C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state att.val r).fg.σ P.root).h < ((tr.state att.val r).fg.σ C.root).h) := by
    obtain ⟨r, hsr, ht, ell, C, E', hto, hC, hE', hE'r, hEC, hTh, hET, hEh, _⟩ :=
      Healing.signAt_report_entry (hrun.upTo hs0) has
        ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    subst hsr
    have ht' : tr.time r = tr.time (r + 1) := ht
    have hrr : tr.time r ≤ tr.time (r + 1) := ht'.le
    have hstr : (tr.upTo (tr.time (r + 1))).state att.val r = tr.state att.val r :=
      RunTrace.upTo_state_of_le hm hrr
    rw [hstr] at hC hE' hEC hTh hET hEh
    have hzr : att.val ∈ H (tr.time r) := ht' ▸ has
    have hr0 := hrun.time_nonneg r
    have hrle : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hm hq.le
    have hsubr := hsub hr0 hrle hzr
    obtain rfl : E = E' := hU.1 (hsub hs0 hsle has hE) (hsubr hE') (hEr.trans hE'r.symm)
    have hXE := honest_anc_of_store_anc_at hs0 hsle has hJE
    have hPC := hPX.trans (hXE.trans (honest_anc_of_store_anc_at hr0 hrle hzr hEC))
    have hXEr := store_anc_of_honest_anc_at hrun hp.noColl hr0 hrle hzr hXE hE'
    have hXr' := mem_of_honest_anc_at hrun hp.noColl hr0 hrle hzr hXE hE'
    have hPXr := store_anc_of_honest_anc_at hrun hp.noColl hr0 hrle hzr hPX hXr'
    have hrr' := fg_reachable_at hrun hr0 hrle hzr
    have hPE := hPXr.trans hXEr
    have hle := Healing.σ_h_le_of_anc hrr' hPE
    have hlt : ((tr.state att.val r).fg.σ P.root).h <
        ((tr.state att.val r).fg.σ E.root).h := by
      apply lt_of_le_of_ne hle
      intro heq
      have hentry := (Healing.Th_eq_of_anc hrr' hPE heq.symm).symm.trans hET
      have hP := mem_of_honest_anc_at hrun hp.noColl hr0 hrle hzr hPC hC
      obtain ⟨⟨E₀, hE₀, hE₀r, hE₀P, _, _⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hrr' P hP
      obtain rfl : E₀ = E := hU.1 (hsubr hE₀) (hsubr hE') (hE₀r.trans hentry)
      exact hne (hPXr.antisymm ((Compose.Growing.honest_blocks_coherent hrun
        hp.noColl).mono hsubr) (hXEr.trans hE₀P))
    exact ⟨⟨r, ell, C, hzr, by omega, (toFGAt_upTo_iff hm hrr).mp hto, hPC,
      hlt.trans_eq hEh⟩⟩
  exact ⟨att.val, r, ell, C, hzr, by omega, hto, hPC, hlt⟩

/-- **Finality compatible with a target is below it, or an earlier strictly higher report
extends the target**, at a cut `k ≤ b` of a node honest at it. -/
theorem finality_below_or_higher_report_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcompat : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P) :
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F P ∨
      ∃ z r ell C, z ∈ H (tr.time r) ∧ r < k ∧ SA.ToFGAt tr.projAC z r ell C ∧
        Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hcompat with h | h
  · exact Or.inl h
  by_cases he : P = (tr.state y k).fg.F
  · exact Or.inl (he ▸ Relation.ReflTransGen.refl)
  have hr := fg_reachable_at hp.run (hp.run.time_nonneg k) (fun _ hq => hp.run.time_mono hq.le) hy
  obtain ⟨hF, -, -, -, -, -, W, hW, hWF⟩ := Store.cache_invariants _ _ _ _ hr
  exact Or.inr (finalized_descendant_report_at hp hy hkb hW hF hWF.symm h he)

/-- **A held target below the head-height floor yields an earlier strictly higher report**, at a
cut `i ≤ b` of a node honest at it, when the target is above a high seed and compatible with every
earlier high origin, and the earlier high origins are pairwise compatible and compatible with the
seed. -/
theorem held_target_high_floor_report_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    {P S : SA.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ (tr.state y i).fg.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hpair : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      ∀ x' r' l' B', r' < i → HighOrigin tr H g x' r' l' B' →
        Compatible (tr.HonestBlocksAt H) B B')
    (hseedcomp : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) S B)
    (hcompare : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) P B)
    (hfloor : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor) :
    ∃ x r ell C, x ∈ H (tr.time r) ∧ r < i ∧ SA.ToFGAt tr.projAC x r ell C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hd := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hrun.time_mono hk.le
  have hr := fg_reachable_at hrun hd hle hy
  have hSy := mem_of_honest_anc_at hrun hp.noColl hd hle hy hSP hPy
  have hSs := highOrigin_mem_at hrun hp.noColl hseed
  have hSh := Healing.σ_h_le_of_anc hr (store_anc_of_honest_anc_at hrun hp.noColl hd hle hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
    rw [σ_eq_honest_at hrun hp.noColl (hrun.time_nonneg q) (fun _ hk => hrun.time_mono hk.le)
      hseed.1 hd hle hy hSs hSy]
    omega
  obtain ⟨x, r, l, B, E, hri, ho, -, hE, hEB, -, hEf, d, att, hrd, hdi, hxd, hs, hT⟩ :=
    hp.high_floor_signed_source_of_row_bound_at hseed hd hle hy hib
      (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z d hz hd' hdi r' l O hrd ho => by
        obtain ⟨-, -, ⟨CV, ℓ, D, -, hfl, -⟩, -⟩ := ho
        have ht : sp.ts l ≤ tr.time r' := by
          rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
          · change tr.time r' = sp.ts l + 6 * sp.Δ at ht
            linarith only [ht, sp.toParams.hΔ]
          · change sp.slot (tr.time r') = l at hsl
            exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r') l).2 (by omega)
        have hlabel := (SA.ts_le_iff_le_slot sp hd l).1
          (ht.trans (hrun.time_mono (by omega)))
        omega) hpair hseedcomp hSf
  have hPE : Anc (tr.HonestBlocksAt H) P E := by
    have hcomp : Compatible (tr.HonestBlocksAt H) P E := by
      rcases hcompare x r l B hri ho with h | h
      · exact SA.anc_total hU h hEB
      · exact Or.inr (hEB.trans h)
    rcases hcomp with h | h
    · exact h
    · have := Healing.σ_h_le_of_anc hr (store_anc_of_honest_anc_at hrun hp.noColl hd hle hy h hPy)
      omega
  obtain ⟨j, ell, C, hxj, hji, hto, hPC, hh⟩ :=
    hp.higher_report_of_signed_entry_at hd hle hy hxd hPy hE hs hdi hT hPE (by omega)
  exact ⟨x, j, ell, C, hxj, hji, hto, hPC, hh⟩

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
