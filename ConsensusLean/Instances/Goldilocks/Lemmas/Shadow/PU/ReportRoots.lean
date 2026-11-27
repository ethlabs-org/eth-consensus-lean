module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Origins
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Geometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CandidateReport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U shadow, report cover: the root and cache suppliers

Shadow copies, over the shadow run, of the stock suppliers that `ReportCover` reads at a cut:
`cutZ_lt_of_anc_at`, `cache_ahead_report` (and its read-time form), and
`low_root_of_held_seed_at`. The stock proofs read only the store's tree, the states `σ`, the
cached `F` and `J` and the store-level `fcRoot`, which the shadow keeps; the shadow frame enters
only as the frame's tree, which is the store's tree above `F` (`mem_frame'_tree`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store Consensus.Goldilocks.Shadow.PU

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time} {hold : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- A high descendant cannot be held before the snapshot by a holder still honest there
(`ProposalImpl.cutZ_lt_of_anc_at`). -/
theorem ProposalImpl.cutZ_lt_of_anc_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {z : Fin sp.n} {k : Nat}
    (hz : z ∈ H (max (tr.time k) (cutZ sp.toParams g)))
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z k).fg.tree)
    (hBW : Anc (tr.HonestBlocksAt H) B W) :
    cutZ sp.toParams g < tr.time k := by
  classical
  by_contra h
  have hkZ : tr.time k ≤ cutZ sp.toParams g := not_lt.mp h
  have hzZ : z ∈ H (cutZ sp.toParams g) := by
    rwa [max_eq_right hkZ] at hz
  have hZ0 : 0 ≤ cutZ sp.toParams g := (hp.run.time_nonneg k).trans hkZ
  have hle : ∀ q < k, tr.time q ≤ cutZ sp.toParams g :=
    fun _ hq => (hp.run.time_mono hq.le).trans hkZ
  have hhigh := Outcome.high_of_anc_at' hp.run hp.noColl ho hZ0 hle hzZ hW hBW
  obtain ⟨c, hc, _⟩ := hp.snapshot
  have hkc : k ≤ c := by
    by_contra hn
    exact (not_lt_of_ge hkZ) (hc.2.trans_le (hp.run.time_mono (by omega)))
  have hWc := Compose.Growing.tree_mono_at' hp.run hZ0 hzZ hc.1 hkc hW
  have hs := σ_eq_honest_at' hp.run hp.noColl hZ0 hle hzZ hZ0 hc.1 hzZ hW hWc
  have hbnd := (cache_invariants_with finalitySpec_updateFinality
    (Compose.Growing.reachable_at' hp.run hZ0 hzZ hc.1).reachableWith).2.2.2.2.1 W hWc
  have hmax : (tr.state z c).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v c).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzZ, c, hc, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hc
    exact ⟨v, rfl⟩
  rw [← hs] at hbnd
  omega


section Static

variable {Hs : Set (Fin sp.n)}

/-- An honest attestation names a report entry (`signAt_report_entry`). -/
theorem signAt_report_entry {ini} (hrun : GoldilocksRun proposer dg Hs tr ini) {v : Fin sp.n}
    (hv : v ∈ Hs) {k : Nat} {a : FG.Att sp.n} (hs : tr.SignAt v k a) :
    ∃ j, k = j + 1 ∧ tr.time j = tr.time k ∧
      ∃ ℓ C E, AC.ToFGAt tr.projAC v j ℓ C ∧
        C ∈ (tr.state v j).fg.tree ∧ E ∈ (tr.state v j).fg.tree ∧
        E.root = a.T ∧ (tr.state v j).fg.Anc E C ∧
        ((tr.state v j).fg.σ C.root).Th = E.root ∧
        ((tr.state v j).fg.σ E.root).Th = E.root ∧
        ((tr.state v j).fg.σ E.root).h = ((tr.state v j).fg.σ C.root).h ∧
        ((tr.state v j).fg.σ C.root).h = a.h := by
  obtain ⟨C, hc⟩ := hs
  obtain ⟨j, rfl, ℓ, hj, hcall, ht, hret, hfg⟩ := Coherence.attest_source hrun.toLocalRun hv hc
  have hpc : tr.projAC.CallAt v j ℓ := Compose.projAC_callAt.2 hj
  have hC : C ∈ ℓ.frame.tree := (AC.toFG_source_below_lock hret).1.1
  have hCt : C ∈ (tr.state v j).fg.tree := by
    rw [((Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw v hv j _ hj)).1] at hC
    exact (mem_frame_tree.1 hC).1
  have hsigned := ((Node.cutStep_attest_some _ _ _ _ _ _).1 (hrun.cutLaw v hv (j + 1) _ hc)).1
  rw [hfg] at hsigned
  obtain ⟨E, hE, hEr, hEC, hTh, hET, hEh, hCa⟩ := entry_of_createAtt_with
    finalitySpec_updateFinality (Node.fg_reachable_at hrun.toLocalRun hv j).reachableWith
    hCt hsigned
  refine ⟨j, rfl, ht, ℓ, C, E, ⟨hpc, hcall, ?_⟩, hCt, hE, hEr, hEC, hTh, hET, hEh, hCa⟩
  rw [Compose.projAC_state hrun.toLocalRun hv j]
  exact hret

/-- A cache strictly ahead of a held target is backed by an actual earlier honest report at a
strictly higher height (`cache_ahead_report`). -/
theorem cache_ahead_report {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg Hs tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hsᶜ.ncard < sp.toParams.fg.q)
    {y : Fin sp.n} (hy : y ∈ Hs) {i : Nat}
    {P X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X = (tr.state y i).fg.F ∨ X = (tr.state y i).fg.J)
    (hP : P ∈ (tr.state y i).fg.tree)
    (hPX : Anc (tr.HonestBlocks Hs) P X) (hne : P ≠ X) :
    ∃ v ∈ Hs, ∃ j < i, ∃ k < i, ∃ a : FG.Att sp.n, ∃ ℓ C,
      tr.SignAt v k a ∧ k = j + 1 ∧ tr.time j = tr.time k ∧ tr.time j ≤ tr.time i ∧
      AC.ToFGAt tr.projAC v j ℓ C ∧ a.T = X.root ∧
      X ∈ (tr.state v j).fg.tree ∧ Anc (tr.HonestBlocks Hs) X C ∧
      ((tr.state v j).fg.σ C.root).Th = X.root ∧
      ((tr.state v j).fg.σ C.root).h = ((tr.state y i).fg.σ X.root).h ∧
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ X.root).h := by
  have hfs := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
  have hU := Coherence.honest_blocks_coherent hrun.toLocalRun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks Hs := fun _ h => ⟨y, hy, i, h⟩
  have hXt : X ∈ (tr.state y i).fg.tree := by
    rcases hX with rfl | rfl
    · exact (cache_invariants_with hfs hr).1
    · exact (cache_invariants_with hfs hr).2.1
  rcases cache_quorum_with hfs hr X (hX.elim Or.inr Or.inl) with hg | ⟨q, hq, hrows⟩
  · have he := Coherence.honest_eq_genesis hrun hU (hsub hXt) hg
    rw [he] at hPX
    rcases Relation.ReflTransGen.cases_tail hPX with heq | ⟨Y, _, hY⟩
    · exact False.elim (hne (heq.symm.trans he.symm))
    · exact absurd hY.2.2 (by simp [Params.genesisBlock])
  have hex : ∃ v ∈ q, v ∈ Hs := by
    by_contra h
    have hsubq : (↑q : Set (Fin sp.n)) ⊆ Hsᶜ := fun v hv hvH => h ⟨v, hv, hvH⟩
    have hn := Set.ncard_le_ncard hsubq (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hn
    exact (not_lt_of_ge (hq.trans hn)) hf
  obtain ⟨v, hvq, hv⟩ := hex
  obtain ⟨B, hB, a, ha, hav, haX⟩ := hrows v hvq
  have haH : a.val ∈ Hs := hav ▸ hv
  obtain ⟨m, hmi, _, k, hkm, hs⟩ := Compose.honest_row_signed_before' hrun hnc hy hB ha haH
  obtain ⟨j, hkj, ht, ℓ, C, E, hto, hC, hE, hEr, hEC, hTh, hET, hEh, _⟩ :=
    signAt_report_entry hrun haH hs
  have hsubv : (tr.state a.val j).fg.tree ⊆ tr.HonestBlocks Hs :=
    fun _ h => ⟨a.val, haH, j, h⟩
  have he : E = X := hU.1 (hsubv hE) (hsub hXt) (hEr.trans haX)
  subst E
  have hrv := (Node.fg_reachable_at hrun.toLocalRun haH j).reachableWith
  have hσ := σ_eq_of_mem_with hr hfs hrv hU.1 hsub hsubv hXt hE
  have hfg := Compose.projFG_localRun' hrun hnc
  have hPX' := Compose.FrameGeometry.honest_held_anc' hrun.toLocalRun hfg haH hPX hE
  have hPv : P ∈ (tr.state a.val j).fg.tree := (Anc.mem hPX' hne).1
  have hσP := σ_eq_of_mem_with hr hfs hrv hU.1 hsub hsubv hP hPv
  have hlt : ((tr.state a.val j).fg.σ P.root).h < ((tr.state a.val j).fg.σ X.root).h := by
    obtain ⟨hle, heq⟩ := Compose.FrameGeometry.honest_held_height' hrun.toLocalRun haH hPX'
    apply lt_of_le_of_ne hle
    intro hh
    have hentry := (heq hh.symm).symm.trans hET
    obtain ⟨⟨E, hE', hEr', hEP, _, _⟩, _⟩ := entry_state_of_source_with hfs hrv P hPv
    have he : E = X := hU.1 (hsubv hE') (hsubv hE) (hEr'.trans hentry)
    subst E
    exact hne (hPX'.antisymm (hU.mono hsubv) hEP)
  refine ⟨a.val, haH, j, by omega, k, by omega, a, ℓ, C, hs, hkj, ht,
    hrun.time_mono (by omega), hto, haX, hE, hEC.mono hsubv, hTh, ?_, ?_⟩
  · rw [hσ]
    exact hEh.symm
  · rw [hσP, hσ]
    exact hlt

end Static

/-- **A cache strictly ahead of a held target is backed by an earlier report**, at a strictly
higher height, of a validator honest at the reading cut (`cache_ahead_report_at`). -/
theorem cache_ahead_report_at' {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q)
    {P X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X = (tr.state y i).fg.F ∨ X = (tr.state y i).fg.J)
    (hP : P ∈ (tr.state y i).fg.tree)
    (hPX : Anc (tr.HonestBlocksAt H) P X) (hne : P ≠ X) :
    ∃ v, v ∈ H (tr.time i) ∧ ∃ j < i, ∃ k < i, ∃ att : FG.Att sp.n, ∃ ℓ C,
      tr.SignAt v k att ∧ k = j + 1 ∧ tr.time j = tr.time k ∧ tr.time j ≤ tr.time i ∧
      AC.ToFGAt tr.projAC v j ℓ C ∧ att.T = X.root ∧
      X ∈ (tr.state v j).fg.tree ∧ Anc (tr.HonestBlocksAt H) X C ∧
      ((tr.state v j).fg.σ C.root).Th = X.root ∧
      ((tr.state v j).fg.σ C.root).h = ((tr.state y i).fg.σ X.root).h ∧
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ X.root).h := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hst : ∀ z k, k ≤ i → (tr.upTo (tr.time i)).state z k = tr.state z k :=
    fun z k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hR := Compose.Growing.reachable_at' hrun hd hy (fun _ hk => hrun.time_mono hk.le)
  have hXt : X ∈ (tr.state y i).fg.tree := by
    rcases hX with rfl | rfl
    · exact (cache_invariants_with finalitySpec_updateFinality hR.reachableWith).1
    · exact (cache_invariants_with finalitySpec_updateFinality hR.reachableWith).2.1
  have hXp : X ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨y, hy, i, by rw [hst y i le_rfl]; exact hXt⟩
  obtain ⟨v, hv, j, hji, k, hki, att, ℓ, C, hs, hkj, hjk, hjt, hto, haT, hXv, hXC, hTh, hCh,
      hPh⟩ := cache_ahead_report (hrun.upTo hd) (hnc.upTo _) hf hy (X := X) (P := P)
    (by rw [hst y i le_rfl]; exact hX) (by rw [hst y i le_rfl]; exact hP)
    (RunTrace.anc_upTo_of_right' hrun hnc hd hXp hPX) hne
  rw [hst v j hji.le] at hXv hTh hCh
  rw [hst y i le_rfl] at hCh hPh
  exact ⟨v, hv, j, hji, k, hki, att, ℓ, C, ((RunTrace.upTo_signAt tr).mp hs).2, hkj, hjk, hjt,
    (toFGAt_upTo_iff hm (hm hji.le)).mp hto, haT, hXv,
    hXC.mono (RunTrace.honestBlocks_upTo_subset hm hd), hTh, hCh, hPh⟩

/-- A cut of a node honest at it, with a low justified height and a held high seed, has its
finalized-chain root compatible with every held block compatible with the seed
(`low_root_of_held_seed_at`). The root is the store's `fcRoot`, which the shadow keeps. -/
theorem ResetPremisesUpTo.low_root_of_held_seed_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B →
      B ∈ (Node.frame (tr.state y i)).tree) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := (Compose.Growing.reachable_at' hrun hi0 hy hlei).reachableWith
  have hFS := hp.low_finalized_below_origin_at hi0 hlei hy hib hlow hS hqb
  have hSh := Outcome.high_of_anc_at' hrun hnc hS hi0 hlei hy hSy .refl
  have hJ : ∀ D ∈ (tr.state y i).fg.tree,
      (tr.state y i).fg.Anc (tr.state y i).fg.F D →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ D.root).h →
      (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬ (tr.state y i).fg.Contest → Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D := by
    intro D hD hFD hDh he hn
    have hle := (cache_invariants_with finalitySpec_updateFinality hreach).2.2.2.2.1 D hD
    have hJD : (tr.state y i).fg.Anc (tr.state y i).fg.J D := by
      by_contra h
      exact hn ⟨he, D, hD, hFD, by clear * - hlow hDh he hle; omega, h⟩
    exact hJD.mono fun X hX => ⟨y, i, tr.time i, hi0, hlei, hy, hX⟩
  unfold Store.fcRoot
  split_ifs with hactive
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU
        (hJ S hSy (store_anc_of_honest_anc_at' hrun hnc hi0 hlei hy hFS hSy) hSh
          hactive.1 hactive.2) hBS
    · have hFB := hFS.trans hSB
      have hBy := (mem_frame_tree.1 (hheld hFB)).1
      have hBhy := Outcome.high_of_anc_at' hrun hnc hS hi0 hlei hy hBy hSB
      exact Or.inl (hJ B hBy (store_anc_of_honest_anc_at' hrun hnc hi0 hlei hy hFB hBy) hBhy
        hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU hFS hBS
    · exact Or.inl (hFS.trans hSB)

end Consensus.Goldilocks.Healing.Growing

end
