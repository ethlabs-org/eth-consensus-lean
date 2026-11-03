module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Candidate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage lock safety: sources, OB-F and VA (card §6)

* `source_compatible` (SRC, §6.1): an FG source is the viable ancestor of a stored live fast lock
  block, so it is compatible with `P` when the stored locks are.
* `rows_sourced`: the honest rows of a tree are sourced by blocks compatible with `P` when the
  sources of the earlier cuts are.
* `caches_compatible` (OB-F, §6.2): `Σ.J` is compatible with `P` (its quorum has an honest row) and
  `Σ.F ⪯ Σ.J`.
* VA (§6.3) is `held_candidate_of_rows` (`Candidate`) at `P`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- `ac_to_fg` returns one of its candidates. -/
private theorem toFG_candidate {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : (SA.acToFG sp A Φ t).2 = some C) :
    C ∈ SA.toFGCandidates sp A Φ t := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1

/-- An attestation names the entry of its entry state. -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

/-- **(SRC)** (§6.1): an FG source at cut `k` is compatible with `B` when every lock stored at `k`
names a held block compatible with `B`. -/
theorem source_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ (tr.state y k).ac.locks, ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧
      Compatible (tr.HonestBlocks H) L B)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC y k ℓ C) : Compatible (tr.HonestBlocks H) C B := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hpc
  rw [projAC_state hrun.toLocalRun hy k] at hC
  obtain ⟨hCv, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlC, -, -⟩ := toFG_candidate hC
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hΦ.coherent.1 hCv.1 hvt hlC.symm
  obtain ⟨L, hL, hLr, hLB⟩ := hlocks l₀ hl₀
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) ⟨y, hy, k, hL⟩ (hB₀r.trans hLr.symm)
  exact compatible_of_anc hU (hva.mono hΦU) hLB

/-- **Honest rows are sourced by compatible blocks**: with every honest FG source before cut `n`
compatible with `B`, every honest row of `y`'s tree at `n` has an honest source compatible with
`B`. -/
theorem rows_sourced (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x ∈ H, ∀ k < n, ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C B)
    {y : Fin sp.n} (hy : y ∈ H) :
    HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n := by
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmn, -, k, hkm, src, hcall⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨j, rfl, ℓ, hcj, hcl, -, hC, hfg⟩ := attest_source hrun.toLocalRun hav hcall
  have hfr := (hrun.cutLaw a.val hav j _ hcj).1
  have hto : SA.ToFGAt tr.projAC a.val j ℓ src :=
    ⟨projAC_callAt.2 hcj, hcl, by rw [projAC_state hrun.toLocalRun hav j]; exact hC⟩
  have hst : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := (toFG_candidate hC).1.1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hrun.toLocalRun hav (j + 1)) _ hst
  have hT := createAtt_T (hrun.cutLaw a.val hav (j + 1) _ hcall).1
  rw [← hEr, hET] at hT
  exact ⟨src, hsrc a.val hav j (by omega) ℓ src hto,
    isHonestSource_iff.2 ⟨a.val, hav, j + 1, hst, hT.symm⟩⟩

/-- **OB-F** (§6.2): with the honest rows of `y`'s tree sourced by blocks compatible with a block
`B` of the honest blocks, `Σ.F` and `Σ.J` are compatible with `B`. -/
theorem caches_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {n : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H)
    (hsrc : HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n) :
    Compatible (tr.HonestBlocks H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y n).fg.J B := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hJ := J_compatible_before hrun hnc hf hy hsrc (fun _ h => h) hBU
  obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy n)
  exact ⟨compatible_of_anc hU (hFJ.mono (fg_tree_subset_honest hy n)) hJ, hJ⟩

end Consensus.Goldilocks.Compose

end
