module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Candidate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage under growing faults: sources and the sourced rows

* `source_compatible_at` (SRC): an FG source of a node honest at its call is the viable ancestor
  of a stored live lock block, so it is compatible with `B` when the stored locks are.
* `rows_sourced_at`: the attestations of the tree of a node honest at cut `n`, by validators
  honest at `t_n`, are sourced (`HonestRowsSourcedAt`) by blocks compatible with `B` when the
  sources at the earlier cuts of nodes honest then are. The attester signed at an earlier cut
  while honest, from its own source (Lemma G at the reading cut), so each attester is read on the
  prefix through `t_n`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

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

/-- **(SRC)**: an FG source at a cut `k` of a node honest then is compatible with `B` when every
lock stored at `k` names a held block compatible with `B`. -/
theorem source_compatible_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ (tr.state y k).ac.locks, ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧
      Compatible (tr.HonestBlocksAt H) L B)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC y k ℓ C) : Compatible (tr.HonestBlocksAt H) C B := by
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hpc
  rw [projAC_state_at hrun hy] at hC
  obtain ⟨hCv, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlC, -, -⟩ := toFG_candidate hC
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hΦ.coherent.1 hCv.1 hvt hlC.symm
  obtain ⟨L, hL, hLr, hLB⟩ := hlocks l₀ hl₀
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) (mem_honestBlocksAt hrun hy hL) (hB₀r.trans hLr.symm)
  exact compatible_of_head_anc hU (hva.mono hΦU) hLB

/-- **The rows are sourced by compatible blocks**: with every FG source, at a cut before `n` of a
node honest then, compatible with `B`, every attestation of the tree of a node honest at cut `n`
by a validator honest at `t_n` has a source compatible with `B`, held by that validator at its
signing cut. -/
theorem rows_sourced_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x k, k < n → x ∈ H (tr.time k) → ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocksAt H) C B)
    {y : Fin sp.n} (hy : y ∈ H (tr.time n)) :
    HonestRowsSourcedAt tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n := by
  have hd := hrun.time_nonneg n
  have hm := hrun.time_mono
  have hst : ∀ x k, k ≤ n → (tr.upTo (tr.time n)).state x k = tr.state x k :=
    fun x k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hr := hrun.upTo hd
  refine honestRowsSourcedAt_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmn, -, k, hkm, src, hcall⟩ :=
    honest_row_signed_before hr (hnc.upTo _) hy (by rw [hst y n le_rfl]; exact hX) ha hav
  obtain ⟨j, rfl, ℓ, hcj, hcl, -, hC, hfg⟩ := attest_source hr.toLocalRun hav hcall
  have hj1 : j + 1 ≤ n := by omega
  obtain ⟨hjd, hcj⟩ := (Trace.upTo_callAt _).mp hcj
  obtain ⟨-, hcall⟩ := (Trace.upTo_callAt _).mp hcall
  rw [hst a.val j (by omega)] at hC
  rw [hst a.val (j + 1) hj1, hst a.val j (by omega)] at hfg
  have hav' : a.val ∈ H (tr.time j) := hrun.antitone hjd hav
  have hav1 : a.val ∈ H (tr.time (j + 1)) := hrun.antitone (hm hj1) hav
  have hfr := (hrun.cutLaw a.val j _ hcj hav').1
  have hto : SA.ToFGAt tr.projAC a.val j ℓ src :=
    ⟨projAC_callAt.2 hcj, hcl, by rw [projAC_state_at hrun hav']; exact hC⟩
  have hst' : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := (toFG_candidate hC).1.1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  have hR := fg_reachable hr.toLocalRun hav (j + 1)
  rw [hst a.val (j + 1) hj1] at hR
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hR _ hst'
  have hT := createAtt_T (hrun.cutLaw a.val (j + 1) _ hcall hav1).1
  rw [← hEr, hET] at hT
  exact ⟨src, hsrc a.val j (by omega) hav' ℓ src hto, a.val, j + 1, hav, hj1, hst', hT.symm⟩

end Consensus.Goldilocks.Compose.Growing

end
