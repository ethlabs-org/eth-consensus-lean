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
  prefix through `t_n`.
* `rows_sourced_by`: the same at a read time `t` after every cut before `n` (signers and sources
  classified at `t`, `HonestRowsSourcedBy`);
* `J_compatible_by`, `caches_compatible_by` (OB-F) at a read time `t`, and their cut forms
  `J_compatible_at`, `caches_compatible_at`: with `2 f_t < n` and the rows sourced by blocks
  compatible with a block `B` held while honest (not necessarily in the prefix through `t`),
  `Σ.J` is compatible with `B` (its quorum has a member honest at `t`, whose source is above
  `Σ.J`), and `Σ.F ⪯ Σ.J`. -/

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
theorem source_compatible_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

/-- **The rows are sourced by compatible blocks, at a read time**: with every FG source, at a cut
before `n` of a node honest then, compatible with `B`, every attestation of the tree at cut `n` of
a node honest at a time `t ≥ 0` after every cut before `n`, by a validator honest at `t`, has a
source compatible with `B`, held by that validator at its signing cut. -/
theorem rows_sourced_by {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x k, k < n → x ∈ H (tr.time k) → ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocksAt H) C B)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) :
    HonestRowsSourcedBy tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n t := by
  have hm := hrun.time_mono
  have hr := hrun.upTo ht0
  refine honestRowsSourcedBy_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmn, -, k, hkm, src, hcall⟩ :=
    honest_row_signed_before hr (hnc.upTo _) hy (by rw [Trace.upTo_state tr y ht]; exact hX) ha
      hav
  obtain ⟨j, rfl, ℓ, hcj, hcl, -, hC, hfg⟩ := attest_source hr.toLocalRun hav hcall
  have hj1 : j + 1 < n := by omega
  have hjt : ∀ k' < j + 1, tr.time k' ≤ t := fun k' hk' => ht k' (by omega)
  have hjt' : ∀ k' < j, tr.time k' ≤ t := fun k' hk' => ht k' (by omega)
  obtain ⟨hjd, hcj⟩ := (Trace.upTo_callAt _).mp hcj
  obtain ⟨-, hcall⟩ := (Trace.upTo_callAt _).mp hcall
  rw [Trace.upTo_state tr a.val hjt'] at hC
  rw [Trace.upTo_state tr a.val hjt, Trace.upTo_state tr a.val hjt'] at hfg
  have hav' : a.val ∈ H (tr.time j) := hrun.antitone hjd hav
  have hav1 : a.val ∈ H (tr.time (j + 1)) := hrun.antitone (ht _ hj1) hav
  have hfr := (hrun.cutLaw a.val j _ hcj hav').1
  have hto : SA.ToFGAt tr.projAC a.val j ℓ src :=
    ⟨projAC_callAt.2 hcj, hcl, by rw [projAC_state_at hrun hav']; exact hC⟩
  have hst' : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := (toFG_candidate hC).1.1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  have hR := fg_reachable hr.toLocalRun hav (j + 1)
  rw [Trace.upTo_state tr a.val hjt] at hR
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hR _ hst'
  have hT := createAtt_T (hrun.cutLaw a.val (j + 1) _ hcall hav1).1
  rw [← hEr, hET] at hT
  exact ⟨src, hsrc a.val j (by omega) hav' ℓ src hto,
    isHonestSourceAt_iff.2 ⟨a.val, j + 1, hav, hjt, hst', hT.symm⟩⟩

/-- **`Σ.J` is compatible with a block compatible with every source satisfying `G`**, at a cut
`i` of a node honest at a time `t ≥ 0` after every cut before `i`, with `2 f_t < n`. The
justification's honest source is found in the prefix through `t`; `B` is only held while
honest. -/
theorem J_compatible_by {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedBy tr H G y i t) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B) (hB : B ∈ tr.HonestBlocksAt H) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hr := hrun.upTo ht0
  have hsub := upTo_subset hrun ht0
  have hst := Trace.upTo_state tr y ht
  by_cases h0 : (tr.state y i).fg.hj = 0
  · have hJ := justified_genesis hr (by rw [hst]; exact h0) hy
    rw [hst] at hJ
    rw [hJ]
    exact Or.inl (honestAt_genesis_anc hrun hB).2
  obtain ⟨-, -, D, ⟨hD, -⟩, hDs⟩ :=
    justified_honest_source_before hr (hnc.upTo _) hf hy (hsrc.upTo_held ht)
      (by rw [hst]; omega)
  rw [hst] at hDs
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hr.toLocalRun hy i)).2.1
  rw [hst] at hJ
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr (hnc.upTo _) hDs
    ⟨y, hy, i, by rw [hst]; exact hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D :=
    (hJD.mono (fg_tree_subset_honest hx k)).mono hsub
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hU hJDU h

/-- **`Σ.J` is compatible with a block compatible with every source**, at a cut `i` of a node
honest then, with `2 f_{t_i} < n`. -/
theorem J_compatible_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedAt tr H G y i) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocksAt H) D B) (hB : B ∈ tr.HonestBlocksAt H) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B :=
  J_compatible_by hrun hnc (hrun.time_nonneg i) (fun _ hk => hrun.time_mono hk.le) hy hf
    (hsrc.by_ hrun) hGB hB

/-- **OB-F at a read time**: at a cut `n` of a node honest at a time `t ≥ 0` after every cut
before `n`, with `2 f_t < n` and the rows sourced by blocks compatible with a block `B` held while
honest, `Σ.F` and `Σ.J` are compatible with `B`. -/
theorem caches_compatible_by {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hsrc : HonestRowsSourcedBy tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n t) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.J B := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hst := Trace.upTo_state tr y ht
  have hJ := J_compatible_by hrun hnc ht0 ht hy hf hsrc (fun _ h => h) hBU
  have hR := fg_reachable (hrun.upTo ht0).toLocalRun hy n
  rw [hst] at hR
  obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hsub : (tr.state y n).fg.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    upTo_subset hrun ht0 ⟨y, hy, n, by rw [hst]; exact hX⟩
  exact ⟨compatible_of_head_anc hU (hFJ.mono hsub) hJ, hJ⟩

/-- **OB-F**: at a cut `n` of a node honest then, with `2 f_{t_n} < n` and the rows sourced by
blocks compatible with a block `B` held while honest, `Σ.F` and `Σ.J` are compatible with `B`. -/
theorem caches_compatible_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {n : Nat} (hy : y ∈ H (tr.time n))
    (hf : 2 * (H (tr.time n))ᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBU : B ∈ tr.HonestBlocksAt H)
    (hsrc : HonestRowsSourcedAt tr H (fun D => Compatible (tr.HonestBlocksAt H) D B) y n) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.J B :=
  caches_compatible_by hrun hnc (hrun.time_nonneg n) (fun _ hk => hrun.time_mono hk.le) hy hf
    hBU (hsrc.by_ hrun)

end Consensus.Goldilocks.Compose.Growing

end
