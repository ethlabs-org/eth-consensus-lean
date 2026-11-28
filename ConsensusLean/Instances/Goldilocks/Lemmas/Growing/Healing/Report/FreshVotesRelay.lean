module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.LocalFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm-frame relay from a historical honest acceptance

The sender's acceptance is retained at its own cut; service remains owed after compromise.
Only the receiver's execution is retained through the receiving call.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

/-- Membership in an honest call frame comes from genesis or an earlier honest acceptance. -/
theorem frame_block_acceptance_at {ini}
    (rc : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {q : Nat}
    (hx : x ∈ H (tr.time q)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt x q ell) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) :
    B = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∨
      ∃ k < q, x ∈ H (tr.time k) ∧ tr.AcceptAt x k B := by
  have hd := rc.time_nonneg q
  have ht : B ∈ ((tr.upTo (tr.time q)).state x q).fg.tree := by
    rw [RunTrace.upTo_state_of_le rc.time_mono le_rfl]
    rw [(rc.cutLaw x q _ (Compose.projAC_callAt.mp hc) hx).1] at hB
    exact hB.1
  rcases Healing.tree_accepted (rc.upTo hd).toLocalRun hx ht with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, hk, rc.antitone (rc.time_mono hk.le) hx,
      ((RunTrace.upTo_acceptAt _).mp ha).2⟩

/-- The AC relay preserves the post-GST deadline after sender compromise. -/
theorem accepted_relay_before_at
    (rc : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i B)
    (hgi : gbar g ≤ tr.time i) (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (hij : tr.time i + sp.Δ ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.time i + sp.Δ := by
  have hbound : ∀ k ≤ j, tr.projAC.deadline y k (tr.time i) ≤ tr.time i + sp.Δ := by
    intro k hkj
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hrk hrs => hnr y r (rc.antitone (rc.time_mono (hrk.trans hkj)) hy)
        (Compose.projAC_restartAt.mp hrs)) (tr.time i)
    change _ ≤ max (tr.time i) (gbar g) + sp.Δ at h
    rwa [max_eq_left hgi] at h
  obtain ⟨k, hkj, hak, hkt⟩ := rc.toLocalRun.acRelayAt (σ := tr.time i) hx ha hy hc hFB
    fun q hqi hx' hq hj hF => by
      have hgq : g ≤ tr.time q := hqi ▸ (Healing.le_gbar g).trans hgi
      have he : max (tr.time q) g = tr.time i := (max_eq_left hgq).trans hqi
      simpa only [he] using hsvc.relay x q B hx' hq hgq y j hy hj
        (by rw [he, ← Compose.projAC_deadline]; exact (hbound j le_rfl).trans hij) hF
  exact ⟨k, hkj, hak, hkt.trans_le (hbound k hkj)⟩

private theorem relayed_accept_before_at
    (rc : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {k j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hxk : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {elly : ACLabel (goldilocksNode sp)} (hcy : tr.projAC.CallAt y j elly)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j) (hkt : tr.time k + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ a < j, tr.AcceptAt y a B ∧ tr.time a < max (tr.time k + sp.Δ) (gbar g + 2 * sp.Δ) := by
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl' : ∀ c ≤ j, tr.deadline y c (max (tr.time k) g) sp.Δ ≤ tr.time k + sp.Δ := by
      intro c hc
      rw [max_eq_left ((Healing.le_gbar g).trans hnew), ← Compose.projAC_deadline]
      have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
        (fun r hrc hrs => hnr r (hrc.trans hc) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
      rwa [max_eq_left hnew] at h
    obtain ⟨a, haj, ha, hat⟩ := hsvc.relay x k B hxk ha ((Healing.le_gbar g).trans hnew)
      y j hy ⟨_, Compose.projAC_callAt.mp hcy⟩ ((hdl' j le_rfl).trans hkt) hF
    refine ⟨a, lt_of_le_of_ne haj ?_, ha,
      lt_max_of_lt_left (hat.trans_le (hdl' a haj))⟩
    intro he
    subst a
    cases Option.some.inj (ha.2.symm.trans (Compose.projAC_callAt.mp hcy).2)
  · obtain ⟨a, haj, ha, hat⟩ := Healing.accept_before_snapshot hg fun q hq hfirst =>
      hcatch x k B hxk ha (not_le.mp hnew) y q (rc.antitone hg hy) hfirst
        ((Compose.Growing.F_mono_at rc (rc.time_nonneg j) hy
          (fun r hr => rc.time_mono hr.le) hq).trans hF)
    exact ⟨a, haj, ha, lt_max_of_lt_right hat⟩

/-- A historical frame block relays into a later frame through honest acceptance. -/
theorem frame_relay_before_at {ini}
    (rc : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {ellx elly : ACLabel (goldilocksNode sp)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hd := rc.time_nonneg j
  have hp := rc.upTo hd
  have hac := Compose.goldilocks_ac_projection_from hp (hnc.upTo _)
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j elly := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcy⟩
  have hPh := Compose.Growing.frameIn_at rc hnc hy hcy
  have hFstate : elly.frame.F = (tr.state y j).fg.F := by
    rw [(rc.cutLaw y j _ (Compose.projAC_callAt.mp hcy) hy).1]
    rfl
  rcases frame_block_acceptance_at rc hx hcx hB with hgB | ⟨k, hk, hxk, ha⟩
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hac.localRun.toU hy j elly hc'
    have he : B = G := (Compose.Growing.honest_blocks_coherent rc hnc).1
      ((Compose.Growing.frameIn_at rc hnc hx hcx).2 hB)
      (RunTrace.honestBlocks_upTo_subset rc.time_mono hd hG)
      ((congrArg Block.root hgB).trans hGr.symm)
    rw [he] at hF
    rcases Relation.ReflTransGen.cases_tail hF with heq | ⟨C, _, hpar⟩
    · rw [he]
      exact heq.symm ▸ hPh.1.rooted.1
    · exact (Option.some_ne_none _ (hpar.2.2.symm.trans hGp)).elim
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have hle := rc.time_mono hk.le
    linarith only [hle, hq]
  obtain ⟨a, haj, ha, -⟩ := relayed_accept_before_at rc hsvc hcatch hxk ha hy hnr hcy hg hkt
    (hFstate ▸ hF)
  have ha' : (tr.upTo (tr.time j)).AcceptAt y a B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨rc.time_mono haj.le, ha⟩
  obtain ⟨hacc, _, _⟩ := Healing.ac_block_after hp.toLocalRun hy ha'
  obtain ⟨ella, hca, hba⟩ := hacc
  have hBa := (AC.accept_new sp hac.localRun hy ⟨ella, hca, hba⟩).1 ella hca
  have hBa' : B ∈ ((tr.upTo (tr.time j)).state y (a + 1)).fg.tree := by
    rw [(hp.toLocalRun.cutLaw y hy (a + 1) _ (Compose.projAC_callAt.mp hca)).1] at hBa
    exact hBa.1
  have hBj := Compose.tree_mono hp.toLocalRun hy (show a + 1 ≤ j by omega) hBa'
  rw [RunTrace.upTo_state_of_le rc.time_mono le_rfl] at hBj
  rw [(rc.cutLaw y j _ (Compose.projAC_callAt.mp hcy) hy).1]
  exact ⟨hBj, store_anc_of_honest_anc_at rc hnc hd
    (fun r hr => rc.time_mono hr.le) hy (hFstate ▸ hF) hBj⟩

end Consensus.Goldilocks.Healing.Growing

end
