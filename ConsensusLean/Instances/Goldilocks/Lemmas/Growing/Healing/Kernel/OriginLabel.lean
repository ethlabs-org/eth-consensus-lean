module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The snapshot bounds each bounded high origin's label

A counted supporter honest at both the snapshot and the lock write really voted
before the snapshot if the label is earlier. Its high head then contradicts HZ.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A high origin written within the finite horizon cannot carry a pre-snapshot label. -/
theorem ResetPremisesUpTo.cutZ_le_ts_of_highOrigin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b) :
    cutZ sp.toParams g ≤ sp.ts j := by
  classical
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hm := hp.run.time_mono
  obtain ⟨k, hk, hkb⟩ := hp.snapshot
  have hz0 : 0 ≤ cutZ sp.toParams g := by
    have := lt_cutZ sp g
    have := Healing.gbar_nonneg g
    have := sp.toParams.hΔ
    linarith
  let t := max (cutZ sp.toParams g) (tr.time i)
  have ht0 : 0 ≤ t := hz0.trans (le_max_left _ _)
  have htb : t ≤ b := max_le (hk.2.le.trans hkb) hib
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨ell', hc', hDt⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hci.2.symm.trans hc'.2)
  obtain ⟨hPhi, hPhiTree⟩ := frame_tree_subset_at hp.run hp.noColl ho.1 hci
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hm hq.le,
      ho.1, hPhiTree hC⟩
  have hBD := (SA.anc_viableAncestor ell.frame D).mono hPhiU
  obtain ⟨hcount, hheads⟩ := SA.Growing.fastLock_counted hac ho.1 hfl
  rw [hp.stock] at hcount
  have hf := hp.faults t ht0 htb
  have hn := sp.toParams.hn
  have hless : (H t)ᶜ.ncard < {u | ∃ v ∈ CV, v.val = u}.ncard := by
    change 0 < sp.n at hn
    omega
  obtain ⟨v, ⟨vote, hvote, rfl⟩, hv⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hless
  have hvt : vote.val ∈ H t := not_not.mp hv
  have hvi := hp.run.antitone (le_max_right _ _) hvt
  have hvz := hp.run.antitone (le_max_left _ _) hvt
  have hpre := hac.upTo (hp.run.time_nonneg i)
  have hfl' := (SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩
  obtain ⟨hvs, R, hRU, hRroot, _, hDR⟩ := hheads vote hvote
  have hvcast : ∃ q ≤ i, ∃ e, SA.VoteAt (tr.projAC.upTo (tr.time i)) vote.val q e ∧
      e.msg = vote := by
    rcases hfl' with ⟨ell', _, hu, _, _, hCV⟩ | ⟨ell', A, hpt, _, _, hCV⟩
    · subst CV
      obtain ⟨q, hq, e, he, hev⟩ := hpre.honest.pool_vote x ho.1 i _ vote hvote.1 hvi
      exact ⟨q, hq.le, e, he, hev⟩
    · subst CV
      exact (SA.optimisticPoint_pool_vote hpre ho.1 hpt hvote.1 hvi).2
  obtain ⟨q, hqi, e, hvq, hev⟩ := hvcast
  have hqtime : tr.time q ≤ sp.ts j + sp.Δ := by
    have htime := SA.vote_time_le hpre.localRun hvi hvq
    have hslot := (SA.vote_signer_slot hpre.localRun hvi hvq).2
    change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htime
    change e.msg.slot = sp.slot (tr.time q) at hslot
    rw [← hslot, hev, hvs] at htime
    exact htime
  by_contra hlt
  have hjZ : sp.ts (j + 1 : Nat) ≤ cutZ sp.toParams g := by
    rw [cutZ_eq]
    apply (SA.ts_le_iff sp).mpr
    rw [cutZ_eq] at hlt
    have := (SA.ts_le_iff sp).not.mp hlt
    push_cast
    omega
  have hqZ : tr.time q ≤ cutZ sp.toParams g := by
    have hsucc : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]
      push_cast
      ring
    rw [hsucc] at hjZ
    have := sp.toParams.hΔ
    linarith
  obtain ⟨ellq, hcq, heq⟩ := (SA.upTo_voteAt.mp hvq).2
  have hqH := hp.run.antitone hqZ hvz
  have hacq := (hac.upTo (hp.run.time_nonneg q)).localRun
  have hcq' := (SA.upTo_castAt).mpr ⟨le_rfl, hcq, heq⟩
  obtain ⟨⟨R', hR'frame, hR'root, _⟩, _⟩ := Compose.cast_head_fcRoot hacq hqH hcq'
  have hcq'' : (tr.upTo (tr.time q)).projAC.CallAt vote.val q ellq := by
    rw [RunTrace.upTo_projAC]
    exact hcq'.1
  have hframe := Compose.frame_of_projAC (hp.run.upTo (hp.run.time_nonneg q)) hqH hcq''
  have hR' : R' ∈ (tr.state vote.val q).fg.tree := by
    rw [hframe, RunTrace.upTo_state_of_le hm le_rfl] at hR'frame
    exact hR'frame.1
  have hR'U : R' ∈ tr.HonestBlocksAt H :=
    ⟨vote.val, q, tr.time q, hp.run.time_nonneg q, fun _ hq => hm hq.le, hqH, hR'⟩
  have hRR : R = R' := hac.localRun.coherent.1 hRU hR'U
    (hRroot.trans (by rw [hev] at hR'root; exact hR'root.symm))
  subst R'
  have hhigh := hp.high_of_anc_at ho hz0 (fun _ hq => (hm hq.le).trans hqZ)
    hvz hR' (hBD.trans hDR)
  have hqk : q ≤ k := by
    by_contra h
    exact (not_lt_of_ge hqZ) (hk.2.trans_le (hm (by omega)))
  have hrz := hp.run.upTo hz0
  have hRq : R ∈ ((tr.upTo (cutZ sp.toParams g)).state vote.val q).fg.tree := by
    rw [Trace.upTo_state tr vote.val (fun _ hq => (hm hq.le).trans hqZ)]
    exact hR'
  have hRk := Compose.tree_mono hrz.toLocalRun hvz hqk hRq
  have hσ := Store.σ_eq_of_mem (Compose.fg_reachable hrz.toLocalRun hvz q)
    (Compose.fg_reachable hrz.toLocalRun hvz k)
    (Compose.honest_blocks_coherent hrz.toLocalRun (hp.noColl.upTo _)).1
    (fun _ hC => ⟨vote.val, hvz, q, hC⟩) (fun _ hC => ⟨vote.val, hvz, k, hC⟩) hRq hRk
  rw [Trace.upTo_state tr vote.val hk.1] at hRk hσ
  rw [Trace.upTo_state tr vote.val (fun _ hq => (hm hq.le).trans hqZ)] at hσ
  have hbound := (Store.cache_invariants _ _ _ _
    (fg_reachable_at hp.run hz0 hk.1 hvz)).2.2.2.2.1 R hRk
  have hmax : (tr.state vote.val k).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun z => (tr.state z k).fg.hmax).subset ?_).bddAbove)
      ⟨vote.val, hvz, k, hk, rfl⟩
    rintro _ ⟨z, -, k', hk', rfl⟩
    obtain rfl := hk'.unique hk
    exact ⟨z, rfl⟩
  rw [← hσ] at hbound
  omega

end Consensus.Goldilocks.Healing.Growing

end
