module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen

public section

/-! # Guarded relay to an independently honest Outcome reader -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An acceptance is relayed without requiring its sender to remain honest at the read. -/
theorem accept_mem_frame (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (ha : tr.AcceptAt x q B) {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (hjb : tr.time j ≤ b)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have ht := hp.run.time_nonneg j
  have htimes : ∀ k < j, tr.time k ≤ tr.time j := fun k hk => hp.run.time_mono hk.le
  have hr := (hp.run.upTo ht).toLocalRun
  have hs : ∀ k ≤ j, (tr.upTo (tr.time j)).state y k = tr.state y k :=
    fun k hk => Trace.upTo_state tr y (fun l hl => hp.run.time_mono (by omega))
  have he := frame_of_call hp.run hy hcall
  have hF' : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B := by rwa [he] at hF
  have hFpast : ∀ k ≤ j, Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
    intro k hk
    have hmono := Healing.run_F_mono hr hy hk
    rw [hs k hk, hs j le_rfl] at hmono
    exact (hmono.mono (RunTrace.honestBlocks_upTo_subset hp.run.time_mono ht)).trans hF'
  have hlift : ∀ k < j, tr.AcceptAt y k B → B ∈ (tr.state y j).fg.tree := by
    intro k hkj hak
    have hak' : (tr.upTo (tr.time j)).AcceptAt y k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨htimes k hkj, hak⟩
    have hmem := Compose.tree_mono hr hy (show k + 1 ≤ j by omega)
      (Healing.accept_mem' (hp.run.upTo ht) hy hak')
    rwa [hs j le_rfl] at hmem
  have hmem : B ∈ (tr.state y j).fg.tree := by
    by_cases hnew : g ≤ tr.time q
    · have hdl := Compose.deadline_le_of_restarts (tr := tr)
        (fun k hkj hk => restart_le_at hp (hp.run.antitone (hp.run.time_mono hkj) hy) hk
          ((hp.run.time_mono hkj).trans hjb)) (max (tr.time q) g) sp.Δ
      have hdl' : tr.deadline y j (max (tr.time q) g) sp.Δ ≤ tr.time j := by
        apply hdl.trans
        rw [max_eq_left hnew, ← max_add_add_right]
        exact max_le hq hjoin
      obtain ⟨k, hkj, hak, hkt⟩ := hp.sync.relay x q B hx ha hnew y j hy
        ⟨.ac ell, Compose.projAC_callAt.mp hcall⟩ hdl' hF'
      have hklt : k < j := by
        by_contra hn
        obtain rfl : k = j := by omega
        exact (not_lt_of_ge hdl') hkt
      exact hlift k hklt hak
    · obtain ⟨j₀, hj₀, hj₀j⟩ := Healing.exists_firstCutFrom_le hg
      obtain ⟨k, hkj₀, hak⟩ := hc x q B hx ha
        (lt_of_lt_of_le (not_le.mp hnew) (le_max_left _ _)) y j₀
        (hp.run.antitone hg hy) hj₀ (hFpast j₀ hj₀j)
      exact hlift k (by omega) hak
  rw [he]
  exact ⟨hmem, store_anc_of_honest_anc_at hp.run hp.noColl ht htimes hy hF' hmem⟩

end Consensus.Goldilocks.Healing.Growing.Outcome

end
