module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Guarded relay from a historical honest acceptance to a later honest call

Source and recipient are read on separate local prefixes. The reset service transports
post-GST acceptances; the growing Catch contract transports acceptances before the GST.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- An old honest acceptance reaches a bounded honest call above its finalization guard. -/
theorem reset_accept_frame_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time q)) (ha : tr.projAC.AcceptAt x q B)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (hjb : tr.time j ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hm := hp.run.time_mono
  have hj0 := hp.run.time_nonneg j
  have hrj := hp.run.upTo hj0
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hR := (hac.upTo hj0).localRun
  have hcall' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcall)
  by_cases hnew : SA.gbar g ≤ tr.time q
  · have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k hkj hk => hp.restart_le_before_at (hp.run.antitone (hm hkj) hy)
        (Compose.projAC_restartAt.mp hk) ((hm hkj).trans hjb)) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      apply hd.trans
      change max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) + sp.Δ ≤ tr.time j
      rw [← max_add_add_right]
      exact max_le hq hjoin
    obtain ⟨k, hkj, hak, _⟩ := hp.frame_relay_at hx ha ((SA.le_gbar g).trans hnew)
      hy hcall hdl hF
    exact SA.mem_tree_of_acceptAt sp hR hy
      ((ACTrace.upTo_acceptAt).mpr ⟨hm hkj, hak⟩) hkj hcall' hF
  · classical
    obtain ⟨ellx, hcx, hb⟩ := ha
    have hrq := hp.run.upTo (hp.run.time_nonneg q)
    have hcx' : (tr.upTo (tr.time q)).CallAt x q (.ac ellx) :=
      (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hcx⟩
    obtain ⟨q', rfl, hacc, hqt⟩ := Compose.acBlock_prev hrq.toLocalRun hx hcx' hb
    have hacc₀ := (Trace.upTo_callAt tr).mp hacc |>.2
    have hqt' : tr.time q' = tr.time (q' + 1) := hqt
    have hex : ∃ k, SA.gbar g + 2 * sp.Δ ≤ tr.time k := ⟨j, hg⟩
    have hfirst : tr.FirstCutFrom (Nat.find hex) (SA.gbar g + 2 * sp.Δ) :=
      ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
    have hfirstj : Nat.find hex ≤ j := Nat.find_min' hex hg
    have hfr : ell.frame.F = (tr.state y j).fg.F := by
      have h := Compose.frame_of_projAC hrj hy (show (tr.upTo (tr.time j)).projAC.CallAt y j ell
        from by rw [RunTrace.upTo_projAC]; exact hcall')
      rw [RunTrace.upTo_state_of_le hm le_rfl] at h
      rw [h]
      rfl
    have hmono : Anc (tr.HonestBlocksAt H)
        (tr.state y (Nat.find hex)).fg.F (tr.state y j).fg.F := by
      have h := Healing.run_F_mono hrj.toLocalRun hy hfirstj
      rw [RunTrace.upTo_state_of_le hm (hm hfirstj), RunTrace.upTo_state_of_le hm le_rfl] at h
      exact h.mono (RunTrace.honestBlocks_upTo_subset hm hj0)
    obtain ⟨k, hk, hak⟩ := hc x q' B (hqt' ▸ hx) hacc₀
      (by rw [hqt']; exact not_le.mp hnew) y _ (hp.run.antitone hg hy) hfirst
      (hmono.trans (hfr ▸ hF))
    have hkj : k < j := lt_of_lt_of_le hk hfirstj
    have hktj := hm hkj.le
    have hak' := (Trace.upTo_callAt tr).mpr (And.intro hktj hak)
    obtain ⟨ellk, hck, hbk, ht⟩ := Compose.accept_next hrj.toLocalRun hy hak'
    have hakAC : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y (k + 1) B := by
      rw [← RunTrace.upTo_projAC]
      exact ⟨ellk, Compose.projAC_callAt.mpr hck, hbk⟩
    exact SA.mem_tree_of_acceptAt sp hR hy hakAC (by omega) hcall' hF

/-- A historically held frame block reaches a bounded honest recipient above its guard. -/
theorem reset_frame_relay_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hjb : tr.time j ≤ b) (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hrq := (hac.upTo (hp.run.time_nonneg q)).localRun
  have hrj := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcx' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcx)
  have hcy' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcy)
  rcases Compose.frame_anc_accepted hrq hx q ellx hcx' B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hrj hy j elly hcy'
    obtain rfl : B = G := hac.localRun.coherent.1 ((SA.frameIn_of_callAt hrq hx hcx').2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hrj hy hcy').1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt).mp ha
    exact hp.reset_accept_frame_at hc (hp.run.antitone hkq hx) ha hy hcy hjb hg hjoin
      (by change tr.time k ≤ tr.time q at hkq; linarith) hF

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
