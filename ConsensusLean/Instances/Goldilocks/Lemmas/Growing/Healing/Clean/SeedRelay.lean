module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Guarded relay from a historical honest acceptance to a later honest call

Source and recipient are read on separate local prefixes. The reset service transports
post-GST acceptances; the growing Catch contract transports acceptances before the GST.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- An old honest acceptance reaches a bounded honest call above its finalization guard. -/
theorem reset_accept_frame_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {x y : Fin sp.n} {q j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time q)) (ha : tr.projAC.AcceptAt x q B)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (hjb : tr.time j ≤ b)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hm := hp.run.time_mono
  have hj0 := hp.run.time_nonneg j
  have hrj := hp.run.upTo hj0
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hR := (hac.upTo hj0).localRun
  have hcall' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcall)
  by_cases hnew : AC.gbar g ≤ tr.time q
  · have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k hkj hk => hp.restart_le_before_at (hp.run.antitone (hm hkj) hy)
        (Compose.projAC_restartAt.mp hk) ((hm hkj).trans hjb)) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      apply hd.trans
      change max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ ≤ tr.time j
      rw [← max_add_add_right]
      exact max_le hq hjoin
    obtain ⟨k, hkj, hak, _⟩ := hp.frame_relay_at hx ha ((AC.le_gbar g).trans hnew)
      hy hcall hdl hF
    exact AC.mem_tree_of_acceptAt sp hR hy
      ((ACTrace.upTo_acceptAt).mpr ⟨hm hkj, hak⟩) hkj hcall' hF
  · obtain ⟨k, hkj, hak, _⟩ := hp.run.toLocalRun.acCatchAt hp.catchUp hx ha (not_le.mp hnew)
      hy hcall hg hF
    exact AC.mem_tree_of_acceptAt sp hR hy
      ((ACTrace.upTo_acceptAt).mpr ⟨hm hkj, hak⟩) hkj hcall' hF

/-- A historically held frame block reaches a bounded honest recipient above its guard. -/
theorem reset_frame_relay_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {x y : Fin sp.n} {q j : Nat} {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hjb : tr.time j ≤ b) (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hrq := (hac.upTo (hp.run.time_nonneg q)).localRun
  have hrj := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcx' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcx)
  have hcy' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcy)
  rcases Compose.frame_anc_accepted hrq hx q ellx hcx' B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_call sp hrj hy j elly hcy'
    obtain rfl : B = G := hac.localRun.coherent.1 ((AC.frameIn_of_callAt hrq hx hcx').2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hrj hy hcy').1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt).mp ha
    exact hp.reset_accept_frame_at (hp.run.antitone hkq hx) ha hy hcy hjb hg hjoin
      (by change tr.time k ≤ tr.time q at hkq; linarith) hF

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
