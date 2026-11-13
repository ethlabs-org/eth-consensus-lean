module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: raw-target heldness at an arbitrary call

The call-time form of `raw_writer_voterBlockTree_window_before` (`Retention/Relay`), for the H.3
invariant after the reset. A block below the result or
fast-lock selection of an honest write of a clean label `s` is held by every honest AC call from
`t_{s+1}` on whose finalized block is below it: the writer's counted head is genesis or was
accepted before `t_s + 2Δ`, and reaches the call by Catch (accepted before `ḡ`) or by the GST
relay (accepted from `ḡ` on, deadline before `t_{s+1}`), both through `reset_accept_frame`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **Heldness of a raw target at an honest AC call** from `t_{s+1}` on, when the call's
finalized block is below the target. -/
theorem raw_target_held_at_call (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s k : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y k ell)
    (ht : sp.ts (s + 1 : Nat) ≤ tr.time k)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcall
  obtain ⟨-, -, D, hD, -, hBD, hg | ⟨q, hq, hqt⟩⟩ := raw_writer_relay_source
    (by rw [hp.stock]; exact sp.toParams.hn) hr hx hwriter hBC
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy _ _ hcall
    obtain rfl : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    have hGt : D ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hF.trans hBD) with
        he | ⟨c, _, hpar⟩
      · exact he ▸ hΦ.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hr.coherent hΦ hΦU hGt hBD hF
  · -- `ḡ + 8Δ < c_z ≤ t_l ≤ t_s`, with `l ≤ slot(a) < s` the label of the reset's seed
    obtain ⟨_, _, l, _, ho, -, hl⟩ := (hp.toUpTo tr H (le_refl a)).reset_seed
    have hzl := cutZ_le_ts_of_highOrigin hp ho
    have hz := lt_cutZ sp g
    rw [cleanLabel_eq] at hs
    have hls : sp.ts l ≤ sp.ts s := (SA.ts_le_iff sp).mpr (by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hqt' : tr.time q < sp.ts s + 2 * sp.Δ := hqt
    have hDt := reset_accept_frame hp hc hx hy hq hcall (by linarith)
      (by linarith) (hF.trans hBD)
    exact SA.frame_mem_of_between sp hr.coherent hΦ hΦU hDt hBD hF

end Consensus.Goldilocks.Healing

end
