module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix

public section

/-! # A left replay entry has an origin honest at its own write

Count signers at the reader's observation. Those signers were honest at delivery
and at signing, even if other historical holders have since been compromised.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g : Time}

/-- A high entry left by a held chain was named by an earlier honest signer.
The source origin's honesty is at its write, not the reader's later observation. -/
theorem left_entry_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hq : (H t)ᶜ.ncard < sp.toParams.fg.q)
    {E C : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H t,
      ∃ d < k, tr.SignAt v d att ∧ att.T = E.root ∧
        ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
          Anc (tr.HonestBlocksAt H) E O := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨W, hW, att, ha, haT, haH⟩ := Healing.honest_att_of_left
    (fg_reachable_at hrun ht hle hy) hq hET hEC hlt
  have he := Trace.upTo_state tr y hle
  have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i att
    (hrun.antitone (hle i hik) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hle i hik) haH)
  have hdk : d < k := hdi.trans hik
  have hv := hrun.antitone (hle d hdk) haH
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
    (hrun.upTo (hrun.time_nonneg d)) hv hs'
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hE' hE'h
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  have hEq : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
  subst E'
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
  obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
    high_row_source_at hrun hnc hv hs (by rw [← hE'h, hσ]; exact hEh)
  have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
      fun q hq => hrun.time_mono hq.le, ho.1, h⟩
  have hEq₀ : E₀ = E := hU.1 (hsub₀ hE₀) (hsub hE) (hE₀r.trans haT)
  subst E₀
  exact ⟨W, hW, att, ha, att.val, haH, d, hdk, hs, haT, r, hrd, l, O, ho,
    hE₀O.mono hsub₀⟩

end Consensus.Goldilocks.Healing.Growing.Outcome

end
