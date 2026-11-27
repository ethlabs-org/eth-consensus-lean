module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Blocks of height `≥ H_z + 2` are held only from the reset on

Under growing faults, a node honest at `t ≥ c_z`, read at a state whose earlier cuts are at times
`≤ t`, with fewer than a third of the validators compromised by `t`, that holds a block of state
height `≥ H_z + 2` reads at or after the reset `a` (`reset_le_of_held_high_at`). The block's chain
carries a row of height `H_z + 1` by a signer honest at `t` (`Store.exists_honest_att_of_lt`, the
growing `honest_row_of_height`); the row was signed while the signer was honest, at a cut no later
than its block's acceptance (`att_unforgeable`, the growing `signed_before_attest`), hence at or
after `a` (`IsReset`). A chain of height exactly `H_z + 1` carries rows of height `H_z` only, which
may be signed in `(c_z, a)`: the bound fails there. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g a : Time}

/-- **A block of height `≥ H_z + 2` is held only from the reset on** (growing faults): see the
module docstring. -/
theorem reset_le_of_held_high_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hR : IsReset tr H g a)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htZ : cutZ sp.toParams g ≤ t) (hf : 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hXh : HZ tr H g + 2 ≤ ((tr.state y k).fg.σ X.root).h) :
    a ≤ t := by
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  have hreach := fg_reachable_at hrun ht hle hy
  obtain ⟨Y, hYX, att, hatt, hattH, hatth⟩ :=
    Store.exists_honest_att_of_lt hreach hq hX (HZ tr H g + 1) (by clear * -; omega)
      (by clear * - hXh; omega)
  have hY : Y ∈ (tr.state y k).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  have hY' : Y ∈ ((tr.upTo t).state y k).fg.tree := by rwa [Trace.upTo_state tr y hle]
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hY' with rfl | ⟨i', hi', hA⟩
  · cases hatt
  obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
    (hrun.antitone (hle i' hi') hy) (Or.inr ⟨Y, ⟨true, ((RunTrace.upTo_acceptAt tr).mp hA).2⟩,
      hatt⟩) (hrun.antitone (hle i' hi') hattH)
  have hdt : tr.time d ≤ t := (hrun.time_mono hdi.le).trans (hle i' hi')
  have ha := hR.2 att.val d att (hrun.antitone (max_le htZ hdt) hattH) hs hatth
  linarith

end Consensus.Goldilocks.Healing.Growing

end
