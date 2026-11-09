module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks Healing: justifications and contests stay

Honest stores keep their blocks and their states (`held_mono`), and ancestry of a held block does
not change as the store grows (`Store.anc_transfer`), so a justification or a contest held at an
honest node at one cut is held at every later cut (HR.2 (b)). Kept apart from `Healing/Phase` so
that the growing-fault phases, which apply these on a retained run, need not widen that module's
interface. -/

namespace Consensus.Goldilocks.Healing

open Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- A justification held at an honest node stays held. -/
theorem justifiedAt_mono (hr : FGLocalRun acp₀ H U tr) {i j : Nat} (hij : i ≤ j)
    {h : Nat} {J : NodeBlock P ACP} (hJ : JustifiedAt tr H i h J) : JustifiedAt tr H j h J := by
  obtain ⟨y, hy, hJ, B, hB, hh, hJr⟩ := hJ
  obtain ⟨hB', hσ⟩ := held_mono hr hy hij hB
  exact ⟨y, hy, (held_mono hr hy hij hJ).1, B, hB', by rw [hσ]; exact hh, by rw [hσ]; exact hJr⟩

/-- A contest held at an honest node stays held. -/
theorem contestAt_mono (hr : FGLocalRun acp₀ H U tr) {i j : Nat} (hij : i ≤ j)
    {m : Nat} {J : NodeBlock P ACP} (hc : ContestAt tr H i m J) : ContestAt tr H j m J := by
  obtain ⟨y, hy, B, hB, hh, hn⟩ := hc
  obtain ⟨hB', hσ⟩ := held_mono hr hy hij hB
  exact ⟨y, hy, B, hB', by rw [hσ]; exact hh, fun ha => hn (Store.anc_transfer hr hy hy ha hB)⟩

end Consensus.Goldilocks.Healing

end
