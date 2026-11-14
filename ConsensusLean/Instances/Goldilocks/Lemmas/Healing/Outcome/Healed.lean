module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service

public section

/-! # Goldilocks Healing: the record half of the Healed bundle

The vocabulary only. `HighEntry … h Z`: `Z` is an entry of the high chain at height `h` (a block
below a high origin, held by an honest node whose state has height `h` and entry `Z`).
`HealedRecords … h₀ E` collects, for the entries `E h`, C2*⁺ (i) (every honest attestation at a
height `h ≥ h₀` names `E h`), C2*⁺ (ii) (every honest `Λ.lock[h]` with `h ≥ h₀` is `⊥` or `E h`)
and R0 (`permits(Λ, h₀, E h₀)` at every cut), with RH (`H_z + 1 ≤ h₀`). The paper derives
C2*⁺ (i), (ii) and R0 from the clean-height premise CH. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- `Z` is an entry of the high chain at height `h`: it is below the block of a high origin, an
honest node holds it, and its state has height `h` and entry `Z`. -/
structure HighEntry (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (h : Nat)
    (Z : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  origin : ∃ x i j B, HighOrigin tr H g x i j B ∧ Anc (tr.HonestBlocks H) Z B
  held : ∃ z ∈ H, ∃ m, Z ∈ (tr.state z m).fg.tree ∧ ((tr.state z m).fg.σ Z.root).h = h ∧
    ((tr.state z m).fg.σ Z.root).Th = Z.root

/-- **The record half of the Healed bundle** from the height `h₀` on, for the entries `E h` of
the chain: RH, C2*⁺ (i) attestations, C2*⁺ (ii) locks, and R0 at `h₀`. -/
structure HealedRecords (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (h₀ : Nat)
    (E : Nat → SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- RH: `h₀` is above the reset height. -/
  rh : HZ tr H g + 1 ≤ h₀
  /-- C2*⁺ (i): every honest attestation at a height `≥ h₀` names the entry at its height. -/
  fgAtts : ∀ v ∈ H, ∀ d att, tr.SignAt v d att → h₀ ≤ att.h → att.T = (E att.h).root
  /-- C2*⁺ (ii): every honest lock at a height `≥ h₀` is `⊥` or the entry at that height. -/
  locks : ∀ y ∈ H, ∀ i h, h₀ ≤ h →
    (tr.state y i).record.lock h = none ∨ (tr.state y i).record.lock h = some (E h).root
  /-- R0: every honest record permits the entry at `h₀` at every cut. -/
  r0 : ∀ y ∈ H, ∀ i, (tr.state y i).record.permits h₀ (E h₀).root

end Consensus.Goldilocks.Healing

end
