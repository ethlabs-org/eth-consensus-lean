module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry

public section

/-! # Left-entry provenance under the reset premises

The growing form of `Healing/Retention/Prefix`'s `left_entry_origin`: the reader is honest at an
observation `t ≤ b`, where the premises bound the faults below the replay quorum, and the
signer's high origin is honest at its own write. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **Left-entry provenance**: a high entry left by a reader honest at `t ≤ b` is the target of
a held attestation whose signer is honest at `t` and wrote a high origin above the entry before
signing. -/
theorem left_entry_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocksAt H) E O := by
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults t ht htb
    have hn := sp.toParams.hn
    have he : sp.n = sp.toParams.n := rfl
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  obtain ⟨W, hW, att, ha, v, hv, d, hd, hs, hT, rest⟩ :=
    Outcome.left_entry_origin_at hp.run hp.noColl ht hle hy hq hE hET hEh hEC hlt
  exact ⟨W, hW, att, ha, v, d, hv, hd, hs, hT, rest⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
