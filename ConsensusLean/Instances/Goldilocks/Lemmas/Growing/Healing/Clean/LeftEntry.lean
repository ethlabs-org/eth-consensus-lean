module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover

public section

/-! # Left-entry provenance under the reset premises

The growing form of `Healing/Retention/Prefix`'s `left_entry_origin`: the reader is honest at an
observation `t ≤ b`, the premises bound the faults below the replay quorum at the later of `t`
and `c_z` (the snapshot is observed by `b`), and the signer's high origin is honest at its own
write and at `c_z`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- The faults at the later of `t ≤ b` and `c_z` are below the replay quorum. -/
private theorem quorum_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {t : Time} (ht : 0 ≤ t)
    (htb : t ≤ b) : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q := by
  obtain ⟨j, hj, hjb⟩ := hp.snapshot
  have h3 := hp.faults _ (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) htb)
  have hn := sp.toParams.hn
  have he : sp.n = sp.toParams.n := rfl
  change (H (max (cutZ sp.toParams g) t))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
  omega

/-- **Left-entry provenance, inside the deep quarantine** (`hpre`): a high entry left by a reader
honest at `t ≤ b` is the target of a held attestation whose signer is honest at `t` and wrote a
high origin above the entry before signing. -/
theorem ResetPremisesUpTo.left_entry_origin_of_quarantine_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocksAt H) E O := by
  have hq := quorum_at hp ht htb
  obtain ⟨W, hW, att, ha, v, hv, d, hd, hs, hT, rest⟩ :=
    Outcome.left_entry_origin_at hp.run hp.noColl ht hle hy hq hE hET hEh hEC hlt
      (hp.snapshot.imp fun _ h => h.1) fun D hD => htb.trans (hpre D hD)
  exact ⟨W, hW, att, ha, v, d, hv, hd, hs, hT, rest⟩

/-- **Left-entry provenance, with the cover**: a high entry left by a reader honest at
`t ≤ b` is the target of a held attestation whose signer is honest at `t`. Inside the deep
quarantine the signer wrote a high origin above the entry before signing; otherwise the bundle
carries the high-source cover, the signer is honest at `t` and at `c_z`, and the entry is covered
up to the slot of `t` by a member written before the cut `k`. -/
theorem ResetPremisesUpTo.left_entry_origin_or_covered_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ((∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O) ∨
          (v ∈ H (max (cutZ sp.toParams g) t) ∧ CoveredBefore tr H g a b (sp.slot t) k E)) := by
  have hq := quorum_at hp ht htb
  have hsnap := hp.snapshot.imp fun _ h => h.1
  rcases hp.quarantine_or_cover_at htb with hpre | hc
  · obtain ⟨W, hW, att, ha, v, hv, d, hd, hs, hT, rest⟩ :=
      Outcome.left_entry_origin_at hp.run hp.noColl ht hle hy hq hE hET hEh hEC hlt hsnap
        hpre
    exact ⟨W, hW, att, ha, v, d, hv, hd, hs, hT, Or.inl rest⟩
  · obtain ⟨W, hW, att, ha, v, hv, d, hd, hs, hT, hcov⟩ :=
      Outcome.left_entry_covered_before_at hp.run hp.noColl ht hle hy hq hE hET hEh hEC hlt
        hsnap hc htb
    exact ⟨W, hW, att, ha, v, d, hp.run.antitone (le_max_right _ _) hv, hd, hs, hT,
      Or.inr ⟨hv, hcov⟩⟩

/-- `left_entry_origin_or_covered_before_at`, with the cover read up to the label only. -/
theorem ResetPremisesUpTo.left_entry_origin_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ((∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O) ∨
          (v ∈ H (max (cutZ sp.toParams g) t) ∧ CoveredUpTo tr H g a b (sp.slot t) E)) :=
  let ⟨W, hW, att, ha, v, d, hv, hd, hs, hT, h⟩ :=
    hp.left_entry_origin_or_covered_before_at ht hle hy htb hE hET hEh hEC hlt
  ⟨W, hW, att, ha, v, d, hv, hd, hs, hT, h.imp id fun h => ⟨h.1, h.2.coveredUpTo⟩⟩

end Consensus.Goldilocks.Healing.Growing

end
