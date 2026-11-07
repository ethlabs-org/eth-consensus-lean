module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Historical raw-writer sources

The counted head is obtained on the writer's own prefix. Its release and
acceptance obligations survive the writer's later compromise.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Vote)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Time → Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}
  {T : SA.SATrace sp FGP ro}

/-- A raw writer supplies a counted head, with honesty charged at its actual acceptance. -/
theorem raw_writer_relay_source_at
    (hr : Consensus.Goldilocks.Growing.ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (T.time i))
    {B C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : SA.ResultAt T x i s C CV ∨ SA.FastLockAt T x i s C CV)
    (hBC : Anc U B C) :
    ∃ v ∈ CV, ∃ D ∈ U, D.root = v.head ∧ Anc U B D ∧
      (D.root = sp.genesisRoot ∨
        ∃ q, x ∈ H (T.time q) ∧ T.AcceptAt x q D ∧ T.time q < sp.ts s + 2 * sp.Δ) := by
  have hm := hr.time_mono
  have hw : SA.ResultAt (T.upTo (T.time i)) x i s C CV ∨
      SA.FastLockAt (T.upTo (T.time i)) x i s C CV :=
    hwriter.elim (fun h => Or.inl ((SA.upTo_resultAt hm).mpr ⟨le_rfl, h⟩))
      (fun h => Or.inr ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, h⟩))
  obtain ⟨v, hv, D, hD, hDr, hBD, hgen | ⟨q, hq, hqt⟩⟩ :=
    Healing.raw_writer_relay_source (hr.upTo (hr.time_nonneg i)) hx hw hBC
  · exact ⟨v, hv, D, hD, hDr, hBD, Or.inl hgen⟩
  · obtain ⟨hqi, hq⟩ := (ACTrace.upTo_acceptAt).mp hq
    exact ⟨v, hv, D, hD, hDr, hBD, Or.inr ⟨q, hr.antitone hqi hx, hq, hqt⟩⟩

end Consensus.Goldilocks.Healing.Growing

end
