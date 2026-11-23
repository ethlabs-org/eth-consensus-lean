module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Historical raw-writer sources

The counted head is obtained on the writer's own prefix. Its release and
acceptance obligations survive the writer's later compromise.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Vote)

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Time → Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
  {T : AC.GTrace sp FGP ro}

/-- A raw writer supplies a counted head, with honesty charged at its actual acceptance. -/
theorem raw_writer_relay_source_at (hcommittee : 0 < sp.committeeSize)
    {ini} (hr : Consensus.Goldilocks.Growing.ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (T.time i))
    {B C : AC.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : AC.ResultAt T x i s C CV ∨ AC.FastLockAt T x i s C CV)
    (hBC : Anc U B C) :
    ∃ v ∈ CV, ∃ D ∈ U, D.root = v.head ∧ Anc U B D ∧
      (D.root = sp.genesisRoot ∨
        ∃ q, x ∈ H (T.time q) ∧ T.AcceptAt x q D ∧ T.time q < sp.ts s + 2 * sp.Δ) := by
  have hm := hr.time_mono
  have hw : AC.ResultAt (T.upTo (T.time i)) x i s C CV ∨
      AC.FastLockAt (T.upTo (T.time i)) x i s C CV :=
    hwriter.elim (fun h => Or.inl ((AC.upTo_resultAt hm).mpr ⟨le_rfl, h⟩))
      (fun h => Or.inr ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, h⟩))
  obtain ⟨v, hv, D, hD, hDr, hBD, hgen | ⟨q, hq, hqt⟩⟩ :=
    Healing.raw_writer_relay_source hcommittee (hr.upTo (hr.time_nonneg i)) hini hx hw hBC
  · exact ⟨v, hv, D, hD, hDr, hBD, Or.inl hgen⟩
  · obtain ⟨hqi, hq⟩ := (ACTrace.upTo_acceptAt).mp hq
    exact ⟨v, hv, D, hD, hDr, hBD, Or.inr ⟨q, hr.antitone hqi hx, hq, hqt⟩⟩

end Consensus.Goldilocks.Healing.Growing

end
