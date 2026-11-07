module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Fast-lock witnesses at their historical cuts

The writer's prefix proves the release and acceptance facts. Transport keeps the
honesty of the writer at those cuts, without assuming survival to another reader.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Vote)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {T : SA.SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}

/-- Counted votes were released and their heads accepted while the writer was honest. -/
theorem fastLock_writer_at
    (hr : Goldilocks.Growing.ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (T.time i))
    {D : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt T x i s D CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, x ∈ H (T.time k) ∧ T.SendOrAdmit x k v ∧
        sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ B ∈ U, B.root = v.head ∧ Anc U D B ∧
        (B.root = sp.genesisRoot ∨
          ∃ k, x ∈ H (T.time k) ∧ T.AcceptAt x k B ∧
            T.time k < sp.ts s + 2 * sp.Δ) := by
  have hp := hr.upTo (hr.time_nonneg i)
  have hf := (SA.upTo_fastLockAt hr.time_mono).mpr ⟨le_rfl, hfl⟩
  intro v hv
  obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, B, hB, hBr, hDB, hacc⟩ :=
    Healing.fastLock_writer hp hx hf v hv
  obtain ⟨hki, hsend⟩ := (ACTrace.upTo_sendOrAdmit hr.time_mono).mp hsend
  refine ⟨hvs, ⟨k, hr.antitone hki hx, hsend, hk1, hk2⟩, B, hB, hBr, hDB, ?_⟩
  rcases hacc with hg | ⟨q, haq, hqt⟩
  · exact Or.inl hg
  · obtain ⟨hqi, haq⟩ := ACTrace.upTo_acceptAt.mp haq
    exact Or.inr ⟨q, hr.antitone hqi hx, haq, hqt⟩

end Consensus.Goldilocks.Healing.Growing

end
