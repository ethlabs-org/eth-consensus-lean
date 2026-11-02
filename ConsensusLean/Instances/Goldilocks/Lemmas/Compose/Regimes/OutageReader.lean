module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Outage reader: receiver-scoped AC service after GST

`ReceiverServiceAfter` is the strict AC service that one receiver gets after GST `g`. The
deadline base is max(source time, `g`), so a pre-GST source is served from `g`. -/

namespace Consensus.Goldilocks.Compose

/-- Receiver-scoped strict AC service after GST `g`, for one receiver `y`. -/
structure ReceiverServiceAfter {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (H : Set (Fin P.n)) (U : Set A.Blk) (g : Time) (y : Fin P.n) (ac : ACTrace A) : Prop where
  /-- Message processing before the effective deadline, not before the source time. -/
  message : ∀ x ∈ H, ∀ i m, ac.SendOrAdmit x i m → ∀ j ℓ, ac.CallAt y j ℓ →
    ac.deadline y j (max (ac.time i) g) ≤ ac.time j →
    ∃ k ≤ j, ac.time i ≤ ac.time k ∧ ac.ProcessAt y k m ∧
      ac.time k < ac.deadline y k (max (ac.time i) g)
  /-- Acceptance relay under the receiver's finalized-ancestor condition. -/
  relay : ∀ x ∈ H, ∀ i B, ac.AcceptAt x i B → ∀ j ℓ, ac.CallAt y j ℓ →
    ac.deadline y j (max (ac.time i) g) ≤ ac.time j → Anc U ℓ.frame.F B →
    ∃ k ≤ j, ac.AcceptAt y k B ∧ ac.time k < ac.deadline y k (max (ac.time i) g)

end Consensus.Goldilocks.Compose
