module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.AC

public section

/-! # Finite AC healing premises under growing faults

The growing forms of `SyncACWindowBefore`, `CatchACWindowBefore` (`Lemmas/AC/Trace`) and
`SA.HealthyBaseUpTo` (`Lemmas/Healing/AC/Setting`): every field is the static one, with each
sender honest at its event cut, each receiver honest at its own call, and the fault bound on
`[0, b]`. Timing, deadlines and cutoffs are unchanged. -/

namespace Consensus.Goldilocks.Growing

/-- AC service from an inclusive source-time lower bound through a recipient-deadline cutoff,
with each node honest at its own cut. -/
structure SyncACWindowBefore {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (H : Time → Set (Fin P.n)) (U : Set A.Blk) (a b : Time) (ac : ACTrace A) : Prop where
  /-- Message processing keeps the source lower bound and strict service deadline. -/
  message : ∀ x i m, x ∈ H (ac.time i) → ac.SendOrAdmit x i m → a ≤ ac.time i →
    ∀ y j ℓ, y ∈ H (ac.time j) → ac.CallAt y j ℓ → ac.deadline y j (ac.time i) ≤ b →
      ac.deadline y j (ac.time i) ≤ ac.time j →
      ∃ k ≤ j, ac.time i ≤ ac.time k ∧ ac.ProcessAt y k m ∧
        ac.time k < ac.deadline y k (ac.time i)
  /-- Acceptance relay retains the receiver's finalized-ancestor condition. -/
  relay : ∀ x i B, x ∈ H (ac.time i) → ac.AcceptAt x i B → a ≤ ac.time i →
    ∀ y j ℓ, y ∈ H (ac.time j) → ac.CallAt y j ℓ → ac.deadline y j (ac.time i) ≤ b →
      ac.deadline y j (ac.time i) ≤ ac.time j → Anc U ℓ.frame.F B →
      ∃ k ≤ j, ac.AcceptAt y k B ∧ ac.time k < ac.deadline y k (ac.time i)

/-- Old acceptances of nodes honest at their cuts are caught up strictly before `a + κ`, as
observed at calls of nodes honest at them from that endpoint through `b`. -/
structure CatchACWindowBefore {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (ac : ACTrace A) (H : Time → Set (Fin P.n)) (U : Set A.Blk) (a κ b : Time) : Prop where
  /-- The receiver must extend its finalized block; the returned acceptance is an actual cut. -/
  relay : ∀ x i B, x ∈ H (ac.time i) → ac.AcceptAt x i B → ac.time i < a →
    ∀ y j ℓ, y ∈ H (ac.time j) → ac.CallAt y j ℓ → a + κ ≤ ac.time j → ac.time j ≤ b →
      Anc U ℓ.frame.F B → ∃ k ≤ j, ac.AcceptAt y k B ∧ ac.time k < a + κ

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **The healthy AC premises through `b`** under growing faults. -/
structure HealthyBaseUpTo (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (proposer : Nat → Fin sp.n) (g b : Time) : Prop where
  run : ACRun proposer tr H U
  driven : Driven proposer tr H
  sync : Consensus.Goldilocks.Growing.SyncACWindowBefore H U (gbar g) b tr
  catchUp : Consensus.Goldilocks.Growing.CatchACWindowBefore tr H U (gbar g) (2 * sp.Δ) b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1

end Consensus.Goldilocks.SA.Growing

end
