module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

@[expose] public section

/-! # Goldilocks milestone vocabulary: service before a time, cut at the deadline

Beside `SyncAC A H U a b tr` (`Milestones/Spec/AC/Trace`), the network premise "every delivery
whose deadline is at most `b₀ + 1` is served", as the AC trace observes it: the AC counterpart of
the delivery rule `Delivers (a + Δ − 1) b₀` (`Spec/Problem/Network`). Unlike `SyncAC 0 b₀`, which
bounds send times and so owes service after `b₀` for a send at `b₀`, it bounds the receiver's
deadline. The message clause asks for service after the receiver's last restart: the processing
witness has no restart of the receiver between it and the call that reads it, which `SyncAC`
does not ask. Definitions only; the lemmas are in `Lemmas/Healing/AC/Frontier`. -/

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type}

/-- **Service before `b₀`, cut at the deadline**: every AC message an honest `x` sends or admits
is processed by every honest `y` before `y`'s deadline and since `y`'s latest restart (no restart
of `y` between the processing and the call that reads it), and every block it accepts is accepted
by every honest `y` (inside `U` above `y`'s finalized tip) before `y`'s deadline, whenever that
deadline is at most `b₀ + 1`; read at every call of `y` at or after the deadline. A restart resets
the AC's pools but not the frame, so blocks need no re-acceptance after it (under trivial frames
the tree is genesis and every block accepted so far). -/
structure SyncUntilAC (A : ACInterface P FGP) (H : Set (Fin P.n)) (U : Set A.Blk) (b₀ : Time)
    (tr : ACTrace A) : Prop where
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      tr.deadline y j (tr.time i) ≤ b₀ + 1 →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (tr.time i) ∧ ∀ r, k < r → r ≤ j → ¬ tr.RestartAt y r
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      tr.deadline y j (tr.time i) ≤ b₀ + 1 → Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)

end Consensus.Goldilocks

end
