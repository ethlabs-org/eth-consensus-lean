module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model

public section

/-! # Acceptance of a received forwarding chain under growing faults

The growing-fault forms of `received_forward_accepted_before`, without a constant-fault premise.
The recipient is honest at a time `t₀` no earlier than every cut before its reading cut `j` (it
may be compromised by the time of cut `j` itself); compatibility is read inside the blocks held
while honest. The signer is honest either at the delivery (`received_forward_accepted_before_at`)
or at its stamp, with the envelope its genuine release there
(`received_forward_accepted_before_of_released_at`): the wrappers nested in a genuine release
are genuine, even when the signer is compromised before the delivery.

OPEN: both are stated, not yet proved. They need the growing form of the parent-first receipt
traversal `forward_receipt_held`, with the signer's trees held while honest through its stamps
and the recipient's through `t₀`. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A receipt before a strict deadline, of a forwarding envelope whose signer is honest at the
delivery, gives an acceptance before that deadline when the recipient's finalized tip at a later
reading cut is below the forwarded block. -/
theorem received_forward_accepted_before_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : v ∉ rho.faultyAt t₀)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.F B)
    (hu : u < deadline) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTraceAt S rho hn).time k ≤ u ∧ (simTraceAt S rho hn).time k < deadline := by
  sorry

/-- The same acceptance when the signer is honest only at its stamp `t`, at which the envelope is
its genuine release. -/
theorem received_forward_accepted_before_of_released_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : v ∉ rho.faultyAt t₀)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt t)
    (hrel : rho.releases (rho.key x) o t)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.F B)
    (hu : u < deadline) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTraceAt S rho hn).time k ≤ u ∧ (simTraceAt S rho hn).time k < deadline := by
  sorry

end Consensus.Goldilocks.Simulation

end
