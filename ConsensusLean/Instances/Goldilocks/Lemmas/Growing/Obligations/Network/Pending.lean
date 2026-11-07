module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC

public section

/-! # Pending simulation interface of the growing network transport

Statements the growing network transport consumes whose home modules are not on this branch yet,
under their agreed names, so that the transport proofs compose against the final interface:

* the canonical growing trace simulates the engine (`simTraceAt_simulates`), hence is a growing
  run (`simTraceAt_goldilocksRun`), and collision freedom transports to it
  (`noCollRun_simTraceAt`), home `Lemmas/Growing/Simulation`;
* a released attestation is a signing cut of the releasing tick (`att_released_inv_at`), home
  `Lemmas/Growing/Simulation/Attestations`;
* the forwarding facts with honesty at the time each law reads it (`received_forward_stamp_le_at`,
  `received_forward_accepted_before_at`, `received_forward_accepted_before_of_released_at`,
  `held_voteForward_source_or_process_at`,
  `tick_proposal_acceptance_queued_at`) and the acceptance-forwarding contract
  `ForwardAtAcceptanceAt`, home `Lemmas/Growing/Simulation/Forward`;
* the healing targets of the network suppliers, `Healing.Growing.Pending.CatchRun` and
  `Healing.Growing.Pending.ResetService` (in a namespace of their own, as copies of the agreed
  definitions of `Milestones/Statements/Healing/Growing/Run` and
  `Lemmas/Growing/Healing/Retention/Defs`).

Each theorem here is an open `sorry`, and each definition a copy of the agreed one; this module is
deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical growing trace of a valid engine run simulates it, with the cut map `cutMap`. -/
theorem simTraceAt_simulates (hv : rho.ExecutionValid) :
    SimulatesAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn) := by
  sorry

/-- The canonical growing trace of a valid engine run is a growing-fault Goldilocks run for the
time-indexed honest keys. -/
theorem simTraceAt_goldilocksRun (hv : rho.ExecutionValid) :
    Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) :=
  (simTraceAt_simulates S rho hn hv).run

/-- Collision freedom of a valid engine run transports to the canonical growing trace. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  sorry

/-- A released attestation is a signing cut of the releasing tick. -/
theorem att_released_inv_at (hv : rho.ExecutionValid)
    {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {b : FG.Att (Fintype.card V)}
    (hb : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ rho.releasesAt j) :
    (S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
      Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
  sorry

/-- A received forwarding wrapper signed by a node honest at the receipt carries a stamp no later
than the receipt. -/
theorem received_forward_stamp_le_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  sorry

/-- A received forwarding wrapper of a node honest at the receipt, with its block above the
recipient's final block at a later reading cut `j` (the recipient honest at a time `t₀` that bounds
every cut before `j`), is accepted by the end of the receipt's event. -/
theorem received_forward_accepted_before_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    {t₀ : Time} (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀)
    (hy : v ∉ rho.faultyAt t₀)
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

/-- `received_forward_accepted_before_at` for a wrapper that is its signer's actual release at its
stamp `t`, with the signer honest at `t` only (it may be compromised by the receipt). -/
theorem received_forward_accepted_before_of_released_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    {t₀ : Time} (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀)
    (hy : v ∉ rho.faultyAt t₀)
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

/-- A held vote-forwarding envelope of a node honest at its stamp is the holder's own, or the
holder processed the vote between the stamp and the holding time. -/
theorem held_voteForward_source_or_process_at (hv : rho.ExecutionValid)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ d : Time}
    {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (hh : rho.log.Held rho.point (rho.key y)
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m]) d) :
    y = x ∨ ∃ k, (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      τ ≤ (simTraceAt S rho hn).time k ∧ (simTraceAt S rho hn).time k ≤ d := by
  sorry

/-- The acceptance of an own proposal at a slot tick queues its forwarding wrapper. -/
theorem tick_proposal_acceptance_queued_at (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
      t (encodeTxs (Model.mempool rho.inbox v t)) .proposal).2) :
    ∃ p, forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (shapeOf S hn
        (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1) := by
  sorry

variable (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- Every acceptance by a node honest at its cut has an actual, exactly decoded same-event
forwarding publication. -/
def ForwardAtAcceptanceAt : Prop :=
  ∀ x k B, x ∈ honestKeysAt S rho (tr.time k) → tr.AcceptAt x k B →
    ∃ r p, pubExec.actual r ∧ r.origin = x ∧
      cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
      pubExec.eventTime r.event = tr.time k ∧
      r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
        some (x, tr.time k, p, B)

/-- Characterize acceptance forwarding without exposing its definition body. -/
theorem forwardAtAcceptanceAt_iff : ForwardAtAcceptanceAt S rho hn tr cutMap pubExec ↔
    ∀ x k B, x ∈ honestKeysAt S rho (tr.time k) → tr.AcceptAt x k B →
      ∃ r p, pubExec.actual r ∧ r.origin = x ∧
        cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
        pubExec.eventTime r.event = tr.time k ∧
        r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
        decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
          some (x, tr.time k, p, B) := by
  rfl

end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.Healing.Growing.Pending
open SA (gbar)

section Catch
variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))

/-- **`Catch(κ)` over a run** under growing faults: a block accepted at a time `< ḡ` by a node
honest at its acceptance is accepted before `ḡ + κ` by every validator `y` honest at `ḡ + κ` whose
`Σ.F` at `ḡ + κ` it extends. -/
def CatchRun (g κ : Time) : Prop :=
  ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y j, y ∈ H (gbar g + κ) → tr.FirstCutFrom j (gbar g + κ) →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B

end Catch

section Reset
variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The service of a healthy run from GST `g` under growing faults: messages, blocks and
acceptance relay at the protocol delay, and signed attestations at `ΔF` at calls by `b`. Senders
are honest at their event, recipients at their call. -/
structure ResetService (g ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → (tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧
        tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

end Reset

end Consensus.Goldilocks.Healing.Growing.Pending

end
