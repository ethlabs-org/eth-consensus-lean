module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SentForward
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DeadlineWake
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Network transport for the concrete publisher/simulation adapter

The full transports of the engine network to the node service premises are not stated here and
are not premises of `MeetsObligations`.
The trace parameters remain independent here. `Setup.params` gives protocol delay Δp = Δe: the
engine holds an object strictly before `a + Δe` (by `a + Δe − 1`), which is the node's strict
deadline `a + Δp`. FG attestation service has its own delay `Δ_F`: the engine serves
standalone attestations (`isFGAtt`) strictly before its FG delay `ΔF` (the `fgAtts` clause of
`PSync`), at the protocol FG delay `Δ_F,p = protoFGDelay (pubOf E) = ΔF`.
Every other object (blocks, votes, forwarding and vote-forwarding wrappers) is served strictly
before the bound `Δ`; no statement here claims a block before `ΔF`.
A full transport would include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. The finite services up to a synchronous horizon
are proved under growing faults (`Growing/Obligations/Network`); full GST remains separate.
-/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The delivery deadline is monotone in its delivery parameter. -/
theorem deadline_mono_delta (y : Fin P.n) (k : Nat) (τ : Time) {Δ₁ Δ₂ : Time}
    (h : Δ₁ ≤ Δ₂) : tr.deadline y k τ Δ₁ ≤ tr.deadline y k τ Δ₂ := by
  unfold deadline
  exact add_le_add le_rfl h

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

/-- The protocol FG delay of the public parameters: `ΔF_p = ΔFG`, the engine FG delay, as the
protocol delay `Δ_p = ΔAC` (`Setup.params`): L0 delivers strictly before the bound
(`CommLog.PSync`), which is the node's deadline `[τ, max(τ, w) + Δ_F)`. -/
def protoFGDelay (pub : Model.Public) : Time := pub.ΔFG

theorem protoFGDelay_eq (pub : Model.Public) : protoFGDelay pub = pub.ΔFG := by rfl

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)

/-- The engine log's message class is the Goldilocks attestation class (`isFGAtt`). -/
theorem log_fgAtt_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (o : Wire (Fintype.card V) S.vote) :
    rho.log.fgAtt o ↔ isFGAtt o := Iff.rfl

/-- A standalone attestation is an attestation. -/
theorem isFGAtt_attObj {binding : VoteBinding} {n : Nat} (a : FG.Att n) :
    isFGAtt (attObj (binding := binding) a) := by
  simp [isFGAtt, IsAttObj, attObj]

/-- A forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_forwardObj {binding : VoteBinding} {sp : SA.SAParams} (origin : Fin sp.n)
    (t : Time) (parent : Option (Wire sp.n binding)) (B : Blk sp) :
    ¬ isFGAtt (forwardObj sp origin t parent B) := by
  simp [forwardObj, isFGAtt, IsAttObj]

/-- An object that decodes as a forwarding wrapper is not an attestation. -/
theorem not_isFGAtt_of_decodeForward {binding : VoteBinding} {sp : SA.SAParams}
    {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {q : Fin sp.n × Time × Option (Wire sp.n binding) × Blk sp}
    (h : decodeForward sp hs o = some q) : ¬ isFGAtt o := by
  obtain ⟨origin, t, parent, B⟩ := q
  rw [forwardObj_of_decodeForward hs o origin t parent B h]
  exact not_isFGAtt_forwardObj origin t parent B

/-- Every well-formed attestation contained in an actual receipt gets a real processing
call at receipt time, including duplicate attestations already present in the pool. -/
theorem received_att_processAt
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    {i : Nat} {v : V} {receipt : Wire (Fintype.card V) S.vote} {t : Time}
    (he : rho.events[i]? = some (.deliver v receipt t)) {a : FG.Att (Fintype.card V)}
    (hwf : a.WellFormed) (hc : Model.Obj.Contains receipt (attObj a)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  let proposer := runProposer S rho hn
  let dg := digestOf S rho
  let hs : List (Header Info × Nat) := Model.digests rho.hash receipt
  have find : ∀ (os : List (Wire (Fintype.card V) S.vote))
      (st : NodeState (goldilocksNode
        (S.params (Model.pubOf E) hn) (S.ro _)))
      (sub : Nat),
      attObj a ∈ os → ∃ r ∈ deliverRecs proposer dg hs (rho.ownKey v) t i os st sub,
        r.label = .fg (.attestation a) := by
    intro os
    induction os with
    | nil => intro st sub h; simp at h
    | cons o os ih =>
      intro st sub hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _
          (canonEvent_attObj
            (sp := S.params (Model.pubOf E) hn)
            (ro := S.ro _) hs a hwf)]
        have hlen : 0 < (groupRecs proposer dg (rho.ownKey v) st t
            (Nat.pair i sub) (.attestation a)).length := by
          simp [length_groupRecs, Node.exec, Node.onAttestation]
        refine ⟨_, List.mem_append_left _ (List.getElem_mem hlen), ?_⟩
        rw [(getElem_groupRecs proposer dg (rho.ownKey v) st t
          (Nat.pair i sub) (.attestation a) 0 hlen).2.2.2.2]
        rfl
      · cases ho : canonEvent
          (S.params
            (Model.pubOf E) hn) (S.ro _) hs o with
        | none =>
          rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
          exact ih st (sub + 1) hm
        | some e =>
          rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
          obtain ⟨r, hr, hl⟩ := ih (Node.exec proposer dg (rho.ownKey v) st t e).1
            (sub + 1) hm
          exact ⟨r, List.mem_append_right _ hr, hl⟩
  have hmem : attObj a ∈ delivered
      (S.params (Model.pubOf E) hn) receipt := hc
  obtain ⟨r, hr, hl⟩ := find (delivered
    (S.params (Model.pubOf E) hn) receipt)
    (stateAt S rho hn v i).node 0 hmem
  obtain ⟨hn', ht, _⟩ := mem_deliverRecs
    (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) proposer dg (rho.ownKey v) hs t i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt t he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[
      cutMap S rho hn i + j]? =
      some r := by
    rw [allCuts_getElem?_add S rho hn i j
      (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap S rho hn i + j, ?_, Or.inl ⟨?_, ?_⟩, ?_⟩
  · rw [cutMap_succ S rho hn]; omega
  · simp only [simTrace_node S rho hn, hk, Option.elim_some, hn']
  · simp only [simTrace_label S rho hn, hk, Option.map_some, hl]
  · simp only [simTrace_time S rho hn, hk, Option.elim_some, ht]

end Consensus.Goldilocks.Obligations
