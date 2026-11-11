module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Correctness
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.FG
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.SyncUntil

public section

/-! # Open correctness assembly edges

All edges are sorry-free proposition definitions, not proofs. Nothing here is supplied as
evidence to a definition, instance, type witness or compiled endpoint. Reductions remain open rows
until the concrete morphism and missing local interfaces have been specified.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

/-- Intended window extraction edge. FrameWindow retains its constant-frame meaning;
the four anchors and their height steps are explicit data, not a second window record.
The designated proposals are a progress premise, not an output guarantee. -/
def final_window_extract_at {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
    (C : ACCorrectLocal A sg) : Prop :=
  ∀ (tr : RunTrace A) (H : Time → Set (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (g ΔF deadline : Time)
    (start gap floor : Nat) (kindJ : Prop) (J : A.Blk)
    (block : Fin 4 → A.Blk) (cut : Fin 4 → Nat),
    C.healing.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF deadline →
    FrameWindow tr H (P.slotTime start) deadline floor kindJ J →
    HealedFrom tr H proposer start deadline → 2 ≤ gap → 3 * gap ≤ P.δt →
    StrictMono cut →
    (∀ a, (block a).slot = start + a.val * gap ∧
      tr.ProposesAt (block a).proposer (cut a) (block a) ∧
      ReadyCut tr H C.catchUp (block a).proposer (cut a) ∧
      (block a).proposer ∈ H (tr.time (cut a) + C.hold)) →
    tr.time (cut 3) + P.Δ ≤ deadline →
    (∀ a, tr.AcceptAt (block a).proposer (cut a) (block a)) ∧
      (∀ a b, a ≤ b → Anc (tr.HonestBlocksAt H) (block a) (block b)) ∧
      ∀ a : Fin 3, ∃ z i j, z ∈ H (tr.time i) ∧ z ∈ H (tr.time j) ∧
        block a.castSucc ∈ (tr.state z i).fg.tree ∧ block a.succ ∈ (tr.state z j).fg.tree ∧
        ((tr.state z i).fg.σ (block a.castSucc).root).h + 1 ≤
          ((tr.state z j).fg.σ (block a.succ).root).h

/-- Intended cache-coverage edge from an explicit four-anchor chain and three height steps.
Population safety and actual processing of the carrier remain explicit inputs. -/
def final_cache_coverage_at {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
    (C : ACCorrectLocal A sg) : Prop :=
  ∀ (tr : RunTrace A) (H : Time → Set (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (g ΔF deadline : Time)
    (start gap floor : Nat) (kindJ : Prop) (J : A.Blk)
    (block : Fin 4 → A.Blk) (cut : Fin 4 → Nat),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    C.healing.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF deadline →
    FrameWindow tr H (P.slotTime start) deadline floor kindJ J →
    HealedFrom tr H proposer start deadline → 2 ≤ gap → 3 * gap ≤ P.δt →
    StrictMono cut →
    (∀ a, (block a).slot = start + a.val * gap ∧
      tr.ProposesAt (block a).proposer (cut a) (block a) ∧
      tr.AcceptAt (block a).proposer (cut a) (block a) ∧
      ReadyCut tr H C.catchUp (block a).proposer (cut a)) →
    (∀ a b, a ≤ b → Anc (tr.HonestBlocksAt H) (block a) (block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ H (tr.time i) ∧ z ∈ H (tr.time j) ∧
      block a.castSucc ∈ (tr.state z i).fg.tree ∧ block a.succ ∈ (tr.state z j).fg.tree ∧
      ((tr.state z i).fg.σ (block a.castSucc).root).h + 1 ≤
        ((tr.state z j).fg.σ (block a.succ).root).h) →
    tr.time (cut 3) + P.Δ ≤ deadline →
    ∀ y j, deadline ≤ tr.time j → ReadyCut tr H C.catchUp y j →
      (H (tr.time j))ᶜ.ncard < 2 * P.q - P.n →
      (∃ k < j, tr.BlockCallAt y k (block 3)) →
      Anc (tr.HonestBlocksAt H) (block 0) (tr.finalizedAt y j)

/-- Prefix-reader bridge on generic runs: freeze honesty at the observation, retain the
prefix run and recover the original state at every cut no later than the observation. -/
def prefix_reader_edge {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n) : Prop :=
  ∀ (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    Growing.LocalRun proposer dg H sg tr →
    ∀ d, 0 ≤ d → Node.LocalRun proposer dg (H d) sg (tr.upTo d) ∧
      ∀ y i, (∀ k < i, tr.time k ≤ d) → (tr.upTo d).state y i = tr.state y i

/-- Collision freedom transports to a prefix; this is not supplied evidence. -/
def noColl_transport_edge {P : Params} (A : NodeAC P) : Prop :=
  ∀ (dg : Digest (List (FG.Att P.n)) A.Payload) (tr : RunTrace A) (d : Time),
    Compose.NoCollRun dg tr → Compose.NoCollRun dg (tr.upTo d)

/-- Deadline service of the generic AC projection supplies actual processing witnesses.
This is the run-level deadline bridge, not an assertion of an unspecified engine morphism. -/
def syncUntil_service_edge {P : Params} (A : NodeAC P) : Prop :=
  ∀ (tr : RunTrace A) (H : Time → Set (Fin P.n)) (b d : Time),
    SyncUntilAC A (H d) (tr.HonestBlocksAt H) b tr.projAC →
    ∀ x, x ∈ H d → ∀ i m, tr.projAC.SendOrAdmit x i m →
      ∀ y, y ∈ H d → ∀ j ℓ, tr.projAC.CallAt y j ℓ →
        tr.projAC.deadline y j (tr.projAC.time i) ≤ tr.projAC.time j →
        tr.projAC.deadline y j (tr.projAC.time i) ≤ b + 1 →
        ∃ k ≤ j, tr.projAC.time i ≤ tr.projAC.time k ∧ tr.projAC.ProcessAt y k m ∧
          tr.projAC.time k < tr.projAC.deadline y k (tr.projAC.time i) ∧
          ∀ r, k < r → r ≤ j → ¬ tr.projAC.RestartAt y r

/-- Intended assembly from the claims and four independent non-claim inputs. -/
def generic_meetsObligations_of {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] : Prop :=
  GenericMeetsObligations (O := O) (Info := Info)

/-- Intended correctness edge through the existing shape obligations endpoint.
No import of its proof or evidence of this implication is supplied. -/
def generic_correct {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] : Prop :=
  ∀ (F : ChainShapeFamily O Info) (K : Contract ProgressReq), ShapeObligations F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      CorrectProtocol (Sys F V) (shapeProgress F V) K

end Consensus.Goldilocks.Generic

end
