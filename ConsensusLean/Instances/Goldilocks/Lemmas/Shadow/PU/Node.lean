module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Shadow P-U node and execution

Finality guard choice: option (i). `updateFinality'` replaces `HasViableDescendant` by
`HasViableDescendant'` over P-U viability. The test reads the intermediate store after the
height and justification updates, before the finalized block moves. No equivalence with the
stock guard is assumed. The composition below copies the stock calls, replacing their frame
and accepted-block handler; the AC, payloads, signatures and event order are unchanged.
-/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

def HasViableDescendant' (st : Store P ACP) (B : NodeBlock P ACP) : Prop :=
  ∃ B' ∈ st.tree, st.Anc B B' ∧ st.IsViable' B'

open Classical in
noncomputable def updateFinality' (st : Store P ACP) (σ : FG.ChainState P.n) :
    Store P ACP :=
  let st₁ : Store P ACP := { st with hmax := max st.hmax σ.h }
  let st₂ : Store P ACP :=
    match st₁.blocks σ.J with
    | some X =>
        if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J) then
          { st₁ with J := X, hj := σ.hj }
        else st₁
    | none => st₁
  match st₂.blocks σ.F with
  | some X =>
      if st₂.Anc st₂.F X ∧ st₂.F ≠ X ∧ st₂.Anc X st₂.J ∧ st₂.HasViableDescendant' X then
        { st₂ with F := X }
      else st₂
  | none => st₂

open Classical in
noncomputable def onBlock' (st : Store P ACP) (B : NodeBlock P ACP) :
    Option (Store P ACP) :=
  match B.parent with
  | none => none
  | some pr =>
      if (st.blocks B.root).isSome ∨ (st.blocks pr).isNone ∨
          ¬ Goldilocks.Anc (insert B st.tree) st.F B then
        none
      else
        match P.fg.stateTransition (st.σ pr) B.fgView with
        | none => none
        | some σ' =>
            let st₁ : Store P ACP :=
              { st with blocks := Function.update st.blocks B.root (some B),
                        σ := Function.update st.σ B.root σ' }
            some ((updateFinality' st₁ σ').addAtts B.fgPayload)

def Step' (st st' : Store P ACP) : Prop :=
  (∃ B, onBlock' st B = some st') ∨ ∃ a, st' = onAttestation st a

def Reachable' (acp₀ : ACP) : Store P ACP → Prop :=
  Relation.ReflTransGen Step' (init acp₀)

open Classical in
theorem updateFinality'_eq (st : Store P ACP) (σ : FG.ChainState P.n) :
    updateFinality' st σ =
      (let st₁ : Store P ACP := { st with hmax := max st.hmax σ.h }
       let st₂ : Store P ACP :=
         match st₁.blocks σ.J with
         | some X =>
             if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J) then
               { st₁ with J := X, hj := σ.hj }
             else st₁
         | none => st₁
       match st₂.blocks σ.F with
       | some X =>
           if st₂.Anc st₂.F X ∧ st₂.F ≠ X ∧ st₂.Anc X st₂.J ∧ st₂.HasViableDescendant' X then
             { st₂ with F := X }
           else st₂
       | none => st₂) := by
  rfl

open Classical in
theorem onBlock'_eq (st : Store P ACP) (B : NodeBlock P ACP) :
    onBlock' st B =
      (match B.parent with
       | none => none
       | some pr =>
           if (st.blocks B.root).isSome ∨ (st.blocks pr).isNone ∨
               ¬ Goldilocks.Anc (insert B st.tree) st.F B then
             none
           else
             match P.fg.stateTransition (st.σ pr) B.fgView with
             | none => none
             | some σ' =>
                 let st₁ : Store P ACP :=
                   { st with blocks := Function.update st.blocks B.root (some B),
                             σ := Function.update st.σ B.root σ' }
                 some ((updateFinality' st₁ σ').addAtts B.fgPayload)) := by
  rfl

theorem step'_iff (st st' : Store P ACP) :
    Step' st st' ↔ (∃ B, onBlock' st B = some st') ∨ ∃ a, st' = onAttestation st a := by
  rfl

theorem reachable'_eq (acp₀ : ACP) :
    Reachable' (P := P) acp₀ = Relation.ReflTransGen Step' (init acp₀) := by
  rfl

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

noncomputable def acCall' (self : Fin P.n) (st : NodeState A) (t : Time) (c : A.Call) :
    NodeState A × Cut A :=
  let Φ := frame' st
  let r := A.step self st.ac Φ t c
  ({ st with ac := r.1 }, .ac ⟨c, Φ, r.2⟩)

noncomputable def acProposal' (st : NodeState A) (t : Time) :
    NodeState A × Cut A × Option (DutyHead P.n (List (FG.Att P.n)) A.Payload × A.Payload) :=
  let Φ := frame' st
  let r := A.proposal st.ac Φ t
  ({ st with ac := r.1 }, .ac ⟨.proposal, Φ, []⟩, r.2)

noncomputable def acToFG' (st : NodeState A) (t : Time) :
    NodeState A × Cut A × Option A.Blk :=
  let Φ := frame' st
  let r := A.toFG st.ac Φ t
  ({ st with ac := r.1 }, .ac ⟨.toFG, Φ, []⟩, r.2)

noncomputable def onBlock' (self : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    NodeState A × List (Cut A) :=
  if P.slotOf t < B.slot then (st, [])
  else
    match st.fg.onBlock' B with
    | none => (st, [.fg (.block B false)])
    | some fg' =>
        let r := acCall' self { st with fg := fg' } t (.block B)
        (r.1, [.fg (.block B true), r.2])

noncomputable def onMessage' (self : Fin P.n) (st : NodeState A) (t : Time) (m : A.Msg) :
    NodeState A × List (Cut A) :=
  let r := acCall' self st t (.message m)
  (r.1, [r.2])

noncomputable def restart' (self : Fin P.n) (st : NodeState A) (t : Time) :
    NodeState A × List (Cut A) :=
  let r := acCall' self st t .restart
  (r.1, [r.2])

noncomputable def proposeBlock' (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (H : A.Blk) (p : A.Payload) :
    NodeState A × List (Cut A) :=
  onBlock' self st t (mkBlock dg self st.fg t x H p)

noncomputable def tickStep' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) : TickStep → NodeState A × List (Cut A)
  | .acTick =>
      let r := acCall' self st t .tick
      (r.1, [r.2])
  | .proposal =>
      if Proposes proposer self t then
        let r := acProposal' st t
        match r.2.2 with
        | none => (r.1, [r.2.1])
        | some (d, p) =>
            let r' := proposeBlock' dg self r.1 t x d.head p
            (r'.1, r.2.1 :: r'.2)
      else (st, [])
  | .fgUpdate =>
      let r := acToFG' st t
      match r.2.2 with
      | none => (r.1, [r.2.1])
      | some C =>
          let r' := attest self r.1 C
          (r'.1, r.2.1 :: r'.2)

noncomputable def runSteps' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (steps : List TickStep) :
    NodeState A × List (Cut A) :=
  steps.foldl (fun acc step =>
    let r := tickStep' proposer dg self acc.1 t x step
    (r.1, acc.2 ++ r.2)) (st, [])

noncomputable def onTick' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (fgDue : Bool) : NodeState A × List (Cut A) :=
  runSteps' proposer dg self st t x (tickSteps fgDue)

noncomputable def exec' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) : Event A → NodeState A × List (Cut A)
  | .tick x fgDue => onTick' proposer dg self st t x fgDue
  | .block B => onBlock' self st t B
  | .message m => onMessage' self st t m
  | .attestation a => onAttestation st a
  | .restart => restart' self st t

theorem acCall'_eq (self : Fin P.n) (st : NodeState A) (t : Time) (c : A.Call) :
    acCall' self st t c =
      (let Φ := frame' st
       let r := A.step self st.ac Φ t c
       ({ st with ac := r.1 }, .ac ⟨c, Φ, r.2⟩)) := by rfl

theorem acProposal'_eq (st : NodeState A) (t : Time) :
    acProposal' st t =
      (let Φ := frame' st
       let r := A.proposal st.ac Φ t
       ({ st with ac := r.1 }, .ac ⟨.proposal, Φ, []⟩, r.2)) := by rfl

theorem acToFG'_eq (st : NodeState A) (t : Time) :
    acToFG' st t =
      (let Φ := frame' st
       let r := A.toFG st.ac Φ t
       ({ st with ac := r.1 }, .ac ⟨.toFG, Φ, []⟩, r.2)) := by rfl

theorem onBlock'_eq (self : Fin P.n) (st : NodeState A) (t : Time) (B : A.Blk) :
    onBlock' self st t B =
      (if P.slotOf t < B.slot then (st, [])
       else match st.fg.onBlock' B with
       | none => (st, [.fg (.block B false)])
       | some fg' =>
           let r := acCall' self { st with fg := fg' } t (.block B)
           (r.1, [.fg (.block B true), r.2])) := by rfl

theorem onMessage'_eq (self : Fin P.n) (st : NodeState A) (t : Time) (m : A.Msg) :
    onMessage' self st t m =
      (let r := acCall' self st t (.message m); (r.1, [r.2])) := by rfl

theorem restart'_eq (self : Fin P.n) (st : NodeState A) (t : Time) :
    restart' self st t =
      (let r := acCall' self st t .restart; (r.1, [r.2])) := by rfl

theorem proposeBlock'_eq (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (H : A.Blk) (p : A.Payload) :
    proposeBlock' dg self st t x H p = onBlock' self st t (mkBlock dg self st.fg t x H p) := by
  rfl

theorem tickStep'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (step : TickStep) :
    tickStep' proposer dg self st t x step =
      (match step with
       | .acTick => let r := acCall' self st t .tick; (r.1, [r.2])
       | .proposal =>
           if Proposes proposer self t then
             let r := acProposal' st t
             match r.2.2 with
             | none => (r.1, [r.2.1])
             | some (d, p) =>
                 let r' := proposeBlock' dg self r.1 t x d.head p
                 (r'.1, r.2.1 :: r'.2)
           else (st, [])
       | .fgUpdate =>
           let r := acToFG' st t
           match r.2.2 with
           | none => (r.1, [r.2.1])
           | some C =>
               let r' := attest self r.1 C
               (r'.1, r.2.1 :: r'.2)) := by rfl

theorem runSteps'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (steps : List TickStep) :
    runSteps' proposer dg self st t x steps =
      steps.foldl (fun acc step =>
        let r := tickStep' proposer dg self acc.1 t x step
        (r.1, acc.2 ++ r.2)) (st, []) := by rfl

theorem onTick'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (fgDue : Bool) :
    onTick' proposer dg self st t x fgDue =
      runSteps' proposer dg self st t x (tickSteps fgDue) := by rfl

theorem exec'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) :
    exec' proposer dg self st t e =
      (match e with
       | .tick x fgDue => onTick' proposer dg self st t x fgDue
       | .block B => onBlock' self st t B
       | .message m => onMessage' self st t m
       | .attestation a => onAttestation st a
       | .restart => restart' self st t) := by rfl

def CutStep' (self : Fin P.n) (t : Time) (st : NodeState A) : Cut A → NodeState A → Prop
  | .ac ℓ, st' =>
      ℓ.frame = frame' st ∧ A.step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) ∧
        st'.fg = st.fg ∧ st'.record = st.record
  | .fg (.block B true), st' =>
      B.slot ≤ P.slotOf t ∧ st.fg.onBlock' B = some st'.fg ∧ st'.ac = st.ac ∧
        st'.record = st.record
  | .fg (.block B false), st' => st.fg.onBlock' B = none ∧ st' = st
  | .fg (.attestation a), st' =>
      st'.fg = st.fg.onAttestation a ∧ st'.ac = st.ac ∧ st'.record = st.record
  | .fg (.attest C none), st' => st.fg.attest st.record self C = none ∧ st' = st
  | .fg (.attest C (some a)), st' =>
      st.fg.attest st.record self C = some (a, st'.record) ∧ st'.fg = st.fg ∧ st'.ac = st.ac

theorem cutStep'_ac (self : Fin P.n) (t : Time) (st st' : NodeState A) (ℓ : ACLabel A) :
    CutStep' self t st (.ac ℓ) st' ↔
      ℓ.frame = frame' st ∧ A.step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) ∧
        st'.fg = st.fg ∧ st'.record = st.record := by rfl

theorem cutStep'_block_true (self : Fin P.n) (t : Time) (st st' : NodeState A) (B : A.Blk) :
    CutStep' self t st (.fg (.block B true)) st' ↔
      B.slot ≤ P.slotOf t ∧ st.fg.onBlock' B = some st'.fg ∧ st'.ac = st.ac ∧
        st'.record = st.record := by rfl

theorem cutStep'_block_false (self : Fin P.n) (t : Time) (st st' : NodeState A) (B : A.Blk) :
    CutStep' self t st (.fg (.block B false)) st' ↔ st.fg.onBlock' B = none ∧ st' = st := by
  rfl

theorem cutStep'_attestation (self : Fin P.n) (t : Time) (st st' : NodeState A)
    (a : FG.Att P.n) :
    CutStep' self t st (.fg (.attestation a)) st' ↔
      st'.fg = st.fg.onAttestation a ∧ st'.ac = st.ac ∧ st'.record = st.record := by rfl

theorem cutStep'_attest_none (self : Fin P.n) (t : Time) (st st' : NodeState A) (C : A.Blk) :
    CutStep' self t st (.fg (.attest C none)) st' ↔
      st.fg.attest st.record self C = none ∧ st' = st := by rfl

theorem cutStep'_attest_some (self : Fin P.n) (t : Time) (st st' : NodeState A)
    (C : A.Blk) (a : FG.Att P.n) :
    CutStep' self t st (.fg (.attest C (some a))) st' ↔
      st.fg.attest st.record self C = some (a, st'.record) ∧ st'.fg = st.fg ∧ st'.ac = st.ac := by
  rfl

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks

abbrev RunTrace' {P : Params} (A : NodeAC P) := RunTrace A

noncomputable abbrev goldilocksNode' (sp : AC.ACParams)
    : NodeAC sp.toParams :=
  AC.goldilocksAC sp (List (FG.Att sp.n))

abbrev GoldilocksTrace' (sp : AC.ACParams)
    := RunTrace' (goldilocksNode' sp)

end Consensus.Goldilocks

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

def GroupAt' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time)
    (e : Node.Event A) : Prop :=
  let cs := (Node.exec' proposer dg y (tr.state y j) t e).2
  cs ≠ [] ∧
    (∀ k, (hk : k < cs.length) → tr.node (j + k) = y ∧ tr.time (j + k) = t ∧
      tr.event (j + k) = tr.event j ∧ tr.pos (j + k) = k ∧ tr.label (j + k) = some cs[k]) ∧
    ∀ i, tr.event i = tr.event j → j ≤ i ∧ i < j + cs.length

def InGroup' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j i : Nat) (t : Time)
    (e : Node.Event A) : Prop :=
  tr.GroupAt' proposer dg y j t e ∧ j ≤ i ∧
    i < j + (Node.exec' proposer dg y (tr.state y j) t e).2.length

def TickAt' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) : Prop :=
  ∃ x fgDue, tr.GroupAt' proposer dg y j t (.tick x fgDue)

def SignTickAt' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) : Prop :=
  ∃ x, tr.GroupAt' proposer dg y j t (.tick x true)

def OwnPublicationAt' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) : Prop :=
  ∃ a, tr.GroupAt' proposer dg y j t (.attestation a) ∧ a.val = y ∧
    a ∉ (tr.state y j).fg.atts ∧
    ∃ j₀ x fgDue, tr.GroupAt' proposer dg y j₀ t (.tick x fgDue) ∧
      j₀ + (Node.exec' proposer dg y (tr.state y j₀) t (.tick x fgDue)).2.length ≤ j ∧
      ∀ k, j₀ + (Node.exec' proposer dg y (tr.state y j₀) t (.tick x fgDue)).2.length ≤ k →
        k < j → tr.node k = y ∧ ∃ b : FG.Att P.n, b.val = y ∧
          tr.label k = some (.fg (.attestation b))

def AllTicksSign' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n)) : Prop :=
  ∀ y ∈ H, ∀ j t, tr.TickAt' proposer dg y j t → tr.SignTickAt' proposer dg y j t

theorem groupAt'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time)
    (e : Node.Event A) :
    tr.GroupAt' proposer dg y j t e ↔
      (let cs := (Node.exec' proposer dg y (tr.state y j) t e).2
       cs ≠ [] ∧
         (∀ k, (hk : k < cs.length) → tr.node (j + k) = y ∧ tr.time (j + k) = t ∧
           tr.event (j + k) = tr.event j ∧ tr.pos (j + k) = k ∧
             tr.label (j + k) = some cs[k]) ∧
         ∀ i, tr.event i = tr.event j → j ≤ i ∧ i < j + cs.length) := by rfl

theorem inGroup'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j i : Nat) (t : Time)
    (e : Node.Event A) :
    tr.InGroup' proposer dg y j i t e ↔ tr.GroupAt' proposer dg y j t e ∧ j ≤ i ∧
      i < j + (Node.exec' proposer dg y (tr.state y j) t e).2.length := by rfl

theorem tickAt'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) :
    tr.TickAt' proposer dg y j t ↔ ∃ x fgDue, tr.GroupAt' proposer dg y j t (.tick x fgDue) := by
  rfl

theorem signTickAt'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) :
    tr.SignTickAt' proposer dg y j t ↔ ∃ x, tr.GroupAt' proposer dg y j t (.tick x true) := by
  rfl

theorem ownPublicationAt'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) :
    tr.OwnPublicationAt' proposer dg y j t ↔
      ∃ a, tr.GroupAt' proposer dg y j t (.attestation a) ∧ a.val = y ∧
        a ∉ (tr.state y j).fg.atts ∧
        ∃ j₀ x fgDue, tr.GroupAt' proposer dg y j₀ t (.tick x fgDue) ∧
          j₀ + (Node.exec' proposer dg y (tr.state y j₀) t (.tick x fgDue)).2.length ≤ j ∧
          ∀ k, j₀ + (Node.exec' proposer dg y (tr.state y j₀) t (.tick x fgDue)).2.length ≤ k →
            k < j → tr.node k = y ∧ ∃ b : FG.Att P.n, b.val = y ∧
              tr.label k = some (.fg (.attestation b)) := by rfl

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Node

variable {P : Params}

/-- The stock local run laws, copied with the shadow execution and cut law. -/
structure LocalRun' {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (ini : Fin P.n → A.State := fun _ => A.initial) : Prop where
  init : ∀ y ∈ H, tr.init y = Node.initWith A (ini y)
  grouped : ∀ y ∈ H, ∀ i c, tr.CallAt y i c →
    ∃ j e, tr.InGroup' proposer dg y j i (tr.time i) e
  cutLaw : ∀ y ∈ H, ∀ i c, tr.CallAt y i c → CutStep' y (tr.time i) (tr.state y i) c (tr.post i)
  wire : ∀ y ∈ H, ∀ j t e, tr.GroupAt' proposer dg y j t e → WireOK dg e
  proposerCredential : ∀ y ∈ H, ∀ j t B, tr.GroupAt' proposer dg y j t (.block B) →
    B.proposer = proposer B.slot
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite
  phase_order : ∀ y ∈ H, ∀ y' ∈ H, ∀ j j' t e e', tr.GroupAt' proposer dg y j t e →
    tr.GroupAt' proposer dg y' j' t e' → j < j' →
    (y = y' ∨ ¬ tr.OwnPublicationAt' proposer dg y j t) → e.phase ≤ e'.phase
  tick_public : ∀ y ∈ H, ∀ j t, tr.TickAt' proposer dg y j t → P.IsPublic t
  tick_unique : ∀ y ∈ H, ∀ j j' t,
    tr.TickAt' proposer dg y j t → tr.TickAt' proposer dg y j' t → j = j'
  tick_of_awake : ∀ y ∈ H, ∀ t, 0 ≤ t → P.IsPublic t → tr.awake y t →
    ∃ j, tr.TickAt' proposer dg y j t
  awake_in_horizon : ∀ y ∈ H, ∀ t, tr.awake y t → tr.InHorizon t
  awake_of_call : ∀ y ∈ H, ∀ i, tr.IsCall y i → tr.awake y (tr.time i)
  restart_of_sleep : ∀ y ∈ H, ∀ i (u : Time), tr.IsCall y i → 0 ≤ u → u < tr.time i →
    ¬ tr.awake y u → (∀ j < i, tr.IsCall y j → tr.time j < u) → tr.RestartAt y i
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  sleep_of_restart : ∀ y ∈ H, ∀ i, tr.RestartAt y i →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧ ∀ j < i, tr.IsCall y j → tr.time j < u
  block_unforgeable : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B → B.proposer ∈ H →
    ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  att_unforgeable : ∀ y ∈ H, ∀ i a,
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) → a.val ∈ H →
      ∃ j < i, tr.SignAt a.val j a
  msg_unforgeable : ∀ y ∈ H, ∀ i m, tr.MsgCallAt y i m → sg m ∈ H → ∃ j < i, tr.EmitAt (sg m) j m

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks

open AC (ACParams Vote Payload)

variable {sp : ACParams}

structure GoldilocksRun' (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace' sp)
    (ini : Fin sp.n → (goldilocksNode' sp).State := fun _ => (goldilocksNode' sp).initial) :
    Prop
    extends Node.LocalRun' proposer dg H (fun v : Vote sp.n => v.val) tr ini where
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode' sp).genesisPayload).RootOk dg
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

theorem cutStep'_fg {self : Fin P.n} {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep' self t st c st') : st'.fg = st.fg ∨ Store.Step' st.fg st'.fg := by
  cases c with
  | ac ℓ => exact Or.inl h.2.2.1
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | false => exact Or.inl (congrArg NodeState.fg h.2)
      | true => exact Or.inr ((Store.step'_iff _ _).2 (Or.inl ⟨B, h.2.1⟩))
    | attestation a => exact Or.inr ((Store.step'_iff _ _).2 (Or.inr ⟨a, h.1⟩))
    | attest C s =>
      cases s with
      | none => exact Or.inl (congrArg NodeState.fg h.2)
      | some a => exact Or.inl h.2.1

theorem fg_reachable_at' {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.Reachable' A.genesisPayload := by
  rw [Store.reachable'_eq]
  induction i with
  | zero => rw [Trace.state, h.init y hy]; exact .refl
  | succ i ih =>
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      rcases cutStep'_fg (h.cutLaw y hy i c hc) with heq | hs
      · exact heq ▸ ih
      · exact ih.tail hs
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact ih

theorem frame_of_call_at' {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) :
    ℓ.frame = frame' (tr.state y i) :=
  (h.cutLaw y hy i (.ac ℓ) hc).1

theorem frame_of_projAC_at' {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel A} (hc : tr.projAC.CallAt y i ℓ) :
    ℓ.frame = frame' (tr.state y i) := by
  apply frame_of_call_at' h hy
  rcases hc with ⟨hn, hl⟩
  refine ⟨hn, ?_⟩
  change (tr.label i).bind RunTrace.acLabel = some ℓ at hl
  cases he : tr.label i with
  | none => simp [he] at hl
  | some c =>
    cases c with
    | fg f => simp [he, RunTrace.acLabel] at hl
    | ac a =>
      have ha : a = ℓ := by simpa [he, RunTrace.acLabel] using hl
      simp [ha]

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem projAC_state' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) (i : Nat) : tr.projAC.state y i = (tr.state y i).ac := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projAC, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl]
        rw [← ih]
        simp [Trace.state, RunTrace.projAC, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | ac ℓ => simp [Trace.state, RunTrace.projAC, hn, hl, RunTrace.acLabel]
        | fg ℓ =>
          rw [show (tr.post i).ac = (tr.state y i).ac by
            cases ℓ with
            | block B acc =>
              cases acc
              · rw [Node.cutStep'_block_false] at hlaw; rw [hlaw.2]
              · exact ((Node.cutStep'_block_true _ _ _ _ _).1 hlaw).2.2.1
            | attestation a => exact ((Node.cutStep'_attestation _ _ _ _ _).1 hlaw).2.1
            | attest C s =>
              cases s
              · rw [Node.cutStep'_attest_none] at hlaw; rw [hlaw.2]
              · exact ((Node.cutStep'_attest_some _ _ _ _ _ _).1 hlaw).2.2, ← ih]
          simp [Trace.state, RunTrace.projAC, hl, RunTrace.acLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projAC, hn]

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp}

theorem toFG_mem_tree' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode' sp)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hto : AC.ToFGAt tr.projAC y k ℓ C) : C ∈ (tr.state y k).fg.tree := by
  have hmem := (AC.toFG_source hto.2.2).1.1
  rw [Node.frame_of_projAC_at' hrun.toLocalRun' hy hto.1, Node.frame'_eq,
    Store.toFrame'_tree] at hmem
  exact hmem.1

end Consensus.Goldilocks.Healing

end
