module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.DutyRelease
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Engine signing history before node simulation

Implementation-refinement history for the obligations skeleton. These declarations use
actual engine duty prefixes, never `eventCuts`, `simTrace`, or `GoldilocksRun`. A poll's FG update
is the only signing operation; all other operations preserve the client history, including
restart. Queue provenance and unforgeability give the inverse from seen attestations to signings.

The paper's G0.5 supplies client safety, not the correspondence between engine execution and
client inputs. The latter and the release provenance obligations below have NO PAPER PROOF.
`ProvenanceGuard` derives non-slashable engine signings and the own-object guard from them.
-/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem onBlock_record {P : Params} {A : NodeAC P} (self : Fin P.n)
    (st : NodeState A) (t : Time) (B : A.Blk) :
    (Node.onBlock self st t B).1.record = st.record := by
  unfold Node.onBlock
  split
  · rfl
  · split <;> rfl

private theorem onBlock_reachable {P : Params} {A : NodeAC P} (self : Fin P.n)
    (st : NodeState A) (t : Time) (B : A.Blk) {acp₀ : A.Payload}
    (h : st.fg.Reachable acp₀) : (Node.onBlock self st t B).1.fg.Reachable acp₀ := by
  unfold Node.onBlock
  split
  · exact h
  · split
    · exact h
    · rename_i fg' he
      exact h.tail (Or.inl ⟨B, he⟩)

private theorem processOne_record {sp : AC.ACParams}
    (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp binding) (o : Wire sp.n binding) :
    (processOne io hs st o).node.record = st.node.record := by
  rw [processOne_eq]
  split
  · simp only [relayIf, apply]
    split <;> exact onBlock_record _ _ _ _
  · rfl
  · rfl
  · rfl

private theorem recordOwn_record {sp : AC.ACParams}
    (st : State sp binding) (o : Wire sp.n binding) (hs : List (Header Info × Nat)) :
    (recordOwn st o hs).node.record = st.node.record := by
  rw [recordOwn_eq]
  split
  · rfl
  · split
    · exact onBlock_record _ _ _ _
    · rfl
  · rfl

/-- Every canonical receipt handler preserves FG-store reachability. -/
theorem processOne_reachable {sp : AC.ACParams}
    (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp binding) (o : Wire sp.n binding)
    (h : st.node.fg.Reachable (goldilocksNode sp).genesisPayload) :
    (processOne io hs st o).node.fg.Reachable (goldilocksNode sp).genesisPayload := by
  rw [processOne_eq]
  split
  · simp only [relayIf, apply]
    split <;> exact onBlock_reachable _ _ _ _ h
  · exact h
  · exact h.tail (Or.inr ⟨_, rfl⟩)
  · exact h

private theorem recordOwn_reachable {sp : AC.ACParams}
    (st : State sp binding) (o : Wire sp.n binding) (hs : List (Header Info × Nat))
    (h : st.node.fg.Reachable (goldilocksNode sp).genesisPayload) :
    (recordOwn st o hs).node.fg.Reachable (goldilocksNode sp).genesisPayload := by
  rw [recordOwn_eq]
  split
  · exact h
  · split
    · exact onBlock_reachable _ _ _ _ h
    · exact h
  · exact h

private theorem client_run_append {n : Nat} (v : Fin n) (Λ : FG.Record)
    (inputs : List (FG.ChainState n)) (σ : FG.ChainState n) :
    FG.Record.run v Λ (inputs ++ [σ]) =
      match (FG.Record.run v Λ inputs).1.createAtt v σ with
      | none => FG.Record.run v Λ inputs
      | some (a, Λ') => (Λ', (FG.Record.run v Λ inputs).2 ++ [a]) := by
  induction inputs generalizing Λ with
  | nil =>
    cases h : Λ.createAtt v σ with
    | none => simp [FG.Record.run, h]
    | some p => cases p; simp [FG.Record.run, h]
  | cons x xs ih =>
    cases h : Λ.createAtt v x with
    | none => simp only [List.cons_append, FG.Record.run, h, ih]
    | some p =>
      rcases p with ⟨a, Λ'⟩
      simp only [List.cons_append, FG.Record.run, h, ih]
      split <;> rfl

private theorem fgUpdate_history {sp : AC.ACParams}
    (st : State sp binding)
    (release : Fin sp.n → Time → Bool)
    (hreach : st.node.fg.Reachable (goldilocksNode sp).genesisPayload)
    (inputs : List (FG.ChainState sp.n)) (hi : FG.EntryInputs sp.toParams.fg inputs)
    (hr : st.node.record = (FG.Record.run st.self FG.Record.empty inputs).1) :
    ∃ inputs' : List (FG.ChainState sp.n), FG.EntryInputs sp.toParams.fg inputs' ∧
      (fgUpdate st release).node.record = (FG.Record.run st.self FG.Record.empty inputs').1 ∧
      (FG.Record.run st.self FG.Record.empty inputs).2 ⊆
        (FG.Record.run st.self FG.Record.empty inputs').2 ∧
      (fgUpdate st release).node.fg.Reachable (goldilocksNode sp).genesisPayload := by
  simp only [fgUpdate_eq]
  split
  · exact ⟨inputs, hi, hr, fun _ h => h, hreach⟩
  · rename_i C hC
    split
    · exact ⟨inputs, hi, hr, fun _ h => h, hreach⟩
    · rename_i a Λ' ha
      let σ := st.node.fg.σ (st.node.fg.σ C.root).Th
      have hsign : st.node.record.createAtt st.self σ = some (a, Λ') := ha
      have hrun : FG.Record.run st.self FG.Record.empty (inputs ++ [σ]) =
          (Λ', (FG.Record.run st.self FG.Record.empty inputs).2 ++ [a]) := by
        rw [client_run_append, ← hr, hsign]
      refine ⟨inputs ++ [σ], ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hi x hx
        · obtain rfl := List.mem_singleton.mp hx
          exact Store.entry_input hreach _
      · rw [hrun]
        split <;> rfl
      · rw [hrun]
        exact List.subset_append_left _ _
      · split
        · exact hreach.tail (Or.inr ⟨a, rfl⟩)
        · exact hreach

private theorem process_record {sp : AC.ACParams}
    (st : State sp binding) (o : Wire sp.n binding) (hs : List (Header Info × Nat)) :
    (process st o hs).node.record = st.node.record := by
  rw [process_eq]
  generalize st.voteIO = io
  generalize delivered io hs st o = os
  induction os generalizing st with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, processOne_record]

private theorem process_reachable {sp : AC.ACParams}
    (st : State sp binding) (o : Wire sp.n binding) (hs : List (Header Info × Nat))
    (h : st.node.fg.Reachable (goldilocksNode sp).genesisPayload) :
    (process st o hs).node.fg.Reachable (goldilocksNode sp).genesisPayload := by
  rw [process_eq]
  generalize st.voteIO = io
  generalize delivered io hs st o = os
  induction os generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (processOne_reachable io hs st x h)

private def HasHistory {sp : AC.ACParams}
    (key : Fin sp.n) (st : State sp binding) (signed : FG.Att sp.n → Prop := fun _
        => False) : Prop :=
  st.self = key ∧ st.node.fg.Reachable (goldilocksNode sp).genesisPayload ∧
    ∃ inputs : List (FG.ChainState sp.n), FG.EntryInputs sp.toParams.fg inputs ∧
      st.node.record = (FG.Record.run key FG.Record.empty inputs).1 ∧
      ∀ a, signed a → a ∈ (FG.Record.run key FG.Record.empty inputs).2

private theorem history_recordOwn {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
        (o : Wire sp.n binding)
    (hs : List (Header Info × Nat)) : HasHistory key (recordOwn st o hs) signed := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  exact ⟨(recordOwn_self _ _ _).trans hk, recordOwn_reachable _ _ _ hr,
    ins, hi, (recordOwn_record _ _ _).trans he, hout⟩

private theorem history_poll {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
        (t : Time) (release : Fin sp.n → Time → Bool) :
    HasHistory key (poll st t release).1 signed := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  have hup : HasHistory key (fgUpdate st release) signed := by
    obtain ⟨ins', hi', hr', hsub, hreach⟩ := fgUpdate_history st release hr ins hi (hk ▸ he)
    refine ⟨?_, hreach, ins', hi', ?_, ?_⟩
    · exact (fgUpdate_self (release := release) st).trans hk
    · simpa only [hk] using hr'
    · intro a ha
      simpa only [hk] using hsub (by simpa only [hk] using hout a ha)
  simp only [poll]
  split <;> simp only <;> split
  · exact hup
  · exact ⟨hk, hr, ins, hi, he, hout⟩
  · exact hup
  · exact ⟨hk, hr, ins, hi, he, hout⟩

private theorem history_poll_sign {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
    (t : Time) (release : Fin sp.n → Time → Bool) (hdue : st.fgDue = true) {C}
    {a : FG.Att sp.n} {Λ'}
    (hC : (Node.acToFG st.node st.now).2.2 = some C)
    (ha : (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')) :
    HasHistory key (poll st t release).1 (fun b => signed b ∨ b = a) := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  let σ := st.node.fg.σ (st.node.fg.σ C.root).Th
  have hsign : st.node.record.createAtt st.self σ = some (a, Λ') := ha
  have hrun : FG.Record.run key FG.Record.empty (ins ++ [σ]) =
      (Λ', (FG.Record.run key FG.Record.empty ins).2 ++ [a]) := by
    rw [client_run_append, ← he, ← hk, hsign]
  have hup : HasHistory key (fgUpdate st release) (fun b => signed b ∨ b = a) := by
    refine ⟨(fgUpdate_self (release := release) st).trans hk, ?_, ins ++ [σ], ?_, ?_, ?_⟩
    · simp only [fgUpdate_eq, hC, ha]
      split
      · exact hr.tail (Or.inr ⟨a, rfl⟩)
      · exact hr
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx
      · obtain rfl := List.mem_singleton.mp hx
        exact Store.entry_input hr _
    · simp only [fgUpdate_eq, hC, ha, hrun]
      split <;> rfl
    · intro b hb
      rw [hrun]
      rcases hb with hb | rfl
      · exact List.mem_append_left _ (hout b hb)
      · exact List.mem_append_right _ (List.mem_singleton_self _)
  simp only [poll, hdue, ↓reduceIte]
  split <;> exact hup

/-- The flush of a batch poll keeps the history: it changes only `held` and the pool, through the
own `on_attestation`. -/
private theorem history_heldDrain {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed) :
    HasHistory key (heldDrain st) signed := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  have hreach : ∀ (l : List (FG.Att sp.n)) (n : NodeState (goldilocksNode sp)),
      n.fg.Reachable (goldilocksNode sp).genesisPayload →
      (l.foldl (fun n a => (Node.onAttestation n a).1) n).fg.Reachable
        (goldilocksNode sp).genesisPayload := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a l ih => exact fun n h => ih _ (h.tail (Or.inr ⟨a, rfl⟩))
  obtain ⟨atts, hd⟩ := heldDrain_eq st
  refine ⟨(heldDrain_self st).trans hk, ?_, ins, hi, ?_, hout⟩
  · rw [heldDrain_node]
    exact hreach _ _ hr
  · rw [hd]
    exact he

private theorem history_pollBatch {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
    (t : Time) (release : Fin sp.n → Time → Bool) :
    HasHistory key (pollBatch st t release).1 signed := by
  rw [pollBatch_fst]
  split
  · exact history_poll (history_heldDrain h) t release
  · exact history_poll h t release

private theorem history_pollBatch_sign {sp : AC.ACParams}
    {key : Fin sp.n}
    {st : State sp binding} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
    (t : Time) (release : Fin sp.n → Time → Bool) (hdue : st.fgDue = true) {C}
    {a : FG.Att sp.n} {Λ'}
    (hC : (Node.acToFG st.node st.now).2.2 = some C)
    (ha : (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')) :
    HasHistory key (pollBatch st t release).1 (fun b => signed b ∨ b = a) := by
  rw [pollBatch_fst]
  split
  · have h' := history_heldDrain h
    obtain ⟨atts, hd⟩ := heldDrain_eq st
    rw [hd] at h' ⊢
    exact history_poll_sign h' t release hdue hC ha
  · exact history_poll_sign h t release hdue hC ha

omit [DecidableEq V] in
private theorem history_release (key : Fin (Fintype.card V))
    {signed : FG.Att (Fintype.card V) → Prop} :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) cs,
      HasHistory key (nd.st.1 hn) signed →
      HasHistory key ((Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash key nd cs).1.st.1 hn) signed
  | nd, [], h => h
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · exact history_release key _ cs (history_recordOwn h c _)
    · exact history_release key nd cs h

omit [DecidableEq V] in
private theorem history_duty {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.dutyStep v nd d).1.st.1 hn) signed := by
  unfold Model.Run.dutyStep
  split
  · apply history_release
    cases d with
    | act s k => exact h
    | propose s hs =>
      change HasHistory _ (((goldilocks S (pubOf E)).propose nd.st.1 s).1 hn) signed
      rw [goldilocks_propose_eq S _ nd.st.1 s, dite_eq_left hn]
      change HasHistory _ (propose (nd.st.1 hn) s).1 signed
      obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
      refine ⟨(propose_self _ _).trans hk, ?_, ins, hi, ?_, hout⟩
      · rw [propose_eq]; dsimp only; split <;> exact hr
      · rw [propose_eq]; dsimp only; split <;> exact he
    | pollPropose t =>
      change HasHistory _ (((goldilocks S (pubOf E)).pollPropose nd.st.1 t).1 hn) signed
      rw [goldilocks_pollPropose_eq S _ nd.st.1 t, dite_eq_left hn]
      change HasHistory _ (nodeTick (nd.st.1 hn) (S.sign (pubOf E))) signed
      rw [nodeTick_eq (sign := _)]
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic (nd.st.1 hn).now
      · rw [ite_eq_left hp]; exact h
      · rw [ite_eq_right hp]; exact h
    | poll t =>
      change HasHistory _ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).1 hn) signed
      rw [goldilocks_pollBatch_eq S _ nd.st.1 t, dite_eq_left hn]
      exact history_pollBatch h _ _
  · exact h

omit [DecidableEq V] in
private theorem history_duties {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) ds
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.runDuties v nd ds).1.st.1 hn) signed := by
  unfold Model.Run.runDuties
  have hfold : ∀ (r : Model.Node (Model.protoOf (compiled (goldilocks S)) E) ×
      List (Model.protoOf (compiled (goldilocks S)) E).Object),
      HasHistory (rho.ownKey v) (r.1.st.1 hn) signed →
      HasHistory (rho.ownKey v)
        ((ds.foldl (fun r d => let s := rho.dutyStep v r.1 d;
          (s.1, r.2 ++ s.2)) r).1.st.1 hn) signed := by
    induction ds with
    | nil => exact fun _ h => h
    | cons d ds ih => exact fun r h => ih _ (history_duty S rho hn r.1 d h)
  exact hfold _ h

omit [DecidableEq V] in
private theorem history_tick {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.tick nd v t).1.st.1 hn) signed := by
  unfold Model.Run.tick
  split
  · apply history_release
    apply history_duties
    exact h
  · exact h

omit [DecidableEq V] in
private theorem history_deliver {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time) (o)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.deliver nd v o t).1.st.1 hn) signed := by
  unfold Model.Run.deliver
  apply history_release
  apply history_duties
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  exact ⟨(process_self _ _ _).trans hk, process_reachable _ _ _ hr,
    ins, hi, (process_record _ _ _).trans he, hout⟩

omit [DecidableEq V] in
private theorem history_restore {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v)
      (((Model.protoOf (compiled (goldilocks S)) E).restore (rho.ownKey v)
        ((Model.protoOf (compiled (goldilocks S)) E).durable nd.st) t).1 hn) signed := by
  obtain ⟨_, hr, ins, hi, he, hout⟩ := h
  exact ⟨rfl, hr, ins, hi, he, hout⟩

omit [DecidableEq V] in
private theorem history_initial (v : V) :
    HasHistory (rho.ownKey v) ((rho.initWorld v).st.1 hn) := by
  exact ⟨rfl, .refl, [], (by intro x hx; cases hx), rfl, (by simp)⟩

private theorem history_step (w : V → Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object) (v : V)
    {signed : FG.Att (Fintype.card V) → Prop}
    (h : HasHistory (rho.ownKey v) ((w v).st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.step w e v).st.1 hn) signed := by
  cases e with
  | tick u t =>
    by_cases heq : v = u
    · subst u
      simpa only [Model.Run.step, Function.update_self] using history_tick S rho hn (w v) t h
    · simpa only [Model.Run.step, Function.update_of_ne heq] using h
  | deliver u o t =>
    by_cases heq : v = u
    · subst u
      simpa only [Model.Run.step, Function.update_self] using history_deliver S rho hn (w v) t o h
    · simpa only [Model.Run.step, Function.update_of_ne heq] using h
  | restart u t =>
    by_cases heq : v = u
    · subst u
      simpa only [Model.Run.step, Function.update_self] using history_restore S rho hn (w v) t h
    · simpa only [Model.Run.step, Function.update_of_ne heq] using h

private theorem history_mono {sp : AC.ACParams}
    {key : Fin sp.n} {st : State sp binding}
    {p q : FG.Att sp.n → Prop} (h : HasHistory key st p) (hp : ∀ a, q a → p a) :
    HasHistory key st q := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  exact ⟨hk, hr, ins, hi, he, fun a ha => hout a (hp a ha)⟩

private def Signs (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (a : FG.Att (Fintype.card V)) : Prop
        :=
  ∃ k : Nat, d = .poll k ∧ rho.ownKey v ∈ rho.sel .poll ∧
    (nd.st.1 hn).fgDue = true ∧ ∃ C Λ',
      (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).2.2 = some C ∧
      (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.fg.attest
        (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.record (nd.st.1 hn).self C =
          some (a, Λ')

omit [DecidableEq V] in
private theorem history_duty_sign {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (d)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.dutyStep v nd d).1.st.1 hn)
      (fun a => signed a ∨ Signs S rho hn v nd d a) := by
  classical
  by_cases hex : ∃ a, Signs S rho hn v nd d a
  · obtain ⟨a, k, rfl, hsel, hdue, C, Λ', hC, ha⟩ := hex
    have hsign := history_pollBatch_sign h k (S.release (pubOf E)) hdue hC ha
    have hall : HasHistory (rho.ownKey v)
        ((rho.dutyStep v nd (.poll k)).1.st.1 hn) (fun b => signed b ∨ b = a) := by
      unfold Model.Run.dutyStep
      simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k)
          = .poll from rfl,
        hsel, ↓reduceIte]
      apply history_release
      change HasHistory _ (((goldilocks S (pubOf E)).pollBatch nd.st.1 k).1 hn) _
      rw [goldilocks_pollBatch_eq S _ nd.st.1 k, dite_eq_left hn]
      exact hsign
    apply history_mono hall
    intro b hb
    rcases hb with hb | ⟨k', hk', _, _, C', Λ'', hC', hb⟩
    · exact Or.inl hb
    · have heq : C' = C := Option.some.inj (hC'.symm.trans hC)
      subst C'
      exact Or.inr (congrArg Prod.fst (Option.some.inj (hb.symm.trans ha)))
  · apply history_mono (history_duty S rho hn nd d h)
    intro a ha
    exact ha.elim id (fun hs => False.elim (hex ⟨a, hs⟩))

omit [DecidableEq V] in
private theorem duties_append (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds ds') :
    (rho.runDuties v nd (ds ++ ds')).1 = (rho.runDuties v (rho.runDuties v nd ds).1 ds').1 := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => rfl
  | cons d ds' ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]

omit [DecidableEq V] in
private theorem history_duties_sign {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.runDuties v nd ds).1.st.1 hn)
      (fun a => signed a ∨ ∃ q d, ds[q]? = some d ∧
        Signs S rho hn v (rho.runDuties v nd (ds.take q)).1 d a) := by
  induction ds using List.reverseRecOn with
  | nil =>
    apply history_mono h
    intro a ha
    rcases ha with ha | ⟨q, d, hq, _⟩
    · exact ha
    · simp at hq
  | append_singleton ds d ih =>
    rw [duties_append]
    change HasHistory _ ((rho.dutyStep v (rho.runDuties v nd ds).1 d).1.st.1 hn) _
    apply history_mono (history_duty_sign S rho hn _ d ih)
    intro a ha
    rcases ha with ha | ⟨q, d', hq, hs⟩
    · exact Or.inl (Or.inl ha)
    · by_cases hlt : q < ds.length
      · have hq' : ds[q]? = some d' := by simpa [List.getElem?_append, hlt] using hq
        exact Or.inl (Or.inr ⟨q, d', hq', by
          simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using hs⟩)
      · have hbound : q < (ds ++ [d]).length := List.getElem?_eq_some_iff.mp hq |>.1
        have heq : q = ds.length := by
          simp only [List.length_append, List.length_singleton] at hbound
          omega
        subst q
        have hd : d' = d := by simpa using hq.symm
        subst d'
        exact Or.inr (by simpa using hs)

/-- An actual duty-prefix boundary after `p` duties of event `i`.
The tick prefix starts after clock/mempool installation, and the delivery prefix after processing
the object and adding it to `seen`. Prefixes use `rho.runDuties`, hence actual `rho.dutyStep`
effects and release guards, not an assumed node-handler replay. At `p = 0` this is the actual
post-clock/post-process state, NEVER the pre-event state. Restart has no duty prefix; its
record boundary is handled separately by `engine_event_signing_history`. -/
inductive EngineDutyCut (v : V) (i p : Nat) :
    Model.Node (Model.protoOf (compiled (goldilocks S)) E) → Prop where
  | tick {t : Time} (he : rho.events[i]? = some (.tick v t))
      (hw : E.awake v t = true)
      (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length) :
      EngineDutyCut v i p
        (rho.runDuties v
          ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
            (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
          (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1
  | deliver {t : Time} {o : (Model.protoOf (compiled (goldilocks S)) E).Object}
      (he : rho.events[i]? = some (.deliver v o t))
      (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).length) :
      EngineDutyCut v i p
        (rho.runDuties v
          ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
            (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
          (((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).take p)).1

/-- An attestation actually generated by the FG update of a scheduled poll. The index `p`
names that poll, not a simulated cut. The engine's poll selection must authorize this duty;
this explicit guard also fits the proposed selection-aware duty semantics. -/
def EngineSignsAt (v : V) (i p : Nat) (a : FG.Att (Fintype.card V)) : Prop :=
  ∃ nd, EngineDutyCut S rho v i p nd ∧
    ∃ k : Nat,
      ((∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
          ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
        ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
          ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k)) ∧
      rho.ownKey v ∈ rho.sel .poll ∧
      (nd.st.1 hn).fgDue = true ∧
      ∃ C Λ', (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).2.2 = some C ∧
        (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.fg.attest
          (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.record (nd.st.1 hn).self C =
            some (a, Λ')

/-- What an engine signing is (`EngineSignsAt`, unfolded). -/
theorem engineSignsAt_iff (v : V) (i p : Nat) (a : FG.Att (Fintype.card V)) :
    EngineSignsAt S rho hn v i p a ↔ ∃ nd, EngineDutyCut S rho v i p nd ∧
      ∃ k : Nat,
        ((∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
            ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
          ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
            ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k)) ∧
        rho.ownKey v ∈ rho.sel .poll ∧
        (nd.st.1 hn).fgDue = true ∧
        ∃ C Λ', (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).2.2 = some C ∧
          (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.fg.attest
            (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.record (nd.st.1 hn).self C =
              some (a, Λ') := Iff.rfl

private theorem signs_tick {v : V} {i q : Nat} {a : FG.Att (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hs : EngineSignsAt S rho hn v i q a) :
    ∃ d, ((Model.protoOf (compiled (goldilocks S)) E).duties t)[q]? = some d ∧
      Signs S rho hn v (rho.runDuties v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        (((Model.protoOf (compiled (goldilocks S)) E).duties t).take q)).1 d a := by
  obtain ⟨nd, hc, k, hk, hsel, hdue, C, Λ', hC, ha⟩ := hs
  cases hc with
  | tick he' hw hp =>
    have ht := Option.some.inj (he'.symm.trans he)
    cases ht
    rcases hk with ⟨t', he'', _, hlookup⟩ | ⟨t', o, he'', _⟩
    · cases Option.some.inj (he''.symm.trans he)
      exact ⟨.poll k, hlookup, k, rfl, hsel, hdue, C, Λ', hC, ha⟩
    · cases Option.some.inj (he''.symm.trans he)
  | deliver he' hp => cases Option.some.inj (he'.symm.trans he)

private theorem signs_deliver {v : V} {i q : Nat} {a : FG.Att (Fintype.card V)} {t : Time} {o}
    (he : rho.events[i]? = some (.deliver v o t)) (hs : EngineSignsAt S rho hn v i q a) :
    ∃ d, ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[q]? = some d ∧
      Signs S rho hn v (rho.runDuties v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
          (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
        (((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).take q)).1 d a := by
  obtain ⟨nd, hc, k, hk, hsel, hdue, C, Λ', hC, ha⟩ := hs
  cases hc with
  | tick he' hw hp => cases Option.some.inj (he'.symm.trans he)
  | deliver he' hp =>
    cases Option.some.inj (he'.symm.trans he)
    rcases hk with ⟨t', he'', _, _⟩ | ⟨t', o', he'', hlookup⟩
    · cases Option.some.inj (he''.symm.trans he)
    · cases Option.some.inj (he''.symm.trans he)
      exact ⟨.poll k, hlookup, k, rfl, hsel, hdue, C, Λ', hC, ha⟩

private theorem signs_event {v : V} {i q : Nat} {a : FG.Att (Fintype.card V)}
    (hs : EngineSignsAt S rho hn v i q a) :
    ∃ e, rho.events[i]? = some e ∧ e.node = v := by
  obtain ⟨nd, hc, _⟩ := hs
  cases hc with
  | tick he hw hp => exact ⟨_, he, rfl⟩
  | deliver he hp => exact ⟨_, he, rfl⟩

private theorem history_events (v : V) (i : Nat) :
    HasHistory (rho.ownKey v) ((rho.stateBefore i v).st.1 hn)
      (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
  induction i with
  | zero =>
    apply history_mono (history_initial S rho hn v)
    rintro a ⟨j, q, hj, _⟩
    omega
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      have hst : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp only [Model.Run.stateBefore, List.take_add_one, he, Option.toList_none,
          List.append_nil]
      rw [hst]
      apply history_mono ih
      rintro a ⟨j, q, hj, hs⟩
      refine ⟨j, q, ?_, hs⟩
      by_contra hnlt
      have : j = i := by omega
      subst j
      obtain ⟨e, he', _⟩ := signs_event S rho hn hs
      simp [he] at he'
    | some e =>
      rw [rho.stateBefore_succ he]
      by_cases hv : e.node = v
      · cases e with
        | tick u t =>
          change u = v at hv
          subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.tick]
          split
          · apply history_release
            apply history_mono (history_duties_sign S rho hn
              ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
                (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _ ih)
            rintro a ⟨j, q, hj, hs⟩
            by_cases hji : j < i
            · exact Or.inl ⟨j, q, hji, hs⟩
            · have : j = i := by omega
              subst j
              obtain ⟨d, hd, hsign⟩ := signs_tick S rho hn he hs
              exact Or.inr ⟨q, d, hd, hsign⟩
          · rename_i hw
            apply history_mono ih
            rintro a ⟨j, q, hj, hs⟩
            refine ⟨j, q, ?_, hs⟩
            by_contra hnlt
            have : j = i := by omega
            subst j
            obtain ⟨nd, hc, _⟩ := hs
            cases hc with
            | tick he' hw' hp =>
              cases Option.some.inj (he'.symm.trans he)
              exact hw hw'
            | deliver he' hp => cases Option.some.inj (he'.symm.trans he)
        | deliver u o t =>
          change u = v at hv
          subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver]
          apply history_release
          have hprocess : HasHistory (rho.ownKey v)
              (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
              (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
            obtain ⟨hk, hr, ins, hi, he', hout⟩ := ih
            exact ⟨(process_self _ _ _).trans hk, process_reachable _ _ _ hr,
              ins, hi, (process_record _ _ _).trans he', hout⟩
          apply history_mono (history_duties_sign S rho hn _ _ hprocess)
          rintro a ⟨j, q, hj, hs⟩
          by_cases hji : j < i
          · exact Or.inl ⟨j, q, hji, hs⟩
          · have : j = i := by omega
            subst j
            obtain ⟨d, hd, hsign⟩ := signs_deliver S rho hn he hs
            exact Or.inr ⟨q, d, hd, hsign⟩
        | restart u t =>
          change u = v at hv
          subst u
          simp only [Model.Run.step, Function.update_self]
          apply history_mono (history_restore S rho hn _ t ih)
          rintro a ⟨j, q, hj, hs⟩
          refine ⟨j, q, ?_, hs⟩
          by_contra hnlt
          have : j = i := by omega
          subst j
          obtain ⟨nd, hc, _⟩ := hs
          cases hc with
          | tick he' hw hp => cases Option.some.inj (he'.symm.trans he)
          | deliver he' hp => cases Option.some.inj (he'.symm.trans he)
      · apply history_mono (history_step S rho hn _ e v ih)
        rintro a ⟨j, q, hj, hs⟩
        refine ⟨j, q, ?_, hs⟩
        by_contra hnlt
        have : j = i := by omega
        subst j
        obtain ⟨e', he', hv'⟩ := signs_event S rho hn hs
        cases Option.some.inj (he'.symm.trans he)
        exact hv hv'

/-- The FG store at every engine event boundary is reachable, independently of wire validity. -/
theorem stateAt_fg_reachable (v : V) (i : Nat) :
    (stateAt S rho hn v i).node.fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn)).genesisPayload := by
  simpa only [stateAt_eq] using (history_events S rho hn v i).2.1

/-- **Implementation event-boundary history.** This is the pre-event
version of the duty-prefix invariant. Initial state has the empty record; clock, processing,
gossip and releases preserve it, and each actual selected poll's FG update appends its entry
input. Restart preserves the durable record. The event/duty induction uses neither execution
validity nor honesty; these interface arguments are retained for callers. -/
theorem engine_event_signing_history (_hv : rho.ExecutionValid) {v : V}
    (_hv' : v ∉ rho.faultyAt 0) (i : Nat) :
    ∃ inputs, FG.EntryInputs (S.params (pubOf E) hn).toParams.fg inputs ∧
      (stateAt S rho hn v i).node.record =
        (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).1 ∧
      ∀ j q a, j < i → EngineSignsAt S rho hn v j q a →
        a ∈ (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).2 := by
  rw [stateAt_eq]
  obtain ⟨_, _, ins, hi, hr, hout⟩ := history_events S rho hn v i
  exact ⟨ins, hi, hr, fun j q a hj hs => hout a ⟨j, q, hj, hs⟩⟩

/-- The event-boundary signing history (`engine_event_signing_history`) without its unused
interface arguments: every engine signing before event `i` is an output of a client run on entry
inputs. -/
private theorem engine_signing_history (v : V) (i : Nat) :
    ∃ inputs, FG.EntryInputs (S.params (pubOf E) hn).toParams.fg inputs ∧
      ∀ j q a, j < i → EngineSignsAt S rho hn v j q a →
        a ∈ (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).2 := by
  obtain ⟨_, _, ins, hi, -, hout⟩ := history_events S rho hn v i
  exact ⟨ins, hi, fun j q a hj hs => hout a ⟨j, q, hj, hs⟩⟩

private theorem run_wellFormed {P : Params} {v : Fin P.n} :
    ∀ (inputs : List (FG.ChainState P.n)) (Λ : FG.Record), FG.EntryInputs P.fg inputs →
      ∀ a ∈ (FG.Record.run v Λ inputs).2, a.WellFormed
  | [], _, _, a, ha => by simp [FG.Record.run] at ha
  | σe :: rest, Λ, hi, a, ha => by
    have hrest : FG.EntryInputs P.fg rest := fun x hx => hi x (List.mem_cons_of_mem _ hx)
    simp only [FG.Record.run] at ha
    split at ha
    · exact run_wellFormed rest Λ hrest a ha
    · rename_i a' Λ' hc
      rcases List.mem_cons.mp ha with rfl | ha
      · obtain ⟨h1, h2, h3⟩ := hi σe List.mem_cons_self
        exact Compose.createAtt_wellFormed h1 h2 h3 hc
      · exact run_wellFormed rest Λ' hrest a ha

/-- An attestation an engine poll signs is well-formed: it is an output of the node's client run
on entry inputs (`engine_signing_history`). -/
theorem engineSignsAt_wellFormed {v : V} {j q : Nat} {a : FG.Att (Fintype.card V)}
    (hs : EngineSignsAt S rho hn v j q a) : a.WellFormed := by
  obtain ⟨ins, hi, hout⟩ := engine_signing_history S rho hn v (j + 1)
  exact run_wellFormed (P := (S.params (pubOf E) hn).toParams) ins _ hi a
    (hout j q a (Nat.lt_succ_self j) hs)

private theorem emitted_no_att {sp : AC.ACParams}
    (io : VoteAuth sp.n binding)
    (cs : List (Cut (goldilocksNode sp))) (a : WireAtt) :
    Body.att a ∉ emitted io cs := by
  simp only [emitted, List.mem_flatMap]
  rintro ⟨c, _, hc⟩
  cases c with
  | fg _ => exact List.not_mem_nil hc
  | ac l =>
    obtain ⟨e, _, he⟩ := List.mem_filterMap.mp hc
    cases ownToken io e.msg <;> simp at he

private theorem apply_att {sp : AC.ACParams}
    (st : State sp binding)
    (origin) (r) (a : WireAtt) :
    Body.att a ∈ (apply st origin r).outbox ↔ Body.att a ∈ st.outbox := by
  simp only [apply, List.mem_append, emitted_no_att, or_false]

private theorem processOne_att {sp : AC.ACParams}
    (io) (hs) (st : State sp binding) (o)
        (a : WireAtt) :
    Body.att a ∈ (processOne io hs st o).outbox ↔ Body.att a ∈ st.outbox := by
  rw [processOne_eq]
  split
  · simp only [relayIf]
    split <;> exact apply_att st none _ a
  · exact apply_att st (some o) _ a
  · exact apply_att st none _ a
  · rfl

private theorem recordOwn_att {sp : AC.ACParams}
    (st : State sp binding) (o) (hs)
        (a : WireAtt) :
    Body.att a ∈ (recordOwn st o hs).outbox ↔ Body.att a ∈ st.outbox := by
  rw [recordOwn_eq]
  split
  · rfl
  · split
    · exact apply_att _ _ _ _
    · rfl
  · rfl

private theorem process_att {sp : AC.ACParams}
    (st : State sp binding) (o) (hs)
        (a : WireAtt) :
    Body.att a ∈ (process st o hs).outbox ↔ Body.att a ∈ st.outbox := by
  rw [process_eq]
  generalize st.voteIO = io
  generalize delivered io hs st o = os
  induction os generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, processOne_att]

private theorem propose_att {sp : AC.ACParams}
    (st : State sp binding) (s) (a : WireAtt) :
    Body.att a ∈ (propose st s).1.outbox ↔ Body.att a ∈ st.outbox := by
  rw [propose_eq]
  dsimp only
  split <;> rfl

private theorem nodeTick_att {sp : AC.ACParams}
    (st : State sp binding) (a : WireAtt)
    {sign : Fin sp.n → Time → Bool} :
    Body.att a ∈ (nodeTick st sign).outbox ↔ Body.att a ∈ st.outbox := by
  rw [nodeTick_eq (sign := _)]
  split
  · exact apply_att st none _ a
  · rfl

private theorem restore_att {sp : AC.ACParams}
    (st : State sp binding) (k t) (a : WireAtt) :
    Body.att a ∈ (restore k st t).outbox ↔ Body.att a ∈ st.outbox := by
  rw [restore_eq]
  exact apply_att { st with self := k, now := t } none _ a

theorem createAtt_val {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σ : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σ = some (a, Λ')) : a.val = v := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    rfl

/-- Every attestation body queued in `outbox`, and every attestation in `held`, is the node's
own and satisfies `signed`. -/
private def Queued {sp : AC.ACParams}
    (st : State sp binding) (signed : FG.Att sp.n → Prop) : Prop :=
  (∀ w, Body.att w ∈ st.outbox → ∃ a, w = encodeAtt a ∧ a.val = st.self ∧ signed a) ∧
    ∀ a ∈ st.held, a.val = st.self ∧ signed a

private theorem poll_queued {sp : AC.ACParams}
    (st : State sp binding) (t : Time)
    (release : Fin sp.n → Time → Bool) {signed : FG.Att sp.n → Prop} (h : Queued st signed) :
    let p := fun a => signed a ∨ st.fgDue = true ∧ ∃ C Λ',
      (Node.acToFG st.node st.now).2.2 = some C ∧
      (Node.acToFG st.node st.now).1.fg.attest
        (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')
    Queued (poll st t release).1 p ∧ ∀ w cs, (poll st t release).2 = some (.att w, cs) →
      ∃ a, w = encodeAtt a ∧ cs = [] ∧ a.val = st.self ∧ p a := by
  dsimp only
  let p := fun a => signed a ∨ st.fgDue = true ∧ ∃ C Λ',
    (Node.acToFG st.node st.now).2.2 = some C ∧
    (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')
  have hold : Queued st p :=
    ⟨fun w hw => (h.1 w hw).imp fun _ ⟨hw, hv, hs⟩ => ⟨hw, hv, Or.inl hs⟩,
      fun a ha => ⟨(h.2 a ha).1, Or.inl (h.2 a ha).2⟩⟩
  have hpre : Queued (if st.fgDue then fgUpdate st release else st) p := by
    split
    · rename_i hd
      simp only [fgUpdate_eq st release]
      split
      · exact hold
      · rename_i C hC
        split
        · exact hold
        · rename_i a Λ' ha
          have hfresh : p a := Or.inr ⟨hd, C, Λ', hC, ha⟩
          split
          · refine ⟨fun w hw => ?_, hold.2⟩
            rcases List.mem_append.mp hw with hw | hw
            · exact hold.1 w hw
            · have hw' : w = encodeAtt a := Body.att.inj (List.mem_singleton.mp hw)
              exact ⟨a, hw', createAtt_val ha, hfresh⟩
          · refine ⟨hold.1, fun b hb => ?_⟩
            rcases List.mem_append.mp hb with hb | hb
            · exact hold.2 b hb
            · obtain rfl := List.mem_singleton.mp hb
              exact ⟨createAtt_val ha, hfresh⟩
    · exact hold
  have hself : (if st.fgDue then fgUpdate st release else st).self = st.self := by
    split
    · exact fgUpdate_self (release := release) st
    · rfl
  simp only [poll]
  split
  · exact ⟨⟨hpre.1, fun a ha => (hpre.2 a ha)⟩, by intro w cs he; cases he⟩
  · rename_i b rest he
    constructor
    · exact ⟨fun w hw => hpre.1 w (by rw [he]; exact List.mem_cons_of_mem b hw), hpre.2⟩
    · intro w cs hp
      cases hp
      obtain ⟨a, hw, hv, hs⟩ := hpre.1 w (by rw [he]; exact List.mem_cons_self)
      exact ⟨a, hw, rfl, hv.trans hself, hs⟩

private theorem queued_mono {sp : AC.ACParams}
    {st : State sp binding}
    {p q : FG.Att sp.n → Prop} (h : Queued st p) (hp : ∀ a, p a → q a) : Queued st q :=
  ⟨fun w hw => (h.1 w hw).imp fun a ⟨he, hv, ha⟩ => ⟨he, hv, hp a ha⟩,
    fun a ha => ⟨(h.2 a ha).1, hp a (h.2 a ha).2⟩⟩

/-- **The batch poll's attestation candidates.** Every attestation body a batch poll emits, its
ordinary emission or a flushed held attestation, is the node's own and either satisfied `signed`
before the poll or was generated by this poll's FG update; the queues it leaves keep the same
property. Forwarding and vote envelopes are not attestation bodies. -/
private theorem pollBatch_queued {sp : AC.ACParams}
    (st : State sp binding) (t : Time)
    (release : Fin sp.n → Time → Bool) {signed : FG.Att sp.n → Prop} (h : Queued st signed) :
    let p := fun a => signed a ∨ st.fgDue = true ∧ ∃ C Λ',
      (Node.acToFG st.node st.now).2.2 = some C ∧
      (Node.acToFG st.node st.now).1.fg.attest
        (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')
    Queued (pollBatch st t release).1 p ∧ ∀ w cs, (Body.att w, cs) ∈ (pollBatch st t release).2 →
      ∃ a, w = encodeAtt a ∧ cs = [] ∧ a.val = st.self ∧ p a := by
  dsimp only
  have hsig : ∀ (u : State sp binding) a, (∃ C Λ', (Node.acToFG u.node u.now).2.2 = some C ∧
      (Node.acToFG u.node u.now).1.fg.attest (Node.acToFG u.node u.now).1.record u.self C =
        some (a, Λ')) ↔ fgSigned u = some a := by
    intro u a
    rw [fgSigned_eq]
    constructor
    · rintro ⟨C, Λ', hC, ha⟩
      simp [hC, ha]
    · intro h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨C, hC, ⟨a', Λ'⟩, ha, rfl⟩ := h
      exact ⟨C, Λ', hC, ha⟩
  set st₀ := if (release st.self st.now && st.ticked) = true then heldDrain st else st with hst₀
  have hflush : Queued st₀ signed := by
    rw [hst₀]
    split
    · refine ⟨?_, fun _ ha => absurd (heldDrain_held st ▸ ha) List.not_mem_nil⟩
      rw [heldDrain_outbox, heldDrain_self]
      exact h.1
    · exact h
  have hfields : st₀.self = st.self ∧ st₀.fgDue = st.fgDue ∧ fgSigned st₀ = fgSigned st := by
    rw [hst₀]
    split
    · exact ⟨heldDrain_self st, heldDrain_fgDue st, fgSigned_heldDrain st⟩
    · exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hself, hdue, hfg⟩ := hfields
  have hpoll := poll_queued st₀ t release hflush
  have himp : ∀ a, (signed a ∨ st₀.fgDue = true ∧ ∃ C Λ',
      (Node.acToFG st₀.node st₀.now).2.2 = some C ∧
      (Node.acToFG st₀.node st₀.now).1.fg.attest
        (Node.acToFG st₀.node st₀.now).1.record st₀.self C = some (a, Λ')) →
      signed a ∨ st.fgDue = true ∧ ∃ C Λ',
      (Node.acToFG st.node st.now).2.2 = some C ∧
      (Node.acToFG st.node st.now).1.fg.attest
        (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ') := by
    rintro a (hs | ⟨hd, hx⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hdue ▸ hd, (hsig st a).2 (hfg ▸ (hsig st₀ a).1 hx)⟩
  refine ⟨?_, fun w cs hm => ?_⟩
  · rw [pollBatch_fst]
    exact queued_mono hpoll.1 himp
  rw [pollBatch_snd] at hm
  simp only [List.mem_append] at hm
  rcases hm with ((hm | hm) | hm) | hm
  · obtain ⟨a, hw, hcs, hv, ha⟩ := hpoll.2 w cs (Option.mem_toList.mp hm)
    exact ⟨a, hw, hcs, hv.trans hself, himp a ha⟩
  · obtain ⟨_, _, he⟩ := List.mem_map.mp hm
    cases he
  · obtain ⟨_, _, he⟩ := List.mem_map.mp hm
    cases he
  · split at hm
    · obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
      obtain ⟨hw, rfl⟩ := Prod.mk.inj he
      exact ⟨a, (Body.att.inj hw).symm, rfl, (h.2 a ha).1, Or.inl (h.2 a ha).2⟩
    · exact absurd hm List.not_mem_nil

/-- A step that keeps the key and the held queue and queues no new attestation body keeps
`Queued`. -/
private theorem queued_transfer {sp : AC.ACParams}
    {st st' : State sp binding}
    {p : FG.Att sp.n → Prop} (hs : st'.self = st.self)
    (ho : ∀ w, Body.att w ∈ st'.outbox → Body.att w ∈ st.outbox) (hh : st'.held = st.held)
    (h : Queued st p) : Queued st' p :=
  ⟨fun w hw => (h.1 w (ho w hw)).imp fun _ ⟨he, hv, ha⟩ => ⟨he, hv.trans hs.symm, ha⟩,
    fun a ha => ⟨(h.2 a (hh ▸ ha)).1.trans hs.symm, (h.2 a (hh ▸ ha)).2⟩⟩

omit [DecidableEq V] in
private theorem queued_release (key : Fin (Fintype.card V))
    {signed : FG.Att (Fintype.card V) → Prop} :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) cs,
      Queued (nd.st.1 hn) signed →
      Queued ((Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash key nd cs).1.st.1 hn) signed
  | nd, [], h => h
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · exact queued_release key _ cs (queued_transfer (recordOwn_self _ _ _)
        (fun w => (recordOwn_att _ _ _ w).mp) (recordOwn_held _ _ _) h)
    · exact queued_release key nd cs h

omit [DecidableEq V] in
private theorem queued_duty {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (d)
    (h : Queued (nd.st.1 hn) signed) :
    Queued ((rho.dutyStep v nd d).1.st.1 hn)
      (fun a => signed a ∨ Signs S rho hn v nd d a) := by
  unfold Model.Run.dutyStep
  split
  · rename_i hsel
    apply queued_release
    cases d with
    | act s k => exact queued_mono h fun _ ha => Or.inl ha
    | propose s hs =>
      change Queued (((goldilocks S (pubOf E)).propose nd.st.1 s).1 hn) _
      rw [goldilocks_propose_eq S _ nd.st.1 s, dite_eq_left hn]
      exact queued_mono (queued_transfer (propose_self _ s) (fun w => (propose_att _ s w).mp)
        (propose_held _ s) h) fun _ ha => Or.inl ha
    | pollPropose t =>
      change Queued (((goldilocks S (pubOf E)).pollPropose nd.st.1 t).1 hn) _
      rw [goldilocks_pollPropose_eq S _ nd.st.1 t, dite_eq_left hn]
      exact queued_mono (queued_transfer (nodeTick_self _) (fun w => (nodeTick_att _ w).mp)
        (nodeTick_held _) h) fun _ ha => Or.inl ha
    | poll t =>
      change Queued (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).1 hn) _
      rw [goldilocks_pollBatch_eq S _ nd.st.1 t, dite_eq_left hn]
      apply queued_mono (pollBatch_queued (nd.st.1 hn) t (S.release (pubOf E)) h).1
      intro a ha
      rcases ha with ha | ⟨hd, C, Λ', hC, ha⟩
      · exact Or.inl ha
      · exact Or.inr ⟨t, rfl, hsel, hd, C, Λ', hC, ha⟩
  · exact queued_mono h (fun _ ha => Or.inl ha)

omit [DecidableEq V] in
private theorem queued_duties {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (h : Queued (nd.st.1 hn) signed) :
    Queued ((rho.runDuties v nd ds).1.st.1 hn)
      (fun a => signed a ∨ ∃ q d, ds[q]? = some d ∧
        Signs S rho hn v (rho.runDuties v nd (ds.take q)).1 d a) := by
  induction ds using List.reverseRecOn with
  | nil => exact queued_mono h (fun _ ha => Or.inl ha)
  | append_singleton ds d ih =>
    rw [duties_append]
    change Queued ((rho.dutyStep v (rho.runDuties v nd ds).1 d).1.st.1 hn) _
    apply queued_mono (queued_duty S rho hn _ d ih)
    intro a ha
    rcases ha with (ha | ⟨q, d', hq, hs⟩) | hs
    · exact Or.inl ha
    · have hlt : q < ds.length := List.getElem?_eq_some_iff.mp hq |>.1
      refine Or.inr ⟨q, d', ?_, ?_⟩
      · simpa [List.getElem?_append, hlt] using hq
      · simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using hs
    · exact Or.inr ⟨ds.length, d, by simp, by simpa using hs⟩

private theorem signs_of_tick {v : V} {i q : Nat} {t : Time} {d} {a}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hd : ((Model.protoOf (compiled (goldilocks S)) E).duties t)[q]? = some d)
    (hs : Signs S rho hn v (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take q)).1 d a) :
    EngineSignsAt S rho hn v i q a := by
  obtain ⟨k, rfl, hsel, hdue, C, Λ', hC, ha⟩ := hs
  exact ⟨_, .tick he hw (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1),
    k, Or.inl ⟨t, he, hw, hd⟩, hsel, hdue, C, Λ', hC, ha⟩

private theorem signs_of_deliver {v : V} {i q : Nat} {t : Time} {o d a}
    (he : rho.events[i]? = some (.deliver v o t))
    (hd : ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[q]? = some d)
    (hs : Signs S rho hn v (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
      (((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).take q)).1 d a) :
    EngineSignsAt S rho hn v i q a := by
  obtain ⟨k, rfl, hsel, hdue, C, Λ', hC, ha⟩ := hs
  exact ⟨_, .deliver he (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1),
    k, Or.inr ⟨t, o, he, hd⟩, hsel, hdue, C, Λ', hC, ha⟩

private theorem queued_before (v : V) (i : Nat) :
    Queued ((rho.stateBefore i v).st.1 hn)
      (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
  induction i with
  | zero => constructor <;> intro _ h <;> cases h
  | succ i ih =>
    have hold : ∀ a, (∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) →
        ∃ j q, j < i + 1 ∧ EngineSignsAt S rho hn v j q a := by
      rintro a ⟨j, q, hj, hs⟩
      exact ⟨j, q, by omega, hs⟩
    cases he : rho.events[i]? with
    | none =>
      have hst : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp only [Model.Run.stateBefore, List.take_add_one, he, Option.toList_none,
          List.append_nil]
      rw [hst]
      exact queued_mono ih hold
    | some e =>
      rw [rho.stateBefore_succ he]
      cases e with
      | tick u t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.tick]
          split
          · rename_i hw
            apply queued_release
            apply queued_mono (queued_duties S rho hn
              ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
                (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _ ih)
            rintro a (ha | ⟨q, d, hd, hs⟩)
            · exact hold a ha
            · exact ⟨i, q, by omega, signs_of_tick S rho hn he hw hd hs⟩
          · exact queued_mono ih hold
        · simpa only [Model.Run.step, Function.update_of_ne hu] using queued_mono ih hold
      | deliver u o t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver]
          apply queued_release
          have hprocess : Queued
              (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
              (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) :=
            queued_transfer (process_self _ _ _) (fun w => (process_att _ _ _ w).mp)
              (process_held _ _ _) ih
          apply queued_mono (queued_duties S rho hn
            ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
              (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hprocess)
          rintro a (ha | ⟨q, d, hd, hs⟩)
          · exact hold a ha
          · exact ⟨i, q, by omega, signs_of_deliver S rho hn he hd hs⟩
        · simpa only [Model.Run.step, Function.update_of_ne hu] using queued_mono ih hold
      | restart u t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self]
          refine ⟨fun w hw => ?_, fun a ha => ?_⟩
          · obtain ⟨a, he', hv, ha⟩ := ih.1 w ((restore_att _ _ _ _).mp hw)
            exact ⟨a, he', hv.trans (history_events S rho hn v i).1, hold a ha⟩
          · obtain ⟨hv, ha⟩ := ih.2 a ((restore_held _ _ _) ▸ ha)
            exact ⟨hv.trans (history_events S rho hn v i).1, hold a ha⟩
        · simpa only [Model.Run.step, Function.update_of_ne hu] using queued_mono ih hold

/-- The node key at an actual duty boundary is its own engine key. -/
theorem cut_self {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) : (nd.st.1 hn).self = rho.ownKey v := by
  have h := history_events S rho hn v i
  cases hc with
  | tick he hw hp =>
    rename_i t
    exact (history_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _ h).1
  | deliver he hp =>
    rename_i t o
    have hh : HasHistory (rho.ownKey v)
        (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
        (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
      obtain ⟨hk, hr, ins, hi, he', hout⟩ := h
      exact ⟨(process_self _ _ _).trans hk, process_reachable _ _ _ hr,
        ins, hi, (process_record _ _ _).trans he', hout⟩
    exact (history_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hh).1

/-- At an actual duty boundary after `p` duties of event `i`, every queued attestation body
and every held attestation is the node's own and was generated by an engine signing at an
earlier duty: at an earlier event, or at one of the first `p` duties of event `i`. -/
private theorem queued_cut {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) :
    Queued (nd.st.1 hn) (fun a => ∃ j q, (j < i ∨ j = i ∧ q < p) ∧
      EngineSignsAt S rho hn v j q a) := by
  cases hc with
  | tick he hw hp =>
    rename_i t
    apply queued_mono (queued_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
      (queued_before S rho hn v i))
    rintro a (⟨j, q, hj, ha⟩ | ⟨q, d, hd, ha⟩)
    · exact ⟨j, q, Or.inl hj, ha⟩
    · have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at ha
      exact ⟨i, q, Or.inr ⟨rfl, hq⟩, signs_of_tick S rho hn he hw hd ha⟩
  | deliver he hp =>
    rename_i t o
    have hproc : Queued
        (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
        (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) :=
      queued_transfer (process_self _ _ _) (fun w => (process_att _ _ _ w).mp)
        (process_held _ _ _) (queued_before S rho hn v i)
    apply queued_mono (queued_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hproc)
    rintro a (⟨j, q, hj, ha⟩ | ⟨q, d, hd, ha⟩)
    · exact ⟨j, q, Or.inl hj, ha⟩
    · have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at ha
      exact ⟨i, q, Or.inr ⟨rfl, hq⟩, signs_of_deliver S rho hn he hd ha⟩

/-- **A held attestation was generated at a strictly earlier duty.** Every attestation the node
holds at an actual duty boundary after `p` duties of event `i` is its own, and was generated by
an engine signing at an earlier event or at one of the first `p` duties of event `i`. -/
theorem engine_held_att_signed {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {a : FG.Att (Fintype.card V)}
    (hm : a ∈ (nd.st.1 hn).held) :
    a.val = (nd.st.1 hn).self ∧ ∃ j q, (j < i ∨ j = i ∧ q < p) ∧
      EngineSignsAt S rho hn v j q a :=
  (queued_cut S rho hn hc).2 a hm

/-- A scheduled poll's ordinary attestation candidate comes from an engine signing,
including an attestation created by this poll's own FG update. -/
theorem engine_poll_att_signed {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k (S.release (pubOf E))).2 = some (.att w, cs)) :
    ∃ a j q, w = encodeAtt a ∧ a.val = (nd.st.1 hn).self ∧
      EngineSignsAt S rho hn v j q a := by
  have hq : Queued (nd.st.1 hn) (fun a => ∃ j q, EngineSignsAt S rho hn v j q a) :=
    queued_mono (queued_cut S rho hn hc) fun _ ⟨j, q, _, ha⟩ => ⟨j, q, ha⟩
  obtain ⟨a, he, -, hv, ha⟩ := (poll_queued (nd.st.1 hn) k (S.release (pubOf E)) hq).2 w cs hm
  rcases ha with ⟨j, q, ha⟩ | ⟨hdue, C, Λ', hC, ha⟩
  · exact ⟨a, j, q, he, hv, ha⟩
  · exact ⟨a, i, p, he, hv, nd, hc, k, hd, hsel, hdue, C, Λ', hC, ha⟩

/-- **Generation before release, per candidate.** Every attestation body a scheduled poll's batch
emits, whether its ordinary emission from the outbox or a held attestation it flushes, carries
nothing and is the node's own attestation `a`, generated by an engine signing: possibly this
poll's own FG update, which runs before the batch is read. -/
theorem engine_batch_att_signed {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (Body.att w, cs) ∈ (pollBatch (nd.st.1 hn) k (S.release (pubOf E))).2) :
    ∃ a j q, w = encodeAtt a ∧ cs = [] ∧ a.val = (nd.st.1 hn).self ∧
      EngineSignsAt S rho hn v j q a := by
  have hq : Queued (nd.st.1 hn) (fun a => ∃ j q, EngineSignsAt S rho hn v j q a) :=
    queued_mono (queued_cut S rho hn hc) fun _ ⟨j, q, _, ha⟩ => ⟨j, q, ha⟩
  obtain ⟨a, he, hcs, hv, ha⟩ :=
    (pollBatch_queued (nd.st.1 hn) k (S.release (pubOf E)) hq).2 w cs hm
  rcases ha with ⟨j, q, ha⟩ | ⟨hdue, C, Λ', hC, ha⟩
  · exact ⟨a, j, q, he, hcs, hv, ha⟩
  · exact ⟨a, i, p, he, hcs, hv, nd, hc, k, hd, hsel, hdue, C, Λ', hC, ha⟩

end Consensus.Goldilocks.Simulation
end
