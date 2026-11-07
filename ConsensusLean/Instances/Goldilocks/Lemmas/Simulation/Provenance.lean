module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Engine signing history before node simulation

Implementation-refinement history for the obligations skeleton. These declarations use
actual engine duty prefixes, never `eventCuts`, `simTrace`, or `GoldilocksRun`. A poll's FG update
is the only signing operation; all other operations preserve the client history, including
restart. Queue provenance and unforgeability give the inverse from seen attestations to signings.

The paper's G0.5 supplies client safety, not the correspondence between engine execution and
client inputs. The latter and the release provenance obligations below have NO PAPER PROOF.
-/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

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

private theorem processOne_record {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n) :
    (processOne hs st o).node.record = st.node.record := by
  unfold processOne
  split
  · simp only [relayIf, apply]
    split <;> exact onBlock_record _ _ _ _
  · rfl
  · rfl
  · rfl

private theorem recordOwn_record {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    (recordOwn st o hs).node.record = st.node.record := by
  unfold recordOwn
  split
  · rfl
  · split
    · exact onBlock_record _ _ _ _
    · rfl
  · rfl

/-- Every canonical receipt handler preserves FG-store reachability. -/
theorem processOne_reachable {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    (h : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload) :
    (processOne hs st o).node.fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  unfold processOne
  split
  · simp only [relayIf, apply]
    split <;> exact onBlock_reachable _ _ _ _ h
  · exact h
  · exact h.tail (Or.inr ⟨_, rfl⟩)
  · exact h

private theorem recordOwn_reachable {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat))
    (h : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload) :
    (recordOwn st o hs).node.fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  unfold recordOwn
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

private theorem fgUpdate_history {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (hreach : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload)
    (inputs : List (FG.ChainState sp.n)) (hi : FG.EntryInputs sp.toParams.fg inputs)
    (hr : st.node.record = (FG.Record.run st.self FG.Record.empty inputs).1) :
    ∃ inputs' : List (FG.ChainState sp.n), FG.EntryInputs sp.toParams.fg inputs' ∧
      (fgUpdate st).node.record = (FG.Record.run st.self FG.Record.empty inputs').1 ∧
      (FG.Record.run st.self FG.Record.empty inputs).2 ⊆
        (FG.Record.run st.self FG.Record.empty inputs').2 ∧
      (fgUpdate st).node.fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  simp only [fgUpdate]
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
        rfl
      · rw [hrun]
        exact List.subset_append_left _ _
      · exact hreach.tail (Or.inr ⟨a, rfl⟩)

private theorem process_record {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    (process st o hs).node.record = st.node.record := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, processOne_record]

private theorem process_reachable {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat))
    (h : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload) :
    (process st o hs).node.fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (processOne_reachable _ _ _ h)

private def HasHistory {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (key : Fin sp.n) (st : State sp ro) (signed : FG.Att sp.n → Prop := fun _ => False) : Prop :=
  st.self = key ∧ st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload ∧
    ∃ inputs : List (FG.ChainState sp.n), FG.EntryInputs sp.toParams.fg inputs ∧
      st.node.record = (FG.Record.run key FG.Record.empty inputs).1 ∧
      ∀ a, signed a → a ∈ (FG.Record.run key FG.Record.empty inputs).2

private theorem history_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {key : Fin sp.n}
    {st : State sp ro} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed) (o : Wire sp.n)
    (hs : List (Header Info × Nat)) : HasHistory key (recordOwn st o hs) signed := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  exact ⟨(recordOwn_self _ _ _).trans hk, recordOwn_reachable _ _ _ hr,
    ins, hi, (recordOwn_record _ _ _).trans he, hout⟩

private theorem history_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {key : Fin sp.n}
    {st : State sp ro} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed) (t : Time) :
    HasHistory key (poll st t).1 signed := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  have hup : HasHistory key (fgUpdate st) signed := by
    obtain ⟨ins', hi', hr', hsub, hreach⟩ := fgUpdate_history st hr ins hi (hk ▸ he)
    refine ⟨?_, hreach, ins', hi', ?_, ?_⟩
    · exact (fgUpdate_self st).trans hk
    · simpa only [hk] using hr'
    · intro a ha
      simpa only [hk] using hsub (by simpa only [hk] using hout a ha)
  simp only [poll]
  split <;> simp only <;> split
  · exact hup
  · exact ⟨hk, hr, ins, hi, he, hout⟩
  · exact hup
  · exact ⟨hk, hr, ins, hi, he, hout⟩

private theorem history_poll_sign {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {key : Fin sp.n}
    {st : State sp ro} {signed : FG.Att sp.n → Prop} (h : HasHistory key st signed)
    (t : Time) (hdue : st.fgDue = true) {C} {a : FG.Att sp.n} {Λ'}
    (hC : (Node.acToFG st.node st.now).2.2 = some C)
    (ha : (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')) :
    HasHistory key (poll st t).1 (fun b => signed b ∨ b = a) := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  let σ := st.node.fg.σ (st.node.fg.σ C.root).Th
  have hsign : st.node.record.createAtt st.self σ = some (a, Λ') := ha
  have hrun : FG.Record.run key FG.Record.empty (ins ++ [σ]) =
      (Λ', (FG.Record.run key FG.Record.empty ins).2 ++ [a]) := by
    rw [client_run_append, ← he, ← hk, hsign]
  have hup : HasHistory key (fgUpdate st) (fun b => signed b ∨ b = a) := by
    refine ⟨(fgUpdate_self st).trans hk, ?_, ins ++ [σ], ?_, ?_, ?_⟩
    · simp only [fgUpdate, hC, ha]
      exact hr.tail (Or.inr ⟨a, rfl⟩)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx
      · obtain rfl := List.mem_singleton.mp hx
        exact Store.entry_input hr _
    · simp only [fgUpdate, hC, ha, hrun]
      rfl
    · intro b hb
      rw [hrun]
      rcases hb with hb | rfl
      · exact List.mem_append_left _ (hout b hb)
      · exact List.mem_append_right _ (List.mem_singleton_self _)
  simp only [poll, hdue, ↓reduceIte]
  split <;> exact hup

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
    | act s k => exact k.elim
    | propose s hs =>
      change HasHistory _ (((goldilocks S (pubOf E)).propose nd.st.1 s).1 hn) signed
      simp only [goldilocks, dite_eq_left hn]
      change HasHistory _ (propose (nd.st.1 hn) s).1 signed
      obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
      refine ⟨(propose_self _ _).trans hk, ?_, ins, hi, ?_, hout⟩
      · unfold propose; dsimp only; split <;> exact hr
      · unfold propose; dsimp only; split <;> exact he
    | pollPropose t =>
      change HasHistory _ (((goldilocks S (pubOf E)).pollPropose nd.st.1 t).1 hn) signed
      simp only [goldilocks, dite_eq_left hn]
      change HasHistory _ (nodeTick (nd.st.1 hn)) signed
      unfold nodeTick
      split <;> exact h
    | poll t =>
      change HasHistory _ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).1 hn) signed
      simp only [goldilocks, dite_eq_left hn]
      change HasHistory _ (poll (nd.st.1 hn) t).1 signed
      exact history_poll h _
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

private theorem history_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {key : Fin sp.n} {st : State sp ro}
    {p q : FG.Att sp.n → Prop} (h : HasHistory key st p) (hp : ∀ a, q a → p a) :
    HasHistory key st q := by
  obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
  exact ⟨hk, hr, ins, hi, he, fun a ha => hout a (hp a ha)⟩

private def Signs (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (a : FG.Att (Fintype.card V)) : Prop :=
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
    have hsign := history_poll_sign h k hdue hC ha
    have hall : HasHistory (rho.ownKey v)
        ((rho.dutyStep v nd (.poll k)).1.st.1 hn) (fun b => signed b ∨ b = a) := by
      unfold Model.Run.dutyStep
      simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k) = .poll from rfl,
        hsel, ↓reduceIte]
      apply history_release
      change HasHistory _ (((goldilocks S (pubOf E)).pollBatch nd.st.1 k).1 hn) _
      simp only [goldilocks, dite_eq_left hn]
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

/-- A selected proposal duty actually scheduled at a tick, with its actual input node.
The index and duty-list lookup supply the slot/time relation through the schedule; no bare
time equality replaces the execution witness. `rho.dutyStep` must gate both `act` and its
state effects by this selection, as in the engine repair. The clock uses the actual
engine time; slot equalities follow from absolute slot lengths/phase offsets, not network Δ. -/
def EngineProposalAt (v : V) (i p : Nat) (t : Time) (s : Slot)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) : Prop :=
  rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
    ∃ hs : 0 < s,
      ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.propose s hs) ∧
      rho.ownKey v ∈ rho.sel (.proposer s) ∧
      nd = (rho.runDuties v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1

/-- Characterization of a selected proposal's actual engine input. -/
theorem engineProposalAt_iff (v : V) (i p : Nat) (t : Time) (s : Slot)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) :
    EngineProposalAt S rho v i p t s nd ↔
      rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ∃ hs : 0 < s,
          ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.propose s hs) ∧
          rho.ownKey v ∈ rho.sel (.proposer s) ∧
          nd = (rho.runDuties v
            ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
              (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
            (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1 := by rfl

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
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload := by
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

/-- **Implementation refinement.** Each actual prefix carries one client
record from the empty record over valid entry inputs, containing all earlier actual signings.
Induction runs over engine events and duties. The FG update appends its source's entry
state, whose bounds give `EntryInputs`; all other duties, received-object processing, clocks,
gossip and releases preserve the record. No proposal simulation or `GoldilocksRun` is assumed. -/
theorem engine_signing_history (_hv : rho.ExecutionValid) {v : V} (_hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) :
    ∃ inputs, FG.EntryInputs (S.params (pubOf E) hn).toParams.fg inputs ∧
      (nd.st.1 hn).node.record = (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).1 ∧
      ∀ j q a, (j < i ∨ j = i ∧ q < p) → EngineSignsAt S rho hn v j q a →
        a ∈ (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).2 := by
  have hbefore := history_events S rho hn v i
  cases hc with
  | tick he hw hp =>
    rename_i t
    have h := history_duties_sign S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p) hbefore
    obtain ⟨_, _, ins, hi, hr, hout⟩ := h
    refine ⟨ins, hi, hr, ?_⟩
    intro j q a hj hs
    apply hout
    rcases hj with hj | ⟨rfl, hq⟩
    · exact Or.inl ⟨j, q, hj, hs⟩
    · obtain ⟨d, hd, hsign⟩ := signs_tick S rho hn he hs
      refine Or.inr ⟨q, d, ?_, ?_⟩
      · simpa [List.getElem?_take, hq] using hd
      · simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] using hsign
  | deliver he hp =>
    rename_i t o
    have hprocess : HasHistory (rho.ownKey v)
        (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
        (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
      obtain ⟨hk, hr, ins, hi, he', hout⟩ := hbefore
      exact ⟨(process_self _ _ _).trans hk, process_reachable _ _ _ hr,
        ins, hi, (process_record _ _ _).trans he', hout⟩
    have h := history_duties_sign S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
      (((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).take p) hprocess
    obtain ⟨_, _, ins, hi, hr, hout⟩ := h
    refine ⟨ins, hi, hr, ?_⟩
    intro j q a hj hs
    apply hout
    rcases hj with hj | ⟨rfl, hq⟩
    · exact Or.inl ⟨j, q, hj, hs⟩
    · obtain ⟨d, hd, hsign⟩ := signs_deliver S rho hn he hs
      refine Or.inr ⟨q, d, ?_, ?_⟩
      · simpa [List.getElem?_take, hq] using hd
      · simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] using hsign

/-- Restart retains the signing record, including at a wake boundary after a sleeping
interval. This follows directly from the engine's durable/restore operations and the node's
restart, independently of execution validity. -/
theorem engine_restart_record (_hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node.record = (stateAt S rho hn v i).node.record := by
  simp only [stateAt_eq, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
  rfl

/-- **Paper G0.5 (`FG.client_safety`) after the implementation history lemma.** Put both
signings in the history before an event after both signings, then apply client safety to its
`EntryInputs`. No node-simulation or network-timing premise is needed. -/
theorem engine_signings_nonFraming (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i p j q : Nat} {a b : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v i p a) (hb : EngineSignsAt S rho hn v j q b) :
    ¬ FG.slashable a b := by
  obtain ⟨inputs, hi, _, hs⟩ := engine_event_signing_history S rho hn hv hv' (max i j + 1)
  exact FG.client_safety _ _ inputs hi a (hs i p a (by omega) ha)
    b (hs j q b (by omega) hb)

private theorem emitted_no_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (cs : List (Cut (goldilocksNode sp ro))) (a : WireAtt) :
    Body.att a ∉ emitted cs := by
  simp only [emitted, List.mem_flatMap]
  rintro ⟨c, _, hc⟩
  cases c <;> simp_all

private theorem apply_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (r) (a : WireAtt) :
    Body.att a ∈ (apply st r).outbox ↔ Body.att a ∈ st.outbox := by
  simp only [apply, List.mem_append, emitted_no_att, or_false]

private theorem processOne_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (hs) (st : State sp ro) (o) (a : WireAtt) :
    Body.att a ∈ (processOne hs st o).outbox ↔ Body.att a ∈ st.outbox := by
  unfold processOne
  split
  · simp only [relayIf]
    split <;> exact apply_att _ _ _
  · exact apply_att _ _ _
  · exact apply_att _ _ _
  · rfl

private theorem recordOwn_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (o) (hs) (a : WireAtt) :
    Body.att a ∈ (recordOwn st o hs).outbox ↔ Body.att a ∈ st.outbox := by
  unfold recordOwn
  split
  · rfl
  · split
    · exact apply_att _ _ _
    · rfl
  · rfl

private theorem process_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (o) (hs) (a : WireAtt) :
    Body.att a ∈ (process st o hs).outbox ↔ Body.att a ∈ st.outbox := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, processOne_att]

private theorem propose_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (s) (a : WireAtt) :
    Body.att a ∈ (propose st s).1.outbox ↔ Body.att a ∈ st.outbox := by
  unfold propose
  dsimp only
  split <;> rfl

private theorem nodeTick_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (a : WireAtt) :
    Body.att a ∈ (nodeTick st).outbox ↔ Body.att a ∈ st.outbox := by
  unfold nodeTick
  split
  · exact apply_att _ _ _
  · rfl

private theorem restore_att {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (k t) (a : WireAtt) :
    Body.att a ∈ (restore k st t).outbox ↔ Body.att a ∈ st.outbox := by
  exact apply_att _ _ _

theorem createAtt_val {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σ : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σ = some (a, Λ')) : a.val = v := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    rfl

private def Queued {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) (signed : FG.Att sp.n → Prop) : Prop :=
  ∀ w, Body.att w ∈ st.outbox → ∃ a, w = encodeAtt a ∧ a.val = st.self ∧ signed a

private theorem poll_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (t : Time)
    {signed : FG.Att sp.n → Prop} (h : Queued st signed) :
    let p := fun a => signed a ∨ st.fgDue = true ∧ ∃ C Λ',
      (Node.acToFG st.node st.now).2.2 = some C ∧
      (Node.acToFG st.node st.now).1.fg.attest
        (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')
    Queued (poll st t).1 p ∧ ∀ w cs, (poll st t).2 = some (.att w, cs) →
      ∃ a, w = encodeAtt a ∧ a.val = st.self ∧ p a := by
  dsimp only
  let p := fun a => signed a ∨ st.fgDue = true ∧ ∃ C Λ',
    (Node.acToFG st.node st.now).2.2 = some C ∧
    (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self C = some (a, Λ')
  have hpre : Queued (if st.fgDue then fgUpdate st else st) p := by
    split
    · rename_i hd
      simp only [fgUpdate]
      split
      · intro w hw
        obtain ⟨a, hw, hv, hs⟩ := h w hw
        exact ⟨a, hw, hv, Or.inl hs⟩
      · rename_i C hC
        split
        · intro w hw
          obtain ⟨a, hw, hv, hs⟩ := h w hw
          exact ⟨a, hw, hv, Or.inl hs⟩
        · rename_i a Λ' ha
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · obtain ⟨b, hw, hv, hs⟩ := h w hw
            exact ⟨b, hw, hv, Or.inl hs⟩
          · have hw' : w = encodeAtt a := Body.att.inj (List.mem_singleton.mp hw)
            exact ⟨a, hw', createAtt_val ha, Or.inr ⟨hd, C, Λ', hC, ha⟩⟩
    · intro w hw
      obtain ⟨a, hw, hv, hs⟩ := h w hw
      exact ⟨a, hw, hv, Or.inl hs⟩
  have hself : (if st.fgDue then fgUpdate st else st).self = st.self := by
    split
    · exact fgUpdate_self st
    · rfl
  simp only [poll]
  split
  · exact ⟨hpre, by intro w cs he; cases he⟩
  · rename_i b rest he
    constructor
    · intro w hw
      exact hpre w (by rw [he]; exact List.mem_cons_of_mem b hw)
    · intro w cs hp
      cases hp
      obtain ⟨a, hw, hv, hs⟩ := hpre w (by rw [he]; exact List.mem_cons_self)
      exact ⟨a, hw, hv.trans hself, hs⟩

private theorem queued_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {st : State sp ro}
    {p q : FG.Att sp.n → Prop} (h : Queued st p) (hp : ∀ a, p a → q a) : Queued st q := by
  intro w hw
  obtain ⟨a, he, hv, ha⟩ := h w hw
  exact ⟨a, he, hv, hp a ha⟩

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
    · apply queued_release key _ cs
      intro w hw
      obtain ⟨a, he, hv, ha⟩ := h w ((recordOwn_att _ _ _ _).mp hw)
      exact ⟨a, he, hv.trans (recordOwn_self _ _ _).symm, ha⟩
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
    | act s k => exact k.elim
    | propose s hs =>
      change Queued (((goldilocks S (pubOf E)).propose nd.st.1 s).1 hn) _
      simp only [goldilocks, dite_eq_left hn]
      intro w hw
      obtain ⟨a, he, hv, ha⟩ := h w ((propose_att _ s _).mp hw)
      exact ⟨a, he, hv.trans (propose_self _ s).symm, Or.inl ha⟩
    | pollPropose t =>
      change Queued (((goldilocks S (pubOf E)).pollPropose nd.st.1 t).1 hn) _
      simp only [goldilocks, dite_eq_left hn]
      intro w hw
      obtain ⟨a, he, hv, ha⟩ := h w ((nodeTick_att _ _).mp hw)
      exact ⟨a, he, hv.trans (nodeTick_self _).symm, Or.inl ha⟩
    | poll t =>
      change Queued (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).1 hn) _
      simp only [goldilocks, dite_eq_left hn]
      apply queued_mono (poll_queued (nd.st.1 hn) t h).1
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
  | zero => intro w hw; cases hw
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
              (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
            intro w hw
            obtain ⟨a, he, hv, ha⟩ := ih w ((process_att _ _ _ _).mp hw)
            exact ⟨a, he, hv.trans (process_self _ _ _).symm, ha⟩
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
          intro w hw
          obtain ⟨a, he', hv, ha⟩ := ih w ((restore_att _ _ _ _).mp hw)
          exact ⟨a, he', hv.trans (history_events S rho hn v i).1, hold a ha⟩
        · simpa only [Model.Run.step, Function.update_of_ne hu] using queued_mono ih hold

omit [DecidableEq V] in
private theorem duty_released_att {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (d)
    (h : Queued (nd.st.1 hn) signed)
    {a : FG.Att (Fintype.card V)} (ha : attObj a ∈ (rho.dutyStep v nd d).2) :
    signed a ∨ Signs S rho hn v nd d a := by
  unfold Model.Run.dutyStep at ha
  split at ha
  · rename_i hsel
    have hc := Model.releaseAll_subset _ _ _ _ _ ha
    obtain ⟨m, cs, hm, _, he⟩ := rho.mem_signedCandidate.mp hc
    have he' := he
    change (Model.Obj.mk (.signed a.val (ShapeRole.poll : ShapeRole Empty))
      (.data (Body.att (encodeAtt a))) [] : Wire (Fintype.card V)) = _ at he'
    injection he' with hauth hmsg hcs
    subst m cs
    cases d with
    | act s k => exact k.elim
    | propose s hs =>
      have hh : (ShapeRole.poll : ShapeRole Empty) = .proposer s := by
        injection hauth
      cases hh
    | pollPropose t =>
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      simp only [goldilocks, dite_eq_left hn] at hm
      cases hm
    | poll t =>
      have hp : (poll (nd.st.1 hn) t).2 = some (.att (encodeAtt a), []) := by
        change _ ∈ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        simp only [goldilocks, dite_eq_left hn] at hm
        change _ ∈ ((pollBatch (nd.st.1 hn) t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        obtain ⟨⟨b, cs⟩, hb, heq⟩ := List.mem_map.mp hm
        have hp := Prod.mk.inj heq
        have hb' := Model.Msg.data.inj hp.1
        have hcs' := hp.2
        subst b cs
        simp only [pollBatch, List.mem_append] at hb
        rcases hb with (hb | hb) | hb
        · exact Option.mem_toList.mp hb
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
      obtain ⟨b, hb, _, hs⟩ := (poll_queued (nd.st.1 hn) t h).2 _ _ hp
      have hab : a = b := by
        have hh := congrArg (decodeAtt (Fintype.card V)) hb
        simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hh
      subst b
      rcases hs with hs | ⟨hd, C, Λ', hC, hs⟩
      · exact Or.inl hs
      · exact Or.inr ⟨t, rfl, hsel, hd, C, Λ', hC, hs⟩
  · cases ha

omit [DecidableEq V] in
private theorem duties_pair_append (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds ds') :
    rho.runDuties v nd (ds ++ ds') =
      let r := rho.runDuties v nd ds
      let r' := rho.runDuties v r.1 ds'
      (r'.1, r.2 ++ r'.2) := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => simp
  | cons d ds' ih =>
    dsimp only
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]
    simp only [List.append_assoc, List.nil_append]

omit [DecidableEq V] in
private theorem duties_released_att {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (h : Queued (nd.st.1 hn) signed) {a : FG.Att (Fintype.card V)}
    (ha : attObj a ∈ (rho.runDuties v nd ds).2) :
    signed a ∨ ∃ q d, ds[q]? = some d ∧
      Signs S rho hn v (rho.runDuties v nd (ds.take q)).1 d a := by
  induction ds using List.reverseRecOn with
  | nil => cases ha
  | append_singleton ds d ih =>
    rw [duties_pair_append] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases ih ha with ha | ⟨q, d', hq, hs⟩
      · exact Or.inl ha
      · have hlt := (List.getElem?_eq_some_iff.mp hq).1
        refine Or.inr ⟨q, d', ?_, ?_⟩
        · simpa [List.getElem?_append, hlt] using hq
        · simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using hs
    · have hq := queued_duties S rho hn (v := v) nd ds h
      have hr := duty_released_att S rho hn _ d hq ha
      rcases hr with (ha | ⟨q, d', hqd, hs⟩) | hs
      · exact Or.inl ha
      · have hlt := (List.getElem?_eq_some_iff.mp hqd).1
        refine Or.inr ⟨q, d', ?_, ?_⟩
        · simpa [List.getElem?_append, hlt] using hqd
        · simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using hs
      · exact Or.inr ⟨ds.length, d, by simp, by simpa using hs⟩

omit [DecidableEq V] in
private theorem gossip_not_att (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Fin (Fintype.card V)) (t : Time) (a : FG.Att (Fintype.card V)) :
    attObj a ∉ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st t)).2 := by
  intro ha
  obtain ⟨mc, _, he⟩ := Model.mem_gossipCandidates.mp
    (Model.releaseAll_subset _ _ _ _ _ ha)
  have hh := congrArg Model.Obj.auth he
  cases hh

private theorem released_att_signed {v : V} {i : Nat} {t : Time}
    (hs : rho.SendsAt v i t) {a : FG.Att (Fintype.card V)}
    (ha : attObj a ∈ rho.releasesAt i) :
    ∃ j q, j ≤ i ∧ EngineSignsAt S rho hn v j q a := by
  rcases hs with he | ⟨o, he⟩
  · simp only [Model.Run.releasesAt, he] at ha
    unfold Model.Run.tick at ha
    split at ha
    · rename_i hw
      rcases List.mem_append.mp ha with ha | ha
      · have h := duties_released_att S rho hn
          ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
            (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
          (queued_before S rho hn v i) ha
        rcases h with ⟨j, q, hj, hs⟩ | ⟨q, d, hd, hs⟩
        · exact ⟨j, q, Nat.le_of_lt hj, hs⟩
        · exact ⟨i, q, Nat.le_refl _, signs_of_tick S rho hn he hw hd hs⟩
      · exact False.elim (gossip_not_att S rho _ _ t a ha)
    · cases ha
  · simp only [Model.Run.releasesAt, he, Model.Run.deliver] at ha
    rcases List.mem_append.mp ha with ha | ha
    · have hprocess : Queued
          (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
          (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
        intro w hw
        obtain ⟨a, he, hv, ha⟩ := queued_before S rho hn v i w ((process_att _ _ _ _).mp hw)
        exact ⟨a, he, hv.trans (process_self _ _ _).symm, ha⟩
      have h := duties_released_att S rho hn
        ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
          (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hprocess ha
      rcases h with ⟨j, q, hj, hs⟩ | ⟨q, d, hd, hs⟩
      · exact ⟨j, q, Nat.le_of_lt hj, hs⟩
      · exact ⟨i, q, Nat.le_refl _, signs_of_deliver S rho hn he hd hs⟩
    · exact False.elim (gossip_not_att S rho _ _ t a ha)

omit [DecidableEq V] in
private theorem duties_closure (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (a : FG.Att (Fintype.card V))
    (ha : attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen) :
    attObj a ∈ Model.closure nd.seen ∨ attObj a ∈ (rho.runDuties v nd ds).2 := by
  induction ds using List.reverseRecOn with
  | nil => exact Or.inl ha
  | append_singleton ds d ih =>
    rw [duties_pair_append] at ha ⊢
    change _ ∨ attObj a ∈ _ ++ (rho.dutyStep v (rho.runDuties v nd ds).1 d).2
    change attObj a ∈ Model.closure (rho.dutyStep v (rho.runDuties v nd ds).1 d).1.seen at ha
    unfold Model.Run.dutyStep at ha ⊢
    split at ha
    · rename_i hsel
      simp only [hsel, ↓reduceIte]
      let Q := fun o => o = attObj a →
        attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen ∨
          attObj a ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v)
            ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
              (rho.runDuties v nd ds).1.seen⟩
            (rho.signedCandidate v d
              ((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).2)).2
      have hp := Model.releaseAll_preserves rho.hash (rho.ownKey v) Q
        ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
          (rho.runDuties v nd ds).1.seen⟩
        (rho.signedCandidate v d
          ((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).2)
        (fun o ho b hb he => Or.inl (he ▸ (Model.mem_closure_iff _ _).mpr ⟨o, ho, hb⟩))
        (fun o ho he => Or.inr (he ▸ ho))
      obtain ⟨o, ho, hc⟩ := (Model.mem_closure_iff _ _).mp ha
      rcases hp.1 o ho _ hc rfl with hh | hh
      · rcases ih hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (List.mem_append_left _ hh)
      · exact Or.inr (List.mem_append_right _ hh)
    · rename_i hsel
      simp only [hsel, ↓reduceIte, List.append_nil]
      exact ih ha

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

/-- Every queued attestation at an actual duty boundary has an actual engine signing.
This supplies guard safety when the ordinary poll removes it from the queue. -/
theorem engine_queued_att_signed {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {w : WireAtt}
    (hm : Body.att w ∈ (nd.st.1 hn).outbox) :
    ∃ a j q, w = encodeAtt a ∧ a.val = (nd.st.1 hn).self ∧
      EngineSignsAt S rho hn v j q a := by
  cases hc with
  | tick he hw hp =>
    rename_i t
    obtain ⟨a, heq, hval, ha⟩ := queued_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
      (queued_before S rho hn v i) w hm
    rcases ha with ⟨j, q, _, ha⟩ | ⟨q, d, hd, ha⟩
    · exact ⟨a, j, q, heq, hval, ha⟩
    · have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at ha
      exact ⟨a, i, q, heq, hval, signs_of_tick S rho hn he hw hd ha⟩
  | deliver he hp =>
    rename_i t o
    have hproc : Queued
        (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
        (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
      intro w hw
      obtain ⟨a, heq, hval, ha⟩ := queued_before S rho hn v i w
        ((process_att _ _ _ _).mp hw)
      exact ⟨a, heq, hval.trans (process_self _ _ _).symm, ha⟩
    obtain ⟨a, heq, hval, ha⟩ := queued_duties S rho hn
      ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hproc w hm
    rcases ha with ⟨j, q, _, ha⟩ | ⟨q, d, hd, ha⟩
    · exact ⟨a, j, q, heq, hval, ha⟩
    · have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at ha
      exact ⟨a, i, q, heq, hval, signs_of_deliver S rho hn he hd ha⟩

/-- A scheduled poll's ordinary attestation candidate comes from an engine signing,
including an attestation created by this poll's own FG update. -/
theorem engine_poll_att_signed {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k).2 = some (.att w, cs)) :
    ∃ a j q, w = encodeAtt a ∧ a.val = (nd.st.1 hn).self ∧
      EngineSignsAt S rho hn v j q a := by
  have hq : Queued (nd.st.1 hn) (fun a => ∃ j q, EngineSignsAt S rho hn v j q a) := by
    intro w hw
    obtain ⟨a, j, q, he, hv, ha⟩ := engine_queued_att_signed S rho hn hc hw
    exact ⟨a, he, hv, j, q, ha⟩
  obtain ⟨a, he, hv, ha⟩ := (poll_queued (nd.st.1 hn) k hq).2 w cs hm
  rcases ha with ⟨j, q, ha⟩ | ⟨hdue, C, Λ', hC, ha⟩
  · exact ⟨a, j, q, he, hv, ha⟩
  · exact ⟨a, i, p, he, hv, nd, hc, k, hd, hsel, hdue, C, Λ', hC, ha⟩

private theorem signing_val {v : V} {i p : Nat} {a}
    (hs : EngineSignsAt S rho hn v i p a) : a.val = rho.ownKey v := by
  obtain ⟨nd, hc, k, _, _, _, C, Λ', _, ha⟩ := hs
  exact (createAtt_val ha).trans (cut_self S rho hn hc)

/-- **Implementation release inverse.** An honest attestation in the
closure of `seen` at an actual duty boundary has an earlier actual signing. Unforgeability gives
earlier honest releases; queue provenance identifies their FG signings. Within the same event
the bound uses duty-prefix order, not strict event order.
Carried attestations use recursive containment, including unsigned wrappers. -/
theorem engine_seen_att_signed (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) {v u : V}
    (_hv' : v ∉ rho.faultyAt 0) (hu : u ∉ rho.faultyAt 0) {i p : Nat}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) {a : FG.Att (Fintype.card V)}
    (ha : a.val = rho.ownKey u) (hm : attObj a ∈ Model.closure nd.seen) :
    ∃ j q, (j < i ∨ j = i ∧ u = v ∧ q < p) ∧ EngineSignsAt S rho hn u j q a := by
  have hsigner : rho.signerOf (attObj a) = some u := by
    change Option.map rho.key (some a.val) = some u
    simp [ha, Model.Run.ownKey]
  have hbefore (hm : attObj a ∈ Model.closure (rho.stateBefore i v).seen) :
      ∃ j q, (j < i ∨ j = i ∧ u = v ∧ q < p) ∧ EngineSignsAt S rho hn u j q a := by
    have hi : i ≤ rho.events.length := by
      cases hc with
      | tick he _ _ => exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
      | deliver he _ => exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨j, hj, t, hs, hr⟩ := rho.signed_seen_released hv hi hm
      (by simpa only [rho.faultyAt_eq_zero hf] using hu) hsigner
    obtain ⟨k, q, hk, ha⟩ := released_att_signed S rho hn hs hr
    exact ⟨k, q, Or.inl (by omega), ha⟩
  cases hc with
  | tick he hw hp =>
    rename_i t
    rcases duties_closure S rho v _ _ a hm with hm | hm
    · exact hbefore hm
    · have hh := duties_released_att S rho hn
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
        (queued_before S rho hn v i) hm
      rcases hh with ⟨j, q, hj, hs⟩ | ⟨q, d, hd, hs⟩
      · have huv : u = v := rho.key.symm.injective (ha.symm.trans (signing_val S rho hn hs))
        subst u
        exact ⟨j, q, Or.inl hj, hs⟩
      · have hq : q < p := by
          have hb := (List.getElem?_eq_some_iff.mp hd).1
          simp only [List.length_take] at hb
          omega
        have hd' := hd
        simp only [List.getElem?_take, ite_eq_left hq] at hd'
        have hs' := signs_of_tick S rho hn he hw hd'
          (by simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] using hs)
        have huv : u = v := rho.key.symm.injective (ha.symm.trans (signing_val S rho hn hs'))
        subst u
        exact ⟨i, q, Or.inr ⟨rfl, rfl, hq⟩, hs'⟩
  | deliver he hp =>
    rename_i t o
    rcases duties_closure S rho v _ _ a hm with hm | hm
    · rw [Model.closure_append] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hbefore hm
      · have hcontains : Model.Obj.Contains o (attObj a) := by
          simp only [Model.closure, List.flatMap_singleton] at hm
          exact hm
        obtain ⟨j, t', hj, hs, hr⟩ := hv.unforgeable i v o t he _ hcontains u hsigner
          (by simpa only [rho.faultyAt_eq_zero hf] using hu)
        obtain ⟨k, q, hk, hs'⟩ := released_att_signed S rho hn hs hr
        exact ⟨k, q, Or.inl (by omega), hs'⟩
    · have hprocess : Queued
          (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o))
          (fun a => ∃ j q, j < i ∧ EngineSignsAt S rho hn v j q a) := by
        intro w hw
        obtain ⟨a, he, hv, ha⟩ := queued_before S rho hn v i w ((process_att _ _ _ _).mp hw)
        exact ⟨a, he, hv.trans (process_self _ _ _).symm, ha⟩
      have hh := duties_released_att S rho hn
        ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
          (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _ hprocess hm
      rcases hh with ⟨j, q, hj, hs⟩ | ⟨q, d, hd, hs⟩
      · have huv : u = v := rho.key.symm.injective (ha.symm.trans (signing_val S rho hn hs))
        subst u
        exact ⟨j, q, Or.inl hj, hs⟩
      · have hq : q < p := by
          have hb := (List.getElem?_eq_some_iff.mp hd).1
          simp only [List.length_take] at hb
          omega
        have hd' := hd
        simp only [List.getElem?_take, ite_eq_left hq] at hd'
        have hs' := signs_of_deliver S rho hn he hd'
          (by simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] using hs)
        have huv : u = v := rho.key.symm.injective (ha.symm.trans (signing_val S rho hn hs'))
        subst u
        exact ⟨i, q, Or.inr ⟨rfl, rfl, hq⟩, hs'⟩

/-- **G0.5 plus implementation provenance; NO independent PAPER PROOF of the engine guard.**
A freshly generated attestation passes the candidate/seen protection boundary: self-conflict
is impossible by client safety; any conflicting own-signed object in `seen` is another actual
signing by `engine_seen_att_signed`. Include both conflict orientations. Earlier releases in
the same event are included in this actual duty-prefix `seen`. -/
theorem engine_att_protected (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) {j q : Nat} {a : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (attObj a) = true := by
  have hinj {a b : FG.Att (Fintype.card V)} (h : attObj a = attObj b) : a = b := by
    injection h with _ h₂
    injection h₂ with h₃
    injection h₃ with h₄
    have hd := congrArg (decodeAtt (Fintype.card V)) h₄
    simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hd
  have hself : conflicts (attObj a) (attObj a) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨b, c, hb, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
    obtain rfl := hinj hb
    obtain rfl := hinj hc'
    exact engine_signings_nonFraming S rho hn hv hv' ha ha hbc
  unfold Model.protects
  split
  · simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hself, ?_⟩
    rw [List.all_eq_true]
    intro o ho
    by_cases hk : o.signer? = some (rho.ownKey v)
    · have hconf : conflicts (attObj a) o = false ∧ conflicts o (attObj a) = false := by
        constructor <;> apply Bool.eq_false_iff.mpr <;> intro h
        · obtain ⟨b, c, hb, rfl, hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
          obtain rfl := hinj hb
          have hcval : c.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', _, hc'⟩ := engine_seen_att_signed S rho hn hf hv hv' hv' hc hcval ho
          exact engine_signings_nonFraming S rho hn hv hv' ha hc' hbc
        · obtain ⟨b, c, rfl, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
          obtain rfl := hinj hc'
          have hbval : b.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', _, hb⟩ := engine_seen_att_signed S rho hn hf hv hv' hv' hc hbval ho
          exact engine_signings_nonFraming S rho hn hv hv' hb ha hbc
      change (_ != _ || !(conflicts (attObj a) o || conflicts o (attObj a))) = true
      simp [hconf.1, hconf.2]
    · simp [hk]
  · rfl

/-- The own-object guard admits the ordinary attestation produced by an actual poll. -/
theorem engine_poll_att_protected (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k).2 = some (.att w, cs)) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true := by
  obtain ⟨a, j, q, rfl, hval, ha⟩ := engine_poll_att_signed S rho hn hc hd hsel hm
  have hp := engine_att_protected S rho hn hf hv hv' hc ha
  have he := hval.trans (cut_self S rho hn hc)
  have ho : attObj a = (.mk (.signed (rho.ownKey v) .poll)
      (.data (.att (encodeAtt a))) [] : Wire (Fintype.card V)) := by
    unfold attObj
    rw [he]
  rw [ho] at hp
  exact hp
end Consensus.Goldilocks.Simulation
end
