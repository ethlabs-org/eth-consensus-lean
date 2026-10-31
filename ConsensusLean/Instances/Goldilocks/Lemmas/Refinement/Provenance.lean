module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Engine signing history before node simulation

Implementation-refinement history for the Accepted skeleton. These declarations use
actual engine duty prefixes, never `eventCuts`, `simTrace`, or `GoldilocksRun`. A poll's FG update
is the only signing operation; all other operations preserve the client history, including
restart. The inverse from seen attestations to actual signings remains open.

The paper's G0.5 supplies client safety, not the correspondence between engine execution and
client inputs. The latter and the release provenance obligations below have NO PAPER PROOF.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

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
  · simp only [relayIf, apply]
    split <;> rfl
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

private theorem processOne_reachable {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    (h : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload) :
    (processOne hs st o).node.fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  unfold processOne
  split
  · simp only [relayIf, apply]
    split <;> exact onBlock_reachable _ _ _ _ h
  · simp only [relayIf, apply]
    split <;> exact h
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
    (hC : (Node.acToFG st.node st.now).2.2.1 = some C)
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
    ∀ (nd : Model.Node (Model.protoOf (compiled (family S)) E)) cs,
      HasHistory key (nd.st.1 hn) signed →
      HasHistory key ((Model.releaseAll (Model.protoOf (compiled (family S)) E)
        rho.hash key nd cs).1.st.1 hn) signed
  | nd, [], h => h
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · exact history_release key _ cs (history_recordOwn h c _)
    · exact history_release key nd cs h

omit [DecidableEq V] in
private theorem history_duty {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.dutyStep v nd d).1.st.1 hn) signed := by
  unfold Model.Run.dutyStep
  split
  · apply history_release
    cases d with
    | act s k => exact k.elim
    | propose s hs =>
      change HasHistory _ (((family S (pubOf E)).propose nd.st.1 s).1 hn) signed
      simp only [family, dite_eq_left hn]
      change HasHistory _ (propose (nd.st.1 hn) s).1 signed
      obtain ⟨hk, hr, ins, hi, he, hout⟩ := h
      refine ⟨(propose_self _ _).trans hk, ?_, ins, hi, ?_, hout⟩
      · unfold propose; dsimp only; split <;> exact hr
      · unfold propose; dsimp only; split <;> exact he
    | pollPropose t =>
      change HasHistory _ (((family S (pubOf E)).pollPropose nd.st.1 t).1 hn) signed
      simp only [family, dite_eq_left hn]
      change HasHistory _ (nodeTick (nd.st.1 hn)) signed
      unfold nodeTick
      split <;> exact h
    | poll t =>
      change HasHistory _ (((family S (pubOf E)).poll nd.st.1 t).1 hn) signed
      simp only [family, dite_eq_left hn]
      change HasHistory _ (poll (nd.st.1 hn) t).1 signed
      exact history_poll h _
  · exact h

omit [DecidableEq V] in
private theorem history_duties {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) ds
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v) ((rho.runDuties v nd ds).1.st.1 hn) signed := by
  unfold Model.Run.runDuties
  have hfold : ∀ (r : Model.Node (Model.protoOf (compiled (family S)) E) ×
      List (Model.protoOf (compiled (family S)) E).Object),
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time)
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) (o)
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time)
    (h : HasHistory (rho.ownKey v) (nd.st.1 hn) signed) :
    HasHistory (rho.ownKey v)
      (((Model.protoOf (compiled (family S)) E).restore (rho.ownKey v)
        ((Model.protoOf (compiled (family S)) E).durable nd.st) t).1 hn) signed := by
  obtain ⟨_, hr, ins, hi, he, hout⟩ := h
  exact ⟨rfl, hr, ins, hi, he, hout⟩

omit [DecidableEq V] in
private theorem history_initial (v : V) :
    HasHistory (rho.ownKey v) ((rho.initWorld v).st.1 hn) := by
  exact ⟨rfl, .refl, [], (by intro x hx; cases hx), rfl, (by simp)⟩

private theorem history_step (w : V → Model.Node (Model.protoOf (compiled (family S)) E))
    (e : Model.Event V (Model.protoOf (compiled (family S)) E).Object) (v : V)
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

private def Signs (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty) (a : FG.Att (Fintype.card V)) : Prop :=
  ∃ k : Nat, d = .poll k ∧ rho.ownKey v ∈ rho.sel .poll ∧
    (nd.st.1 hn).fgDue = true ∧ ∃ C Λ',
      (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).2.2.1 = some C ∧
      (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.fg.attest
        (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.record (nd.st.1 hn).self C =
          some (a, Λ')

omit [DecidableEq V] in
private theorem history_duty_sign {v : V} {signed : FG.Att (Fintype.card V) → Prop}
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (d)
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
      simp only [show (Model.protoOf (compiled (family S)) E).role (.poll k) = .poll from rfl,
        hsel, ↓reduceIte]
      apply history_release
      change HasHistory _ (((family S (pubOf E)).poll nd.st.1 k).1 hn) _
      simp only [family, dite_eq_left hn]
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (ds ds') :
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (ds)
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
    Model.Node (Model.protoOf (compiled (family S)) E) → Prop where
  | tick {t : Time} (he : rho.events[i]? = some (.tick v t))
      (hw : E.awake v t = true)
      (hp : p ≤ ((Model.protoOf (compiled (family S)) E).duties t).length) :
      EngineDutyCut v i p
        (rho.runDuties v
          ⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
            (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
          (((Model.protoOf (compiled (family S)) E).duties t).take p)).1
  | deliver {t : Time} {o : (Model.protoOf (compiled (family S)) E).Object}
      (he : rho.events[i]? = some (.deliver v o t))
      (hp : p ≤ ((Model.protoOf (compiled (family S)) E).deliverDuties t).length) :
      EngineDutyCut v i p
        (rho.runDuties v
          ⟨(Model.protoOf (compiled (family S)) E).process (rho.stateBefore i v).st o
            (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
          (((Model.protoOf (compiled (family S)) E).deliverDuties t).take p)).1

/-- A selected proposal duty actually scheduled at a tick, with its actual input node.
The index and duty-list lookup supply the slot/time relation through the schedule; no bare
time equality replaces the execution witness. `rho.dutyStep` must gate both `act` and its
state effects by this selection, as in the approved engine repair. The clock uses the actual
engine time; slot equalities follow from absolute slot lengths/phase offsets, not network Δ. -/
def EngineProposalAt (v : V) (i p : Nat) (t : Time) (s : Slot)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) : Prop :=
  rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
    ∃ hs : 0 < s,
      ((Model.protoOf (compiled (family S)) E).duties t)[p]? = some (.propose s hs) ∧
      rho.ownKey v ∈ rho.sel (.proposer s) ∧
      nd = (rho.runDuties v
        ⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        (((Model.protoOf (compiled (family S)) E).duties t).take p)).1

/-- An attestation actually generated by the FG update of a scheduled poll. The index `p`
names that poll, not a simulated cut. The engine's poll selection must authorize this duty;
this explicit guard also fits the proposed selection-aware duty semantics. -/
def EngineSignsAt (v : V) (i p : Nat) (a : FG.Att (Fintype.card V)) : Prop :=
  ∃ nd, EngineDutyCut S rho v i p nd ∧
    ∃ k : Nat,
      ((∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
          ((Model.protoOf (compiled (family S)) E).duties t)[p]? = some (.poll k)) ∨
        ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
          ((Model.protoOf (compiled (family S)) E).deliverDuties t)[p]? = some (.poll k)) ∧
      rho.ownKey v ∈ rho.sel .poll ∧
      (nd.st.1 hn).fgDue = true ∧
      ∃ C Λ', (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).2.2.1 = some C ∧
        (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.fg.attest
          (Node.acToFG (nd.st.1 hn).node (nd.st.1 hn).now).1.record (nd.st.1 hn).self C =
            some (a, Λ')

private theorem signs_tick {v : V} {i q : Nat} {a : FG.Att (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hs : EngineSignsAt S rho hn v i q a) :
    ∃ d, ((Model.protoOf (compiled (family S)) E).duties t)[q]? = some d ∧
      Signs S rho hn v (rho.runDuties v
        ⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        (((Model.protoOf (compiled (family S)) E).duties t).take q)).1 d a := by
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
    ∃ d, ((Model.protoOf (compiled (family S)) E).deliverDuties t)[q]? = some d ∧
      Signs S rho hn v (rho.runDuties v
        ⟨(Model.protoOf (compiled (family S)) E).process (rho.stateBefore i v).st o
          (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
        (((Model.protoOf (compiled (family S)) E).deliverDuties t).take q)).1 d a := by
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
              ⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
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

/-- **Implementation event-boundary history.** This is the pre-event
version of the duty-prefix invariant. Initial state has the empty record; clock, processing,
gossip and releases preserve it, and each actual selected poll's FG update appends its entry
input. Restart preserves the durable record. The event/duty induction uses neither execution
validity nor honesty; these interface arguments are retained for callers. -/
theorem engine_event_signing_history (_hv : rho.ExecutionValid) {v : V}
    (_hv' : v ∈ rho.honest) (i : Nat) :
    ∃ inputs, FG.EntryInputs (S.params (pubOf E) hn).toParams.fg inputs ∧
      (stateAt S rho hn v i).node.record =
        (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).1 ∧
      ∀ j q a, j < i → EngineSignsAt S rho hn v j q a →
        a ∈ (FG.Record.run (rho.ownKey v) FG.Record.empty inputs).2 := by
  obtain ⟨_, _, ins, hi, hr, hout⟩ := history_events S rho hn v i
  exact ⟨ins, hi, hr, fun j q a hj hs => hout a ⟨j, q, hj, hs⟩⟩

/-- **Implementation refinement.** Each actual prefix carries one client
record from the empty record over valid entry inputs, containing all earlier actual signings.
Induction runs over engine events and duties. The FG update appends its source's entry
state, whose bounds give `EntryInputs`; all other duties, received-object processing, clocks,
gossip and releases preserve the record. No proposal simulation or `GoldilocksRun` is assumed. -/
theorem engine_signing_history (_hv : rho.ExecutionValid) {v : V} (_hv' : v ∈ rho.honest)
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (family S)) E)}
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
      ⟨(Model.protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (family S)) E).duties t).take p) hbefore
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
      ⟨(Model.protoOf (compiled (family S)) E).process (rho.stateBefore i v).st o
        (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
      (((Model.protoOf (compiled (family S)) E).deliverDuties t).take p) hprocess
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
  simp only [stateAt, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
  rfl

/-- **Paper G0.5 (`FG.client_safety`) after the implementation history lemma.** Put both
signings in the history before an event after both signings, then apply client safety to its
`EntryInputs`. No node-simulation or network-timing premise is needed. -/
theorem engine_signings_nonFraming (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p j q : Nat} {a b : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v i p a) (hb : EngineSignsAt S rho hn v j q b) :
    ¬ FG.slashable a b := by
  obtain ⟨inputs, hi, _, hs⟩ := engine_event_signing_history S rho hn hv hv' (max i j + 1)
  exact FG.client_safety _ _ inputs hi a (hs i p a (by omega) ha)
    b (hs j q b (by omega) hb)

/-- **NO PAPER PROOF — implementation release inverse.** An honest attestation in the
closure of `seen` at an actual duty boundary has an earlier actual signing. Credentials gives
role membership; Unforgeable gives earlier honest releases. Inspect poll candidates for their
queued FG signing. Within the same event use the duty-prefix order, not strict event order.
Carried attestations use recursive containment, including unsigned wrappers. -/
theorem engine_seen_att_signed (hv : rho.ExecutionValid) {v u : V}
    (hv' : v ∈ rho.honest) (hu : u ∈ rho.honest) {i p : Nat}
    {nd : Model.Node (Model.protoOf (compiled (family S)) E)}
    (hc : EngineDutyCut S rho v i p nd) {a : FG.Att (Fintype.card V)}
    (ha : a.val = rho.ownKey u) (hm : attObj a ∈ Model.closure nd.seen) :
    ∃ j q, (j < i ∨ j = i ∧ u = v ∧ q < p) ∧ EngineSignsAt S rho hn u j q a := by
  sorry

/-- **G0.5 plus implementation provenance; NO independent PAPER PROOF of the engine guard.**
A freshly generated attestation passes the candidate/seen protection boundary: self-conflict
is impossible by client safety; any conflicting own-signed object in `seen` is another actual
signing by `engine_seen_att_signed`. Include both conflict orientations. Earlier releases in
the same event are included in this actual duty-prefix `seen`. -/
theorem engine_att_protected (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (family S)) E)}
    (hc : EngineDutyCut S rho v i p nd) {j q : Nat} {a : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
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
    obtain ⟨b, c, hb, hc', hbc⟩ := (conflicts_iff _ _ _).mp h
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
        · obtain ⟨b, c, hb, rfl, hbc⟩ := (conflicts_iff _ _ _).mp h
          obtain rfl := hinj hb
          have hcval : c.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', _, hc'⟩ := engine_seen_att_signed S rho hn hv hv' hv' hc hcval ho
          exact engine_signings_nonFraming S rho hn hv hv' ha hc' hbc
        · obtain ⟨b, c, rfl, hc', hbc⟩ := (conflicts_iff _ _ _).mp h
          obtain rfl := hinj hc'
          have hbval : b.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', _, hb⟩ := engine_seen_att_signed S rho hn hv hv' hv' hc hbval ho
          exact engine_signings_nonFraming S rho hn hv hv' hb ha hbc
      change (_ != _ || !(conflicts (attObj a) o || conflicts o (attObj a))) = true
      simp [hconf.1, hconf.2]
    · simp [hk]
  · rfl

end Consensus.Goldilocks.Refinement

end
