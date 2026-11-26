module
public import ConsensusLean.Spec.Model.Guard
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Signing
import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AttGuard
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ProvenanceGuard

public section

/-! # Slashing protection never fires for Goldilocks

On every valid execution of the compiled Goldilocks family, no event has a candidate that
slashing protection would refuse (`guardIdle`): Goldilocks' non-framing. Only an attestation
body signed in the poll role and carrying nothing can conflict (`protects_of_not_att`). Such a
candidate comes only from a scheduled poll's batch: its ordinary emission, or a held attestation
the batch flushes at a time the release schedule allows. Each is an engine signing
(`batch_att_candidate`) and is checked against the `seen` log at its own turn: the poll's duty
prefix plus the batch's earlier releases, whose own attestations are engine signings too
(`guardRefusals_eq_nil_of_preserves`). The node's own FG record admits it there: no two engine
signings of an honest node are slashable (`FG.client_safety`). Every other candidate (proposals,
forwarding and vote-forward envelopes, unsigned gossip) passes against any `seen` log. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

section Release

variable {pub : Model.Public} {Out : Type} {P : Model.Protocol pub Out}

/-- Candidates that the guard passes against every `seen` log are never refused, from any node. -/
private theorem guardRefusals_eq_nil (hash : P.Item → Nat) (k : Model.Key pub)
    {cs : List P.Object} (h : ∀ c ∈ cs, ∀ seen, Model.protects P k seen c = true) :
    ∀ nd, Model.guardRefusals P hash k nd cs = [] := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro nd
    simp only [Model.guardRefusals, h c List.mem_cons_self, ↓reduceIte, List.nil_append]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

end Release

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

omit [DecidableEq V] in
/-- A candidate whose message is not an attestation body passes the guard against any `seen`. -/
private theorem protects_of_msg (k x : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (goldilocks S)) E).Object) (r)
    (m : Model.Msg (Model.protoOf (compiled (goldilocks S)) E).Item
      (Model.protoOf (compiled (goldilocks S)) E).Body) (cs)
    (h : ∀ w, m ≠ .data (.att w)) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) k seen (.mk (.signed x r) m cs) =
      true :=
  protects_of_not_att S k seen _ fun _ w he => h w (Model.Obj.mk.inj he).2.1

omit [DecidableEq V] in
/-- Unsigned gossip is never refused. -/
private theorem gossipRefusals_eq_nil (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (st) (t : Time) :
    Model.guardRefusals (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) st t) = [] :=
  guardRefusals_eq_nil _ _ (fun c hc seen => by
    obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp hc
    exact protects_of_not_att S k seen _ fun _ _ h => by cases h) _

/-- **No duty of an actual event prefix has a refused candidate.** Every attestation candidate of a
poll's batch, its ordinary emission or a flushed held attestation, is an engine signing, checked
against the prefix's `seen` plus the batch's earlier releases, where the guard admits it. Every
other candidate of every duty is not an attestation body. -/
private theorem dutyRefusals_eq_nil (hv : rho.ExecutionValid) {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {d}
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some d) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some d) :
    rho.dutyRefusals v nd d = [] := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold Model.Run.dutyRefusals
  split
  · rename_i hsel
    cases d with
    | poll k =>
      have hact : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll k)).2 =
          (pollBatch (nd.st.1 hn) (k : Time) (S.release (pubOf E))).2.map
            fun bc => (Model.Msg.data bc.1, bc.2) := by
        change (((goldilocks S (pubOf E)).pollBatch nd.st.1 (k : Time)).2.map _) = _
        rw [goldilocks_pollBatch_eq S _ nd.st.1 (k : Time), dite_eq_left hn]
        rfl
      have hv0 : v ∉ rho.faultyAt 0 := by
        cases hc with
        | tick he _ _ => exact event_honest_zero S rho hv he
        | deliver he _ => exact event_honest_zero S rho hv he
      dsimp only
      rw [hact]
      -- every own attestation object at any depth of the log is an engine signing
      refine guardRefusals_eq_nil_of_preserves _ _
        (fun x => ∀ a : FG.Att (Fintype.card V), a.val = rho.ownKey v → x = attObj a →
          ∃ j q, EngineSignsAt S rho hn v j q a) _
        (fun c hc' a hav he => ?_) (fun c hc' seen hseen => ?_) _ (fun o ho d hd a hav he => ?_)
      · -- a batch candidate: the ordinary emission or a flushed held attestation
        obtain ⟨b, j, q, hb, -, hs⟩ := batch_att_candidate S rho hn hc hd hsel hc' he
        cases attObj_inj S (he.symm.trans hb)
        exact ⟨j, q, hs⟩
      · -- checked against the log at its own turn, which holds the earlier releases
        by_cases hatt : ∃ x w, c = .mk (.signed x .poll) (.data (.att w)) []
        · obtain ⟨x, w, he⟩ := hatt
          obtain ⟨a, j, q, rfl, -, ha⟩ := batch_att_candidate S rho hn hc hd hsel hc' he
          exact att_protected_of_signings S rho hn (nd := ⟨nd.st, seen⟩)
            (engine_signings_nonFraming S rho hn hv hv0)
            (fun {b} hbv hm => by
              obtain ⟨o, ho, hco⟩ := (Model.mem_closure_iff _ _).mp hm
              exact hseen o ho _ hco b hbv rfl) ha
        · exact protects_of_not_att S _ _ _ fun x w he => hatt ⟨x, w, he⟩
      · -- the duty prefix's log
        subst he
        exact engine_seen_att_signed_at S rho hn hv hc (duty_honest_at S rho hv hc) hav
          ((Model.mem_closure_iff _ _).mpr ⟨o, ho, hd⟩)
    | propose s hs =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      apply protects_of_msg
      intro w hw
      subst hw
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).propose nd.st.1 s).2).toList at hm
      obtain ⟨⟨par, info, cs'⟩, -, he⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hm)
      cases (Prod.mk.inj he).1
    | act s k' =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      exact absurd hm List.not_mem_nil
    | pollPropose t =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      rw [goldilocks_pollPropose_eq S _ nd.st.1 (t : Time), dite_eq_left hn] at hm
      cases hm
  · rfl

omit [DecidableEq V] in
/-- The refusals of a duty list vanish if those of each duty at its actual prefix do. -/
private theorem runDutiesRefusals_eq_nil (v : V)
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    ∀ nd, (∀ p d, ds[p]? = some d → rho.dutyRefusals v (rho.runDuties v nd (ds.take p)).1 d = []) →
      rho.runDutiesRefusals v nd ds = [] := by
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds ih =>
    intro nd h
    simp only [Model.Run.runDutiesRefusals]
    rw [show rho.dutyRefusals v nd d = [] from h 0 d rfl, List.nil_append]
    refine ih _ fun p d' hp => ?_
    have h' := h (p + 1) d' (by simpa using hp)
    simpa only [List.take_succ_cons, rho.runDuties_cons] using h'

/-- **The slashing guard never fires for Goldilocks**: on every valid execution, no event puts a
candidate to the engine's slashing protection that it refuses. The honest node's own FG record
keeps it from signing a slashable pair. -/
theorem guardIdle (hv : rho.ExecutionValid) : rho.GuardIdle := by
  intro i
  unfold Model.Run.guardRefusalsAt
  split
  · rename_i v t he
    unfold Model.Run.tickRefusals
    split
    · rename_i hw
      dsimp only
      rw [runDutiesRefusals_eq_nil S rho v _ _ fun p d hp =>
          dutyRefusals_eq_nil S rho hv
            (.tick he hw (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hp).1))
            (Or.inl ⟨t, he, hw, hp⟩),
        gossipRefusals_eq_nil, List.append_nil]
    · rfl
  · rename_i v o t he
    unfold Model.Run.deliverRefusals
    dsimp only
    rw [runDutiesRefusals_eq_nil S rho v _ _ fun p d hp =>
        dutyRefusals_eq_nil S rho hv
          (.deliver he (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hp).1))
          (Or.inr ⟨t, o, he, hp⟩),
      gossipRefusals_eq_nil, List.append_nil]
  · rfl

end Consensus.Goldilocks.Simulation

end
