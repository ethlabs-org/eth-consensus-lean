module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Unforgeable
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Simulation: the simulating trace's schedule and credentials

The initial state, timing, wake/restart schedule and block/message credentials of `simTrace`,
from a valid engine run. `RunBlocks` continues with payload credentials and blocks of cuts;
`Run` assembles the Goldilocks run. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `LocalRun` -/

/-- Each honest node starts from the initial node state with its own-role vote permission. -/
theorem simTrace_init :
    ∀ y ∈ honestKeys S rho, (simTrace S rho hn).init y =
      Node.initWith (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
        (S.vote.installVote (fun r => decide (y ∈ rho.sel r))
          (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).initial) :=
  by
    intro y _
    rw [(simTrace_encoding S rho hn).1]
    refine traceEncoding_induction S hn (fun e _ =>
      (NodeAsChainShape.CanonicalTrace.simTrace e rho).init y = _) ?_
    intro e _
    have hinit := NodeAsChainShape.CanonicalTrace.initial_eq e rho y
    have hf : (NodeAsChainShape.CanonicalTrace.initial e rho y).fg =
        Store.init (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload := by
      rw [hinit]; rfl
    have hr : (NodeAsChainShape.CanonicalTrace.initial e rho y).record = FG.Record.empty := by
      rw [hinit]; rfl
    rw [NodeAsChainShape.CanonicalTrace.init e rho y hf hr, hinit]
    simp only [NodeAsChainShape.CanonicalTrace.engineRole_eq]
    rfl

/-! ### The engine's schedule and the trace's cuts -/

omit [DecidableEq V] in
theorem ownKey_key (y : Fin (Fintype.card V)) : rho.ownKey (rho.key y) = y :=
  rho.key.symm_apply_apply y

omit [DecidableEq V] in
theorem ownKey_key' (v : V) : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v

omit [DecidableEq V] in
theorem key_of_ownKey {v : V} {y : Fin (Fintype.card V)} (h : rho.ownKey v = y) :
    v = rho.key y := by
  rw [← h]; exact (rho.key.apply_symm_apply v).symm

/-- Protocol actions, unlike observation filler, stay within the engine horizon. -/
theorem simTrace_labelled_time_le (hv : rho.ExecutionValid) {k : Nat}
    (hl : (simTrace S rho hn).label k ≠ none) :
    (simTrace S rho hn).time k ≤ rho.horizon := by
  obtain ⟨_, _, ev, _, he, _, _, _, _, ht, _⟩ := simTrace_cut S rho hn hl
  rw [ht]
  exact (hv.in_horizon ev (List.mem_of_getElem? he)).2

theorem awake_iff' (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ E.awake (rho.key y) t = true ∧ 0 ≤ t ∧
      t ≤ rho.horizon := by
  rw [simTrace_awake_iff, awakeAt_iff]

/-- Canonical labelled coverage cannot extend its explicit observation horizon. -/
theorem simTrace_inHorizon_le (hv : rho.ExecutionValid) {t : Time}
    (ht : (simTrace S rho hn).InHorizon t) : t ≤ rho.horizon := by
  rw [(simTrace_encoding S rho hn).1] at ht
  exact (NodeAsChainShape.CanonicalTrace.inHorizon_iff (traceEncoding S hn) rho hv t).mp ht

/-- Cuts are at times from `0` on. -/
theorem simTrace_time_nonneg (hv : rho.ExecutionValid) :
    ∀ i, 0 ≤ (simTrace S rho hn).time i := by
  rw [(simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.time_nonneg (traceEncoding S hn) rho hv

/-- The cut order is by time. -/
theorem simTrace_time_mono (hv : rho.ExecutionValid) : Monotone (simTrace S rho hn).time := by
  rw [(simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.time_mono (traceEncoding S hn) rho hv

/-- Finitely many labelled cuts in every bounded interval. -/
theorem simTrace_finite (_hv : rho.ExecutionValid) :
    ∀ T : Time,
      {i | (simTrace S rho hn).label i ≠ none ∧ (simTrace S rho hn).time i ≤ T}.Finite := by
  rw [(simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.finite (traceEncoding S hn) rho

/-- At one time, across the honest nodes, the groups are in phase order. -/
theorem simTrace_phase_order (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ y' ∈ honestKeys S rho, ∀ j j' t e e',
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y' j' t e' → j < j' →
        e.phase ≤ e'.phase := by
  intro y _ y' _ j j' t e e' hg hg' hjj'
  obtain ⟨hp, hd⟩ := runProposer_digestOf S rho hn
  simp only [(simTrace_encoding S rho hn).1, hp, hd] at hg hg'
  exact NodeAsChainShape.CanonicalTrace.phase_order (traceEncoding S hn) rho hv hg hg' hjj'

/-- A tick is at a public time. -/
theorem simTrace_tick_public (_hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t,
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t →
      (S.params (pubOf E) hn).toParams.IsPublic t := by
  intro y _ j t hg
  obtain ⟨hp, hd⟩ := runProposer_digestOf S rho hn
  rw [(simTrace_encoding S rho hn).1, hp, hd] at hg
  exact NodeAsChainShape.CanonicalTrace.tick_public (traceEncoding S hn) rho hg

/-- One tick per node and time. -/
theorem simTrace_tick_unique (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j j' t,
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t →
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j' t → j = j' := by
  intro y _ j j' t hg hg'
  obtain ⟨hp, hd⟩ := runProposer_digestOf S rho hn
  simp only [(simTrace_encoding S rho hn).1, hp, hd] at hg hg'
  exact NodeAsChainShape.CanonicalTrace.tick_unique (traceEncoding S hn) rho hv hg hg'

/-- An honest node is called only while awake. -/
theorem simTrace_awake_of_call (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).IsCall y i →
      (simTrace S rho hn).awake y ((simTrace S rho hn).time i) := by
  intro y _ i hc
  rw [(simTrace_encoding S rho hn).1] at hc ⊢
  exact NodeAsChainShape.CanonicalTrace.awake_of_call (traceEncoding S hn) rho hv hc

/-- A restart is a wake. -/
theorem simTrace_sleep_of_restart (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).RestartAt y i →
      ∃ u : Time, 0 ≤ u ∧ u < (simTrace S rho hn).time i ∧ ¬ (simTrace S rho hn).awake y u ∧
        ∀ j < i, (simTrace S rho hn).IsCall y j → (simTrace S rho hn).time j < u := by
  intro y _ i hr
  rw [(simTrace_encoding S rho hn).1] at hr ⊢
  exact NodeAsChainShape.CanonicalTrace.sleep_of_restart (traceEncoding S hn) rho hv hr

/-- An honest node is asleep one tick before each of its restarts. -/
theorem simTrace_asleep_before_restart (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).RestartAt y i →
      ¬ (simTrace S rho hn).awake y ((simTrace S rho hn).time i - 1) := by
  rintro y hy i ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ h
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨r, i₀, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  obtain ⟨-, -, hw2⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  have hw := ((awake_iff' S rho hn y _).mp h).1
  rw [ht, hw2] at hw
  exact Bool.false_ne_true hw

omit [DecidableEq V] in
theorem blockObj_fields {B C : Blk (S.params (pubOf E) hn)}
    (hB : B.parent ≠ none) (hC : C.parent ≠ none)
    (hrB : B.RootOk (digestOf S rho)) (hrC : C.RootOk (digestOf S rho))
    (he : blockObj (S.params (pubOf E) hn) (binding := S.vote) B =
      blockObj (S.params (pubOf E) hn) C) : B = C := by
  have hh := congrArg Model.Obj.msg he
  have ha := congrArg Model.Obj.auth he
  simp only [blockObj_eq, Model.Obj.msg, Model.Msg.item.injEq] at hh
  simp only [blockObj_eq, Model.Obj.auth, Model.Auth.signed.injEq] at ha
  have hp := congrArg (fun h => parentRoot S.genesisRoot h.parent) hh
  have hs := congrArg Header.pos hh
  have hx := congrArg Header.input hh
  have hi := congrArg (fun h => decodeInfo (Fintype.card V) h.info) hh
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hB
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hC
  simp only [headerOf_eq, hb, hc, parentRoot_parentRef] at hp
  simp only [headerOf_eq, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hi
  have hparent : B.parent = C.parent := by simpa [hb, hc] using hp
  change B.slot = C.slot at hs
  change B.input = C.input at hx
  have hroot : B.root = C.root := by
    change B.root = digestOf S rho B.parent B.slot B.input B.fgPayload B.acPayload at hrB
    rw [hrB, hparent, hs, hx, hi.1, hi.2]
    exact hrC.symm
  have hv := ha.1
  cases B; cases C
  simp_all

/-- Engine `Credentials` assigns every delivered proposal, including a faulty signer's,
to the selected proposer. Decode the group's source object and use `selValid_proposer` to
identify its signer with the run schedule. This is separate from honest-source unforgeability. -/
theorem simTrace_proposerCredential (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t B,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t (.block B) →
        B.proposer = runProposer S rho hn B.slot := by
  intro y _ j t B hg
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  rw [(simTrace_encoding S rho hn).1, hpr, hdg] at hg
  rw [hpr]
  exact NodeAsChainShape.CanonicalTrace.proposerCredential (traceEncoding S hn) rho hv
    (fun s => by simpa only [hpr] using selValid_proposer S rho hn hv.selValid s) hg

/-- A released canonical own vote comes from an emission before the event's end cut. -/
theorem released_vote_cut (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time}
    (hs : rho.SendsAt v i t) (hv' : v ∉ rho.faultyAt 0) {m : Vote (Fintype.card V)}
    (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m :=
  released_vote_cut_of S rho hn hv hs (fun _ => hv') (preNode_releasable S rho hn hf hv hv') hb

end Consensus.Goldilocks.Simulation

end
