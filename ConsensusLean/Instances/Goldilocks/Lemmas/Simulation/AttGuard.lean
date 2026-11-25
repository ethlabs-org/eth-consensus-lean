module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
public import ConsensusLean.Spec.Model.Guard
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # Slashing protection at an engine duty prefix, given the signing facts

The argument behind `guardIdle` (`Growing/Simulation/GuardIdle`). An actual engine signing passes
slashing protection against a `seen` log when no two engine signings of the node are slashable
(`hns`) and every own-signed attestation the log has seen is an engine signing (`hseen`,
`att_protected_of_signings`). A batch releases its candidates one after the other, each checked
against the log at its own turn, which holds the candidates released before it
(`guardRefusals_eq_nil_of_preserves`); every attestation candidate of a poll's batch, its ordinary
emission or a flushed held attestation, is an engine signing (`batch_att_candidate`), so `hseen`
holds at every turn of the batch. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

section Release

variable {pub : Model.Public} {Out : Type} {P : Model.Protocol pub Out}

/-- **Guard bookkeeping over the actual release prefix.** Let `Q` hold of every candidate, and of
everything the node has seen, at any depth. If every candidate passes `protects` against any log
whose contents satisfy `Q` at every depth, none is refused: each turn's log is the starting log
plus the candidates released before it, and a released candidate carries only what the log
already holds. -/
theorem guardRefusals_eq_nil_of_preserves (hash : P.Item → Nat) (k : Model.Key pub)
    (Q : P.Object → Prop) :
    ∀ cs : List P.Object, (∀ c ∈ cs, Q c) →
      (∀ c ∈ cs, ∀ seen : List P.Object, (∀ o ∈ seen, ∀ d, Model.Obj.Contains o d → Q d) →
        Model.protects P k seen c = true) →
      ∀ nd : Model.Node P, (∀ o ∈ nd.seen, ∀ d, Model.Obj.Contains o d → Q d) →
        Model.guardRefusals P hash k nd cs = []
  | [], _, _, _, _ => rfl
  | c :: cs, hq, hp, nd, hs => by
    rw [Model.guardRefusals_cons]
    simp only [hp c List.mem_cons_self nd.seen hs, ↓reduceIte, List.nil_append]
    exact guardRefusals_eq_nil_of_preserves hash k Q cs
      (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      _ (Model.releaseAll_preserves hash k Q nd [c] hs fun o ho => hq o
        (List.mem_singleton.mp (Model.releaseAll_subset hash k nd [c] o ho) ▸
          List.mem_cons_self)).1

end Release

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Distinct attestations have distinct attestation objects. -/
theorem attObj_inj {a b : FG.Att (Fintype.card V)}
    (h : attObj (binding := S.vote) a = attObj b) : a = b := by
  injection h with _ h₂
  injection h₂ with h₃
  injection h₃ with h₄
  have hd := congrArg (decodeAtt (Fintype.card V)) h₄
  simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hd

/-- **An engine signing passes the own-object guard** of a duty prefix `nd`: self-conflict is
excluded by `hns`; any conflicting own-signed object `nd` has seen is another engine signing by
`hseen`, which `hns` excludes too. Both conflict orientations are covered. -/
theorem att_protected_of_signings {v : V}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hns : ∀ {j q j' q' : Nat} {a b : FG.Att (Fintype.card V)},
      EngineSignsAt S rho hn v j q a → EngineSignsAt S rho hn v j' q' b → ¬ FG.slashable a b)
    (hseen : ∀ {a : FG.Att (Fintype.card V)}, a.val = rho.ownKey v →
      attObj a ∈ Model.closure nd.seen → ∃ j q, EngineSignsAt S rho hn v j q a)
    {j q : Nat} {a : FG.Att (Fintype.card V)} (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (attObj a) = true := by
  have hself : conflicts (binding := S.vote) (attObj a) (attObj a) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨b, c, hb, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _ _).mp h
    obtain rfl := attObj_inj S hb
    obtain rfl := attObj_inj S hc'
    exact hns ha ha hbc
  unfold Model.protects
  split
  · simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hself, ?_⟩
    rw [List.all_eq_true]
    intro o ho
    by_cases hk : o.signer? = some (rho.ownKey v)
    · have hconf : conflicts (attObj a) o = false ∧ conflicts o (attObj a) = false := by
        constructor <;> apply Bool.eq_false_iff.mpr <;> intro h
        · obtain ⟨b, c, hb, rfl, hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _ _).mp h
          obtain rfl := attObj_inj S hb
          obtain ⟨j', q', hc'⟩ := hseen (Option.some.inj hk) ho
          exact hns ha hc' hbc
        · obtain ⟨b, c, rfl, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _ _).mp h
          obtain rfl := attObj_inj S hc'
          obtain ⟨j', q', hb⟩ := hseen (Option.some.inj hk) ho
          exact hns hb ha hbc
      change (_ != _ || !(conflicts (attObj a) o || conflicts o (attObj a))) = true
      simp [hconf.1, hconf.2]
    · simp [hk]
  · rfl

/-- **Every attestation candidate of a poll's batch is an engine signing.** A candidate of a
scheduled poll's batch that is an attestation body signed in the poll role, whether the poll's
ordinary emission or a held attestation it flushes, is the node's own attestation object of an
engine signing. Block wrappers and vote envelopes are not attestation bodies. -/
theorem batch_att_candidate {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {c}
    (hm : c ∈ rho.signedCandidate v (.poll k)
      ((pollBatch (nd.st.1 hn) k (S.release (Model.pubOf E))).2.map
        fun bc => (Model.Msg.data bc.1, bc.2)))
    {x w} (he : c = .mk (.signed x .poll) (.data (.att w)) []) :
    ∃ a j q, c = attObj a ∧ a.val = rho.ownKey v ∧ EngineSignsAt S rho hn v j q a := by
  obtain ⟨m, cs, hmc, -, -, rfl⟩ := rho.mem_signedCandidate.mp hm
  obtain ⟨hauth, hmsg, rfl⟩ := Model.Obj.mk.inj he
  subst hmsg
  obtain ⟨⟨b, cs'⟩, hb, heq⟩ := List.mem_map.mp hmc
  obtain ⟨hb', rfl⟩ := Prod.mk.inj heq
  cases Model.Msg.data.inj hb'
  obtain ⟨a, j, q, rfl, -, hval, ha⟩ := engine_batch_att_signed S rho hn hc hd hsel hb
  have hav := hval.trans (cut_self S rho hn hc)
  refine ⟨a, j, q, ?_, hav, ha⟩
  injection hauth with _ hr
  unfold attObj
  rw [hav, hr]
  rfl

end Consensus.Goldilocks.Simulation

end
