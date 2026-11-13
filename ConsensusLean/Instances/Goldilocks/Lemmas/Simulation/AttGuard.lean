module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # The own-object guard at an engine duty prefix, given the signing facts

The guard argument shared by the constant-fault `engine_att_protected` and
`engine_poll_att_protected` (`Simulation/ProvenanceGuard`) and their growing-fault forms
(`Growing/Simulation/Signing`). An actual engine signing passes the candidate/seen protection
boundary of a duty prefix when no two engine signings of the node are slashable (`hns`) and every
own-signed attestation the prefix has seen is an engine signing (`hseen`); each fault model
supplies both from its own honesty premise. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **An engine signing passes the own-object guard** of a duty prefix `nd`: self-conflict is
excluded by `hns`; any conflicting own-signed object `nd` has seen is another engine signing by
`hseen`, which `hns` excludes too. Both conflict orientations are covered. -/
theorem att_protected_of_signings {v : V}
    {nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E)}
    (hns : ∀ {j q j' q' : Nat} {a b : FG.Att (Fintype.card V)},
      EngineSignsAt S rho hn v j q a → EngineSignsAt S rho hn v j' q' b → ¬ FG.slashable a b)
    (hseen : ∀ {a : FG.Att (Fintype.card V)}, a.val = rho.ownKey v →
      attObj a ∈ Model.closure nd.seen → ∃ j q, EngineSignsAt S rho hn v j q a)
    {j q : Nat} {a : FG.Att (Fintype.card V)} (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) (rho.ownKey v) nd.seen
      (attObj a) = true := by
  have hinj {a b : FG.Att (Fintype.card V)}
      (h : attObj (binding := S.vote) a = attObj b) : a = b := by
    injection h with _ h₂
    injection h₂ with h₃
    injection h₃ with h₄
    have hd := congrArg (decodeAtt (Fintype.card V)) h₄
    simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hd
  have hself : conflicts (binding := S.vote) (attObj a) (attObj a) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨b, c, hb, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _ _).mp h
    obtain rfl := hinj hb
    obtain rfl := hinj hc'
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
          obtain rfl := hinj hb
          obtain ⟨j', q', hc'⟩ := hseen (Option.some.inj hk) ho
          exact hns ha hc' hbc
        · obtain ⟨b, c, rfl, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _ _).mp h
          obtain rfl := hinj hc'
          obtain ⟨j', q', hb⟩ := hseen (Option.some.inj hk) ho
          exact hns hb ha hbc
      change (_ != _ || !(conflicts (attObj a) o || conflicts o (attObj a))) = true
      simp [hconf.1, hconf.2]
    · simp [hk]
  · rfl

/-- **The ordinary attestation of an actual poll passes the own-object guard** of the poll's duty
prefix, given that every engine signing of the node passes it (`hprot`). -/
theorem poll_att_protected_of {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hprot : ∀ {j q : Nat} {a : FG.Att (Fintype.card V)}, EngineSignsAt S rho hn v j q a →
      Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) (rho.ownKey v) nd.seen
        (attObj a) = true)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocksWith S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocksWith S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k).2 = some (.att w, cs)) :
    Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) (rho.ownKey v) nd.seen
      (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true := by
  obtain ⟨a, j, q, rfl, hval, ha⟩ := engine_poll_att_signed S rho hn hc hd hsel hm
  have hp := hprot ha
  have he := hval.trans (cut_self S rho hn hc)
  have ho : attObj a = (.mk (.signed (rho.ownKey v) .poll)
      (.data (.att (encodeAtt a))) [] : Wire (Fintype.card V) S.vote) := by
    unfold attObj
    rw [he]
  rw [ho] at hp
  exact hp

end Consensus.Goldilocks.Simulation

end
