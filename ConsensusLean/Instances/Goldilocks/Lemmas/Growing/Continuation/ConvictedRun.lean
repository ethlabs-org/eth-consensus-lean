module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Continuation.HeldViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The conviction bridge of an engine run

`Obligations.Growing.chainConvictedBelow_at`: `ConvictedBelow` of the engine run (the continuation
premise) gives `ChainConvictedBelow` (`Healing/Frontier/Accountable`) on `simTraceAt` with the
time-indexed honest keys. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup) (A : ContractAssumptions S)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The engine premise gives the trace form.** `ConvictedBelow` of the run (at `α = 1/3`) gives
`ChainConvictedBelow` on the canonical trace with the time-indexed honest keys. A trace state
before cut `i` of a node honest at `t ≥ 0`, after every cut before `i`, maps to the engine cut `q`
after the event of its last labelled cut before `i`: its owner is honest at `cutTime q ≤ t`, and
every attestation on a chain of its tree is in its engine view `ViewIdx v q` (its blocks are
genesis or accepted before `cutMap q`, `accepted_in_view_at`). `convicted_count` then bounds the
crossing set by the convictions of the two views. Consumed by the continuation endpoint, which
supplies `ChainConvictedBelow` to the seeded invariant and the continued reads. -/
theorem chainConvictedBelow_at (hv : rho.ExecutionValid)
    (hcb : (Sys (goldilocks S) V).ConvictedBelow (K S A) ⟨E, rho⟩) :
    Compose.Growing.ChainConvictedBelow (simTraceAt S rho hn)
        (honestKeysAt S rho) := by
  classical
  refine Compose.Growing.chainConvictedBelow_iff.2
    fun y z i j t t' ht hi hy ht' hj hz X₁ hX₁ X₂ hX₂ W hW => ?_
  obtain ⟨q₁, hq₁, hh₁, hv₁⟩ := held_atts_in_view_at S rho hn hv ht hi hy
  obtain ⟨q₂, hq₂, hh₂, hv₂⟩ := held_atts_in_view_at S rho hn hv ht' hj hz
  set Vw := rho.ViewIdx (rho.key y) q₁ ∪ rho.ViewIdx (rho.key z) q₂
  have hcount := convicted_count S rho (A := Vw) W fun k hk => by
    obtain ⟨a, ha, b, hb, hak, hab⟩ := hW k hk
    have hmem : ∀ c ∈ Regimes.ChainAtts (simTraceAt S rho hn) y i X₁ ∪
        Regimes.ChainAtts (simTraceAt S rho hn) z j X₂, attObj c ∈ Vw := by
      rintro c (⟨B, hB, -, hc⟩ | ⟨B, hB, -, hc⟩)
      · exact Or.inl (hv₁ B hB c hc)
      · exact Or.inr (hv₂ B hB c hc)
    exact ⟨a, b, hmem a ha, hmem b hb, hak, hab⟩
  have hc := hcb (rho.key y) (rho.key z) q₁ q₂ hq₁ hq₂ hh₁ hh₂
  have hsub : convicted rho.Slashable Vw ⊆ convicted
      ((Sys (goldilocks S) V).convicts ⟨E, rho⟩)
      ((Sys (goldilocks S) V).view ⟨E, rho⟩ (rho.key y) q₁ ∪
        (Sys (goldilocks S) V).view ⟨E, rho⟩ (rho.key z) q₂) := by
    intro x hx
    simp only [convicted, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨o, ho, o', ho', h⟩ := hx
    refine ⟨o, ?_, o', ?_, h⟩
    · rcases ho with ho | ho
      · exact Or.inl ⟨o, ho, rfl⟩
      · exact Or.inr ⟨o, ho, rfl⟩
    · rcases ho' with ho' | ho'
      · exact Or.inl ⟨o', ho', rfl⟩
      · exact Or.inr ⟨o', ho', rfl⟩
  have hle := (hcount.trans (Finset.card_le_card hsub))
  have hα : (K S A).params.α = 1 / 3 := rfl
  rw [hα] at hc
  have hq : ((W.card : Nat) : ℚ) < 1 / 3 * Fintype.card V :=
    lt_of_le_of_lt (by exact_mod_cast hle) hc
  have : (3 * W.card : ℚ) < Fintype.card V := by linarith
  exact_mod_cast this

end Consensus.Goldilocks.Obligations.Growing

end
