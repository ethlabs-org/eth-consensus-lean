module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Publication
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups

public section

/-! # Own-block publication in the growing canonical trace -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Own blocks are released by their actual engine tick; no global static run is needed. -/
theorem simTraceAt_block_released (hv : rho.ExecutionValid) :
    ∀ y k B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k B _ hB
  exact own_block_released_of S rho hn
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).1) hB

/-- A wire block accepted at position zero is relayed at the delivery's time. -/
theorem simTraceAt_block_relayed (hv : rho.ExecutionValid) :
    ∀ y k B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).AcceptAt y k B → (simTraceAt S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B)
          ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k B _ ⟨hnode, hlab⟩ hpos
  erw [relayedFrom_iff]
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inl ⟨B, Option.some.inj (hrl.symm.trans hlab), rfl⟩)
  exact ⟨cs, hx, hcs⟩

/-- A wire attestation at position zero is relayed at the delivery's time. -/
theorem simTraceAt_att_relayed (hv : rho.ExecutionValid) :
    ∀ y k a, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).AttCallAt y k a → (simTraceAt S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (attObj a) ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k a _ ⟨hnode, hlab⟩ hpos
  erw [relayedFrom_iff]
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inr ⟨a, Option.some.inj (hrl.symm.trans hlab), rfl⟩)
  exact ⟨cs, hx, hcs⟩

end Consensus.Goldilocks.Simulation
