module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Publication
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates

public section

/-! # Own-block publication in the growing canonical trace -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Own blocks are released by their actual engine tick; no global static run is needed. -/
theorem simTraceAt_block_released (hv : rho.ExecutionValid) :
    ∀ y k B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k B _ ⟨⟨acc, hnode, hlab⟩, hpos⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, hp', hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hpos' : r.pos ≠ 0 := hp' ▸ hpos
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he,
      (tick_block_vote_releases_at S rho hn hv he hp r hmem).1 B acc hrl hpos'⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, hposk⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    exact hpos' (hposk.trans
      (pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk (hlabk.symm.trans hrl)))
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, hposk, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    exact hpos' (hposk.trans (pos_of_block_cut _ _ _ _ _ (e := .restart)
      (fun x h => by cases h) hk' (hlabk.symm.trans hrl)))

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
