module
public import AvailableChainGeneric.Statements.AC.Lease -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.AC.LeaseWindow
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import Mathlib.Data.Finset.Card

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- A write keeps at most one deadline for each key.
Source: GridCO/Proofs/Map.lean:1693–1717; step4b-plan.md, S4b-08, Q4 A. -/
theorem write_unique_keys {n : Nat} (st : GridCO.State n) (b : Block) (g : Nat)
    (deadline : Time) (hu : UniqueLeaseKeys st) :
    UniqueLeaseKeys (GridCO.writeObligation st b g deadline) := by
  intro x hx y hy hkey
  dsimp only [GridCO.writeObligation] at hx hy
  simp only [List.mem_append, List.mem_singleton] at hx hy
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact hu x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hkey
    · subst y
      have hneq := (List.mem_filter.mp hx).2
      have heq : x.1 = b ∧ x.2.1 = g := by
        simpa only [Prod.mk.injEq] using hkey
      simp [heq.1, heq.2] at hneq
  · subst x
    rcases hy with hy | hy
    · have hneq := (List.mem_filter.mp hy).2
      have heq : y.1 = b ∧ y.2.1 = g := by
        simpa only [Prod.mk.injEq] using hkey.symm
      simp [heq.1, heq.2] at hneq
    · subst y
      rfl

/-- A unique stored row supplies its deadline to a renewal.
Source: GridCO/Proofs/Protection.lean:37–51; step4b-plan.md, S4b-08, Q4 A. -/
theorem deadlineOf_eq_of_lease_row {n : Nat} (st : GridCO.State n) (B : Block) (g : Nat)
    (d : Time) (hu : UniqueLeaseKeys st) (hr : (B, g, d) ∈ st.obligations) :
    GridCO.deadlineOf st B g = some d := by
  unfold GridCO.deadlineOf
  cases hf : st.obligations.find? (fun (target, level, _) => target == B && level == g) with
  | none =>
      have := List.find?_eq_none.mp hf (B, g, d) hr
      simp at this
  | some row =>
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have hk : (row.1, row.2.1) = (B, g) := by
        simpa using hp
      have he := hu row hm (B, g, d) hr hk
      simp [he]

/-- A write at any key cannot shorten a protected deadline.
Source: GridCO/Proofs/Protection.lean:55–66; step4b-plan.md, S4b-08, Q4 A. -/
theorem write_protectsUntil {n : Nat} (st : GridCO.State n) (B C : Block) (g k : Nat)
    (d limit : Time) (hu : UniqueLeaseKeys st) (h : ProtectsUntil st B g d) :
    ProtectsUntil (GridCO.writeObligation st C k limit) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  by_cases hk : (B, g) = (C, k)
  · have ⟨hB, hg⟩ := Prod.mk.inj hk
    subst C
    subst k
    refine ⟨max deadline limit, le_trans hd (le_max_left _ _), ?_⟩
    dsimp only [GridCO.writeObligation]
    simp [deadlineOf_eq_of_lease_row st B g deadline hu hr]
  · refine ⟨deadline, hd, List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hr, ?_⟩))⟩
    simpa only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      Prod.mk.injEq, not_and_or] using hk

/-- Expiry keeps a row whose protected deadline is still in the future.
Source: GridCO/Proofs/Protection.lean:25–29; step4b-plan.md, S4b-08, Q4 A. -/
theorem expire_protectsUntil {n : Nat} (st : GridCO.State n) (B : Block) (g : Nat)
    (d t : Time) (h : ProtectsUntil st B g d) (ht : t < d) :
    ProtectsUntil (GridCO.expire st t) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  exact ⟨deadline, hd, List.mem_filter.mpr ⟨hr, decide_eq_true (lt_of_lt_of_le ht hd)⟩⟩

/-- Release keeps protection when the conflict count is below the level.
Source: GridCO/Proofs/Protection.lean:31–35; step4b-plan.md, S4b-08, Q4 A. -/
theorem release_protectsUntil (p : GridCO.Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (B : Block) (g : Nat) (d : Time) (h : ProtectsUntil st B g d)
    (hc : GridCO.releaseCount p st r B < g) :
    ProtectsUntil (GridCO.release p st r) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  exact ⟨deadline, hd, List.mem_filter.mpr ⟨hr, decide_eq_true hc⟩⟩

/-- Seats counted against `B` remove its row when they meet its level.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Model/Protocol.lean:396–403.
The count is read from `st`, before release. -/
theorem release_of_supporters (p : GridCO.Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (B : Block) (g : Nat) (d : Time) (Q : Finset (Fin n))
    (hg : g ≤ Q.card) (hcount : Q.card ≤ GridCO.releaseCount p st r B) :
    (B, g, d) ∉ (GridCO.release p st r).obligations := by
  intro hr
  have hlt : GridCO.releaseCount p st r B < g :=
    of_decide_eq_true (List.mem_filter.mp hr).2
  exact Nat.not_lt_of_ge (le_trans hg hcount) hlt

/-- S4b-01, Q1 A: both live targets are below the same output. -/
theorem lease_chain_statement : LeaseChainStatement := by
  rw [LeaseChainStatement_def]
  intro V In P E rho A laws i x hx l k hl hk hll hkl
  exact Pure.block_compatible_of_common
    (laws.lease_le_output i x hx l hl hll)
    (laws.lease_le_output i x hx k hk hkl)

/-- S4b-01, Q1 A. Adapted from GridCO/Proofs/Protection.lean:139–179;
expiry and output normalization follow the event-indexed gate law. -/
theorem pendingGate_harmless_statement : PendingGateHarmlessStatement := by
  rw [PendingGateHarmlessStatement_def]
  intro V In P E rho A laws i s x he B g d hr hd hB
  have gate := laws.gate_write i s x he
  have hrow : (B, g, d) ∈ (A.gateView i x s).obligations := by
    rw [ACReads.gateView_def]
    change (B, g, d) ∈ ((A.activeView i x).obligations.filter
      (fun (_, _, deadline) => SA.gateTime A.prm s < deadline))
    exact List.mem_filter.mpr
      ⟨gate.view_leases.symm ▸ hr, by simpa only [decide_eq_true_eq] using hd⟩
  rcases gate.effects with skip | run
  · rw [skip.2.1]
    exact hB
  · cases hraw : A.raw i s x with
    | none =>
        rw [(run.empty hraw).1]
        exact hB
    | some candidate =>
        classical
        by_cases hveto : ∃ lease ∈ (A.gateView i x s).obligations,
            ¬ Block.Compatible (Lease.target lease) candidate
        · rw [(run.veto candidate hraw hveto).1]
          exact hB
        · have hall : ∀ lease ∈ (A.gateView i x s).obligations,
              Block.Compatible (Lease.target lease) candidate := by
            intro lease hlease
            exact Classical.byContradiction (fun h => hveto ⟨lease, hlease, h⟩)
          have hcomp : Block.Compatible B candidate := hall (B, g, d) hrow
          have hadvance : Block.Preceq B (GridCO.advance (A.output i x) candidate) := by
            unfold GridCO.advance
            split
            · exact hB
            · rename_i hn
              rcases Bool.or_eq_true_iff.mp hcomp with hforward | hback
              · exact hforward
              · exact (hn (Pure.block_preceq_trans hback hB)).elim
          rw [(run.accept candidate hraw hall).1, normalizeOutput_def]
          split
          · exact hadvance
          · rename_i hn
            rcases Pure.block_preceq_total_of_common hB (laws.anchor_le_output i x) with
              hprefix | hanchor
            · exact hprefix
            · exact (hn (Pure.block_preceq_trans hanchor hadvance)).elim

variable {V : Type} {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

/-- The live targets of two leases at an honest node are compatible. -/
theorem lease_chain (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
    (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
    (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
    (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k) :
    Block.Compatible (Lease.target l) (Lease.target k) :=
  lease_chain_statement A laws i x hx l k hl hk hll hkl

/-- A gate retains an output prefix whose lease is live at the gate time. -/
theorem pendingGate_harmless (A : ACReads E rho) (laws : ACLaws A)
    (i : Nat) (s : Slot) (x : V)
    (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
    (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
    (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)) :
    Block.Preceq B (A.output (i + 1) x) :=
  pendingGate_harmless_statement A laws i s x he B g d hr hd hB

end AvailableChain.Gen.AC

namespace AvailableChain.Gen.AC

open AvailableChain

/-- A live origin must be inside the saved window; its prefixes are compatible.
DC: none; INTENTIONAL addition: SA lease windows use release schedules; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem slow_window_conflict_absurd_statement : SlowWindowConflictAbsurdStatement := by
  rw [SlowWindowConflictAbsurdStatement_def]
  intro leases result releaseTime s k B hmono horigin hwindow hsame lease hlease hlive hconf
  obtain ⟨w, C, hws, hdeadline, hC, htarget⟩ := horigin lease hlease
  have hwindowLabel : s + 1 ≤ w + k := by
    by_contra hn
    have hold : w + k ≤ s := by omega
    exact (not_le_of_gt hlive) (le_trans hdeadline (hmono hold))
  obtain ⟨D, hD, hB⟩ := hwindow w hws hwindowLabel
  have hCD := hsame w hws hwindowLabel C D hC hD
  have htargetD := Pure.block_compatible_of_preceq_compatible htarget hCD
  have hDtarget : Block.Compatible D (Lease.target lease) := by
    simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using htargetD
  have hBtarget := Pure.block_compatible_of_preceq_compatible hB hDtarget
  apply hconf
  simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using hBtarget

/-- The usable Gen slow-window conflict theorem.
DC: none; INTENTIONAL addition: SA lease windows use release schedules; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem slow_window_conflict_absurd : SlowWindowConflictAbsurdStatement :=
  slow_window_conflict_absurd_statement

/-- Monotone thresholds put the deadline at or before the expiry time.
DC: none; INTENTIONAL addition: SA expires lease rows at thresholds; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem expire_by_threshold_statement : ExpireByThresholdStatement := by
  rw [ExpireByThresholdStatement_def]
  intro n st expiry w c B g d t hmono hwc hdeadline htime hrow
  have hdt : d ≤ t := le_trans hdeadline (le_trans (hmono hwc) htime)
  have hlive : t < d := of_decide_eq_true (List.mem_filter.mp hrow).2
  exact (not_lt_of_ge hdt) hlive

/-- The usable Gen threshold-expiry theorem, including equality.
DC: none; INTENTIONAL addition: SA expires lease rows at thresholds; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem expire_by_threshold : ExpireByThresholdStatement :=
  expire_by_threshold_statement

end AvailableChain.Gen.AC
