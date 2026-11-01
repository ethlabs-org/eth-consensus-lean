module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSAProofs.Proofs.Shared.Walk

public section

/-! The short lock-window bound (pcsa34-r4.3b §5.6.2).
Run provenance and anchor compatibility are explicit inputs. The bound
applies at both the proposal read and the HEAD read. -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- The oldest saved result in a slow write bounds the target's slot.
The two store inputs express result-label validity and slot order. -/
theorem slow_lock_oldest_label (p : Params) (v : GridCO.State p.n .root)
    (j : Slot) (B : Block)
    (heligible : SA.Root.slowEligible p.toParams v j B = true)
    (resultLabels : ∀ i C, GridCO.savedGenuine v i = some (some C) → C.slot ≤ i)
    (slotOrder : ∀ i C, GridCO.savedGenuine v i = some (some C) →
      Block.Preceq B C → B.slot ≤ C.slot) :
    p.k ≤ j + 1 ∧ B.slot ≤ j - (p.k - 1) := by
  try delta Slot Time at *
  have hk := p.kLarge
  change (decide (p.k ≤ j + 1) && (List.range (p.k - 1)).all (fun d =>
    match GridCO.savedGenuine v (j - (d + 1)) with
    | some (some C) => Block.preceq B C
    | _ => false)) = true at heligible
  obtain ⟨hj, hall⟩ := Bool.and_eq_true_iff.mp heligible
  have he := List.all_eq_true.mp hall (p.k - 2) (List.mem_range.mpr (by omega))
  have hi : p.k - 2 + 1 = p.k - 1 := by omega
  rw [hi] at he
  refine ⟨of_decide_eq_true hj, ?_⟩
  cases hc : GridCO.savedGenuine v (j - (p.k - 1)) with
  | none => simp only [hc, Bool.false_eq_true] at he
  | some C =>
    cases C with
    | none => simp only [hc, Bool.false_eq_true] at he
    | some C =>
      rw [hc] at he
      exact (slotOrder _ C hc he).trans (resultLabels _ C hc)

/-- A compatible target with a full slow window before s₁ is below the anchor. -/
theorem lock_window_below_anchor (p : Params) (cA s₁ j : Slot) (P B : Block)
    (hwindow : s₁ - 1 - cA ≤ p.k - 1) (horder : cA < s₁)
    (hj : j ≤ s₁ - 1) (_hk : p.k ≤ j + 1)
    (holdest : B.slot ≤ j - (p.k - 1))
    (hcompat : Block.Compatible B P)
    (strictSlots : Block.Preceq P B → P ≠ B → cA < B.slot) :
    Block.Preceq B P := by
  try delta Slot Time at *
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · exact h
  · by_cases he : P = B
    · subst B
      exact block_preceq_refl _
    · have hs := strictSlots h he
      omega

/-- Locks below the base cannot change the effective root. -/
theorem liveRoot_eq_base_of_locks_below (p : Params) (st : State p.n)
    (pc : Option (PC p.n)) (P : Block)
    (hbase : Block.Preceq P (walkBase p st pc))
    (hlocks : ∀ B, LiveLease st B → Block.Preceq B P) :
    liveRoot p st pc = walkBase p st pc := by
  try delta Slot Time at *
  rcases pcsa_liveRoot_origin p st pc with he | hm
  · exact he
  · obtain ⟨row, hr, he, ht, _, _, hd, _⟩ := (pcsa_walkLocks_mem p st pc _).mp hm
    have hb := block_preceq_trans (hlocks _ ⟨row, hr, he, ht⟩) hbase
    have hdepth := prefix_depth _ _ hb
    omega

/-- Corrected F4's proposer clause when the live root equals the base. -/
theorem root_reachable_of_locks_below (p : Params) (st : State p.n)
    (pc : Option (PC p.n)) (P : Block)
    (hbase : Block.Preceq P (walkBase p st pc))
    (hlocks : ∀ B, LiveLease st B → Block.Preceq B P)
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost (walkBase p st pc) tree
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) := by
  try delta Slot Time at *
  rw [liveRoot_eq_base_of_locks_below p st pc P hbase hlocks]
  exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _

/-- Corrected F4's voter upper bound is vacuous when all locks are below the base. -/
theorem lock_upper_bound_of_below_base (st : State n) (P V H : Block)
    (hbase : Block.Preceq P V)
    (hlocks : ∀ B, LiveLease st B → Block.Preceq B P) :
    ∀ B, LiveLease st B → V.depth < B.depth → Block.Preceq B H := by
  try delta Slot Time at *
  intro B hB hd
  have hb := prefix_depth _ _ (block_preceq_trans (hlocks B hB) hbase)
  omega

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- Lemma 5.6.2 at both required reads, conditional on run lock provenance
and the anchor persistence and slot-order facts. No common lock store is assumed. -/
theorem recovery_lock_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (cA s₁ : Slot) (P : Block)
    (hwindow : s₁ - 1 - cA ≤ p.k - 1) (horder : cA < s₁)
    (lockOrigin : ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B →
      ∃ j, SA.gateTime p.toParams j ≤ t ∧ p.k ≤ j + 1 ∧ B.slot ≤ j - (p.k - 1))
    (anchorCompatible : ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B →
      Block.Compatible B P)
    (strictSlots : ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B →
      Block.Preceq P B → P ≠ B → cA < B.slot) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd →
      ∀ B, LiveLease nd.st B → Block.Preceq B P := by
  try delta Slot Time at *
  intro x hx t ht nd hnd B hB
  obtain ⟨j, hj, hk, hb⟩ := lockOrigin x hx t ht nd hnd B hB
  have hbefore : j ≤ s₁ - 1 := by
    try delta Slot Time at *
    have hd : (0 : Int) < p.Δ := p.deltaPos
    have htime : t ≤ 4 * p.Δ * (s₁ : Int) + p.Δ := by
      try delta Slot Time at *
      rcases ht with rfl | rfl
      · change 4 * p.Δ * (s₁ : Int) ≤ _
        linarith
      · exact le_rfl
    change 4 * p.Δ * (j : Int) + 6 * p.Δ ≤ t at hj
    by_contra hn
    have hge : (s₁ : Int) ≤ (j : Int) := by omega
    have hmul := mul_le_mul_of_nonneg_left hge (show (0 : Int) ≤ 4 * p.Δ by positivity)
    linarith
  exact lock_window_below_anchor p cA s₁ j P B hwindow horder hbefore hk hb
    (anchorCompatible x hx t ht nd hnd B hB) (strictSlots x hx t ht nd hnd B hB)

end AvailableChain.PCSA.Run
end
