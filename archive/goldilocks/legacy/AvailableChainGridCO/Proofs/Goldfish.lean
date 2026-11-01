module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Proofs.Basic

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic

/-- Every obligation deadline is itself a later release cutoff. -/
theorem deadline_eq_release (p : Params) (r : Slot) :
    gateTime p r + lifetime p = releaseTime p (r + p.m) := by
  simp [gateTime, lifetime, releaseTime, proposalTime, Nat.cast_add]
  ring

omit [LeasePolicy] in
/-- An anchored genuine result extends its walk anchor. -/
theorem confirmationFrom_extends (p : Params) {n : Nat} (a : Block) (st : State n)
    (r : Slot) (B : Block) (hc : confirmationFrom p a st r = some B) :
    Block.Preceq a B := by
  unfold confirmationFrom at hc
  dsimp only at hc
  split at hc
  · cases hc
    exact ghost_extends a _ _ _
  · contradiction

theorem forkChoice_extends_liveRoot {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (Wire n)) (current : Slot) :
    Block.preceq (liveRoot st) (forkChoice st tree raw support current) = true := by
  exact ghost_extends (liveRoot st) tree _ _

/-- The late participant seats of one local genuine window. -/
def lateSeats (p : Params) {n : Nat} (st : State n) (r : Slot) : Finset (Fin n) :=
  (seats n (lateVotes p st r)).toFinset

theorem lateSeats_card (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (lateSeats p st r).card = voterCount (lateVotes p st r) := by
  exact List.toFinset_card_of_nodup (List.nodup_dedup _)

/-- A genuine result passes the late-participant majority test at its own
target. The result is local to one reader and one label. -/
theorem confirmation_majority (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (h : confirmation p st r = some B) :
    2 * prefixSupport p st r B > voterCount (lateVotes p st r) := by
  unfold confirmation at h
  dsimp only at h
  split at h
  · rename_i htest
    cases h
    simpa [prefixSupport] using htest
  · simp at h

/-- The numerical core of same-label compatibility. The two cross-view
premises say that both surviving sets occur in each late participant pool.
The disjointness premise is the seat-level consequence of conflicting targets
and late equivocation removal. These premises must be derived from the run's
accepted-object delivery before applying the lemma to `confirmation`. -/
theorem same_label_compatible_of_window_bounds
    {n : Nat} (p : Params) (left right : State n) (r : Slot)
    (B C : Block) (ZB ZC : Finset (Fin n))
    (hB : confirmation p left r = some B)
    (hC : confirmation p right r = some C)
    (hsupportB : ZB.card = prefixSupport p left r B)
    (hsupportC : ZC.card = prefixSupport p right r C)
    (hcrossB : ZB ∪ ZC ⊆ lateSeats p left r)
    (hcrossC : ZB ∪ ZC ⊆ lateSeats p right r)
    (hdisjoint : Block.compatible B C = false → Disjoint ZB ZC) :
    Block.compatible B C = true := by
  by_cases h : Block.compatible B C = true
  · exact h
  · have hf : Block.compatible B C = false := by
      cases hbool : Block.compatible B C <;> simp_all
    have hmajorB : 2 * ZB.card > (lateSeats p left r).card := by
      rw [hsupportB, lateSeats_card]
      exact confirmation_majority p left r B hB
    have hmajorC : 2 * ZC.card > (lateSeats p right r).card := by
      rw [hsupportC, lateSeats_card]
      exact confirmation_majority p right r C hC
    have hd := hdisjoint hf
    have hu : (ZB ∪ ZC).card = ZB.card + ZC.card :=
      Finset.card_union_of_disjoint hd
    have hBL := Finset.card_le_card hcrossB
    have hCL := Finset.card_le_card hcrossC
    omega

/-- Same-label compatibility on a run. The support and cross-view premises
are explicit delivery/participation premises at the two gate inputs; no
claim that the generic delivery predicate supplies them is hidden here. -/
theorem same_label_compatible_in_run
    {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (u v : V)
    (B C : Block) (ZB ZC : Finset (Fin p.n))
    (hB : confirmation p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) u) r = some B)
    (hC : confirmation p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) v) r = some C)
    (hsupportB : ZB.card = prefixSupport p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) u) r B)
    (hsupportC : ZC.card = prefixSupport p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) v) r C)
    (hcrossB : ZB ∪ ZC ⊆ lateSeats p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) u) r)
    (hcrossC : ZB ∪ ZC ⊆ lateSeats p
      (Run.stateBeforeTime (gridCO p) rho (gateTime p r) v) r)
    (hdisjoint : Block.compatible B C = false → Disjoint ZB ZC) :
    Block.compatible B C = true := by
  exact same_label_compatible_of_window_bounds p
    (Run.stateBeforeTime (gridCO p) rho (gateTime p r) u)
    (Run.stateBeforeTime (gridCO p) rho (gateTime p r) v)
    r B C ZB ZC hB hC hsupportB hsupportC hcrossB hcrossC hdisjoint

private theorem foldl_stable {n : Nat} {α : Type}
    (f : State n → α → State n) (xs : List α) (st : State n)
    (hf : ∀ acc x, (f acc x).stableRecord = acc.stableRecord) :
    (xs.foldl f st).stableRecord = st.stableRecord := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, hf]

/-- The local gate records a genuine result when the live obligations permit
it and the result cannot be an ancestor of the prior record. The latter fact
is the outstanding fresh-proposal slot argument in the run-level repair proof. -/
theorem gate_repairs_record (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (hgenuine : confirmation p st r = some B)
    (hguard : st.obligations.any (fun (target, _, _) =>
      !Block.compatible target B) = false)
    (hfresh : Block.preceq B st.stableRecord = false) :
    (gate p st r).stableRecord = B := by
  simp only [gate, hgenuine, hguard, advance, hfresh]
  apply foldl_stable
  intro acc b
  apply foldl_stable
  intro acc g
  rfl

/-- A conflicting stored target is enough to trigger the gate veto. -/
theorem gate_veto_of_live_target (p : Params) {n : Nat}
    (st : State n) (r : Slot) (B K : Block) (g : Nat)
    (deadline : Time) (hgenuine : confirmation p st r = some B)
    (hrow : (K, g, deadline) ∈ st.obligations)
    (hconflict : Block.compatible K B = false) :
    (gate p st r).stableRecord = st.stableRecord ∧
      (gate p st r).obligations = st.obligations := by
  apply gate_veto p st r B hgenuine
  apply List.any_eq_true.mpr
  exact ⟨(K, g, deadline), hrow, by simp [hconflict]⟩

/-- Parent slots increase on an admitted block path. This predicate is a
separate run invariant; it is not true for arbitrary structural blocks. -/
def SlotOrdered : Block → Prop
  | .genesis => True
  | .node parent slot _ _ => parent.slot < slot ∧ SlotOrdered parent

private theorem preceq_slot_le (B C : Block) (hordered : SlotOrdered C)
    (hBC : Block.preceq B C = true) : B.slot ≤ C.slot := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [Block.preceq] using hBC
      subst B
      exact le_refl _
  | node parent slot r_slot root ih =>
      obtain ⟨hparent, horderedParent⟩ := hordered
      have h : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases h with h | h
      · subst B
        exact le_refl _
      · exact le_trans (ih horderedParent h) (Nat.le_of_lt hparent)

theorem gate_repairs_fresh_slot (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block)
    (hgenuine : confirmation p st r = some B)
    (hguard : st.obligations.any (fun (target, _, _) =>
      !Block.compatible target B) = false)
    (hordered : SlotOrdered st.stableRecord)
    (hfresh : st.stableRecord.slot < B.slot) :
    (gate p st r).stableRecord = B := by
  apply gate_repairs_record p st r B hgenuine hguard
  by_contra h
  have hpreceq : Block.preceq B st.stableRecord = true := by
    cases hbool : Block.preceq B st.stableRecord <;> simp_all
  exact Nat.not_lt_of_ge (preceq_slot_le B st.stableRecord hordered hpreceq) hfresh

end AvailableChain.GridCO
end
