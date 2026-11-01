module
public import AvailableChainSAPC.Proofs.Archive
public import AvailableChainGridCO.Proofs.Stamps

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic

theorem fold_field {α β γ : Type} (f : α → γ) (step : α → β → α)
    (h : ∀ st x, f (step st x) = f st) (xs : List β) (st : α) :
    f (xs.foldl step st) = f st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (h st x)

/-- The PC gate changes no receipt data, in either mode. -/
theorem gateWithPC_receiptData (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (c : Option (PC n)) :
    GridCO.receiptData (gateWithPC p st r c) = GridCO.receiptData st := by
  cases c with
  | none => exact @GridCO.gate_receiptData GridCO.slowLeasePolicy p.engine n st r
  | some cert =>
      cases hc : SA.confirmation p st r with
      | none => simp [gateWithPC, hc, GridCO.receiptData]
      | some b =>
        simp only [gateWithPC, hc]
        split
        · rfl
        · rw [fold_field GridCO.receiptData _ (by
            intro acc b
            exact fold_field GridCO.receiptData _ (by intros; rfl) _ _)]
          split <;> rfl

theorem clock_receiptData (p : Params) {n : Nat} (st : State n) (t : Time) :
    GridCO.receiptData (clock p st t).base = GridCO.receiptData st.base := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, gateWithPC_receiptData, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem clock_blocks (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).base.blocks = st.base.blocks :=
  congrArg Prod.fst (clock_receiptData p st t)

theorem clock_bestPC (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).bestPC = st.bestPC := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem receiveHead_blocks (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    (receiveHead p st o).base.blocks = st.base.blocks := by
  unfold receiveHead
  split
  · dsimp only
    split
    · rfl
    · simp only [GridCO.admitVote]
      split <;> (try split_ifs) <;> rfl
  · rfl

theorem receiveHead_now (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    (receiveHead p st o).base.now = st.base.now := by
  unfold receiveHead
  split
  · dsimp only
    split
    · rfl
    · simp only [GridCO.admitVote]
      split <;> (try split_ifs) <;> rfl
  · rfl

theorem receiveHead_bestPC (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    (receiveHead p st o).bestPC = st.bestPC := by
  unfold receiveHead
  split
  · dsimp only
    split <;> (try split_ifs) <;> rfl
  · rfl

/-- Each admitted raw signature is stored, including third targets and
ack variants. The ordinary cache can reject its base key independently. -/
theorem receiveHead_mem (p : Params) {n : Nat} (st : State n) (o : HeadWire n)
    (r : Slot) (hr : headLabel? o = some r)
    (ht : r ≤ (st.base.now / (4 * p.Δ)).toNat) :
    o ∈ (receiveHead p st o).receivedHeads := by
  cases o with
  | mk auth data =>
      cases auth with
      | seat label i =>
          simp only [headLabel?, Option.some.injEq] at hr
          subst label
          simp only [receiveHead, Nat.not_lt.mpr ht, ↓reduceIte]
          split <;> simp_all
      | proposer label => simp [headLabel?] at hr
      | none => simp [headLabel?] at hr

theorem receiveHeads_blocks (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    (xs.foldl (receiveHead p) st).base.blocks = st.base.blocks :=
  fold_field (fun s => s.base.blocks) _ (receiveHead_blocks p) xs st

theorem receiveHeads_now (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    (xs.foldl (receiveHead p) st).base.now = st.base.now :=
  fold_field (fun s => s.base.now) _ (receiveHead_now p) xs st

theorem receiveHeads_bestPC (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    (xs.foldl (receiveHead p) st).bestPC = st.bestPC :=
  fold_field State.bestPC _ (receiveHead_bestPC p) xs st

theorem receiveHeads_archive_mono (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    st.receivedHeads ⊆ (xs.foldl (receiveHead p) st).receivedHeads := by
  induction xs generalizing st with
  | nil => exact List.Subset.refl _
  | cons x xs ih => exact List.Subset.trans (receiveHead_archive_mono p st x) (ih _)

theorem receiveHeads_mem (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) (o : HeadWire n) (ho : o ∈ xs)
    (r : Slot) (hr : headLabel? o = some r)
    (ht : r ≤ (st.base.now / (4 * p.Δ)).toNat) :
    o ∈ (xs.foldl (receiveHead p) st).receivedHeads := by
  induction xs generalizing st with
  | nil => simp at ho
  | cons x xs ih =>
      rcases List.mem_cons.mp ho with rfl | ho
      · exact receiveHeads_archive_mono p _ xs (receiveHead_mem p st o r hr ht)
      · exact ih (receiveHead p st x) ho (by simpa [receiveHead_now] using ht)

theorem proposalBase_blocks_mono (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (b : Block) (raw support : List (HeadWire n)) :
    st.base.blocks ⊆ (proposalBase p st o b raw support).blocks := by
  unfold proposalBase GridCO.admitProposal
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · exact List.subset_append_left _ _

theorem process_blocks_mono (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.base.blocks ⊆ (process p st o).base.blocks := by
  unfold process
  split
  · simp only [admitHead, collectPCs_base, receiveHead_blocks]
    exact List.Subset.refl _
  · unfold admitProposal
    split
    · simp only [collectPCs_base, receiveHeads_blocks]
      exact proposalBase_blocks_mono p st o _ _ _
    · exact List.Subset.refl _
  · split
    · simp only [collectPCs_base, installPC, receiveHeads_blocks]
      exact List.Subset.refl _
    · exact List.Subset.refl _
  · exact List.Subset.refl _

/-- Every fold of actual engine steps preserves a local invariant. The
list can be an event prefix, a strict-time input, or a public read. -/
theorem fold_invariant {V : Type} [DecidableEq V] (p : Params)
    (Q : State p.n → Prop) (hinit : Q (initial p.n))
    (hclock : ∀ st t, Q st → Q (clock p st t))
    (hprocess : ∀ st o, Q st → Q (process p st o))
    (events : List (Event V (sapc p).Object)) (v : V) :
    Q ((events.foldl World.step World.init) v) := by
  set_option backward.isDefEq.respectTransparency false in
  have hfold (events : List (Event V (sapc p).Object)) (w : World V (sapc p))
      (hw : ∀ u, Q (w u)) : ∀ u, Q ((events.foldl World.step w) u) := by
    induction events generalizing w with
    | nil => exact hw
    | cons e events ih =>
        apply ih
        intro u
        cases e with
        | tick node t =>
            by_cases hu : u = node
            · subst u; simpa [World.step, sapc] using hclock (w node) t (hw node)
            · simpa [World.step, hu] using hw u
        | deliver node o t =>
            by_cases hu : u = node
            · subst u; simpa [World.step, sapc] using hprocess (w node) o (hw node)
            · simpa [World.step, hu] using hw u
  exact hfold events World.init (fun _ => hinit) v

end AvailableChain.SAPC
end
