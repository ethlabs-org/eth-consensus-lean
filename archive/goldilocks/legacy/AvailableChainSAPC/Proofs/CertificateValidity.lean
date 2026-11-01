module
public import AvailableChainSAPC.Proofs.ReceiptState

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic

theorem pathKnown_eq_of_blocks_eq {n : Nat} (a b : State n)
    (h : a.base.blocks = b.base.blocks) (target : Block) :
    pathKnown a target = pathKnown b target := by
  induction target with
  | genesis => simp only [pathKnown, GridCO.blockKnown, h]
  | node parent s r_s root ih => simp only [pathKnown, GridCO.blockKnown, h, ih]

theorem pcValid_eq_of_data (p : Params) {n : Nat} (a b : State n)
    (hb : a.base.blocks = b.base.blocks) (hh : a.receivedHeads = b.receivedHeads) (c : PC n) :
    pcValid p a c = pcValid p b c := by
  simp only [pcValid, pcPaths, pathKnown_eq_of_blocks_eq a b hb, hh]

theorem pathKnown_mono {n : Nat} (before after : State n)
    (hsub : before.base.blocks ⊆ after.base.blocks) (b : Block)
    (h : pathKnown before b = true) : pathKnown after b = true := by
  induction b with
  | genesis => exact decide_eq_true (hsub (of_decide_eq_true h))
  | node parent slot r_slot root ih =>
      simp only [pathKnown, Bool.and_eq_true] at h ⊢
      exact ⟨decide_eq_true (hsub (of_decide_eq_true h.1)), ih h.2⟩

theorem pcPaths_mono {n : Nat} (before after : State n)
    (hsub : before.base.blocks ⊆ after.base.blocks) (c : PC n)
    (h : pcPaths before c = true) : pcPaths after c = true := by
  simp only [pcPaths, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨pathKnown_mono before after hsub c.target h.1,
    fun o ho => pathKnown_mono before after hsub o.payload.target (h.2 o ho)⟩

/-- Late evidence and extra paths cannot invalidate a certificate. In
particular, an equivocation does not remove its original signatures. -/
theorem pcValid_mono (p : Params) {n : Nat} (before after : State n)
    (hb : before.base.blocks ⊆ after.base.blocks)
    (hh : before.receivedHeads ⊆ after.receivedHeads) (c : PC n)
    (h : pcValid p before c = true) : pcValid p after c = true := by
  simp only [pcValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1, pcPaths_mono before after hb c h.1.2⟩, fun o ho => hh (h.2 o ho)⟩

theorem pcWellFormed_witness (p : Params) {n : Nat} (c : PC n)
    (h : pcWellFormed p c = true) (o : HeadWire n) (ho : o ∈ c.witnesses) :
    headLabel? o = some (c.slot + 1) ∧ o.payload.ack = some (c.slot, c.target) ∧
      Block.Preceq c.target o.payload.target ∧ o.payload.target.slot ≤ c.slot + 1 := by
  have hw := (Bool.and_eq_true_iff.mp h).2
  have ho := List.all_eq_true.mp hw o ho
  simpa only [pcWitness, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, Block.Preceq] using ho

theorem assemblePC_valid (p : Params) {n : Nat} (st : State n)
    (s : Slot) (b : Block) (c : PC n) (h : assemblePC p st s b = some c) :
    pcValid p st c = true := by
  unfold assemblePC at h
  dsimp only at h
  split at h
  · cases h; assumption
  · contradiction

/-- Every installed certificate is valid in the local raw archive. -/
def StoredPCValid (p : Params) {n : Nat} (st : State n) : Prop :=
  ∀ c, st.bestPC = some c → pcValid p st c = true

theorem installPC_valid (p : Params) {n : Nat} (st : State n) (c : PC n)
    (hold : StoredPCValid p st) (hc : pcValid p st c = true) :
    StoredPCValid p (installPC st c) := by
  intro d hd
  change preferPC st.bestPC c = some d at hd
  have hvalid : pcValid p st d = true := by
    cases he : st.bestPC with
    | none => simp only [preferPC, he, Option.some.injEq] at hd; subst d; exact hc
    | some previous =>
        simp only [preferPC, he] at hd
        split at hd
        · cases hd; exact hc
        · cases hd; exact hold _ he
  exact pcValid_mono p st (installPC st c) (List.Subset.refl _)
    (List.Subset.refl _) d hvalid

theorem collectPCs_valid (p : Params) {n : Nat} (st : State n)
    (h : StoredPCValid p st) : StoredPCValid p (collectPCs p st) := by
  have hf (pairs : List (Slot × Block)) (st : State n) (h : StoredPCValid p st) :
      StoredPCValid p (pairs.foldl (fun acc pair =>
        match assemblePC p acc pair.1 pair.2 with
        | none => acc
        | some c => installPC acc c) st) := by
    induction pairs generalizing st with
    | nil => exact h
    | cons pair pairs ih =>
        apply ih
        dsimp only
        cases he : assemblePC p st pair.1 pair.2 with
        | none => exact h
        | some c => exact installPC_valid p st c h (assemblePC_valid p st _ _ c he)
  exact hf _ st h

theorem receiveHead_valid (p : Params) {n : Nat} (st : State n) (o : HeadWire n)
    (h : StoredPCValid p st) : StoredPCValid p (receiveHead p st o) := by
  intro c hc
  rw [receiveHead_bestPC] at hc
  apply pcValid_mono p st _ ?_ (receiveHead_archive_mono p st o) c (h c hc)
  rw [receiveHead_blocks]

theorem receiveHeads_valid (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) (h : StoredPCValid p st) :
    StoredPCValid p (xs.foldl (receiveHead p) st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (receiveHead_valid p st x h)

/-- A ready direct envelope has all original witnesses in the archive
after the actual member calls. This includes lower-ranked certificates. -/
theorem pcEnvelopeReady_valid (p : Params) {n : Nat} (st : State n) (c : PC n)
    (h : pcEnvelopeReady p st c = true) :
    pcValid p (c.witnesses.foldl (receiveHead p) st) c = true := by
  simp only [pcEnvelopeReady, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [pcValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨h.1.1, pcPaths_mono st _ ?_ c h.1.2⟩, ?_⟩
  · rw [receiveHeads_blocks]
  · intro o ho
    exact receiveHeads_mem p st c.witnesses o ho (c.slot + 1)
      (pcWellFormed_witness p c h.1.1 o ho).1 h.2

/-- A direct PC with a missing path is a missing dependency: `pcEnvelopeReady`
fails and the handler returns the state unchanged. -/
theorem process_pc_missingPaths (p : Params) {n : Nat} (st : State n) (c : PC n)
    (h : pcPaths st c = false) : process p st ⟨.none, .pc c⟩ = st := by
  simp [process, pcEnvelopeReady, h]

theorem process_valid (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : StoredPCValid p st) : StoredPCValid p (process p st o) := by
  unfold process
  split
  · exact collectPCs_valid p _ (receiveHead_valid p st _ h)
  · unfold admitProposal
    split
    · rename_i s b raw support cert ha hp hen
      apply collectPCs_valid
      apply receiveHeads_valid
      intro c hc
      exact pcValid_mono p st
        { st with base := proposalBase p st o b raw support, proposals := st.proposals ++ [o] }
        (proposalBase_blocks_mono p st o b raw support)
        (List.Subset.refl _) c (h c hc)
    · exact h
  · split
    · rename_i c _ _ hready
      exact collectPCs_valid p _ (installPC_valid p _ c
        (receiveHeads_valid p st c.witnesses h) (pcEnvelopeReady_valid p st c hready))
    · exact h
  · exact h

theorem clock_valid (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : StoredPCValid p st) : StoredPCValid p (clock p st t) := by
  intro c hc
  rw [clock_bestPC] at hc
  apply pcValid_mono p st _ ?_ ?_ c (h c hc)
  · rw [clock_blocks]
  · rw [clock_archive]

theorem installedPC_valid_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    StoredPCValid p ((events.foldl World.step World.init) v) :=
  fold_invariant p (StoredPCValid p) (by simp [StoredPCValid, initial])
    (clock_valid p) (process_valid p) events v

/-- No regime premise is required for local certificate validity. -/
theorem installedPC_valid_at_read {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (t : Time) (c : PC p.n)
    (h : (Run.readAt (sapc p) rho t v).bestPC = some c) :
    pcValid p (Run.readAt (sapc p) rho t v) c = true :=
  installedPC_valid_at_fold p _ v c h

theorem installedPC_valid_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (index : Nat) (c : PC p.n)
    (h : (Run.stateBefore (sapc p) rho index v).bestPC = some c) :
    pcValid p (Run.stateBefore (sapc p) rho index v) c = true :=
  installedPC_valid_at_fold p _ v c h

theorem installedPC_valid_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (t : Time) (c : PC p.n)
    (h : (Run.stateBeforeTime (sapc p) rho t v).bestPC = some c) :
    pcValid p (Run.stateBeforeTime (sapc p) rho t v) c = true :=
  installedPC_valid_at_fold p _ v c h

end AvailableChain.SAPC
end
