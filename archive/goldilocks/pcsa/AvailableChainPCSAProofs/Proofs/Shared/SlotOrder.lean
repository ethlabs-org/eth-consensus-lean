module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainFGSA.Proofs.Head.Pool

public section

/-! Strict slot order of stored blocks and slot bounds of saved results. -/
namespace AvailableChain.PCSA

/-- Parent slots increase on each non-genesis edge. -/
def RecoverySlotOrdered : Block → Prop
  | .genesis => True
  | .node parent slot _ _ => parent.slot < slot ∧ RecoverySlotOrdered parent

/-- A prefix of a slot-ordered block has at most its slot. -/
theorem pcsa_slot_le_of_prefix (B C : Block) (ho : RecoverySlotOrdered C)
    (hp : Block.Preceq B C) : B.slot ≤ C.slot := by
  induction C with
  | genesis =>
    have he : B = .genesis := of_decide_eq_true hp
    subst B
    exact le_rfl
  | node parent s r b ih =>
    change (decide (B = .node parent s r b) || Block.preceq B parent) = true at hp
    rcases Bool.or_eq_true_iff.mp hp with he | hp
    · have he' := of_decide_eq_true he
      subst B
      exact le_rfl
    · exact (ih ho.2 hp).trans (Nat.le_of_lt ho.1)

/-- A prefix of a slot-ordered block with at least its slot is the block. -/
theorem pcsa_prefix_eq_of_slot_ge (B C : Block) (ho : RecoverySlotOrdered C)
    (hp : Block.Preceq B C) (hs : C.slot ≤ B.slot) : B = C := by
  cases C with
  | genesis => exact of_decide_eq_true hp
  | node parent s r b =>
    change (decide (B = .node parent s r b) || Block.preceq B parent) = true at hp
    rcases Bool.or_eq_true_iff.mp hp with he | hp
    · exact of_decide_eq_true he
    · have hb := pcsa_slot_le_of_prefix B parent ho.2 hp
      have ht := ho.1
      change s ≤ B.slot at hs
      exact (Nat.not_lt_of_ge hs (lt_of_le_of_lt hb ht)).elim

/-- Every stored block is slot-ordered. -/
def StoreSlotOrdered {n : Nat} (st : State n) : Prop :=
  ∀ B ∈ st.base.blocks, RecoverySlotOrdered B

private theorem grid_proposal_ordered (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (B : Block)
    (raw : List (GridCO.HeadWire n .root))
    (h : ∀ C ∈ st.blocks, RecoverySlotOrdered C) :
    ∀ C ∈ (GridCO.admitProposal p st o B raw).blocks, RecoverySlotOrdered C := by
  delta GridCO.admitProposal
  dsimp only
  cases o.auth <;> dsimp only <;> split
  all_goals first | exact h | skip
  all_goals
    rename_i ha
    apply List.foldlRecOn (motive := fun v : GridCO.State n .root =>
      ∀ C ∈ v.blocks, RecoverySlotOrdered C)
    · intro C hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h C hc
      · cases List.mem_singleton.mp hc
        have htests := ha
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          not_or, Bool.not_eq_false, decide_eq_false_iff_not] at htests
        have hp : GridCO.blockKnown st B.parent = true := by tauto
        have hs : B.parent.slot < B.slot := by tauto
        have ho := h B.parent (of_decide_eq_true hp)
        cases B with
        | genesis => trivial
        | node P s r b => exact ⟨hs, ho⟩
    · intro acc hh a _ C hc
      exact hh C (by simpa only [GridCO.admitVote_blocks] using hc)

private theorem normalize_ordered {n : Nat} (st : State n) (h : StoreSlotOrdered st) :
    StoreSlotOrdered (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem reconcile_ordered {n : Nat} (st : State n) (h : StoreSlotOrdered st) :
    StoreSlotOrdered (reconcile st) := normalize_ordered _ h

private theorem row_ordered (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : StoreSlotOrdered st) : StoreSlotOrdered (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem raw_ordered {n : Nat} (st : State n) (a : AckWire n)
    (h : StoreSlotOrdered st) : StoreSlotOrdered (poolAckRaw st a) := by
  intro B hb
  exact h B (by simpa only [(poolAckRaw_frame st a).2.2.1] using hb)

private theorem process_ordered (p : Params) (st : State p.n) (o : Wire p.n)
    (h : StoreSlotOrdered st) : StoreSlotOrdered (process p st o) := by
  have hc (st : State p.n) (h : StoreSlotOrdered st) : StoreSlotOrdered (collectPCs st) := by
    intro B hb
    exact h B (by simpa only [(collectPCs_frame st).2.1] using hb)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : StoreSlotOrdered st) :
      StoreSlotOrdered (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => raw_ordered acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      intro B hb
      change B ∈ (GridCO.admitVote _ _ _).blocks at hb
      exact h B (by simpa only [GridCO.admitVote_blocks] using hb)
    | row i body => exact row_ordered p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb := grid_proposal_ordered p.toParams.engine st.base
                (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_ordered; exact hb)
                | exact hb
            · intro acc hh a _
              exact row_ordered p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

private theorem gate_ordered (p : Params) {n : Nat} (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot)
    (h : StoreSlotOrdered st) : StoreSlotOrdered (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact h
  | some B =>
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc hh b _
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact hh'

private theorem clock_ordered (p : Params) (st : State p.n) (t : Time)
    (h : StoreSlotOrdered st) : StoreSlotOrdered (clock p st t) := by
  have hc : StoreSlotOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply normalize_ordered
    split
    · exact hc
    · exact gate_ordered p _ _ _ _ _ hc
  · exact hc

/-- Every block in a reachable PC-SA tree has strictly increasing parent slots. -/
theorem pcsa_reachable_slot_order (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ B ∈ st.base.blocks, RecoverySlotOrdered B := by
  induction h with
  | init => intro B hb; have he : B = .genesis := List.mem_singleton.mp hb; subst B; trivial
  | tick t _ ih => exact clock_ordered p _ t ih
  | deliver o _ ih => exact process_ordered p _ o ih

/-- A proper ancestor of a stored block has a strictly smaller slot. -/
theorem pcsa_stored_strict_slots (p : Params) (st : State p.n) (h : Reachable p st)
    (P B : Block) (hb : B ∈ st.base.blocks) (hp : Block.Preceq P B) (hne : P ≠ B) :
    P.slot < B.slot := by
  by_contra hn
  exact hne (pcsa_prefix_eq_of_slot_ge P B (pcsa_reachable_slot_order p st h B hb)
    hp (Nat.le_of_not_gt hn))

/-- Every prefix of a genuine result has slot at most the result label. -/
theorem pcsa_result_prefix_slot (p : Params) (v : GridCO.State p.n .root)
    (a C B : Block) (s : Slot) (ho : ∀ D ∈ v.blocks, RecoverySlotOrdered D)
    (hc : SA.Root.confirmationFrom p.toParams a v s = some C)
    (hb : Block.Preceq B C) : B.slot ≤ s := by
  change GridCO.confirmationFrom p.toParams.engine a v s = some C at hc
  delta GridCO.confirmationFrom at hc
  dsimp only at hc
  split at hc
  · rename_i hpos
    have he := Option.some.inj hc
    rw [he] at hpos
    have hscore : 0 < GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks
        (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) C := by
      omega
    delta GridCO.goldfishScoreOn at hscore
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp hscore)
    have ht := (List.mem_filter.mp hi).2
    rw [FGSA.fgsa_cleanSupport_no_equivocation, Bool.false_or] at ht
    obtain ⟨o, ho', ht⟩ := List.any_eq_true.mp ht
    have hclean := (List.mem_filter.mp ho').1
    have hlabel : GridCO.headLabel? o = some s := by
      simpa using (List.mem_filter.mp
        (List.mem_filter.mp (List.mem_filter.mp hclean).1).1).2
    cases hr : GridCO.headTarget? o with
    | none => simp only [hr, Bool.false_eq_true] at ht
    | some r =>
      rw [hr] at ht
      dsimp only at ht
      cases hresolve : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
      | none => simp only [hresolve, Bool.false_eq_true] at ht
      | some D =>
        rw [hresolve] at ht
        dsimp only at ht
        simp only [hlabel, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at ht
        exact (pcsa_slot_le_of_prefix B D (ho D ht.1.1)
          (Gen.Pure.block_preceq_trans hb ht.2)).trans ht.1.2
  · cases hc


/-- Every prefix of a saved result has slot at most its label. -/
def ResultsSlotBound {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
    ∀ B, Block.Preceq B C → B.slot ≤ row.1

private theorem grid_vote_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    (GridCO.admitVote p st o).genuine = st.genuine := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> delta GridCO.admitVote <;> dsimp only
  all_goals first | rfl | (split <;> rfl)

private theorem grid_proposal_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (B : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal p st o B raw).genuine = st.genuine := by
  delta GridCO.admitProposal
  dsimp only
  cases o.auth <;> dsimp only <;> split
  all_goals first | rfl | skip
  all_goals
    apply List.foldlRecOn (motive := fun v : GridCO.State n .root => v.genuine = st.genuine)
    · rfl
    · intro acc hh a _
      rw [grid_vote_genuine]
      exact hh

private theorem collect_genuine {n : Nat} (st : State n) :
    (collectPCs st).base.genuine = st.base.genuine := by
  apply collectPCs_preserves (fun st : State n => st.base.genuine)
  intro st pc
  rw [installPC_def]
  split <;> rfl

private theorem normalize_results {n : Nat} (st : State n) (h : ResultsSlotBound st) :
    ResultsSlotBound (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem reconcile_results {n : Nat} (st : State n) (h : ResultsSlotBound st) :
    ResultsSlotBound (reconcile st) := by
  apply normalize_results
  intro row hr C hc B hb
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hr
  cases he
  exact h old hold C (Option.filter_eq_some_iff.mp hc).1 B hb

private theorem row_results (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : ResultsSlotBound st) : ResultsSlotBound (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem raw_results {n : Nat} (st : State n) (a : AckWire n)
    (h : ResultsSlotBound st) : ResultsSlotBound (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem process_results (p : Params) (st : State p.n) (o : Wire p.n)
    (h : ResultsSlotBound st) : ResultsSlotBound (process p st o) := by
  have hc (st : State p.n) (h : ResultsSlotBound st) : ResultsSlotBound (collectPCs st) := by
    delta ResultsSlotBound at h ⊢
    simpa only [collect_genuine] using h
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : ResultsSlotBound st) :
      ResultsSlotBound (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => raw_results acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      delta ResultsSlotBound at h ⊢
      delta admitHead
      simpa only [grid_vote_genuine] using h
    | row i body => exact row_results p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : ResultsSlotBound { st with base := (GridCO.admitProposal
                  p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                    N.erase (N.raw.map baseHead)) } := by
                delta ResultsSlotBound at h ⊢
                simpa only [grid_proposal_genuine] using h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_results; exact hb)
                | exact hb
            · intro acc hh a _
              exact row_results p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

/-- Recording a result bounded by its label keeps the result bound. -/
theorem pcsa_record_results (p : Params) (st : State p.n) (s : Slot)
    (oc : Option Block)
    (h : ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C → ∀ B, Block.Preceq B C → B.slot ≤ row.1)
    (hn : ∀ C, oc = some C → ∀ B, Block.Preceq B C → B.slot ≤ s) :
    ∀ row ∈ @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s oc,
      ∀ C, row.2 = some C → ∀ B, Block.Preceq B C → B.slot ≤ row.1 := by
  delta GridCO.recordGenuine
  split
  · intro row hr C hc B hb
    rcases List.mem_append.mp hr with hr | hr
    · exact h row hr C hc B hb
    · cases List.mem_singleton.mp hr
      exact hn C hc B hb
  · exact h

private theorem gate_results (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : StoreSlotOrdered st) (h : ResultsSlotBound st) :
    ResultsSlotBound (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact pcsa_record_results p st s none h (by intro C he; cases he)
  | some C =>
    have hi := pcsa_record_results p st s (some C) h (by
      intro D hd B hb
      cases Option.some.inj hd
      exact pcsa_result_prefix_slot p (actView st) a C B s
        (fun D hd => ht D (List.mem_filter.mp hd).1) hc hb)
    dsimp only
    split
    · exact hi
    · apply List.foldlRecOn
      · exact hi
      · intro acc hh b _
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact hh'

private theorem clock_results (p : Params) (st : State p.n) (t : Time)
    (ht : StoreSlotOrdered st) (h : ResultsSlotBound st) : ResultsSlotBound (clock p st t) := by
  have hc : ResultsSlotBound (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  have hct : StoreSlotOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply normalize_results
    split
    · exact hc
    · exact gate_results p _ _ _ _ _ hct hc
  · exact hc

/-- Every prefix of a saved result is bounded by its label. -/
theorem pcsa_saved_result_slot (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
      ∀ B, Block.Preceq B C → B.slot ≤ row.1 := by
  induction h with
  | init => intro row hr; exact (List.not_mem_nil hr).elim
  | tick t hh ih => exact clock_results p _ t (pcsa_reachable_slot_order p _ hh) ih
  | deliver o _ ih => exact process_results p _ o ih

end AvailableChain.PCSA

end
