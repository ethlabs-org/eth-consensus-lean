module
public import AvailableChainGridCO.Proofs.TransferViews

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem fold_proposals {n : Nat} {α : Type} (xs : List α)
    (f : State n → α → State n) (st : State n)
    (h : ∀ st x, (f st x).proposals = st.proposals) :
    (xs.foldl f st).proposals = st.proposals := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, h]

private theorem gate_proposals (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).proposals = st.proposals := by
  unfold gate
  split
  · rfl
  · dsimp only
    split
    · rfl
    · apply fold_proposals
      intro st B
      exact fold_proposals _ _ st (by intros; rfl)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The clock never changes the stored proposal objects. -/
theorem clock_proposals (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  unfold clock
  dsimp only
  split
  all_goals try rw [gate_proposals]
  all_goals split <;> split <;> split <;> rfl

private theorem admitVote_proposals (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).proposals = st.proposals := by
  unfold admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

private theorem fold_vote_blocks (p : Params) {n : Nat} (st : State n)
    (raw : List (HeadWire n)) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih => rw [List.foldl_cons, ih, admitVote_blocks]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A new proposal entry comes from its admitted block envelope. -/
theorem process_proposal_origin (p : Params) {n : Nat} (st : State n)
    (parent o : Wire n) (ho : o ∈ (process p st parent).proposals) :
    o ∈ st.proposals ∨ parent = o ∧ ∃ B raw support,
      o.payload = .proposal B raw support ∧ B ∉ st.blocks ∧
      B ∈ (process p st parent).blocks ∧ B.slot ≤ (st.now / (4 * p.Δ)).toNat := by
  unfold process at ho
  split at ho
  · exact Or.inl (by simpa [admitVote_proposals] using ho)
  · rename_i slot B raw support ha hp
    unfold admitProposal at ho
    simp only [ha] at ho
    split at ho
    · exact Or.inl ho
    · rename_i hgood
      rw [fold_proposals _ _ _ (fun st o => admitVote_proposals p st (fromHead o))] at ho
      rcases List.mem_append.mp ho with hold | hnew
      · exact Or.inl hold
      · have he : o = parent := by simpa using hnew
        subst o
        have hn : B ∉ st.blocks := by intro h; simp [h] at hgood
        have hslot : B.slot ≤ (st.now / (4 * p.Δ)).toNat := by
          by_contra h
          have hgt : (st.now / (4 * p.Δ)).toNat < B.slot := Nat.lt_of_not_ge h
          simp [hgt] at hgood
        refine Or.inr ⟨rfl, B, raw, support, hp, hn, ?_, hslot⟩
        simp only [process, ha, hp, admitProposal, hgood, Bool.false_eq_true, ite_false]
        rw [fold_vote_blocks]
        simp
  · exact Or.inl ho

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Each stored proposal has an earlier direct admission. The source
includes the complete wire views, the handler call, and the slot guard. -/
theorem stored_proposal_admission {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (o : Wire p.n)
    (ho : o ∈ (Run.stateBefore (gridCO p) rho index reader).proposals) :
    ∃ j < index, ∃ t B raw support,
      rho.events[j]? = some (.deliver reader o t) ∧
      o.payload = .proposal B raw support ∧
      B ∉ (Run.stateBefore (gridCO p) rho j reader).blocks ∧
      B ∈ (process p (Run.stateBefore (gridCO p) rho j reader) o).blocks ∧
      B.slot ≤ ((Run.stateBefore (gridCO p) rho j reader).now / (4 * p.Δ)).toNat := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at ho
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          obtain ⟨j, hj, hrest⟩ := ih (by simpa [Run.stateBefore, List.take_add_one, hi] using ho)
          exact ⟨j, by omega, hrest⟩
      | some e =>
          rw [stateBefore_succ_event hi] at ho
          cases e with
          | tick v t =>
              have hold : o ∈ (Run.stateBefore (gridCO p) rho index reader).proposals := by
                by_cases hv : reader = v
                · subst v; simpa [World.step, gridCO, clock_proposals] using ho
                · simpa [World.step, hv] using ho
              obtain ⟨j, hj, hrest⟩ := ih hold
              exact ⟨j, by omega, hrest⟩
          | deliver v parent t =>
              by_cases hv : reader = v
              · subst v
                have hm : o ∈ (process p (Run.stateBefore (gridCO p) rho index reader)
                    parent).proposals := by simpa [World.step] using! ho
                rcases process_proposal_origin p _ parent o hm with hold | ⟨he, hrest⟩
                · obtain ⟨j, hj, hrest⟩ := ih hold
                  exact ⟨j, by omega, hrest⟩
                · subst parent
                  obtain ⟨B, raw, support, hp, hn, hm, hslot⟩ := hrest
                  exact ⟨index, by omega, t, B, raw, support, hi, hp, hn, hm, hslot⟩
              · obtain ⟨j, hj, hrest⟩ := ih (by simpa [World.step, hv] using ho)
                exact ⟨j, by omega, hrest⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every stored proposal passed the wire check at its direct delivery. -/
theorem stored_proposal_wellFormed {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (index : Nat) (reader : V) (o : Wire p.n)
    (ho : o ∈ (Run.stateBefore (gridCO p) rho index reader).proposals) :
    wellFormed o = true := by
  obtain ⟨j, _, t, _, _, _, hi, _⟩ := stored_proposal_admission p rho index reader o ho
  exact hx.wire j reader o t hi

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Proposal metadata in the next HEAD state also passed the wire check. -/
theorem nextHeadState_proposal_wellFormed {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (reader : V) (o : Wire p.n)
    (ho : o ∈ (nextHeadState p rho r reader).proposals) : wellFormed o = true := by
  change o ∈ (clock p _ _).proposals at ho
  rw [clock_proposals] at ho
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader).proposals at ho
  rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at ho
  exact stored_proposal_wellFormed p E rho hx _ reader o ho

private theorem wellFormed_support_subset {n : Nat} (o : Wire n)
    (B : Block) (raw support : List (HeadWire n)) (hp : o.payload = .proposal B raw support)
    (hw : wellFormed o = true) : ∀ v ∈ support, v ∈ raw := by
  cases ha : o.auth <;> simp only [wellFormed, ha, hp] at hw
  all_goals first
    | contradiction
    | intro v hv
      exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 v hv)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The merged resolved view is a subset of the merged raw view. The
wire check prevents a proposal from declaring an extra support vote. -/
theorem nextHeadState_support_subset_raw_of_execution {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hx : ExecutionValid (gridCO p) E rho) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    voterSupportView p (nextHeadState p rho r reader) (r + 1) ⊆
      voterView p (nextHeadState p rho r reader) (r + 1) := by
  intro o ho
  simp only [voterSupportView, Nat.add_sub_cancel,
    nextHeadState_frozenAt_of_execution p E rho hΔ r hx hh reader hr] at ho
  apply List.mem_eraseDups.mpr
  simp only [Nat.add_sub_cancel,
    nextHeadState_frozenAt_of_execution p E rho hΔ r hx hh reader hr]
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hf | hc
  · apply List.mem_append_left
    obtain ⟨hm, hres⟩ := List.mem_filter.mp hf
    apply List.mem_filter.mpr
    refine ⟨hm, ?_⟩
    have hold := (resolvedBefore_block _ o _).symm.trans hres
    cases ht : headTarget? o with
    | none => simp [ht] at hold
    | some target =>
        simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hold
        exact decide_eq_true hold.1.2
  · apply List.mem_append_right
    obtain ⟨hc, htest⟩ := List.mem_filter.mp hc
    apply List.mem_filter.mpr
    refine ⟨?_, (Bool.and_eq_true_iff.mp htest).1⟩
    obtain ⟨parent, hp, hraw⟩ := List.mem_flatMap.mp hc
    refine List.mem_flatMap.mpr ⟨parent, hp, ?_⟩
    have hw := nextHeadState_proposal_wellFormed p E rho hx r reader parent
      (List.mem_filter.mp hp).1
    cases hmsg : parent.payload with
    | head target => simp [hmsg] at hraw
    | proposal B raw support =>
        simp only [hmsg] at hraw ⊢
        obtain ⟨v, hv, he⟩ := List.mem_map.mp hraw
        exact List.mem_map.mpr ⟨v, wellFormed_support_subset parent B raw support hmsg hw v hv, he⟩

theorem nextHeadState_support_subset_raw {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) (reader : V) (hr : reader ∈ rho.honest) :
    voterSupportView p (nextHeadState p rho r reader) (r + 1) ⊆
      voterView p (nextHeadState p rho r reader) (r + 1) :=
  nextHeadState_support_subset_raw_of_execution p E rho hΔ r hsync.1 hsync.2.2.1 reader hr

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A raw HEAD in a current proposal is stored at release, or its seat
already has two distinct copies there. The admission guard supplies the
current/previous-label window; no extra clock premise is used. -/
theorem nextHeadState_carried_raw_receipt {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (reader : V)
    (o : Wire p.n) (i : Fin p.n) (hi : headSeat? o = some i)
    (ho : o ∈ carriedRaw (nextHeadState p rho r reader) (r + 1)) :
    o ∈ votesAt (releaseInput p rho r reader) r ∨
      equivocates (votesAt (releaseInput p rho r reader) r) i = true := by
  obtain ⟨ho, hl⟩ := List.mem_filter.mp ho
  have hlabel : headLabel? o = some r := by simpa using hl
  have hhead : ∃ target, o = ⟨.seat r i, .head target⟩ := by
    rcases o with ⟨auth, payload⟩
    cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]
  obtain ⟨target, rfl⟩ := hhead
  obtain ⟨parent, hp, hraw⟩ := List.mem_flatMap.mp ho
  obtain ⟨hm, hslot⟩ := List.mem_filter.mp hp
  change parent ∈ (clock p _ _).proposals at hm
  rw [clock_proposals] at hm
  change parent ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader).proposals at hm
  rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at hm
  obtain ⟨j, hj, t, B, raw, support, he, hb, hn, hB, hcurrent⟩ :=
    stored_proposal_admission p rho _ reader parent hm
  have hBs : B.slot = r + 1 := by simpa [hb] using hslot
  have ht : t < releaseTime p r := Int.le_sub_one_iff.mp
    ((index_lt_read_length_iff hx.toScheduleWellFormed (releaseTime p r - 1) he).mp hj)
  have hnow := (stateBefore_now_le_event p E rho hx.toScheduleWellFormed he reader).trans_lt ht
  have hupper : ((Run.stateBefore (gridCO p) rho j reader).now / (4 * p.Δ)).toNat ≤ r + 1 := by
    apply Int.toNat_le.mpr
    apply (Int.ediv_le_iff_le_mul (by linarith [p.deltaPos])).mpr
    dsimp [releaseTime, proposalTime] at hnow
    push_cast
    nlinarith [p.deltaPos]
  have hwindow : ((Run.stateBefore (gridCO p) rho j reader).now / (4 * p.Δ)).toNat = r + 1 := by
    exact le_antisymm hupper (hBs ▸ hcurrent)
  have hcall : handles p (Run.stateBefore (gridCO p) rho j reader) parent
      ⟨.seat r i, .head target⟩ := by
    apply Or.inr
    simpa [hb] using And.intro hn (And.intro hB hraw)
  have hrec := handled_head_mem_or_equivocates p (Run.stateBefore (gridCO p) rho j reader)
    parent r i target
    (by simpa only [hwindow, Nat.add_sub_cancel] using (le_refl r))
    (by simpa only [hwindow] using (Nat.le_succ r)) hcall
  have hsub : votesAt (process p (Run.stateBefore (gridCO p) rho j reader) parent) r ⊆
      votesAt (releaseInput p rho r reader) r := by
    have hprefix := stateBefore_receiptPrefix p rho (Nat.succ_le_of_lt hj) reader
    intro q hq
    obtain ⟨hq, hlabel⟩ := List.mem_filter.mp hq
    apply List.mem_filter.mpr
    refine ⟨?_, hlabel⟩
    change q ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader).votes
    rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed]
    apply hprefix.votes.subset
    rw [stateBefore_succ_event he]
    simpa [World.step] using! hq
  rcases hrec with hm | heq
  · exact Or.inl (hsub (List.mem_filter.mpr ⟨hm, by simp [headLabel?]⟩))
  · exact Or.inr (equivocates_mono _ _ i hsub heq)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The whole next raw view has a stored release receipt or two-copy
evidence. This includes the frozen part and every admitted proposal. -/
theorem nextHeadState_raw_receipt_of_execution {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hx : ExecutionValid (gridCO p) E rho) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (i : Fin p.n) (hi : headSeat? o = some i)
    (ho : o ∈ voterView p (nextHeadState p rho r reader) (r + 1)) :
    o ∈ votesAt (releaseInput p rho r reader) r ∨
      equivocates (votesAt (releaseInput p rho r reader) r) i = true := by
  simp only [voterView, Nat.add_sub_cancel,
    nextHeadState_frozenAt_of_execution p E rho hΔ r hx hh reader hr] at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hf | hc
  · apply Or.inl
    rw [(freezeView_at_input p E rho hx.toScheduleWellFormed r reader).1] at hf
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hf
    apply List.mem_filter.mpr
    refine ⟨?_, hl⟩
    exact (time_input_receiptPrefix p E rho hx.toScheduleWellFormed
      (freezeTime p r) (releaseTime p r)
      (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos]) reader).votes.subset hm
  · exact nextHeadState_carried_raw_receipt p E rho hx r reader o i hi hc

theorem nextHeadState_raw_receipt {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) (reader : V) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (i : Fin p.n) (hi : headSeat? o = some i)
    (ho : o ∈ voterView p (nextHeadState p rho r reader) (r + 1)) :
    o ∈ votesAt (releaseInput p rho r reader) r ∨
      equivocates (votesAt (releaseInput p rho r reader) r) i = true :=
  nextHeadState_raw_receipt_of_execution p E rho hΔ r hsync.1 hsync.2.2.1 reader hr o i hi ho

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Reverse relay covers the complete merged raw view. A capped carried
copy supplies equivocation evidence at the source gate instead. -/
theorem synchronous_voter_raw_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (i : Fin p.n) (hi : headSeat? o = some i)
    (ho : o ∈ voterView p (nextHeadState p rho r reader) (r + 1)) :
    o ∈ lateVotes p (gateInput p rho r source) r ∨
      equivocates (lateVotes p (gateInput p rho r source) r) i = true := by
  have hback : ∀ q ∈ votesAt (releaseInput p rho r reader) r, headSeat? q = some i →
      q ∈ lateVotes p (gateInput p rho r source) r ∨
      equivocates (lateVotes p (gateInput p rho r source) r) i = true := by
    intro q hq hqi
    exact synchronous_release_vote_late p E rho hΔ r hsync reader source hr hs q hq i hqi
  rcases nextHeadState_raw_receipt p E rho hΔ r hsync reader hr o i hi ho with hm | he
  · exact hback o hm hi
  · exact Or.inr (equivocates_of_mem_or_equivocates _ _ i hback he)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The engine supplies every receipt condition for genuine-prefix
transfer. There is no equal-view, uncapped-handler, or honest-seat premise. -/
theorem transferReceipts_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest) (B : Block) :
    TransferReceipts p (gateInput p rho r source) r (nextHeadState p rho r reader).blocks
      (voterView p (nextHeadState p rho r reader) (r + 1))
      (voterSupportView p (nextHeadState p rho r reader) (r + 1)) B := by
  refine ⟨?_, ?_, nextHeadState_support_subset_raw p E rho hΔ r hsync reader hr⟩
  · intro o ho _
    exact synchronous_early_head_in_voterSupport p E rho hΔ r hsync
      source reader hs hr o ho
  · intro o ho i hi
    exact synchronous_voter_raw_late p E rho hΔ r hsync source reader hs hr o i hi ho

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Transfer follows from the engine, saved views, receipt relay,
compatible live targets, and the ordinary strict-majority walk. -/
theorem transfer_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, SynchronousLabel p E rho r → ∀ source ∈ rho.honest,
      ∀ B C, confirmation p (gateInput p rho r source) r = some C →
        Block.preceq B C = true →
        (∀ reader ∈ rho.honest, ∀ K ∈ liveTargets (nextHeadState p rho r reader),
          Block.compatible K B = true) →
        ∀ reader ∈ rho.honest,
          Block.preceq B (nextHead p (nextHeadState p rho r reader) r) = true := by
  intro r hsync source hs B C hc hp hroots reader hr
  have hroot : Block.Compatible (liveRoot (nextHeadState p rho r reader)) B := by
    rcases (liveRoot_is_deepest (nextHeadState p rho r reader)).1 with hg | hm
    · rw [hg]
      exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix B))
    · exact hroots reader hr _ hm
  have hpositive : 0 < (prefixSupportSeats p (gateInput p rho r source) r B).card := by
    have hm := confirmation_majority p (gateInput p rho r source) r C hc
    have hle := prefixSupport_mono p (gateInput p rho r source) r B C hp
    rw [prefixSupport_eq_card p _ r B] at hle
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpositive
  obtain ⟨o, ho, _, target, ht, htarget⟩ :=
    prefixSupportSeats_witness p (gateInput p rho r source) r B i hi
  exact forkChoice_covers_of_transfer p (gateInput p rho r source)
    (nextHeadState p rho r reader) r (r + 1) _ _ _ B C hc hp
    (transferReceipts_from_engine p E rho hΔ r hsync source reader hs hr B) hroot
    (fun A hn hA => synchronous_early_path_in_voterTree p E rho hΔ r hsync
      source reader hs hr o (List.mem_filter.mp ho).1 target A ht hn
      (prefix_trans A B target hA htarget))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The recovery descent now uses engine transfer after release. Only
compatibility of strictly stronger rows remains a stage premise. -/
theorem transfer_of_stronger_rows_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) (source : V) (hs : source ∈ rho.honest)
    (B C : Block) (hc : confirmation p (gateInput p rho r source) r = some C)
    (hp : Block.Preceq B C)
    (hstrong : ∀ reader ∈ rho.honest, ∀ K g deadline,
      (K, g, deadline) ∈ (nextHeadState p rho r reader).obligations →
      prefixSupport p (gateInput p rho r source) r B < g → Block.Compatible K B) :
    ∀ reader ∈ rho.honest,
      Block.Preceq B (nextHead p (nextHeadState p rho r reader) r) := by
  exact transfer_from_engine p E rho hΔ r hsync source hs B C hc hp
    (nextHeadState_targets_compatible p E rho hΔ r hsync source hs B C hc hp hstrong)

end AvailableChain.GridCO
end
