module
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSAClaims.Statements.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME the vote handler does not write the block field. -/
private theorem frame_vote_blocks (st : GridCO.State p.n .root) (o : GridCO.Wire p.n .root) :
    (GridCO.admitVote p.toParams.engine st o).blocks = st.blocks := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> cases msg <;> delta GridCO.admitVote <;> dsimp only
  all_goals first
    | rfl
    | split <;> rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME carried HEAD admission does not change stored blocks. -/
private theorem frame_vote_fold_blocks (xs : List (GridCO.HeadWire p.n .root))
    (st : GridCO.State p.n .root) :
    (xs.foldl (fun acc o => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead o)) st).blocks =
      st.blocks := by
  induction xs generalizing st with
  | nil => rfl
  | cons o xs ih => rw [List.foldl_cons, ih, frame_vote_blocks]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME the admitted parent has a smaller slot and all prefixes are slot-bounded.
Only the permitted StoreFacts library is used for the carried vote fold. -/
private theorem frame_admitProposal_slots (st : GridCO.State p.n .root)
    (o : GridCO.Wire p.n .root) (target : Block) (raw : List (GridCO.HeadWire p.n .root))
    (ho : ∀ B ∈ st.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) :
    ∀ B ∈ (GridCO.admitProposal p.toParams.engine st o target raw).blocks,
      ∀ A, Block.Preceq A B → A.slot ≤ B.slot := by
  cases ha : o.auth <;> delta GridCO.admitProposal <;> rw [ha] <;> dsimp only
  all_goals
    split
    · exact ho
    · rename_i hgood
      rw [frame_vote_fold_blocks]
      intro B hb A hAB
      rcases List.mem_append.mp hb with hold | hnew
      · exact ho B hold A hAB
      · have he := List.mem_singleton.mp hnew
        subst B
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          not_or, Bool.not_eq_false, decide_eq_false_iff_not] at hgood
        have hparent : GridCO.blockKnown st target.parent = true := by tauto
        have hslot : target.parent.slot < target.slot := by tauto
        cases target with
        | genesis =>
          have he : A = .genesis := by simpa [Block.Preceq, Block.preceq] using hAB
          subst A
          rfl
        | node parent s root root =>
          rcases Bool.or_eq_true_iff.mp hAB with he | hp
          · exact (of_decide_eq_true he) ▸ le_rfl
          · exact (ho parent (of_decide_eq_true hparent) A hp).trans hslot.le

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME an early resolved vote is in the late pool. -/
private theorem frame_clean_subset_late (v : GridCO.State p.n .root) (s : Slot) :
    GridCO.cleanSupport p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s := by
  intro o ho
  obtain ⟨hv, hr⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
  apply List.mem_filter.mpr
  refine ⟨hv, decide_eq_true ?_⟩
  cases ht : GridCO.resolvedHead? v o with
  | none =>
    delta GridCO.resolvedBefore at hr
    rw [ht] at hr
    cases hr
  | some b =>
    delta GridCO.resolvedBefore at hr
    rw [ht] at hr
    dsimp only at hr
    have ht' := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).2
    have htime : GridCO.earlyTime p.toParams.engine s < GridCO.gateTime p.toParams.engine s := by
      change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    exact ht'.trans htime

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME genuine support has a stored target whose slot is at most its vote label. -/
private theorem frame_prefixSupport_target (v : GridCO.State p.n .root) (s : Slot) (B : Block)
    (hpos : 0 < SA.Root.prefixSupport p.toParams v s B) :
    ∃ target ∈ v.blocks, target.slot ≤ s ∧ Block.Preceq B target := by
  obtain ⟨_, K, _, _, hm, hs, hp, _⟩ := prefixSupport_body p v s B hpos
  exact ⟨K, hm, hs, hp⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME ordered stored slots and preserved write labels under reconciliation. -/
private theorem frame_slots_reconcile (st : State p.n)
    (ho : ∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot)
    (hw : ∀ row ∈ st.fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) :
    (∀ B ∈ (reconcile st).base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) ∧
      (∀ row ∈ (reconcile st).fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) := by
  constructor
  · rw [reconcile_eq]; exact ho
  · intro row hr B hb
    rw [reconcile_fastWrite] at hr
    obtain ⟨old, hold, he⟩ := List.mem_map.mp hr
    subst row
    exact hw old hold B (List.mem_filter.mp hb).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME row admission does not write blocks or fast-write labels. -/
private theorem frame_slots_rows (rows : List (RowWire p.n)) (st : State p.n)
    (ho : ∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot)
    (hw : ∀ row ∈ st.fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) :
    (∀ B ∈ (rows.foldl (admitRow p) st).base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) ∧
      (∀ row ∈ (rows.foldl (admitRow p) st).fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) := by
  induction rows generalizing st with
  | nil => exact ⟨ho, hw⟩
  | cons a rows ih =>
    rw [List.foldl_cons]
    rcases admitRow_eq p st a with he | he <;> rw [he] <;> exact ih _ ho hw

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME a block admission checks strict parent-slot order; reconcile only filters. -/
private theorem frame_slots_process (st : State p.n) (o : Wire p.n)
    (ho : ∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot)
    (hw : ∀ row ∈ st.fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) :
    (∀ B ∈ (process p st o).base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) ∧
      (∀ row ∈ (process p st o).fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) := by
  unfold process
  cases hd : o.decode with
  | none => exact ⟨ho, hw⟩
  | some m =>
    cases m with
    | vote s i B => exact ⟨by rw [admitHead_base_blocks]; exact ho, hw⟩
    | row i body =>
      dsimp only
      rcases admitRow_eq p st ⟨o.auth, body⟩ with he | he <;> rw [he] <;> exact ⟨ho, hw⟩
    | block s N =>
      dsimp only
      unfold admitBlock
      split
      · exact ⟨ho, hw⟩
      · cases hp : parentFG st N.erase with
        | none => exact ⟨ho, hw⟩
        | some P =>
          dsimp only
          split
          · have hb := frame_admitProposal_slots p st.base
              (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) ho
            apply frame_slots_rows
            · split
              · exact hb
              · exact (frame_slots_reconcile p
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
                hb hw).1
            · split
              · exact hw
              · exact (frame_slots_reconcile p
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
                hb hw).2
          · exact ⟨ho, hw⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME positive fast support supplies a slot-bounded target. -/
private theorem frame_fastSet_slot (st : State p.n) (s : Slot)
    (ho : ∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) :
    ∀ B ∈ fastSet p (eraseFG st.fg.F) (actView st) s, B.slot ≤ s := by
  intro B hb
  cases hc : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s with
  | none =>
    delta fastSet at hb
    rw [hc] at hb
    exact (List.not_mem_nil hb).elim
  | some h =>
    delta fastSet at hb
    rw [hc] at hb
    dsimp only at hb
    split at hb
    · exact (List.not_mem_nil hb).elim
    · have hsupport := of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
      have hthreshold : 0 < SA.releaseThreshold p.toParams := by
        change 0 < (p.n + 1) / 2
        have hn := p.nPos
        omega
      have hpos := hthreshold.trans_le hsupport
      obtain ⟨T, hT, hslot, hBT⟩ := frame_prefixSupport_target p
        (actView st) s B hpos
      exact (ho T ((actView_blocks st T).mp hT).1 B hBT).trans hslot

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME a new fast-write set retains its original gate label. -/
private theorem frame_slots_clock (st : State p.n) (t : Time)
    (ho : ∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot)
    (hw : ∀ row ∈ st.fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) :
    (∀ B ∈ (clock p st t).base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) ∧
      (∀ row ∈ (clock p st t).fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) := by
  refine ⟨by rw [clock_base_blocks]; exact ho, ?_⟩
  have hp : ∀ row ∈ (clockPre p st t).fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1 := by
    rw [clockPre_fastWrite]; exact hw
  have hop : ∀ B ∈ (clockPre p st t).base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot := by
    rw [(clockPre_fields p st t).2.1]; exact ho
  unfold clock
  dsimp only
  split
  · intro row hr B hb
    cases hs : GridCO.savedGenuine (clockPre p st t).base
        (((t - 6 * p.Δ) / (4 * p.Δ)).toNat) with
    | none =>
      rw [(gateStep_fresh_cases p _ _ hs).2] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hp row hr B hb
      · have he := List.mem_singleton.mp hr
        subst row
        split at hb
        · exact frame_fastSet_slot p _ _ hop B hb
        · exact (List.not_mem_nil hb).elim
    | some result =>
      rw [gateStep_saved p _ _ (by rw [hs]; rfl), normalizeS_fields] at hr
      exact hp row hr B hb
  · exact hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME local induction preserves ordered slots and bounded fast-write labels. -/
private theorem frame_slots_reachable (st : State p.n) (hr : Reachable p st) :
    (∀ B ∈ st.base.blocks, ∀ A, Block.Preceq A B → A.slot ≤ B.slot) ∧
      (∀ row ∈ st.fastWrite, ∀ B ∈ row.2, B.slot ≤ row.1) := by
  induction hr with
  | init =>
    constructor
    · intro B hb
      have he : B = .genesis := List.mem_singleton.mp hb
      subst B
      intro A ha
      have he : A = .genesis := by simpa [Block.Preceq, Block.preceq] using ha
      subst A
      rfl
    · intro row hr
      exact (List.not_mem_nil hr).elim
  | restart t _ ih =>
    constructor
    · exact ih.1
    · intro row hr
      exact (List.not_mem_nil hr).elim
  | tick t _ ih => exact frame_slots_clock p _ t ih.1 ih.2
  | deliver o _ ih => exact frame_slots_process p _ o ih.1 ih.2

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1288–1308; plan S30, H-FRAME/F3.
DC: SAME a source's fast-write label bounds its block slot.
The proof keeps the original gate label through local steps. It needs neither
a fresh row emission nor TSrc as an additional public premise. -/
theorem healing_source_slot {x : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (_hx : x ∈ rho.honest) (hc : actionSourceFG p c E rho x r = some (some C)) :
    C.slot ≤ r * p.R := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hc
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hc
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hc
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (p.actionTime r)).st
    have hinv := (frame_slots_reachable p st (reachable_postClock E rho i x _)).2
    have hround : p.round (st.slot p) = r := (fgsa_action_slot_round (c := c) _ r).2
    have hfw := (Finset.mem_filter.mp (pickPair_some_spec _ _ hc).1).2
    change (decide (eraseFG C ∈ (fastWriteAt st (p.round (st.slot p) * p.R)).getD []) && _) =
      true at hfw
    have hmem := of_decide_eq_true (Bool.and_eq_true_iff.mp hfw).1
    rw [hround] at hmem
    unfold fastWriteAt at hmem
    cases hf : st.fastWrite.find? (fun row => row.1 == r * p.R) with
    | none => simp only [hf, Option.map_none, Option.getD_none] at hmem
              exact (List.not_mem_nil hmem).elim
    | some row =>
      simp only [hf, Option.map_some, Option.getD_some] at hmem
      have hlabel : row.1 = r * p.R := by simpa using List.find?_some hf
      have hslot := hinv row (List.mem_of_find?_eq_some hf) (eraseFG C) hmem
      rw [eraseFG_slot, hlabel] at hslot
      exact hslot

end AvailableChain.FGSA.Run
end
