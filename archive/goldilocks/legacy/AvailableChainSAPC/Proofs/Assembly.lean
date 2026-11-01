module
public import AvailableChainSAPC.Proofs.Quorum
public import AvailableChainSAPC.Proofs.Rank

@[expose] public section
namespace AvailableChain.SAPC

/-- Seat selection retains only original signatures. -/
theorem firstPerSeat_subset {n : Nat} (xs : List (HeadWire n)) : firstPerSeat xs ⊆ xs := by
  induction xs using List.reverseRecOn with
  | nil => simp [firstPerSeat]
  | append_singleton xs x ih =>
      simp only [firstPerSeat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      · exact List.Subset.trans ih (List.subset_append_left _ _)
      · intro o ho
        rcases List.mem_append.mp ho with hm | hm
        · exact List.mem_append_left _ (ih hm)
        · exact List.mem_append_right _ hm

theorem firstPerSeat_nodup {n : Nat} (xs : List (HeadWire n)) :
    ((firstPerSeat xs).map headSeat?).Nodup := by
  induction xs using List.reverseRecOn with
  | nil => simp [firstPerSeat]
  | append_singleton xs x ih =>
      simp only [firstPerSeat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      · exact ih
      · rename_i hn
        have hnot : headSeat? x ∉ (firstPerSeat xs).map headSeat? := by
          intro hm
          obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
          exact hn (List.any_eq_true.mpr ⟨o, ho, by simpa using he⟩)
        change ((firstPerSeat xs ++ [x]).map headSeat?).Nodup
        rw [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        exact ⟨ih, by simp, fun a ha b hb => by
          have he : b = headSeat? x := by simpa using hb
          subst b
          intro heq
          exact hnot (heq ▸ ha)⟩

/-- No seat disappears when duplicate copies are removed. -/
theorem firstPerSeat_seats {n : Nat} (xs : List (HeadWire n)) :
    ((firstPerSeat xs).filterMap headSeat?).toFinset = (xs.filterMap headSeat?).toFinset := by
  induction xs using List.reverseRecOn with
  | nil => simp [firstPerSeat]
  | append_singleton xs x ih =>
      simp only [firstPerSeat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      · rename_i hdup
        obtain ⟨old, hm, he⟩ := List.any_eq_true.mp hdup
        have heq : headSeat? old = headSeat? x := by simpa using he
        change ((firstPerSeat xs).filterMap headSeat?).toFinset = _
        rw [ih]
        have hmem := firstPerSeat_subset xs hm
        cases hx : headSeat? x with
        | none => simp [List.filterMap_append, hx]
        | some i =>
            have hi : i ∈ (xs.filterMap headSeat?).toFinset :=
              List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨old, hmem, heq.trans hx⟩)
            simp [List.filterMap_append, hx, hi]
      · change (((firstPerSeat xs) ++ [x]).filterMap headSeat?).toFinset = _
        simp only [List.filterMap_append, List.toFinset_append, ih]

theorem firstPerSeat_filterMap_nodup {n : Nat} (xs : List (HeadWire n)) :
    ((firstPerSeat xs).filterMap headSeat?).Nodup := by
  apply List.Nodup.of_map (f := some)
  rw [List.map_filterMap_some_eq_filter_map_isSome]
  exact (firstPerSeat_nodup xs).filter _

/-- Assembly succeeds from any q distinct usable ack seats. Extra copies,
equivocations, and receipt order do not prevent completion. -/
theorem assemblePC_complete (p : Params) {n : Nat} (st : State n) (s : Slot) (b : Block)
    (hs : 0 < s) (hb : b ≠ .genesis) (hslot : b.slot = s)
    (hpath : pathKnown st b = true)
    (hq : pcQuorum p ≤ ((st.receivedHeads.filter (fun o =>
      pcWitness s b o && pathKnown st o.payload.target)).filterMap headSeat?).toFinset.card) :
    ∃ c, assemblePC p st s b = some c ∧ c.slot = s ∧ c.target = b ∧
      pcValid p st c = true := by
  let xs := st.receivedHeads.filter (fun o => pcWitness s b o && pathKnown st o.payload.target)
  let selected := firstPerSeat xs
  let ws := selected.take (pcQuorum p)
  have hlen : pcQuorum p ≤ selected.length := by
    calc
      pcQuorum p ≤ (xs.filterMap headSeat?).toFinset.card := hq
      _ = (selected.filterMap headSeat?).toFinset.card := (congrArg Finset.card
        (firstPerSeat_seats xs)).symm
      _ ≤ (selected.filterMap headSeat?).length := List.toFinset_card_le _
      _ ≤ selected.length := List.length_filterMap_le _ _
  have hwlen : ws.length = pcQuorum p := List.length_take_of_le hlen
  have hmem (o : HeadWire n) (ho : o ∈ ws) :
      o ∈ st.receivedHeads ∧ pcWitness s b o = true ∧ pathKnown st o.payload.target = true := by
    have hx := firstPerSeat_subset xs (List.mem_of_mem_take ho)
    exact ⟨(List.mem_filter.mp hx).1, Bool.and_eq_true_iff.mp (List.mem_filter.mp hx).2⟩
  have hseats : (ws.filterMap headSeat?).length = ws.length := by
    apply List.filterMap_length_eq_length.mpr
    intro o ho
    have hl := (hmem o ho).2.1
    cases o with
    | mk auth data =>
        cases auth <;> simp_all [pcWitness, headLabel?, headSeat?]
  have hnodup : (ws.filterMap headSeat?).Nodup :=
    (firstPerSeat_filterMap_nodup xs).sublist ((List.take_sublist _ _).filterMap _)
  let c := PC.mk s b ws
  have hc : pcValid p st c = true := by
    have hw : pcWellFormed p c = true := by
      simp only [pcWellFormed, c, Bool.and_eq_true_iff, decide_eq_true_eq,
        bne_iff_ne, beq_iff_eq]
      exact ⟨⟨⟨⟨⟨hs, hb⟩, hslot⟩, hwlen⟩, by rw [hnodup.dedup, hseats, hwlen]⟩,
        List.all_eq_true.mpr (fun o ho => (hmem o ho).2.1)⟩
    have hp : pcPaths st c = true :=
      Bool.and_eq_true_iff.mpr ⟨hpath, List.all_eq_true.mpr (fun o ho => (hmem o ho).2.2)⟩
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hw, hp⟩,
      List.all_eq_true.mpr (fun o ho => by simpa using (hmem o ho).1)⟩
  refine ⟨c, ?_, rfl, rfl, hc⟩
  change (if pcValid p st c then some c else none) = some c
  rw [ite_eq_left hc]

/-- Any valid local certificate suffices for deterministic assembly,
even if the stored encoding uses a different subset or order. -/
theorem assemblePC_of_valid (p : Params) {n : Nat} (st : State n) (c : PC n)
    (hc : pcValid p st c = true) :
    ∃ d, assemblePC p st c.slot c.target = some d ∧ d.slot = c.slot ∧
      d.target = c.target ∧ pcValid p st d = true := by
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hp := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  have hwparts := hw
  simp only [pcWellFormed, Bool.and_eq_true_iff, decide_eq_true_eq,
    bne_iff_ne, beq_iff_eq] at hwparts
  apply assemblePC_complete p st c.slot c.target hwparts.1.1.1.1.1
    hwparts.1.1.1.1.2 hwparts.1.1.1.2 (Bool.and_eq_true_iff.mp hp).1
  rw [← pcSeats_card p c hw]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hi)
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  refine ⟨o, List.mem_filter.mpr ⟨?_, ?_⟩, he⟩
  · exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 o ho)
  · exact Bool.and_eq_true_iff.mpr
      ⟨List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 o ho,
        List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2 o ho⟩

/-- The existing single-candidate step in `collectPCs`. -/
def assemblyStep (p : Params) {n : Nat} (st : State n) (pair : Slot × Block) : State n :=
  match assemblePC p st pair.1 pair.2 with
  | none => st
  | some c => installPC st c

theorem assemblePC_eq_of_data (p : Params) {n : Nat} (a b : State n)
    (hb : a.base.blocks = b.base.blocks) (hh : a.receivedHeads = b.receivedHeads)
    (s : Slot) (target : Block) : assemblePC p a s target = assemblePC p b s target := by
  simp only [assemblePC, pathKnown_eq_of_blocks_eq a b hb, hh, pcValid_eq_of_data p a b hb hh]

theorem assemblyFold_rank (p : Params) {n : Nat} (pairs : List (Slot × Block)) (st : State n) :
    PCRankLE st.bestPC (pairs.foldl (assemblyStep p) st).bestPC := by
  induction pairs generalizing st with
  | nil => exact .refl _
  | cons pair pairs ih =>
      apply PCRankLE.trans (b := (assemblyStep p st pair).bestPC) ?_ (ih _)
      unfold assemblyStep
      split
      · exact .refl _
      · exact preferPC_rank _ _

theorem preferPC_candidate_rank {n : Nat} (old : Option (PC n)) (c : PC n) :
    ∃ d, preferPC old c = some d ∧ c.slot ≤ d.slot := by
  cases old with
  | none => exact ⟨c, rfl, le_rfl⟩
  | some old =>
      simp only [preferPC]
      split_ifs with hlt
      · exact ⟨c, rfl, le_rfl⟩
      · exact ⟨old, rfl, Nat.le_of_not_gt hlt⟩

theorem assemblyFold_complete (p : Params) {n : Nat} (pairs : List (Slot × Block))
    (st : State n) (s : Slot) (b : Block) (c : PC n) (hm : (s, b) ∈ pairs)
    (hc : assemblePC p st s b = some c) :
    ∃ d, (pairs.foldl (assemblyStep p) st).bestPC = some d ∧ c.slot ≤ d.slot := by
  induction pairs generalizing st with
  | nil => simp at hm
  | cons pair pairs ih =>
      rcases List.mem_cons.mp hm with he | hm
      · subst pair
        obtain ⟨d, hd, hcd⟩ := preferPC_candidate_rank st.bestPC c
        have hstep : (assemblyStep p st (s, b)).bestPC = some d := by
          simpa only [assemblyStep, hc, installPC] using hd
        obtain ⟨e, he, hde⟩ := assemblyFold_rank p pairs (assemblyStep p st (s, b)) d hstep
        refine ⟨e, he, ?_⟩
        rcases hde with rfl | hde
        · exact hcd
        · exact hcd.trans hde.le
      · apply ih (assemblyStep p st pair) hm
        unfold assemblyStep
        split
        · exact hc
        · rename_i _ chosen _
          rw [assemblePC_eq_of_data p (installPC st chosen) st rfl rfl]
          exact hc

/-- A valid certificate is never missed by the archive scan. The scan
may retain another encoding or a higher target slot. -/
theorem collectPCs_complete (p : Params) {n : Nat} (st : State n) (c : PC n)
    (hc : pcValid p st c = true) :
    ∃ d, (collectPCs p st).bestPC = some d ∧ c.slot ≤ d.slot := by
  obtain ⟨d, hd, hs, _, _⟩ := assemblePC_of_valid p st c hc
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hpos : 0 < (pcSeats c).card := by rw [pcSeats_card p c hw]; exact (quorum_bounds p).1
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨data, hm, hack, _⟩ := pcSeats_witness p c hw i hi
  have har := of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 _ hm)
  have hpair : (c.slot, c.target) ∈
      (st.receivedHeads.filterMap (fun o => o.payload.ack)).eraseDups := by
    simpa only [List.mem_eraseDups] using List.mem_filterMap.mpr
      ⟨⟨.seat (c.slot + 1) i, data⟩, har, hack⟩
  obtain ⟨e, he, hde⟩ := assemblyFold_complete p _ st c.slot c.target d hpair hd
  exact ⟨e, he, by simpa only [hs] using hde⟩

/-- Every complete local PC has been considered for storage. This is a
rank-completeness invariant, with no prefix-safety assertion. -/
def PCComplete (p : Params) {n : Nat} (st : State n) : Prop :=
  ∀ c, pcValid p st c = true → ∃ d, st.bestPC = some d ∧ c.slot ≤ d.slot

theorem collectPCs_PCComplete (p : Params) {n : Nat} (st : State n) :
    PCComplete p (collectPCs p st) := by
  intro c hc
  apply collectPCs_complete p st c
  exact pcValid_mono p _ st (by simp only [collectPCs_base]; exact List.Subset.refl _)
    (by simp only [collectPCs_archive]; exact List.Subset.refl _) c hc

theorem process_PCComplete (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : PCComplete p st) : PCComplete p (process p st o) := by
  unfold process
  split
  · exact collectPCs_PCComplete p _
  · unfold admitProposal
    split
    · exact collectPCs_PCComplete p _
    · exact h
  · split
    · exact collectPCs_PCComplete p _
    · exact h
  · exact h

theorem clock_PCComplete (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : PCComplete p st) : PCComplete p (clock p st t) := by
  intro c hc
  have hv := pcValid_mono p _ st (by simp only [clock_blocks]; exact List.Subset.refl _)
    (by simp only [clock_archive]; exact List.Subset.refl _) c hc
  simpa only [clock_bestPC] using h c hv

theorem PCComplete_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (AvailableChain.Generic.Event V (sapc p).Object)) (v : V) :
    PCComplete p ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v) := by
  apply fold_invariant p (PCComplete p)
  · intro c hc
    have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
    have hpos : 0 < (pcSeats c).card := by
      rw [pcSeats_card p c hw]; exact (quorum_bounds p).1
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    obtain ⟨data, hm, _, _⟩ := pcSeats_witness p c hw i hi
    have har := of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 _ hm)
    simp [initial] at har
  · exact clock_PCComplete p
  · exact process_PCComplete p

end AvailableChain.SAPC
end
