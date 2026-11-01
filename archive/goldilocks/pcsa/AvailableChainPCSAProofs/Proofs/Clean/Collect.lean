module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Shared.CleanGate

public section

/-! C3 exact-target assembly, collection, and saturation. -/

namespace AvailableChain.PCSA
open Gen.Pure
variable {n : Nat}

private theorem select_subset (as : List (AckWire n)) : firstPerSeat as ⊆ as := by
  delta firstPerSeat
  suffices ∀ acc : List (AckWire n), acc ⊆ as →
      (as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
        else acc ++ [a]) acc) ⊆ as from this [] (by simp)
  intro acc h
  apply List.foldlRecOn (motive := fun acc => acc ⊆ as)
  · exact h
  · intro acc ha a hm
    split
    · exact ha
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ha hb
      · simpa only [List.mem_singleton.mp hb] using hm

private theorem select_nodup (as acc : List (AckWire n))
    (h : (acc.map AckWire.seat?).Nodup) :
    ((as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
      else acc ++ [a]) acc).map AckWire.seat?).Nodup := by
  refine List.foldlRecOn as _
    (motive := fun (acc : List (AckWire n)) => (acc.map AckWire.seat?).Nodup) ?_ ?_
  · exact h
  · intro acc ha a _
    split
    · exact ha
    · rename_i hn
      rw [List.map_append, List.nodup_append]
      refine ⟨ha, by simp, ?_⟩
      intro x hx y hy he
      have hy' : y = a.seat? := by simpa using hy
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hx
      apply hn
      apply List.any_eq_true.mpr
      exact ⟨old, ho, beq_iff_eq.mpr (he.trans hy')⟩

private theorem select_cover (as acc : List (AckWire n)) (i : Option (Fin n)) :
    i ∈ (as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
      else acc ++ [a]) acc).map AckWire.seat? ↔
      i ∈ acc.map AckWire.seat? ∨ i ∈ as.map AckWire.seat? := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    split
    · rename_i h
      obtain ⟨old, ho, hs⟩ := List.any_eq_true.mp h
      have hm : a.seat? ∈ acc.map AckWire.seat? :=
        List.mem_map.mpr ⟨old, ho, beq_iff_eq.mp hs⟩
      simp only [List.map_cons, List.mem_cons]
      constructor
      · tauto
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hm)
        · exact Or.inr h
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      tauto

/-- Seat selection preserves each input seat and keeps it only once. -/
theorem pcsa_firstPerSeat_seats (as : List (AckWire n)) :
    ((firstPerSeat as).map AckWire.seat?).Nodup ∧
      ∀ i, i ∈ (firstPerSeat as).map AckWire.seat? ↔ i ∈ as.map AckWire.seat? := by
  delta firstPerSeat
  constructor
  · exact select_nodup as [] (by simp)
  · intro i
    simpa only [List.map_nil, List.not_mem_nil, false_or] using select_cover as [] i

private theorem decoded_seat {a : AckWire n} {s : Slot} {i : Fin n} {r : BlockId}
    (h : a.decode? = some (s, i, r)) : a.seat? = some i := by
  change (a.decode?.map (fun x => x.2.1)) = some i
  rw [h]
  rfl

private theorem filterMap_size (as : List (AckWire n))
    (hn : (as.map AckWire.seat?).Nodup) (hs : ∀ a ∈ as, ∃ i, a.seat? = some i) :
    (as.filterMap AckWire.seat?).Nodup ∧ (as.filterMap AckWire.seat?).length = as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    obtain ⟨i, hi⟩ := hs a (by simp)
    obtain ⟨hne, hnd⟩ := List.nodup_cons.mp hn
    obtain ⟨hd, hl⟩ := ih hnd (fun a ha => hs a (List.mem_cons_of_mem _ ha))
    rw [List.filterMap_cons, hi]
    dsimp only
    refine ⟨List.nodup_cons.mpr ⟨?_, hd⟩, by simp [hl]⟩
    intro hm
    obtain ⟨b, hb, hbi⟩ := List.mem_filterMap.mp hm
    exact hne (List.mem_map.mpr ⟨b, hb, hbi.trans hi.symm⟩)

/-- A quorum of pooled exact acks assembles the full resolved target. -/
theorem pcsa_assemblePC_quorum (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hs : 0 < s) (hb : B.slot = s) (hmem : B ∈ st.base.blocks)
    (hF : st.fg.F = .genesis) (Q : Finset (Fin p.n))
    (hQ : pcQuorum p.n ≤ Q.card)
    (hpool : ∀ i ∈ Q, (⟨.seat (.ack s) i, B.root⟩ : AckWire p.n) ∈ st.ackPool) :
    ∃ C, assemblePC st s B = some C ∧ C.slot = s ∧ C.target = B := by
  classical
  let as := firstPerSeat (acksOn st s B.root)
  have hexact : ∀ a ∈ as, ∃ i, a.decode? = some (s, i, B.root) := by
    intro a ha
    exact ((mem_acksOn_iff st s B.root a).mp (select_subset _ ha)).2
  have hseats := pcsa_firstPerSeat_seats (acksOn st s B.root)
  have hsize := filterMap_size as hseats.1 (fun a ha =>
    let ⟨i, hi⟩ := hexact a ha; ⟨i, decoded_seat hi⟩)
  have hcover : Q ⊆ (as.filterMap AckWire.seat?).toFinset := by
    intro i hi
    have hm : (⟨.seat (.ack s) i, B.root⟩ : AckWire p.n) ∈ acksOn st s B.root :=
      (mem_acksOn_iff _ _ _ _).mpr ⟨hpool i hi, i, rfl⟩
    have hh := (hseats.2 (some i)).mpr (List.mem_map.mpr ⟨_, hm, rfl⟩)
    obtain ⟨a, ha, hai⟩ := List.mem_map.mp hh
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨a, ha, hai⟩)
  have hlen : pcQuorum p.n ≤ as.length := by
    have := le_trans hQ (Finset.card_le_card hcover)
    rwa [List.toFinset_card_of_nodup hsize.1, hsize.2] at this
  have hng : B ≠ .genesis := by
    intro he
    subst B
    change 0 = s at hb
    exact (Nat.ne_of_gt hs) hb.symm
  let C : PC p.n := ⟨s, B, as⟩
  have hw : C.wellFormed = true := by
    delta PC.wellFormed
    dsimp only [C, PC.seats]
    simp (config := { iota := false }) only
      [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨hs, hng⟩, hb⟩, hlen⟩, ?_⟩, ?_⟩
    · rw [List.dedup_eq_self.mpr hsize.1, hsize.2]
    · apply List.all_eq_true.mpr
      intro a ha
      obtain ⟨i, hi⟩ := hexact a ha
      rcases a with ⟨auth, payload⟩
      cases auth with
      | none => cases hi
      | proposer j => cases hi
      | seat l j =>
        cases l with
        | fg => cases hi
        | head k => cases hi
        | ack k =>
          have he : k = s ∧ j = i ∧ payload = B.root := by
            change some (k, j, payload) = some (s, i, B.root) at hi
            simpa only [Option.some.injEq, Prod.mk.injEq, and_assoc] using hi
          rcases he with ⟨rfl, rfl, rfl⟩
          dsimp only [AckWire.decode?, Label.ackSlot?, Option.map]
          simp only [BEq.rfl, Bool.and_self]
  refine ⟨C, (assemblePC_some_iff _ _ _ _).mpr ⟨rfl, ?_⟩, rfl, rfl⟩
  change (C.wellFormed && decide (B ∈ st.base.blocks) && activeCompatible st B) = true
  rw [hw, decide_eq_true hmem]
  change activeCompatible st B = true
  delta activeCompatible
  rw [hF]
  exact block_compatible_of_common (block_preceq_refl _) (block_genesis_preceq _)

private def collectStep (st : State n) (sr : Slot × BlockId) : State n :=
  match st.base.blocks.find? (fun b => b.root == sr.2) with
  | none => st
  | some b => match assemblePC st sr.1 b with
    | none => st
    | some C => installPC st C

private theorem step_frame (st : State n) (sr : Slot × BlockId) :
    (collectStep st sr).base.blocks = st.base.blocks ∧
    (collectStep st sr).ackPool = st.ackPool ∧ (collectStep st sr).fg = st.fg ∧
    st.pcs ⊆ (collectStep st sr).pcs := by
  unfold collectStep
  cases st.base.blocks.find? (fun b => b.root == sr.2) with
  | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
  | some b =>
    dsimp only
    cases assemblePC st sr.1 b with
    | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
    | some C => exact ⟨(installPC_frame _ _).2.1, (installPC_frame _ _).2.2.1,
        (installPC_frame _ _).2.2.2.2, installPC_pcs_mono _ _⟩

private theorem assemble_congr (st st' : State n) (s : Slot) (B : Block)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) : assemblePC st' s B = assemblePC st s B := by
  delta assemblePC pcValid acksOn activeCompatible
  rw [hb, ha, hf]

private theorem install_has (st : State n) (C : PC n) :
    ∃ D ∈ (installPC st C).pcs, D.slot = C.slot ∧ D.target = C.target := by
  by_cases h : st.pcs.any (fun D => D.slot == C.slot && D.target == C.target) = true
  · rw [installPC_duplicate st C h]
    obtain ⟨D, hd, hs⟩ := List.any_eq_true.mp h
    exact ⟨D, hd, by simpa only [Bool.and_eq_true, beq_iff_eq] using hs⟩
  · rw [installPC_pcs_new st C (Bool.eq_false_iff.mpr h)]
    exact ⟨C, List.mem_append_right _ (by simp), rfl, rfl⟩

private theorem collect_hit (cs : List (Slot × BlockId)) (st : State n)
    (s : Slot) (B : Block) (C : PC n) (hm : (s, B.root) ∈ cs)
    (hr : st.base.blocks.find? (fun b => b.root == B.root) = some B)
    (ha : assemblePC st s B = some C) :
    ∃ D ∈ (cs.foldl collectStep st).pcs, D.slot = s ∧ D.target = B := by
  induction cs generalizing st with
  | nil => simp at hm
  | cons sr cs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with he | hm
    · have hshape := ((assemblePC_some_iff _ _ _ _).mp ha).1
      subst sr
      have hstep : collectStep st (s, B.root) = installPC st C := by
        unfold collectStep
        rw [hr]
        dsimp only
        rw [ha]
      rw [hstep]
      obtain ⟨D, hd, hs, ht⟩ := install_has st C
      refine ⟨D, ?_, hs.trans (congrArg PC.slot hshape), ht.trans (congrArg PC.target hshape)⟩
      exact List.foldlRecOn cs collectStep
        (motive := fun acc : State n => D ∈ acc.pcs) hd
        (fun acc hm sr _ => (step_frame acc sr).2.2.2 hm)
    · have hf := step_frame st sr
      apply ih (collectStep st sr) hm
      · rwa [hf.1]
      · rwa [assemble_congr st _ s B hf.1 hf.2.1 hf.2.2.1]

/-- Collection installs a PC for every resolved candidate that can assemble.
A prior PC with the same slot and target is sufficient. -/
theorem pcsa_collectPCs_of_assemble (st : State n) (s : Slot) (B : Block)
    (C : PC n) (i : Fin n) (a : AckWire n) (hm : a ∈ st.ackPool)
    (hd : a.decode? = some (s, i, B.root))
    (hr : st.base.blocks.find? (fun b => b.root == B.root) = some B)
    (ha : assemblePC st s B = some C) :
    ∃ D ∈ (collectPCs st).pcs, D.slot = s ∧ D.target = B := by
  delta collectPCs
  apply collect_hit _ st s B C ?_ hr ha
  apply List.mem_eraseDups.mpr
  exact List.mem_filterMap.mpr ⟨a, hm, by rw [hd]; rfl⟩

/-- Exact target collection from the pooled quorum, with explicit resolution.
The run proof must establish the receiver's held target and its root lookup. -/
theorem pcsa_collectPCs_quorum (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hs : 0 < s) (hb : B.slot = s)
    (hr : st.base.blocks.find? (fun b => b.root == B.root) = some B)
    (hF : st.fg.F = .genesis) (Q : Finset (Fin p.n))
    (hQ : pcQuorum p.n ≤ Q.card)
    (hpool : ∀ i ∈ Q, (⟨.seat (.ack s) i, B.root⟩ : AckWire p.n) ∈ st.ackPool) :
    ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = B := by
  obtain ⟨C, hc, _, _⟩ := pcsa_assemblePC_quorum p st s B hs hb
    (List.mem_of_find?_eq_some hr) hF Q hQ hpool
  have hpos : 0 < Q.card := by
    have hn := p.nPos
    change (p.n + 1) / 2 ≤ Q.card at hQ
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact pcsa_collectPCs_of_assemble st s B C i _ (hpool i hi) rfl hr hc

/-- Every collectable slot and root already has a held PC. -/
def PCSaturated (st : State n) : Prop :=
  ∀ a ∈ st.ackPool, ∀ s i r, a.decode? = some (s, i, r) →
    ∀ B, st.base.blocks.find? (fun b => b.root == r) = some B →
    ∀ C, assemblePC st s B = some C →
      ∃ D ∈ st.pcs, D.slot = s ∧ D.target = B

theorem PCSaturated_def (st : State n) : PCSaturated st =
    (∀ a ∈ st.ackPool, ∀ s i r, a.decode? = some (s, i, r) →
      ∀ B, st.base.blocks.find? (fun b => b.root == r) = some B →
      ∀ C, assemblePC st s B = some C →
        ∃ D ∈ st.pcs, D.slot = s ∧ D.target = B) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Collection leaves no collectable target without a PC. -/
theorem pcsa_collectPCs_saturated (st : State n) : PCSaturated (collectPCs st) := by
  intro a ha s i r hd B hr C hc
  have hf := collectPCs_frame st
  rw [hf.2.2.1] at ha
  rw [hf.2.1] at hr
  rw [assemble_congr st _ s B hf.2.1 hf.2.2.1 hf.2.2.2.2] at hc
  have hroot : B.root = r := by simpa only [beq_iff_eq] using List.find?_some hr
  rw [← hroot] at hd hr
  exact pcsa_collectPCs_of_assemble st s B C i a ha hd hr hc

/-- Repeating collection in a saturated store changes nothing. -/
theorem pcsa_collectPCs_eq_of_saturated (st : State n) (h : PCSaturated st) :
    collectPCs st = st := by
  let cs := (st.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups
  have hstep : ∀ sr ∈ cs, collectStep st sr = st := by
    intro sr hm
    obtain ⟨a, ha, had⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hm)
    obtain ⟨⟨s, i, r⟩, hd, he⟩ := Option.map_eq_some_iff.mp had
    dsimp only at he
    subst sr
    unfold collectStep
    cases hr : st.base.blocks.find? (fun b => b.root == r) with
    | none => rfl
    | some B =>
      dsimp only
      cases hc : assemblePC st s B with
      | none => rfl
      | some C =>
        obtain ⟨D, hD, hs, ht⟩ := h a ha s i r hd B hr C hc
        have heq := ((assemblePC_some_iff _ _ _ _).mp hc).1
        apply installPC_duplicate
        apply List.any_eq_true.mpr
        refine ⟨D, hD, ?_⟩
        rw [heq]
        simpa only [Bool.and_eq_true, beq_iff_eq] using And.intro hs ht
  change cs.foldl collectStep st = st
  suffices ∀ xs : List (Slot × BlockId), (∀ sr ∈ xs, collectStep st sr = st) →
      xs.foldl collectStep st = st from this cs hstep
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons sr xs ih =>
    intro hh
    rw [List.foldl_cons, hh sr (by simp)]
    exact ih (fun x hx => hh x (List.mem_cons_of_mem _ hx))

/-- Saturation depends only on the ack pool, tree, frame, and held PC set. -/
theorem pcsa_saturated_transfer (st st' : State n) (h : PCSaturated st)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) (hp : st.pcs ⊆ st'.pcs) : PCSaturated st' := by
  intro a ham s i r hd B hr C hc
  rw [ha] at ham
  rw [hb] at hr
  rw [assemble_congr st st' s B hb ha hf] at hc
  obtain ⟨D, hm, hs, ht⟩ := h a ham s i r hd B hr C hc
  exact ⟨D, hp hm, hs, ht⟩

end AvailableChain.PCSA
end
