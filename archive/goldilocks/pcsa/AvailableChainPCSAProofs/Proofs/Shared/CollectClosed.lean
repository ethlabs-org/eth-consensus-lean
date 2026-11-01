module
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! Collection closure (pcsa34-r4.3 §3.6). `collectPCs` assembles a PC for
every `(slot, root)` candidate of the ack pool whose root resolves to a
stored block. When stored roots name one block, every key `(s, b)` that the
store can assemble (a stored target `b` and a valid first-per-seat set of
pooled acks on its root) is held after collection (`CollectClosed`). Every
delivery that pools acks or stores a block ends with collection; the other
steps keep the pool, the tree, `Σ` and the held PCs. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

variable {n : Nat}

/-- A PC of slot `s` on the target `B` is held. -/
def KeyHeld (st : State n) (s : Slot) (B : Block) : Prop :=
  ∃ c' ∈ st.pcs, c'.slot = s ∧ c'.target = B

theorem KeyHeld_def (st : State n) (s : Slot) (B : Block) :
    KeyHeld st s B = ∃ c' ∈ st.pcs, c'.slot = s ∧ c'.target = B := by
  delta KeyHeld
  rfl

/-- The key test of `installPC` is `KeyHeld`. -/
theorem pcsa_keyHeld_iff_any (st : State n) (s : Slot) (B : Block) :
    KeyHeld st s B ↔ st.pcs.any (fun d => d.slot == s && d.target == B) = true := by
  rw [KeyHeld_def, List.any_eq_true]
  simp only [Bool.and_eq_true, beq_iff_eq]

/-- A held key stays held when the PCs only grow. -/
theorem pcsa_keyHeld_mono {st st' : State n} (h : st.pcs ⊆ st'.pcs) {s : Slot} {B : Block}
    (hk : KeyHeld st s B) : KeyHeld st' s B := by
  rw [KeyHeld_def] at hk ⊢
  obtain ⟨c', hc, h1, h2⟩ := hk
  exact ⟨c', h hc, h1, h2⟩

/-- The parts of the structural check of a PC. -/
theorem pcsa_pc_wellFormed_parts (c : PC n) (h : c.wellFormed = true) :
    0 < c.slot ∧ c.target ≠ .genesis ∧ c.target.slot = c.slot ∧
      pcQuorum n ≤ c.acks.length ∧ c.seats.length = c.acks.length ∧
      ∀ a ∈ c.acks, ∃ i, a.decode? = some (c.slot, i, c.target.root) := by
  obtain ⟨h12345, h6⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h1234, h5⟩ := Bool.and_eq_true_iff.mp h12345
  obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp h1234
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  refine ⟨of_decide_eq_true h1, bne_iff_ne.mp h2, beq_iff_eq.mp h3, of_decide_eq_true h4,
    beq_iff_eq.mp h5, fun a ha => ?_⟩
  have hd := List.all_eq_true.mp h6 a ha
  revert hd
  cases a.decode? with
  | none => intro hd; cases hd
  | some v =>
    rcases v with ⟨s', i, r⟩
    intro hd
    have hd' : (s' == c.slot && r == c.target.root) = true := hd
    obtain ⟨hs, hr⟩ := Bool.and_eq_true_iff.mp hd'
    rw [beq_iff_eq.mp hs, beq_iff_eq.mp hr]
    exact ⟨i, rfl⟩

/-- The structural check of a PC from its parts. -/
theorem pcsa_pc_wellFormed_of (c : PC n) (h1 : 0 < c.slot) (h2 : c.target ≠ .genesis)
    (h3 : c.target.slot = c.slot) (h4 : pcQuorum n ≤ c.acks.length)
    (h5 : c.seats.length = c.acks.length)
    (h6 : ∀ a ∈ c.acks, ∃ i, a.decode? = some (c.slot, i, c.target.root)) :
    c.wellFormed = true := by
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true h1, bne_iff_ne.mpr h2⟩,
      beq_iff_eq.mpr h3⟩, decide_eq_true h4⟩, beq_iff_eq.mpr h5⟩,
    List.all_eq_true.mpr (fun a ha => ?_)⟩
  obtain ⟨i, hi⟩ := h6 a ha
  rw [hi]
  exact Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _, beq_self_eq_true _⟩

/-! ### Seat selection -/

/-- One step of seat selection. -/
theorem pcsa_firstPerSeat_cons (acc : List (AckWire n)) (a : AckWire n) (as : List (AckWire n)) :
    as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
      else acc ++ [a]) (if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a]) =
    (a :: as).foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
      else acc ++ [a]) acc := rfl

/-- Seat selection keeps pairwise distinct seats. -/
theorem pcsa_firstPerSeat_pairwise (as : List (AckWire n)) :
    (firstPerSeat as).Pairwise (fun x y => x.seat? ≠ y.seat?) := by
  delta firstPerSeat
  apply List.foldlRecOn (motive := fun acc : List (AckWire n) =>
    acc.Pairwise (fun x y => x.seat? ≠ y.seat?))
  · exact List.Pairwise.nil
  · intro acc ha a _
    split
    · exact ha
    · rename_i hn
      refine List.pairwise_append.mpr ⟨ha, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton.mp hy]
      intro he
      apply hn
      exact List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr he⟩

/-- Seat selection keeps an ack of every seat of its input. -/
theorem pcsa_firstPerSeat_seat (as : List (AckWire n)) (a : AckWire n) (ha : a ∈ as) :
    ∃ b ∈ firstPerSeat as, b.seat? = a.seat? := by
  delta firstPerSeat
  suffices h : ∀ (as : List (AckWire n)) (acc : List (AckWire n)),
      (∀ a ∈ as, ∃ b ∈ as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?)
        then acc else acc ++ [a]) acc, b.seat? = a.seat?) ∧
      (∀ x ∈ acc, ∃ b ∈ as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?)
        then acc else acc ++ [a]) acc, b.seat? = x.seat?) from (h as []).1 a ha
  intro as
  induction as with
  | nil => exact fun acc => ⟨fun a ha => absurd ha (List.not_mem_nil), fun x hx => ⟨x, hx, rfl⟩⟩
  | cons a as ih =>
    intro acc
    rw [← pcsa_firstPerSeat_cons]
    obtain ⟨h1, h2⟩ := ih (if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a])
    have hacc : ∀ x ∈ acc, x ∈ (if acc.any (fun old => old.seat? == a.seat?) then acc
        else acc ++ [a]) := by
      intro x hx
      split
      · exact hx
      · exact List.mem_append_left _ hx
    refine ⟨fun b hb => ?_, fun x hx => h2 x (hacc x hx)⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · by_cases hany : acc.any (fun old => old.seat? == b.seat?) = true
      · obtain ⟨old, ho, he⟩ := List.any_eq_true.mp hany
        obtain ⟨c, hc, hce⟩ := h2 old (hacc old ho)
        exact ⟨c, hc, hce.trans (beq_iff_eq.mp he)⟩
      · refine h2 b ?_
        simp only [hany, Bool.false_eq_true, ↓reduceIte]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact h1 b hb

/-- The seat count of a list with distinct decoded seats is its length. -/
theorem pcsa_distinct_seats_length (as : List (AckWire n))
    (hd : ∀ a ∈ as, (a.seat?).isSome)
    (hp : as.Pairwise (fun x y => x.seat? ≠ y.seat?)) :
    (as.filterMap AckWire.seat?).dedup = as.filterMap AckWire.seat? ∧
      (as.filterMap AckWire.seat?).length = as.length := by
  induction as with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hd a (List.mem_cons_self ..))
    obtain ⟨h1, h2⟩ := ih (fun b hb => hd b (List.mem_cons_of_mem _ hb))
      (List.Pairwise.of_cons hp)
    have hnot : i ∉ as.filterMap AckWire.seat? := by
      intro hm
      obtain ⟨b, hb, hbe⟩ := List.mem_filterMap.mp hm
      exact (List.rel_of_pairwise_cons hp hb) (hi.trans hbe.symm)
    rw [List.filterMap_cons, hi]
    refine ⟨?_, ?_⟩
    · rw [List.dedup_cons_of_notMem hnot, h1]
    · rw [List.length_cons, List.length_cons, h2]

/-! ### Assembly -/

/-- Assembly reads only the ack pool, the tree and `Σ`. -/
theorem pcsa_assemblePC_congr {st st' : State n} (hp : st'.ackPool = st.ackPool)
    (hb : st'.base.blocks = st.base.blocks) (hf : st'.fg = st.fg) (s : Slot) (b : Block) :
    assemblePC st' s b = assemblePC st s b := by
  have ha : acksOn st' s b.root = acksOn st s b.root := by
    change st'.ackPool.filter _ = st.ackPool.filter _
    rw [hp]
  have hv : ∀ c : PC n, pcValid st' c = pcValid st c := by
    intro c
    change (c.wellFormed && decide (c.target ∈ st'.base.blocks) &&
        Block.compatible c.target (eraseFG st'.fg.F)) =
      (c.wellFormed && decide (c.target ∈ st.base.blocks) &&
        Block.compatible c.target (eraseFG st.fg.F))
    rw [hb, hf]
  change (if pcValid st' (⟨s, b, firstPerSeat (acksOn st' s b.root)⟩ : PC n) = true then
      some (⟨s, b, firstPerSeat (acksOn st' s b.root)⟩ : PC n) else none) =
    (if pcValid st (⟨s, b, firstPerSeat (acksOn st s b.root)⟩ : PC n) = true then
      some (⟨s, b, firstPerSeat (acksOn st s b.root)⟩ : PC n) else none)
  rw [ha, hv]

/-- [pcsa34-r4.3 §3.6] The store assembles the key of a well-formed PC `C`
whose acks are pooled and whose target is stored and compatible with `F`:
seat selection keeps one ack per seat of `C`. -/
theorem pcsa_assemblePC_of_pool (st : State n) (C : PC n) (hwf : C.wellFormed = true)
    (hpool : ∀ a ∈ C.acks, a ∈ st.ackPool) (hB : C.target ∈ st.base.blocks)
    (hF : activeCompatible st C.target = true) :
    ∃ c', assemblePC st C.slot C.target = some c' := by
  obtain ⟨hs0, hgen, hsl, hq, hseats, hdecC⟩ := pcsa_pc_wellFormed_parts C hwf
  refine ⟨⟨C.slot, C.target, firstPerSeat (acksOn st C.slot C.target.root)⟩,
    (assemblePC_some_iff st C.slot C.target _).mpr ⟨rfl, ?_⟩⟩
  set L := acksOn st C.slot C.target.root with hL
  have hCL : ∀ a ∈ C.acks, a ∈ L := by
    intro a ha
    obtain ⟨i, hi⟩ := hdecC a ha
    exact (mem_acksOn_iff st _ _ a).mpr ⟨hpool a ha, i, hi⟩
  have hFL : ∀ b ∈ firstPerSeat L, ∃ i, b.decode? = some (C.slot, i, C.target.root) :=
    fun b hb => ((mem_acksOn_iff st _ _ b).mp (pcsa_firstPerSeat_subset L hb)).2
  have hsome : ∀ b ∈ firstPerSeat L, (b.seat?).isSome := by
    intro b hb
    obtain ⟨i, hi⟩ := hFL b hb
    change ((b.decode?).map (fun x => x.2.1)).isSome = true
    rw [hi]
    rfl
  obtain ⟨hdd, hlen⟩ := pcsa_distinct_seats_length (firstPerSeat L) hsome
    (pcsa_firstPerSeat_pairwise L)
  -- the seat count
  have hcount : C.acks.length ≤ (firstPerSeat L).length := by
    have h1 : C.acks.length = (C.acks.filterMap AckWire.seat?).toFinset.card := by
      rw [← hseats]
      exact pcsa_pc_seats_card C
    have h2 : (C.acks.filterMap AckWire.seat?).toFinset ⊆
        ((firstPerSeat L).filterMap AckWire.seat?).toFinset := by
      intro i hi
      rw [pcsa_ack_count_witness] at hi ⊢
      obtain ⟨a, ha, hai⟩ := hi
      obtain ⟨b, hb, hbe⟩ := pcsa_firstPerSeat_seat L a (hCL a ha)
      exact ⟨b, hb, hbe.trans hai⟩
    have h3 := Finset.card_le_card h2
    have h4 := List.toFinset_card_le ((firstPerSeat L).filterMap AckWire.seat?)
    omega
  change (PC.wellFormed ⟨C.slot, C.target, firstPerSeat L⟩ &&
    decide (C.target ∈ st.base.blocks) && activeCompatible st C.target) = true
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨pcsa_pc_wellFormed_of _ hs0 hgen
    hsl (by change pcQuorum n ≤ (firstPerSeat L).length; omega) ?_ hFL,
    decide_eq_true hB⟩, hF⟩
  change (((firstPerSeat L).filterMap AckWire.seat?).dedup).length = _
  rw [hdd, hlen]

/-- An assemblable key is a collection candidate of the pool. -/
theorem pcsa_assemble_candidate (hn : 0 < n) (st : State n) (s : Slot) (b : Block) (c : PC n)
    (h : assemblePC st s b = some c) :
    (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups := by
  obtain ⟨rfl, hv⟩ := (assemblePC_some_iff st s b c).mp h
  have hwf : PC.wellFormed (⟨s, b, firstPerSeat (acksOn st s b.root)⟩ : PC n) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  have hq := (pcsa_pc_wellFormed_parts _ hwf).2.2.2.1
  have hq0 : 0 < pcQuorum n := by
    change 0 < (n + 1) / 2
    omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (lt_of_lt_of_le hq0 hq)
  obtain ⟨hp, i, hi⟩ := (mem_acksOn_iff st s b.root a).mp (pcsa_firstPerSeat_subset _ ha)
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.mpr ⟨a, hp, by rw [hi]; rfl⟩

/-! ### Closure -/

/-- Stored roots name one block. -/
def RootsUnique (st : State n) : Prop :=
  ∀ b ∈ st.base.blocks, ∀ b' ∈ st.base.blocks, b.root = b'.root → b = b'

theorem RootsUnique_def (st : State n) : RootsUnique st =
    ∀ b ∈ st.base.blocks, ∀ b' ∈ st.base.blocks, b.root = b'.root → b = b' := by
  delta RootsUnique
  rfl

/-- [pcsa34-r4.3 §3.6] Collection closure: every key that the store can
assemble on a stored target is held. -/
def CollectClosed (st : State n) : Prop :=
  ∀ (s : Slot) (b : Block) (c : PC n), b ∈ st.base.blocks → assemblePC st s b = some c →
    KeyHeld st s b

theorem CollectClosed_def (st : State n) : CollectClosed st =
    ∀ (s : Slot) (b : Block) (c : PC n), b ∈ st.base.blocks → assemblePC st s b = some c →
      KeyHeld st s b := by
  delta CollectClosed
  rfl

/-- Closure transfers to a store with the same pool, tree, `Σ` and held PCs. -/
theorem pcsa_collectClosed_frame {st st' : State n} (hc : st'.pcs = st.pcs)
    (hp : st'.ackPool = st.ackPool) (hb : st'.base.blocks = st.base.blocks)
    (hf : st'.fg = st.fg) (h : CollectClosed st) : CollectClosed st' := by
  rw [CollectClosed_def] at h ⊢
  intro s b c hbm ha
  rw [hb] at hbm
  rw [pcsa_assemblePC_congr hp hb hf] at ha
  have hk := h s b c hbm ha
  rw [KeyHeld_def] at hk ⊢
  rw [hc]
  exact hk

/-- [pcsa34-r4.3 §3.6] After collection every assemblable key on a stored
target is held, when stored roots name one block. -/
theorem pcsa_collectClosed_collectPCs (hn : 0 < n) (st : State n) (hu : RootsUnique st) :
    CollectClosed (collectPCs st) := by
  rw [CollectClosed_def]
  intro s B c hB hc
  obtain ⟨-, f2, f3, -, f5⟩ := collectPCs_frame st
  rw [f2] at hB
  rw [pcsa_assemblePC_congr f3 f2 f5] at hc
  have hkey := pcsa_assemble_candidate hn st s B c hc
  rw [RootsUnique_def] at hu
  delta collectPCs
  generalize (st.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups = cs at hkey
  suffices h : ∀ (cs : List (Slot × BlockId)) (acc : State n), acc.ackPool = st.ackPool →
      acc.base.blocks = st.base.blocks → acc.fg = st.fg →
      (KeyHeld acc s B ∨ (s, B.root) ∈ cs) →
      KeyHeld (cs.foldl (fun acc sr =>
        match acc.base.blocks.find? (fun b => b.root == sr.2) with
        | none => acc
        | some b =>
          match assemblePC acc sr.1 b with
          | none => acc
          | some c => installPC acc c) acc) s B from
    h cs st rfl rfl rfl (Or.inr hkey)
  intro cs
  induction cs with
  | nil =>
    intro acc _ _ _ hk
    rcases hk with hk | hk
    · exact hk
    · exact absurd hk (List.not_mem_nil)
  | cons sr cs ih =>
    intro acc hp hb hf hk
    rw [List.foldl_cons]
    have hframe : ∀ c, (installPC acc c).ackPool = st.ackPool ∧
        (installPC acc c).base.blocks = st.base.blocks ∧ (installPC acc c).fg = st.fg := by
      intro c
      obtain ⟨-, f2, f3, -, f5⟩ := installPC_frame acc c
      exact ⟨f3.trans hp, f2.trans hb, f5.trans hf⟩
    by_cases hka : KeyHeld acc s B
    · cases hfind : acc.base.blocks.find? (fun b => b.root == sr.2) with
      | none => exact ih acc hp hb hf (Or.inl hka)
      | some b =>
        dsimp only
        cases hc : assemblePC acc sr.1 b with
        | none => exact ih acc hp hb hf (Or.inl hka)
        | some c =>
          obtain ⟨g1, g2, g3⟩ := hframe c
          exact ih _ g1 g2 g3 (Or.inl (pcsa_keyHeld_mono (installPC_pcs_mono acc c) hka))
    · have hk' : sr = (s, B.root) ∨ (s, B.root) ∈ cs := by
        rcases hk with hk | hk
        · exact absurd hk hka
        · rcases List.mem_cons.mp hk with h | h
          · exact Or.inl h.symm
          · exact Or.inr h
      rcases hk' with rfl | hk'
      · -- the key step installs the key
        have hfind : acc.base.blocks.find? (fun b => b.root == B.root) = some B := by
          cases hf' : acc.base.blocks.find? (fun b => b.root == B.root) with
          | none =>
            exfalso
            have := List.find?_eq_none.mp hf' B (hb ▸ hB)
            simp at this
          | some b =>
            have hbm := List.mem_of_find?_eq_some hf'
            have hbr := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hf').1
            rw [hu b (hb ▸ hbm) B hB hbr]
        dsimp only
        rw [hfind]
        dsimp only
        rw [pcsa_assemblePC_congr hp hb hf, hc]
        dsimp only
        obtain ⟨g1, g2, g3⟩ := hframe c
        refine ih _ g1 g2 g3 (Or.inl ?_)
        obtain ⟨rfl, -⟩ := (assemblePC_some_iff st s B c).mp hc
        have hfalse : acc.pcs.any (fun o => o.slot == s && o.target == B) = false := by
          cases h : acc.pcs.any (fun o => o.slot == s && o.target == B)
          · rfl
          · exact absurd ((pcsa_keyHeld_iff_any acc s B).mpr h) hka
        rw [KeyHeld_def, installPC_pcs_new acc _ hfalse]
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
      · cases hfind : acc.base.blocks.find? (fun b => b.root == sr.2) with
        | none => exact ih acc hp hb hf (Or.inr hk')
        | some b =>
          dsimp only
          cases hc : assemblePC acc sr.1 b with
          | none => exact ih acc hp hb hf (Or.inr hk')
          | some c =>
            obtain ⟨g1, g2, g3⟩ := hframe c
            exact ih _ g1 g2 g3 (Or.inr hk')

/-- [pcsa34-r4.3 §3.6] A closed store holds the key of a well-formed PC
whose acks are pooled and whose target is stored and compatible with `F`. -/
theorem pcsa_keyHeld_of_collectClosed (st : State n) (h : CollectClosed st) (C : PC n)
    (hwf : C.wellFormed = true) (hpool : ∀ a ∈ C.acks, a ∈ st.ackPool)
    (hB : C.target ∈ st.base.blocks) (hF : activeCompatible st C.target = true) :
    KeyHeld st C.slot C.target := by
  obtain ⟨c', hc'⟩ := pcsa_assemblePC_of_pool st C hwf hpool hB hF
  exact (CollectClosed_def st ▸ h) C.slot C.target c' hB hc'

/-! ### New keys -/

/-- A new PC of collection is assembled at the collection input. -/
theorem pcsa_mem_collectPCs (X : State n) (d : PC n) (hd : d ∈ (collectPCs X).pcs) :
    d ∈ X.pcs ∨ (d.target ∈ X.base.blocks ∧ assemblePC X d.slot d.target = some d) := by
  revert hd
  delta collectPCs
  generalize (X.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups = cs
  suffices h : ∀ (cs : List (Slot × BlockId)) (acc : State n), acc.ackPool = X.ackPool →
      acc.base.blocks = X.base.blocks → acc.fg = X.fg →
      (∀ d ∈ acc.pcs, d ∈ X.pcs ∨
        (d.target ∈ X.base.blocks ∧ assemblePC X d.slot d.target = some d)) →
      ∀ d ∈ (cs.foldl (fun acc sr =>
        match acc.base.blocks.find? (fun b => b.root == sr.2) with
        | none => acc
        | some b =>
          match assemblePC acc sr.1 b with
          | none => acc
          | some c => installPC acc c) acc).pcs,
        d ∈ X.pcs ∨ (d.target ∈ X.base.blocks ∧ assemblePC X d.slot d.target = some d) from
    h cs X rfl rfl rfl (fun d hd => Or.inl hd) d
  intro cs
  induction cs with
  | nil => intro acc _ _ _ hacc; exact hacc
  | cons sr cs ih =>
    intro acc hp hb hf hacc
    rw [List.foldl_cons]
    cases hfind : acc.base.blocks.find? (fun b => b.root == sr.2) with
    | none => exact ih acc hp hb hf hacc
    | some b =>
      dsimp only
      cases hc : assemblePC acc sr.1 b with
      | none => exact ih acc hp hb hf hacc
      | some c =>
        obtain ⟨-, f2, f3, -, f5⟩ := installPC_frame acc c
        refine ih _ (f3.trans hp) (f2.trans hb) (f5.trans hf) ?_
        intro d hd
        rcases mem_installPC_pcs acc c d hd with hd | rfl
        · exact hacc d hd
        · right
          obtain ⟨rfl, -⟩ := (assemblePC_some_iff acc sr.1 b _).mp hc
          refine ⟨by rw [← hb]; exact List.mem_of_find?_eq_some hfind, ?_⟩
          exact (pcsa_assemblePC_congr hp hb hf sr.1 b).symm.trans hc

/-- Assembly from its parts. -/
theorem pcsa_assemblePC_of_parts (st : State n) (s : Slot) (b : Block) (L : List (AckWire n))
    (hL : acksOn st s b.root = L) (hwf : PC.wellFormed (⟨s, b, firstPerSeat L⟩ : PC n) = true)
    (hb : b ∈ st.base.blocks) (hF : activeCompatible st b = true) :
    assemblePC st s b = some ⟨s, b, firstPerSeat L⟩ := by
  subst hL
  refine (assemblePC_some_iff st s b _).mpr ⟨rfl, ?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hwf, decide_eq_true hb⟩, hF⟩

/-- The pooled acks of a key after appending acks. -/
theorem pcsa_acksOn_append {st st' : State n} {extra : List (AckWire n)}
    (hpool : st'.ackPool = st.ackPool ++ extra) (s : Slot) (r : BlockId) :
    acksOn st' s r = acksOn st s r ++ extra.filter (fun a => match a.decode? with
      | some (s', _, r') => s' == s && r' == r
      | none => false) := by
  change st'.ackPool.filter _ = st.ackPool.filter _ ++ _
  rw [hpool, List.filter_append]
  rfl

/-- [pcsa34-r4.3 §3.6] A key that a closed store does not hold and that a store
with more acks (same target, `F`-compatible) assembles needs a new ack of the
key. -/
theorem pcsa_new_key_ack {st X : State n} {extra : List (AckWire n)}
    (hpool : X.ackPool = st.ackPool ++ extra) (hcl : CollectClosed st) {s : Slot} {b : Block}
    {C : PC n} (hasm : assemblePC X s b = some C) (hb : b ∈ st.base.blocks)
    (hF : activeCompatible st b = true) (hk : ¬ KeyHeld st s b) :
    ∃ a ∈ extra, ∃ i, a.decode? = some (s, i, b.root) := by
  obtain ⟨rfl, hv⟩ := (assemblePC_some_iff X s b C).mp hasm
  have hwf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  by_contra hno
  have hnil : extra.filter (fun a => match a.decode? with
      | some (s', _, r') => s' == s && r' == b.root
      | none => false) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hm
    revert hm
    cases hd : a.decode? with
    | none => intro hm; cases hm
    | some v =>
      rcases v with ⟨s', i, r'⟩
      intro hm
      have hm' : (s' == s && r' == b.root) = true := hm
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hm'
      rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2] at hd
      exact hno ⟨a, ha, i, hd⟩
  have heq : acksOn X s b.root = acksOn st s b.root := by
    rw [pcsa_acksOn_append hpool, hnil, List.append_nil]
  rw [heq] at hwf
  have hst := pcsa_assemblePC_of_parts st s b _ rfl hwf hb hF
  exact hk ((CollectClosed_def st ▸ hcl) s b _ hb hst)

/-- Seat selection over one more ack. -/
theorem pcsa_firstPerSeat_append (L : List (AckWire n)) (a : AckWire n) :
    firstPerSeat (L ++ [a]) = if (firstPerSeat L).any (fun old => old.seat? == a.seat?) then
      firstPerSeat L else firstPerSeat L ++ [a] := by
  delta firstPerSeat
  rw [List.foldl_append]
  rfl

/-- [pcsa34-r4.3 §3.6] A key that a closed store does not hold and that the
store with one more ack assembles contains that ack. -/
theorem pcsa_new_key_single {st X : State n} {a : AckWire n}
    (hpool : X.ackPool = st.ackPool ++ [a]) (hcl : CollectClosed st) {s : Slot} {b : Block}
    {C : PC n} (hasm : assemblePC X s b = some C) (hb : b ∈ st.base.blocks)
    (hF : activeCompatible st b = true) (hk : ¬ KeyHeld st s b) : a ∈ C.acks := by
  obtain ⟨a', ha', i, hd⟩ := pcsa_new_key_ack hpool hcl hasm hb hF hk
  rw [List.mem_singleton] at ha'
  subst a'
  obtain ⟨rfl, hv⟩ := (assemblePC_some_iff X s b C).mp hasm
  have hwf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  have hfa : [a].filter (fun a => match a.decode? with
      | some (s', _, r') => s' == s && r' == b.root
      | none => false) = [a] := by
    rw [List.filter_singleton]
    have hm : (match a.decode? with
        | some (s', _, r') => s' == s && r' == b.root
        | none => false) = true := by
      rw [hd]
      exact Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _, beq_self_eq_true _⟩
    rw [hm]
    rfl
  have heq : acksOn X s b.root = acksOn st s b.root ++ [a] := by
    rw [pcsa_acksOn_append hpool, hfa]
  change a ∈ firstPerSeat (acksOn X s b.root)
  rw [heq] at hwf ⊢
  rw [pcsa_firstPerSeat_append] at hwf ⊢
  by_cases hany : (firstPerSeat (acksOn st s b.root)).any
      (fun old => old.seat? == a.seat?) = true
  · exfalso
    simp only [hany, ↓reduceIte] at hwf
    have hst := pcsa_assemblePC_of_parts st s b _ rfl hwf hb hF
    exact hk ((CollectClosed_def st ▸ hcl) s b _ hb hst)
  · simp only [hany, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end AvailableChain.PCSA
end
