module
public import AvailableChainPCSAProofs.Proofs.Clean.PCPool
public import AvailableChainPCSAProofs.Proofs.Clean.TargetCollect

public section

/-! C6 RelayCollect: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.PCSA.CleanPCPool
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


end AvailableChain.PCSA.CleanPCRelay

namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.PCSA.CleanPCPool
variable {n : Nat}
/-- Saturation gives complete assembly when every held target has an exact root lookup. -/
theorem pcsa_saturated_collectClosed (st : State n) (hn : 0 < n) (h : PCSaturated st)
    (hlookup : ∀ B ∈ st.base.blocks, st.base.blocks.find? (fun b => b.root == B.root) = some B) :
    CollectClosed st := by
  intro s B C hB hC
  obtain ⟨rfl, hv⟩ := (assemblePC_some_iff st s B C).mp hC
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  have hq := (pcsa_pc_wellFormed_parts _ hw).2.2.2.1
  have hq0 : 0 < pcQuorum n := by
    change 0 < (n + 1) / 2
    omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (lt_of_lt_of_le hq0 hq)
  obtain ⟨hm, i, hd⟩ := (mem_acksOn_iff st s B.root a).mp
    (pcsa_firstPerSeat_subset _ ha)
  rw [PCSaturated_def] at h
  exact h a hm s i B.root hd B (hlookup B hB) _ hC
end AvailableChain.PCSA.CleanPCRelay

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every honest run store is complete for exact-target PC assembly. -/
theorem pcsa_clean_collectClosed (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) :
    CleanPCRelay.CollectClosed (V2.D.Run.stateBefore E rho k x).st := by
  exact CleanPCRelay.pcsa_saturated_collectClosed _ p.nPos (pcsa_saturated_stateBefore E rho k x)
    (fun B hB => pcsa_lookup_held_target E rho h k x hx B hB)
end AvailableChain.PCSA.Run

end
