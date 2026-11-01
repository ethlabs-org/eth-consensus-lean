module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayFrames
public import AvailableChainPCSAProofs.Proofs.Clean.RelayCollect

public section

/-! C6 RelayStore: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.SimplexFG
variable {n : Nat}

/-- Checked ack pooling appends at most the ack. -/
theorem pcsa_poolAck_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).ackPool = st.ackPool ∨ (poolAck p st a).ackPool = st.ackPool ++ [a] := by
  delta poolAck
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · rename_i v
    rcases v with ⟨_, _, _⟩
    dsimp only
    split_ifs
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

/-- A raw ack batch appends acks of the batch. -/
theorem pcsa_fold_poolAckRaw_extra (st : State n) (as : List (AckWire n)) :
    ∃ extra, (as.foldl poolAckRaw st).ackPool = st.ackPool ++ extra ∧ ∀ a ∈ extra, a ∈ as := by
  induction as generalizing st with
  | nil => exact ⟨[], (List.append_nil _).symm, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    obtain ⟨extra, he, hm⟩ := ih (poolAckRaw st a)
    have h1 : (poolAckRaw st a).ackPool = st.ackPool ∨
        (poolAckRaw st a).ackPool = st.ackPool ++ [a] := by
      delta poolAckRaw
      cases hdecode : a.decode? <;> dsimp only
      rotate_left
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl rfl
    rcases h1 with h1 | h1
    · exact ⟨extra, by rw [he, h1], fun b hb => List.mem_cons_of_mem _ (hm b hb)⟩
    · refine ⟨a :: extra, by rw [he, h1, List.append_assoc]; rfl, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hm b hb)

/-- [pcsa34-r4.3 §3.6] Stage 1: a key that a closed store does not hold and
that collection after a raw ack batch installs is on a new block `B0` or has
a batch ack. -/
theorem pcsa_collect_new_key (st Y : State n) (acks : List (AckWire n)) (B0 : Block)
    (hY1 : Y.pcs ⊆ st.pcs) (hY2 : Y.ackPool = st.ackPool)
    (hY3 : ∀ x ∈ Y.base.blocks, x ∈ st.base.blocks ∨ x = B0)
    (hcl : CollectClosed st) (hF : st.fg.F = .genesis) (C : PC n)
    (hC : C ∈ (collectPCs (acks.foldl poolAckRaw Y)).pcs)
    (hk : ¬ KeyHeld st C.slot C.target) :
    (C.target ∈ Y.base.blocks ∧ C.target ∉ st.base.blocks ∧ C.target = B0 ∧
      C.slot = B0.slot) ∨
      ∃ a ∈ acks, ∃ i, a.decode? = some (C.slot, i, C.target.root) := by
  obtain ⟨f1, -, -, -, f5, -, -⟩ := pcsa_fold_poolAckRaw_frame Y acks
  rcases pcsa_mem_collectPCs _ C hC with hm | ⟨hb, hasm⟩
  · rw [f1] at hm
    exact absurd ((KeyHeld_def _ _ _).mpr ⟨C, hY1 hm, rfl, rfl⟩) hk
  · rw [f5] at hb
    by_cases hbs : C.target ∈ st.base.blocks
    · right
      obtain ⟨extra, he, hx⟩ := pcsa_fold_poolAckRaw_extra Y acks
      rw [hY2] at he
      obtain ⟨a, ha, i, hi⟩ := pcsa_new_key_ack he hcl hasm hbs
        (pcsa_activeCompatible_genesis st hF _) hk
      exact ⟨a, hx a ha, i, hi⟩
    · left
      have hB0 := (hY3 _ hb).resolve_left hbs
      obtain ⟨hc, hv⟩ := (assemblePC_some_iff _ C.slot C.target C).mp hasm
      have hwf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
      refine ⟨hb, hbs, hB0, ?_⟩
      rw [← hB0]
      exact ((pcsa_pc_wellFormed_parts C hwf).2.2.1).symm

/-- [pcsa34-r4.3 §3.6] Stage 1: a key that a closed store does not hold and
that an ack call installs contains the ack. -/
theorem pcsa_ack_new_key (p : Params) (st : State p.n) (a : AckWire p.n)
    (hcl : CollectClosed st) (hF : st.fg.F = .genesis) (C : PC p.n)
    (hC : C ∈ (collectPCs (poolAck p st a)).pcs) (hk : ¬ KeyHeld st C.slot C.target) :
    a ∈ C.acks := by
  obtain ⟨g1, -, -, -, g5⟩ := pcsa_poolAck_frame p st a
  rcases pcsa_mem_collectPCs _ C hC with hm | ⟨hb, hasm⟩
  · rw [g1] at hm
    exact absurd ((KeyHeld_def _ _ _).mpr ⟨C, hm, rfl, rfl⟩) hk
  · rw [g5] at hb
    have hFb := pcsa_activeCompatible_genesis st hF C.target
    rcases pcsa_poolAck_pool p st a with hp | hp
    · obtain ⟨b, hb', -⟩ := pcsa_new_key_ack (extra := []) (by rw [hp, List.append_nil]) hcl
        hasm hb hFb hk
      exact absurd hb' List.not_mem_nil
    · exact pcsa_new_key_single hp hcl hasm hb hFb hk

/-- [pcsa34-r4.3 §3.6] Stage 1: the new keys of the block admission tail are on
the new block or have an ack of the carried PC. -/
theorem pcsa_admitBlock_new_key (p : Params) (st st1 : State p.n) (Cnd : Prop) [Decidable Cnd]
    (rows : List (RowWire p.n)) (acks : List (AckWire p.n)) (B0 : Block)
    (h1 : st1.pcs ⊆ st.pcs) (h2 : st1.ackPool = st.ackPool)
    (h3 : ∀ x ∈ st1.base.blocks, x ∈ st.base.blocks ∨ x = B0)
    (hcl : CollectClosed st) (hF : st.fg.F = .genesis) (C : PC p.n)
    (hC : C ∈ (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if Cnd then st1 else reconcile st1)))).pcs)
    (hk : ¬ KeyHeld st C.slot C.target) :
    (C.target ∉ st.base.blocks ∧ C.target = B0 ∧ C.slot = B0.slot) ∨
      ∃ a ∈ acks, ∃ i, a.decode? = some (C.slot, i, C.target.root) := by
  rw [(pcsa_fold_admitRow_frame p _ rows).1] at hC
  obtain ⟨r1, -, r3, -, -, r6⟩ := pcsa_reconcile_frame st1
  have hY1 : (if Cnd then st1 else reconcile st1).pcs ⊆ st.pcs := by
    split
    · exact h1
    · rw [r1]
      exact fun x hx => h1 (List.mem_of_mem_filter hx)
  have hY3 : ∀ x ∈ (if Cnd then st1 else reconcile st1).base.blocks,
      x ∈ st.base.blocks ∨ x = B0 := by
    split
    · exact h3
    · rw [r6]
      exact h3
  have hY2 : (if Cnd then st1 else reconcile st1).ackPool = st.ackPool := by
    split
    · exact h2
    · rw [r3]
      exact h2
  rcases pcsa_collect_new_key st _ acks B0 hY1 hY2 hY3 hcl hF C hC hk with ⟨-, hn, hB, hs⟩ | hr
  · exact Or.inl ⟨hn, hB, hs⟩
  · exact Or.inr hr

/-! ### The ack pool grows -/

/-- The admission tail keeps the ack pool of its collection input. -/
theorem pcsa_tail_pool (p : Params) (X : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) (collectPCs X)).ackPool = X.ackPool :=
  (pcsa_fold_admitRow_frame p (collectPCs X) rows).2.2.1.trans (collectPCs_frame X).2.2.1

/-- Reconciliation keeps the ack pool. -/
theorem pcsa_ite_reconcile_pool (P : Prop) [Decidable P] (X : State n) :
    (if P then X else reconcile X).ackPool = X.ackPool := by
  split
  · rfl
  · exact (pcsa_reconcile_frame X).2.2.1

/-- A delivery keeps every pooled ack. -/
theorem pcsa_process_pool_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.ackPool ⊆ (process p st o).ackPool := by
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body =>
      dsimp only
      rw [(pcsa_admitRow_frame p st _).2.2.1]
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact List.Subset.refl _
      · cases hP : parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          dsimp only
          split
          · rw [pcsa_tail_pool]
            refine List.Subset.trans ?_ (pcsa_fold_poolAckRaw_frame _ N.pcAcks).2.2.2.2.2.1
            rw [pcsa_ite_reconcile_pool]
            cases N.pc <;> dsimp only <;> (try split_ifs) <;>
              (try simp only [deleteConflictingLeases_def])
            all_goals exact List.Subset.refl _
          · exact List.Subset.refl _
    | ack s i r =>
      dsimp only
      delta admitAck
      rw [(collectPCs_frame _).2.2.1]
      exact poolAck_mono p st _
    | pc d =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.1]
        exact (pcsa_fold_poolAckRaw_frame st d.acks).2.2.2.2.2.1
      · exact List.Subset.refl _
  | none => exact List.Subset.refl _

/-- A received well-formed PC pools its acks. -/
theorem pcsa_admitPC_pool (st : State n) (C : PC n) (hwf : C.wellFormed = true) :
    ∀ a ∈ C.acks, a ∈ (admitPC st C).ackPool := by
  intro a ha
  delta admitPC
  rw [show (if C.wellFormed then collectPCs (C.acks.foldl poolAckRaw st) else st) =
    collectPCs (C.acks.foldl poolAckRaw st) by simp only [hwf, ↓reduceIte],
    (collectPCs_frame _).2.2.1]
  refine (pcsa_fold_poolAckRaw_frame st C.acks).2.2.2.2.2.2 a ha ?_
  obtain ⟨i, hi⟩ := (pcsa_pc_wellFormed_parts C hwf).2.2.2.2.2 a ha
  rw [hi]
  rfl

end AvailableChain.PCSA.CleanPCRelay

end
