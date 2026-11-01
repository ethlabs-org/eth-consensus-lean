module
public import AvailableChainPCSAProofs.Proofs.Shared.StageStore
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSAClaims.Statements.OutageItems

public section

/-! Store steps of the S case (pcsa34-r4.3 §5.5 steps 2–4). A delivery keeps
`S`, the saved results and the time, and only deletes locks that conflict
with a PC it uses; the pre-gate clock keeps `S` and deletes only expired
and released locks; a gate keeps `S ⪰ A` behind a live lock on `A` and
writes only locks below its result. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

variable {n : Nat}

/-! ### Deliveries -/

/-- The base fields of the S case. -/
structure SlowBase (st st' : State n) : Prop where
  stable : st'.base.stableRecord = st.base.stableRecord
  genuine : st'.base.genuine = st.base.genuine
  now : st'.base.now = st.base.now

theorem SlowBase.slow_refl (st : State n) : SlowBase st st := ⟨rfl, rfl, rfl⟩

theorem SlowBase.slow_trans {a b c : State n} (h₁ : SlowBase a b) (h₂ : SlowBase b c) :
    SlowBase a c :=
  ⟨h₂.stable.trans h₁.stable, h₂.genuine.trans h₁.genuine, h₂.now.trans h₁.now⟩

theorem SlowBase.of_base {st st' : State n} (h : st'.base = st.base) : SlowBase st st' :=
  ⟨by rw [h], by rw [h], by rw [h]⟩

/-- A lock row of `st` that is missing in `st'` conflicts with a PC of `U`. -/
def LockLoss (U : PC n → Prop) (st st' : State n) : Prop :=
  st'.base.obligations ⊆ st.base.obligations ∧
    ∀ row ∈ st.base.obligations, row ∉ st'.base.obligations →
      ∃ c, U c ∧ Block.compatible c.target row.1 = false

theorem LockLoss_def (U : PC n → Prop) (st st' : State n) : LockLoss U st st' =
    (st'.base.obligations ⊆ st.base.obligations ∧
      ∀ row ∈ st.base.obligations, row ∉ st'.base.obligations →
        ∃ c, U c ∧ Block.compatible c.target row.1 = false) := by
  delta LockLoss
  rfl

theorem LockLoss.loss_refl (U : PC n → Prop) (st : State n) : LockLoss U st st :=
  ⟨List.Subset.refl _, fun _ h h' => absurd h h'⟩

theorem LockLoss.of_eq {U : PC n → Prop} {st st' : State n}
    (h : st'.base.obligations = st.base.obligations) : LockLoss U st st' :=
  ⟨by rw [h], fun _ h₁ h₂ => absurd (h ▸ h₁) h₂⟩

theorem LockLoss.loss_trans {U : PC n → Prop} {a b c : State n} (h₁ : LockLoss U a b)
    (h₂ : LockLoss U b c) : LockLoss U a c := by
  refine ⟨List.Subset.trans h₂.1 h₁.1, fun row hr hn => ?_⟩
  by_cases hb : row ∈ b.base.obligations
  · exact h₂.2 row hb hn
  · exact h₁.2 row hr hb

theorem LockLoss.loss_mono {U U' : PC n → Prop} {st st' : State n} (h : LockLoss U st st')
    (hU : ∀ c, U c → U' c) : LockLoss U' st st' := by
  refine ⟨h.1, fun row hr hn => ?_⟩
  obtain ⟨c, hc, hx⟩ := h.2 row hr hn
  exact ⟨c, hU c hc, hx⟩

/-- PC installation deletes only locks that conflict with the installed PC. -/
theorem pcsa_installPC_slow (st : State n) (c : PC n) :
    SlowBase st (installPC st c) ∧
      LockLoss (fun d => d ∈ (installPC st c).pcs) st (installPC st c) := by
  rw [installPC_def]
  split
  · exact ⟨SlowBase.slow_refl _, LockLoss.loss_refl _ _⟩
  · rw [deleteConflictingLeases_def]
    refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro row hr
      exact (List.mem_filter.mp hr).1
    · intro row hr hn
      refine ⟨c, List.mem_append_right _ (List.mem_singleton_self c), ?_⟩
      by_contra hc
      apply hn
      refine List.mem_filter.mpr ⟨hr, ?_⟩
      have hc' : Block.compatible c.target row.1 = true := by
        cases h : Block.compatible c.target row.1
        · exact absurd h hc
        · rfl
      rw [hc']
      simp

/-- PC collection deletes only locks that conflict with a collected PC. -/
theorem pcsa_collectPCs_slow (st : State n) :
    SlowBase st (collectPCs st) ∧
      LockLoss (fun d => d ∈ (collectPCs st).pcs) st (collectPCs st) := by
  have key := collectPCs_invariant (n := n)
    (fun acc => SlowBase st acc ∧ LockLoss (fun d => d ∈ acc.pcs) st acc)
    (fun acc c h _ => by
      obtain ⟨h1, h2⟩ := pcsa_installPC_slow acc c
      exact ⟨h.1.slow_trans h1,
        (h.2.loss_mono (fun d hd => installPC_pcs_mono acc c hd)).loss_trans h2⟩)
    st ⟨SlowBase.slow_refl _, LockLoss.loss_refl _ _⟩
  exact key

/-- Raw ack pooling writes no base field and no PC. -/
theorem pcsa_fold_poolAckRaw_base (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base = st.base := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    exact (poolAckRaw_frame st a).2.2.1

/-- Vote admission keeps the S-case base fields and the locks. -/
theorem pcsa_admitVote_slow (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) :
    (GridCO.admitVote q v o).stableRecord = v.stableRecord ∧
      (GridCO.admitVote q v o).genuine = v.genuine ∧
      (GridCO.admitVote q v o).now = v.now ∧
      (GridCO.admitVote q v o).obligations = v.obligations := by
  delta GridCO.admitVote
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> dsimp only <;> (try split_ifs) <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The carried-vote fold keeps the S-case base fields and the locks. -/
theorem pcsa_foldVotes_slow (q : GridCO.Params) (raw : List (GridCO.HeadWire n .root))
    (w : GridCO.State n .root) :
    (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) w).stableRecord =
        w.stableRecord ∧
      (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) w).genuine =
        w.genuine ∧
      (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) w).now = w.now ∧
      (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) w).obligations =
        w.obligations := by
  induction raw generalizing w with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (GridCO.admitVote q w (GridCO.fromHead a))
    obtain ⟨g1, g2, g3, g4⟩ := pcsa_admitVote_slow q w (GridCO.fromHead a)
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

/-- Proposal admission keeps the S-case base fields and the locks. -/
theorem pcsa_admitProposal_slow (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q v o b raw).stableRecord = v.stableRecord ∧
      (GridCO.admitProposal q v o b raw).genuine = v.genuine ∧
      (GridCO.admitProposal q v o b raw).now = v.now ∧
      (GridCO.admitProposal q v o b raw).obligations = v.obligations := by
  delta GridCO.admitProposal
  dsimp only
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact pcsa_foldVotes_slow q raw _

/-- A PC a store uses: held, or carried by a stored proposal. -/
def UsedPC (st : State n) (c : PC n) : Prop := c ∈ st.pcs ∨ ∃ s, c ∈ carriedPCs st s

theorem UsedPC_def (st : State n) (c : PC n) :
    UsedPC st c = (c ∈ st.pcs ∨ ∃ s, c ∈ carriedPCs st s) := by
  delta UsedPC
  rfl

/-- The admission tail (carried acks, collection, carried rows) without
reconciliation keeps the S-case base fields and deletes only locks that
conflict with a collected PC. -/
theorem pcsa_admitBlock_tail_slow (p : Params) (st1 : State p.n) (rows : List (RowWire p.n))
    (acks : List (AckWire p.n)) :
    SlowBase st1 (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw st1))) ∧
      LockLoss (fun c => c ∈ (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
        st1))).pcs) st1 (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw st1))) ∧
      (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw st1))).base.blocks =
        st1.base.blocks ∧
      (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw st1))).proposals =
        st1.proposals ∧
      (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw st1))).fg = st1.fg := by
  obtain ⟨r1, -, -, r4, r5, r6⟩ := pcsa_fold_admitRow_frame p
    (collectPCs (acks.foldl poolAckRaw st1)) rows
  obtain ⟨c1, c2⟩ := pcsa_collectPCs_slow (acks.foldl poolAckRaw st1)
  obtain ⟨-, -, a3, a4, a5, -⟩ := pcsa_fold_poolAckRaw_frame st1 acks
  have hb : SlowBase st1 (acks.foldl poolAckRaw st1) := SlowBase.of_base a5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hb.slow_trans c1).slow_trans (SlowBase.of_base r6)
  · rw [r1]
    exact ((LockLoss.of_eq (by rw [a5])).loss_trans c2).loss_trans (LockLoss.of_eq (by rw [r6]))
  · rw [r6, (collectPCs_frame _).2.1, a5]
  · rw [r4, pcsa_collectPCs_proposals, a3]
  · rw [r5, (collectPCs_frame _).2.2.2.2, a4]

/-- The admission tail after the proposal and the carried-PC deletion: with
`F` genesis before and after, there is no reconciliation, and a carried PC
that deleted a lock is a carried PC of the result. -/
theorem pcsa_admitBlock_post_slow (p : Params) (st st1 : State p.n) (s : Slot)
    (N : NamedProposal p.n) (C : Prop) [Decidable C] (hCiff : C ↔ st1.fg.F = st.fg.F)
    (hb : SlowBase st st1)
    (hl : LockLoss (fun c => N.pc = some c ∧ c.wellFormed = true ∧
      c.target ∈ st1.base.blocks) st st1)
    (hbl : st.base.blocks ⊆ st1.base.blocks)
    (hprop : st1.proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩])
    (hF0 : st.fg.F = .genesis)
    (hF : (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).fg.F = .genesis) :
    SlowBase st (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
        (if C then st1 else reconcile st1)))) ∧
      LockLoss (UsedPC (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
        (if C then st1 else reconcile st1))))) st
        (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
          (if C then st1 else reconcile st1)))) ∧
      st.base.blocks ⊆ (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
        (if C then st1 else reconcile st1)))).base.blocks := by
  have hfg : (if C then st1 else reconcile st1).fg = st1.fg := by
    split
    · rfl
    · exact (pcsa_reconcile_frame st1).2.2.2.2.1
  have hC : C := by
    rw [hCiff]
    obtain ⟨-, -, -, -, t5⟩ := pcsa_admitBlock_tail_slow p
      (if C then st1 else reconcile st1) N.rows N.pcAcks
    rw [hF0, ← hfg, ← t5]
    exact hF
  rw [ite_eq_left hC] at hF ⊢
  obtain ⟨t1, t2, t3, t4, t5⟩ := pcsa_admitBlock_tail_slow p st1 N.rows N.pcAcks
  rw [t5] at hF
  refine ⟨hb.slow_trans t1, ?_, ?_⟩
  · refine (hl.loss_mono ?_).loss_trans (t2.loss_mono (fun c hc => Or.inl hc))
    intro c ⟨hc, hw, ht⟩
    rw [UsedPC_def]
    right
    refine ⟨N.slot, List.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [t4, hprop]
      refine List.mem_filterMap.mpr ⟨⟨.proposer s, .proposal N⟩,
        List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      change (if N.slot = N.slot then N.pc else none) = some c
      rw [ite_eq_left rfl, hc]
    · change (c.wellFormed && decide (c.target ∈ _) && activeCompatible _ c.target) = true
      rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
      refine ⟨⟨hw, ?_⟩, pcsa_activeCompatible_genesis _ (by rw [t5]; exact hF) _⟩
      rw [t3]
      exact decide_eq_true ht
  · rw [t3]
    exact hbl

/-- [pcsa34-r4.3 §5.5 steps 2–3] In a stage-1 block admission (`F` genesis
before and after), `S`, the saved results and the time stay, the tree grows,
and a deleted lock conflicts with a PC the result uses. -/
theorem pcsa_admitBlock_slow (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (hF0 : st.fg.F = .genesis) (hF : (admitBlock p st s N).fg.F = .genesis) :
    SlowBase st (admitBlock p st s N) ∧
      LockLoss (UsedPC (admitBlock p st s N)) st (admitBlock p st s N) ∧
      st.base.blocks ⊆ (admitBlock p st s N).base.blocks := by
  have hrefl : SlowBase st st ∧ LockLoss (UsedPC st) st st ∧ st.base.blocks ⊆ st.base.blocks :=
    ⟨SlowBase.slow_refl _, LockLoss.loss_refl _ _, List.Subset.refl _⟩
  revert hF
  delta admitBlock
  split
  · intro _; exact hrefl
  · cases hP : parentFG st N.erase with
    | none => intro _; exact hrefl
    | some P =>
      dsimp only
      split
      · intro hF
        obtain ⟨a1, a2, a3, a4⟩ := pcsa_admitProposal_slow p.toParams.engine st.base
          (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
        have hbl := pcsa_admitProposal_blocks_mono p.toParams.engine st.base
          (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
        refine pcsa_admitBlock_post_slow p st _ s N _ Iff.rfl ?_ ?_ ?_ ?_ hF0 hF
        rotate_left 3
        · rfl
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try rw [deleteConflictingLeases_def]) <;> exact ⟨a1, a2, a3⟩
        · cases hc : N.pc with
          | none => exact LockLoss.of_eq a4
          | some c =>
            dsimp only
            split_ifs with hv
            · rw [deleteConflictingLeases_def]
              refine ⟨fun row hr => a4 ▸ (List.mem_filter.mp hr).1, ?_⟩
              intro row hr hn
              have hv' := (Bool.and_eq_true_iff.mp hv).1
              change (c.wellFormed && decide (c.target ∈ _) && activeCompatible _ c.target) =
                true at hv'
              rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hv'
              refine ⟨c, ⟨rfl, hv'.1.1, of_decide_eq_true hv'.1.2⟩, ?_⟩
              by_contra hx
              apply hn
              refine List.mem_filter.mpr ⟨a4 ▸ hr, ?_⟩
              have hx' : Block.compatible c.target row.1 = true := by
                cases h : Block.compatible c.target row.1
                · exact absurd h hx
                · rfl
              rw [hx']
              simp
            · exact LockLoss.of_eq a4
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try rw [deleteConflictingLeases_def]) <;> exact hbl
      · intro _; exact hrefl

/-- [pcsa34-r4.3 §5.5 steps 2–3] A stage-1 delivery (`F` genesis before and
after) keeps `S`, the saved results and the time, grows the tree, and
deletes only locks that conflict with a PC the result uses. -/
theorem pcsa_process_slow (p : Params) (st : State p.n) (o : Wire p.n)
    (hF0 : st.fg.F = .genesis) (hF : (process p st o).fg.F = .genesis) :
    SlowBase st (process p st o) ∧ LockLoss (UsedPC (process p st o)) st (process p st o) ∧
      st.base.blocks ⊆ (process p st o).base.blocks := by
  revert hF
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      intro _
      dsimp only
      delta admitHead
      obtain ⟨h1, h2, h3, h4⟩ := pcsa_admitVote_slow p.toParams.engine st.base
        ⟨.seat s i, .head r⟩
      refine ⟨⟨h1, h2, h3⟩, LockLoss.of_eq h4, ?_⟩
      change st.base.blocks ⊆ (GridCO.admitVote _ st.base _).blocks
      rw [pcsa_admitVote_blocks]
    | row i body =>
      intro _
      dsimp only
      have hb := (pcsa_admitRow_frame p st ⟨o.auth, body⟩).2.2.2.2.2
      exact ⟨SlowBase.of_base hb, LockLoss.of_eq (by rw [hb]), by rw [hb]⟩
    | block s N =>
      intro hF
      exact pcsa_admitBlock_slow p st s N hF0 hF
    | ack s i r =>
      intro _
      dsimp only
      delta admitAck
      have hb := (pcsa_poolAck_frame p st ⟨o.auth, r⟩).2.2.2.2
      obtain ⟨c1, c2⟩ := pcsa_collectPCs_slow (poolAck p st ⟨o.auth, r⟩)
      refine ⟨(SlowBase.of_base hb).slow_trans c1,
        ((LockLoss.of_eq (by rw [hb])).loss_trans c2).loss_mono (fun c hc => Or.inl hc), ?_⟩
      rw [(collectPCs_frame _).2.1, hb]
    | pc d =>
      intro _
      dsimp only
      delta admitPC
      split
      · have hb := (pcsa_fold_poolAckRaw_frame st d.acks).2.2.2.2.1
        obtain ⟨c1, c2⟩ := pcsa_collectPCs_slow (d.acks.foldl poolAckRaw st)
        refine ⟨(SlowBase.of_base hb).slow_trans c1,
          ((LockLoss.of_eq (by rw [hb])).loss_trans c2).loss_mono (fun c hc => Or.inl hc),
          ?_⟩
        rw [(collectPCs_frame _).2.1, hb]
      · exact ⟨SlowBase.slow_refl _, LockLoss.loss_refl _ _, List.Subset.refl _⟩
  | none => intro _; exact ⟨SlowBase.slow_refl _, LockLoss.loss_refl _ _, List.Subset.refl _⟩

/-! ### The pre-gate clock -/

/-- [pcsa34-r4.3 §5.5 step 2] The pre-gate clock keeps `S`, the saved
results, the tree and the votes, sets the time, and keeps every lock that has
not expired and is not released. The release count is read on a view of a
store with the votes and tree of `st`. -/
theorem pcsa_clockPre_slow (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.stableRecord = st.base.stableRecord ∧
      (clockPre p st t).base.genuine = st.base.genuine ∧
      (clockPre p st t).base.now = t ∧
      (clockPre p st t).base.obligations ⊆ st.base.obligations ∧
      ∀ row ∈ st.base.obligations, t < row.2.2 →
        (0 ≤ t - 5 * p.Δ → t = SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat →
          ∀ X : State p.n, X.base.votes = st.base.votes → X.base.blocks = st.base.blocks →
          GridCO.releaseCount p.toParams.engine (actView X)
            ((t - 5 * p.Δ) / (4 * p.Δ)).toNat row.1 < row.2.1) →
        row ∈ (clockPre p st t).base.obligations := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, he⟩ : ∃ X : State p.n,
      X.base.stableRecord = st.base.stableRecord ∧ X.base.genuine = st.base.genuine ∧
      X.base.now = t ∧ X.base.votes = st.base.votes ∧ X.base.blocks = st.base.blocks ∧
      X.base.obligations = st.base.obligations.filter (fun row => decide (t < row.2.2)) ∧
      clockPre p st t = if (0 ≤ t - 5 * p.Δ && t == SA.releaseTime p.toParams
          ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) = true then
        onView (fun v => SA.Root.release p.toParams v ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) X
        else X := by
    unfold clockPre
    dsimp only
    refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals (split <;> split <;> rfl)
  have hX : ∀ row, row ∈ X.base.obligations ↔ row ∈ st.base.obligations ∧ t < row.2.2 := by
    intro row
    rw [h6, List.mem_filter, decide_eq_true_iff]
  rw [he]
  split
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hc
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · intro row hr
      change row ∈ (actView X).obligations.filter _ at hr
      exact ((hX row).mp (List.mem_filter.mp hr).1).1
    · intro row hr ht hc'
      change row ∈ (actView X).obligations.filter _
      refine List.mem_filter.mpr ⟨(hX row).mpr ⟨hr, ht⟩, ?_⟩
      rcases row with ⟨b, g, dl⟩
      exact decide_eq_true (hc' hc.1 hc.2 X h4 h5)
  · refine ⟨h1, h2, h3, fun row hr => ((hX row).mp hr).1, ?_⟩
    intro row hr ht _
    exact (hX row).mpr ⟨hr, ht⟩

/-! ### Gates -/

/-- A block below `h` is compatible with every block compatible with `h`. -/
theorem pcsa_compatible_of_preceq {b h A : Block} (hb : Block.Preceq b h)
    (hA : Block.Compatible h A) : Block.Compatible b A := by
  rcases Bool.or_eq_true_iff.mp hA with h' | h'
  · exact block_compatible_of_common (block_preceq_trans hb h') (block_preceq_refl A)
  · exact block_compatible_of_common hb h'

/-- [pcsa34-r4.3 §5.5 step 4] `advance` keeps `S ⪰ A` for a result
compatible with `A`. -/
theorem pcsa_advance_above {A S h : Block} (hS : Block.Preceq A S)
    (hA : Block.Compatible h A) : Block.Preceq A (GridCO.advance S h) := by
  change Block.Preceq A (if Block.preceq h S then S else h)
  split
  · exact hS
  · rename_i hn
    rcases Bool.or_eq_true_iff.mp hA with h' | h'
    · exact absurd (block_preceq_trans h' hS) hn
    · exact h'

/-- `advance` keeps the old record or takes the result. -/
theorem pcsa_advance_cases (S h : Block) : GridCO.advance S h = S ∨ GridCO.advance S h = h := by
  change (if Block.preceq h S then S else h) = S ∨ (if Block.preceq h S then S else h) = h
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- [pcsa34-r4.3 §5.5 step 2] `advance` to a result `⪰ A` gives a record `⪰ A`. -/
theorem pcsa_advance_of_above {A S h : Block} (hAh : Block.Preceq A h) :
    Block.Preceq A (GridCO.advance S h) := by
  change Block.Preceq A (if Block.preceq h S then S else h)
  split
  · rename_i hhS
    exact block_preceq_trans hAh hhS
  · exact hAh

/-- A lock write keeps the rows of other targets or levels, and writes one
row on its target with a deadline at least its own. -/
theorem pcsa_writeLease_rows (st : State n) (b : Block) (g : Nat) (dl : Time)
    (ρ : Option PCRank) (row : Block × Nat × Time) :
    row ∈ (writeLease st b g dl ρ).base.obligations ↔
      (row ∈ st.base.obligations ∧ ¬ (row.1 = b ∧ row.2.1 = g)) ∨
        (row.1 = b ∧ row.2.1 = g ∧
          row.2.2 = max ((GridCO.deadlineOf st.base b g).getD dl) dl) := by
  rw [writeLease_def]
  change row ∈ st.base.obligations.filter (fun (target, level, _) =>
    !(target == b && level == g)) ++ [(b, g, max ((GridCO.deadlineOf st.base b g).getD dl) dl)] ↔ _
  rw [List.mem_append, List.mem_filter, List.mem_singleton]
  rcases row with ⟨b', g', dl'⟩
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, Prod.mk.injEq,
    not_and]
  constructor
  · rintro (⟨hr, hn⟩ | ⟨rfl, rfl, rfl⟩)
    · refine Or.inl ⟨hr, fun h1 h2 => ?_⟩
      rcases hn with hn | hn
      · exact hn h1
      · exact hn h2
    · exact Or.inr ⟨rfl, rfl, rfl⟩
  · rintro (⟨hr, hn⟩ | ⟨rfl, rfl, rfl⟩)
    · refine Or.inl ⟨hr, ?_⟩
      by_cases h1 : b' = b
      · exact Or.inr (hn h1)
      · exact Or.inl h1
    · exact Or.inr ⟨rfl, rfl, rfl⟩

/-- A lock write keeps a lock row whose deadline bound is at most the
written deadline. -/
theorem pcsa_writeLease_lockRow (st : State n) (b : Block) (g : Nat) (dl : Time)
    (ρ : Option PCRank) {A : Block} {g' : Nat} {D : Time} (h : LockRow st A g' D)
    (hD : D ≤ dl) : LockRow (writeLease st b g dl ρ) A g' D := by
  rw [LockRow_def] at h ⊢
  obtain ⟨row, hr, hA, hg, hd⟩ := h
  by_cases hb : row.1 = b ∧ row.2.1 = g
  · refine ⟨(b, g, max ((GridCO.deadlineOf st.base b g).getD dl) dl),
      (pcsa_writeLease_rows st b g dl ρ _).mpr (Or.inr ⟨rfl, rfl, rfl⟩), ?_, ?_, ?_⟩
    · exact hb.1 ▸ hA
    · exact hb.2 ▸ hg
    · exact le_trans hD (le_max_right _ _)
  · exact ⟨row, (pcsa_writeLease_rows st b g dl ρ row).mpr (Or.inl ⟨hr, hb⟩), hA, hg, hd⟩

/-- A lock write on `A` leaves a row on `A` with at least the written deadline. -/
theorem pcsa_writeLease_lockRow_new (st : State n) (A : Block) (g : Nat) (dl : Time)
    (ρ : Option PCRank) : LockRow (writeLease st A g dl ρ) A g dl := by
  rw [LockRow_def]
  exact ⟨(A, g, max ((GridCO.deadlineOf st.base A g).getD dl) dl),
    (pcsa_writeLease_rows st A g dl ρ _).mpr (Or.inr ⟨rfl, rfl, rfl⟩), rfl, rfl,
    le_max_right _ _⟩

/-- The base fields of the S case at a lock write. -/
structure GateBase (st st' : State n) : Prop where
  stable : st'.base.stableRecord = st.base.stableRecord
  genuine : st'.base.genuine = st.base.genuine
  now : st'.base.now = st.base.now
  blocks : st'.base.blocks = st.base.blocks

/-- The lock fold of a gate: written rows are compatible with `A`, a lock row
with deadline bound at most the written deadline stays, and the base fields
stay. -/
theorem pcsa_lockFold_slow (p : Params) (s : Slot) (ρ : Option PCRank) (A : Block)
    (D : Time) (l : List Block) (hl : ∀ b ∈ l, Block.Compatible b A)
    (hD : D ≤ SA.gateTime p.toParams s + SA.lifetime p.toParams)
    (st : State p.n) (hrows : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A) :
    (∀ row ∈ (l.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
        (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
          SA.lifetime p.toParams) ρ) acc) st).base.obligations, Block.Compatible row.1 A) ∧
      (LockRow st A (SA.releaseThreshold p.toParams) D →
        LockRow (l.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
        (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
          SA.lifetime p.toParams) ρ) acc) st) A (SA.releaseThreshold p.toParams) D) ∧
      GateBase st (l.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
        (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
          SA.lifetime p.toParams) ρ) acc) st) := by
  induction l generalizing st with
  | nil => exact ⟨hrows, id, ⟨rfl, rfl, rfl, rfl⟩⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    have hb : Block.Compatible b A := hl b (List.mem_cons_self ..)
    have hstep : (∀ row ∈ ((slowLevels p (actView st) s b).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st).base.obligations, Block.Compatible row.1 A) ∧
        (LockRow st A (SA.releaseThreshold p.toParams) D →
          LockRow ((slowLevels p (actView st) s b).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st) A (SA.releaseThreshold p.toParams) D) ∧
        GateBase st ((slowLevels p (actView st) s b).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st) := by
      change (∀ row ∈ ((if SA.Root.slowEligible p.toParams (actView st) s b then
            [SA.releaseThreshold p.toParams] else []).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st).base.obligations, Block.Compatible row.1 A) ∧
        (LockRow st A (SA.releaseThreshold p.toParams) D →
          LockRow ((if SA.Root.slowEligible p.toParams (actView st) s b then
            [SA.releaseThreshold p.toParams] else []).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st) A (SA.releaseThreshold p.toParams) D) ∧
        GateBase st ((if SA.Root.slowEligible p.toParams (actView st) s b then
            [SA.releaseThreshold p.toParams] else []).foldl
          (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
            SA.lifetime p.toParams) ρ) st)
      split
      · refine ⟨fun row hr => ?_, fun hrow => pcsa_writeLease_lockRow st b _ _ ρ hrow hD,
          ⟨rfl, rfl, rfl, rfl⟩⟩
        rcases (pcsa_writeLease_rows st b _ _ ρ row).mp hr with ⟨hr', -⟩ | ⟨he, -⟩
        · exact hrows row hr'
        · rw [he]
          exact hb
      · exact ⟨hrows, id, ⟨rfl, rfl, rfl, rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) _
      hstep.1
    exact ⟨h1, fun hrow => h2 (hstep.2.1 hrow), ⟨h3.stable.trans hstep.2.2.stable,
      h3.genuine.trans hstep.2.2.genuine, h3.now.trans hstep.2.2.now,
      h3.blocks.trans hstep.2.2.blocks⟩⟩

/-- [pcsa34-r4.3 §5.5 steps 2, 4] A gate with a live lock row on `A` and
every lock compatible with `A` keeps `S ⪰ A` (the guard vetoes a conflicting
result), writes only locks compatible with `A`, and keeps a lock row on `A`
whose deadline bound is at most the written deadline. -/
theorem pcsa_gateFrom_slow (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) (A : Block) (D : Time)
    (hS : Block.Preceq A st.base.stableRecord)
    (hrows : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A)
    (hrow : LockRow st A (SA.releaseThreshold p.toParams) D) (hlive : st.base.now < D)
    (hD : D ≤ SA.gateTime p.toParams s + SA.lifetime p.toParams) :
    Block.Preceq A (gateFrom p a cs ρ st s).base.stableRecord ∧
      (∀ row ∈ (gateFrom p a cs ρ st s).base.obligations, Block.Compatible row.1 A) ∧
      LockRow (gateFrom p a cs ρ st s) A (SA.releaseThreshold p.toParams) D ∧
      (gateFrom p a cs ρ st s).base.now = st.base.now ∧
      (gateFrom p a cs ρ st s).base.blocks = st.base.blocks := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact ⟨hS, hrows, hrow, rfl, rfl⟩
  | some h =>
    dsimp only
    split
    · exact ⟨hS, hrows, hrow, rfl, rfl⟩
    · rename_i hg
      have hhA : Block.Compatible h A := by
        rw [LockRow_def] at hrow
        obtain ⟨row, hr, hA, -, hd⟩ := hrow
        by_contra hn
        apply hg
        refine List.any_eq_true.mpr ⟨row, hr, ?_⟩
        rw [Bool.and_eq_true, decide_eq_true_iff]
        refine ⟨lt_of_lt_of_le hlive hd, ?_⟩
        rw [Bool.not_eq_true', hA, block_compatible_comm]
        cases hx : Block.compatible h A
        · rfl
        · exact absurd hx hn
      have hl : ∀ b ∈ (actView st).blocks.filter (fun b => b != Block.genesis &&
          Block.preceq b h && leaseWriteOK cs ρ b), Block.Compatible b A := by
        intro b hb
        have hb' := (List.mem_filter.mp hb).2
        simp only [Bool.and_eq_true] at hb'
        exact pcsa_compatible_of_preceq hb'.1.2 hhA
      generalize hst1 : ({ st with base := { st.base with
        goldfishRecord := GridCO.advance (actView st).goldfishRecord h
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h)
        stableRecord := GridCO.advance st.base.stableRecord h } } : State p.n) = st1
      have e1 : st1.base.obligations = st.base.obligations := by rw [← hst1]
      have e2 : st1.base.stableRecord = GridCO.advance st.base.stableRecord h := by rw [← hst1]
      have e3 : st1.base.now = st.base.now := by rw [← hst1]
      have e4 : st1.base.blocks = st.base.blocks := by rw [← hst1]
      have hrows1 : ∀ row ∈ st1.base.obligations, Block.Compatible row.1 A := e1 ▸ hrows
      have hrow1 : LockRow st1 A (SA.releaseThreshold p.toParams) D := by
        rw [LockRow_def, e1]
        rw [LockRow_def] at hrow
        exact hrow
      obtain ⟨h1, h2, h3⟩ := pcsa_lockFold_slow p s ρ A D _ hl hD st1 hrows1
      exact ⟨h3.stable ▸ e2 ▸ pcsa_advance_above hS hhA, h1, h2 hrow1, h3.now.trans e3,
        h3.blocks.trans e4⟩

/-- A saved result stays saved, with its value, when a gate records a label. -/
theorem pcsa_savedGenuine_record (v : GridCO.State n .root) (s r : Slot) (res : Option Block)
    (x : Option Block) (h : GridCO.savedGenuine v r = some x) :
    GridCO.savedGenuine { v with genuine :=
      (@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s res) } r = some x := by
  change ((@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s res).find?
    (fun row => row.1 == r)).map Prod.snd = some x
  change (v.genuine.find? (fun row => row.1 == r)).map Prod.snd = some x at h
  delta GridCO.recordGenuine
  split
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [List.find?_append, hy]
    rfl
  · exact h

/-- [pcsa34-r4.3 §5.5 step 2, the pending gate] A gate whose result `h ⪰ A`
is compatible with every lock, with `A` in the tree, the write check passing
on `A`, and the `k − 1` previous saved results `⪰ A`, writes a lock row on
`A` with the full deadline. -/
theorem pcsa_gateFrom_renew (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) (A h : Block)
    (hrows : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A)
    (hc : SA.Root.confirmationFrom p.toParams a (actView st) s = some h)
    (hAh : Block.Preceq A h)
    (hguard : ∀ row ∈ st.base.obligations, Block.Compatible row.1 h)
    (hAb : A ∈ st.base.blocks) (hAg : A ≠ .genesis) (hF : st.fg.F = .genesis)
    (hok : leaseWriteOK cs ρ A = true) (hk : p.k ≤ s + 1)
    (hsaved : ∀ j < p.k - 1, ∃ C, GridCO.savedGenuine st.base (s - (j + 1)) = some (some C) ∧
      Block.Preceq A C) :
    Block.Preceq A (gateFrom p a cs ρ st s).base.stableRecord ∧
      (∀ row ∈ (gateFrom p a cs ρ st s).base.obligations, Block.Compatible row.1 A) ∧
      LockRow (gateFrom p a cs ρ st s) A (SA.releaseThreshold p.toParams)
        (SA.gateTime p.toParams s + SA.lifetime p.toParams) ∧
      (gateFrom p a cs ρ st s).base.now = st.base.now ∧
      (gateFrom p a cs ρ st s).base.blocks = st.base.blocks := by
  have hhA : Block.Compatible h A :=
    block_compatible_of_common (block_preceq_refl h) hAh
  rw [gateFrom_def]
  dsimp only
  rw [hc]
  dsimp only
  split
  · rename_i hg
    exfalso
    obtain ⟨row, hr, hx⟩ := List.any_eq_true.mp hg
    rw [Bool.and_eq_true] at hx
    have := hguard row hr
    rw [Block.Compatible] at this
    rw [this] at hx
    exact absurd hx.2 (by decide)
  · have hl : ∀ b ∈ (actView st).blocks.filter (fun b => b != Block.genesis &&
        Block.preceq b h && leaseWriteOK cs ρ b), Block.Compatible b A := by
      intro b hb
      have hb' := (List.mem_filter.mp hb).2
      simp only [Bool.and_eq_true] at hb'
      exact pcsa_compatible_of_preceq hb'.1.2 hhA
    have hAl : A ∈ (actView st).blocks.filter (fun b => b != Block.genesis &&
        Block.preceq b h && leaseWriteOK cs ρ b) := by
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · exact List.mem_filter.mpr ⟨hAb, pcsa_activeCompatible_genesis st hF A⟩
      · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨⟨hAg, hAh⟩, hok⟩
    generalize hst1 : ({ st with base := { st.base with
      goldfishRecord := GridCO.advance (actView st).goldfishRecord h
      genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h)
      stableRecord := GridCO.advance st.base.stableRecord h } } : State p.n) = st1
    have e1 : st1.base.obligations = st.base.obligations := by rw [← hst1]
    have e2 : st1.base.stableRecord = GridCO.advance st.base.stableRecord h := by rw [← hst1]
    have e3 : st1.base.now = st.base.now := by rw [← hst1]
    have e4 : st1.base.blocks = st.base.blocks := by rw [← hst1]
    have e5 : st1.base.genuine =
        @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h) := by
      rw [← hst1]
    have hrows1 : ∀ row ∈ st1.base.obligations, Block.Compatible row.1 A := e1 ▸ hrows
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hAl
    rw [hsplit, List.foldl_append, List.foldl_cons]
    obtain ⟨a1, -, a3⟩ := pcsa_lockFold_slow p s ρ A
      (SA.gateTime p.toParams s + SA.lifetime p.toParams) l₁
      (fun b hb => hl b (hsplit ▸ List.mem_append_left _ hb)) le_rfl st1 hrows1
    generalize hacc : l₁.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
        (fun acc g => writeLease acc b g (SA.gateTime p.toParams s +
          SA.lifetime p.toParams) ρ) acc) st1 = acc at a1 a3 ⊢
    have helig : SA.Root.slowEligible p.toParams (actView acc) s A = true := by
      change (decide (p.k ≤ s + 1) && (List.range (p.k - 1)).all (fun j =>
        match GridCO.savedGenuine (actView acc) (s - (j + 1)) with
        | some (some C) => Block.preceq A C
        | _ => false)) = true
      rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
      refine ⟨hk, fun j hj => ?_⟩
      obtain ⟨C, hC, hAC⟩ := hsaved j (List.mem_range.mp hj)
      have hC' : GridCO.savedGenuine (actView acc) (s - (j + 1)) = some (some C) := by
        change (acc.base.genuine.find? (fun row => row.1 == s - (j + 1))).map Prod.snd = _
        rw [a3.genuine, e5]
        exact pcsa_savedGenuine_record (actView st) s _ (some h) (some C) hC
      rw [hC']
      exact hAC
    have hstepA : (slowLevels p (actView acc) s A).foldl (fun acc' g => writeLease acc' A g
        (SA.gateTime p.toParams s + SA.lifetime p.toParams) ρ) acc =
        writeLease acc A (SA.releaseThreshold p.toParams)
          (SA.gateTime p.toParams s + SA.lifetime p.toParams) ρ := by
      change (if SA.Root.slowEligible p.toParams (actView acc) s A then
        [SA.releaseThreshold p.toParams] else []).foldl _ acc = _
      rw [ite_eq_left helig]
      rfl
    rw [hstepA]
    have hrowsA : ∀ row ∈ (writeLease acc A (SA.releaseThreshold p.toParams)
        (SA.gateTime p.toParams s + SA.lifetime p.toParams) ρ).base.obligations,
        Block.Compatible row.1 A := by
      intro row hr
      rcases (pcsa_writeLease_rows acc A _ _ ρ row).mp hr with ⟨hr', -⟩ | ⟨he, -⟩
      · exact a1 row hr'
      · rw [he]
        exact block_compatible_of_common (block_preceq_refl A) (block_preceq_refl A)
    obtain ⟨b1, b2, b3⟩ := pcsa_lockFold_slow p s ρ A
      (SA.gateTime p.toParams s + SA.lifetime p.toParams) l₂
      (fun b hb => hl b (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb))) le_rfl
      _ hrowsA
    refine ⟨?_, b1, b2 (pcsa_writeLease_lockRow_new acc A _ _ ρ), ?_, ?_⟩
    · rw [b3.stable]
      change Block.Preceq A acc.base.stableRecord
      rw [a3.stable, e2]
      exact pcsa_advance_of_above hAh
    · rw [b3.now]
      change acc.base.now = _
      rw [a3.now, e3]
    · rw [b3.blocks]
      change acc.base.blocks = _
      rw [a3.blocks, e4]

/-! ### The clock -/

/-- With `F` genesis, normalization is the identity. -/
theorem pcsa_normalizeS_genesis (st : State n) (hF : st.fg.F = .genesis) :
    normalizeS st = st := by
  delta normalizeS
  rw [hF]
  exact ite_eq_left (block_genesis_preceq _)

/-- With `F` genesis, the composite gate is the SA gate from genesis, unless
the label is saved. -/
theorem pcsa_gateStep_genesis (p : Params) (st : State p.n) (s : Slot)
    (hF : st.fg.F = .genesis) :
    gateStep p st s = if (GridCO.savedGenuine st.base s).isSome then st else
      gateFrom p .genesis st.pcs (gateRank p st s) st s := by
  rw [gateStep_def]
  dsimp only
  rw [hF]
  split
  · exact pcsa_normalizeS_genesis st hF
  · apply pcsa_normalizeS_genesis
    rw [(pcsa_gateFrom_frame p _ st.pcs _ st s).2.2.2.2.1]
    exact hF

/-- The clock is the pre-gate clock, then the gate of `d_s` when `t = d_s`. -/
theorem pcsa_clock_cases (p : Params) (st : State p.n) (t : Time) :
    (clock p st t = clockPre p st t ∧
        ¬ (0 ≤ t - 6 * p.Δ ∧ t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)) ∨
      (0 ≤ t - 6 * p.Δ ∧ t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat ∧
        clock p st t = gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) := by
  unfold clock
  dsimp only
  split
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hc
    exact Or.inr ⟨hc.1, hc.2, rfl⟩
  · rename_i hc
    refine Or.inl ⟨rfl, fun h => hc ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
    exact h

end AvailableChain.PCSA
end
