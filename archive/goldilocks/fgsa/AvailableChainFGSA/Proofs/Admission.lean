module
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainFGSA.Proofs.HeadDomain

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! Admission agreement (comp §4.3), the block-step SA bridge (J3) and
acceptance sufficiency (K8). The composite test decides; the FG and GridCO
tests then take their accepting branch. -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; G10 m3] The first three fields of `CStoreInv`. -/
theorem CStoreInv.toInv0 {p : Params} {st : State p.n} (h : CStoreInv p st) : Inv0 p st :=
  ⟨h.fg, h.rootInj, h.baseTree⟩

/-! ### Selectors and the FG block of a wire -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Selector soundness (audit: `pickPair_eq_of_unique` is
only the
sufficient direction). -/
theorem pickPair_some_spec {α : Type} [DecidableEq α] (T : Finset α) (q : α → Bool) {a : α}
    (h : pickPair T q = some a) : a ∈ T ∧ q a = true := by
  unfold pickPair at h
  split at h
  · next hu =>
    cases h
    exact Finset.choose_spec (fun a => q a = true) T hu
  · cases h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M3] Under root injectivity the parent lookup is exact. -/
theorem parentFG_spec {n : Nat} (st : State n)
    (b : Block) (P : FGBlock (Fin n)) :
    parentFG st b = some P ↔ P ∈ st.fg.TF ∧ eraseFG P = b.parent := by
  constructor
  · intro h
    have := pickPair_some_spec _ _ h
    exact ⟨this.1, by simpa using this.2⟩
  · rintro ⟨hP, he⟩
    unfold parentFG
    apply KitFG.pickPair_eq_of_unique _ _ P hP (by simpa using he)
    intro P' _ he'
    simp only [decide_eq_true_eq] at he'
    exact eraseFG_injective (he'.trans he.symm)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [store lookup; Review Focus 1] Under the store correspondence,
the FG parent
lookup succeeds exactly when a stored base block has the parent's root. The
test reads the store only; no wire carries a root to check. -/
theorem parentFG_isSome_iff_root (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block)
    (hr : ∀ q ∈ st.base.blocks, q.root = b.parent.root → q = b.parent) :
    (parentFG st b).isSome = true ↔ ∃ q ∈ st.base.blocks, q.root = b.parent.root := by
  rw [← parent_mem_iff_root b st.base.blocks hr, h.baseTree, Option.isSome_iff_exists]
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, (parentFG_spec st b P).1 hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, (parentFG_spec st b P).2 hP⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [missing dependency] A proposal whose parent is not stored
returns the state
before any write: no base block, no FG block, no wire, no carried vote or row. -/
theorem admitBlock_missingParent (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (h : parentFG st N.erase = none) : admitBlock p st s N = st :=
  admitBlock_refused p st s N (Or.inr (Or.inl h))

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.carrier.v1; D9] (the flat form of `eraseFG (fg B) =
erase B`, DQ1)
The erasure law: the FG block of a wire block whose body packs its rows erases
to the wire block. -/
theorem eraseFG_fgBlock {n : Nat} {P : FGBlock (Fin n)} {b : Block} (hb : b ≠ .genesis)
    (hP : eraseFG P = b.parent) (rows : List (RowWire n)) (hrows : rowsOk b rows = true) :
    eraseFG (fgBlock P b rows) = b := by
  cases b with
  | genesis => exact absurd rfl hb
  | node q s r_s x =>
      rw [rowsOk_iff] at hrows
      simp only [Block.body] at hrows
      simp only [fgBlock, eraseFG, Block.slot, Block.body]
      rw [hP]
      change Block.node q s r_s (packBody (appOf x) rows) = _
      rw [← hrows]
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] -/
theorem fgBlock_parent {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).parent = P := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] -/
theorem fgBlock_slot {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).slot = b.slot := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [ROOT-DIGEST W1; DC NamedBlocks] The FG view copies the
supplied root. -/
theorem fgBlock_root {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).root = b.root := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] -/
theorem fgBlock_rows {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).rows = rows.filterMap RowWire.toRow? := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; DQ2] A block with a fresh root is not in Σ.T. The
three premises
make its FG root the wire root (`fgBlock_root`). -/
theorem fgBlock_notMem {n : Nat} (st : State n) (P : FGBlock (Fin n)) (b : Block)
    (rows : List (RowWire n)) (_hb : b ≠ .genesis) (_hP : eraseFG P = b.parent)
    (_hrows : rowsOk b rows = true) (hfresh : ¬ ∃ Y ∈ st.fg.TF, Y.root = b.root) :
    fgBlock P b rows ∉ st.fg.TF :=
  fun hm => hfresh ⟨_, hm, fgBlock_root P b rows⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [audit M2; DQ12] A row list whose rows all decode loses no
occurrence: the
FG rows are the decoded rows, position by position. -/
theorem toRow_forall₂ {n : Nat} (rows : List (RowWire n))
    (h : ∀ a ∈ rows, (RowWire.decode? a).isSome) :
    List.Forall₂ (fun a x => a.toRow? = some x) rows (rows.filterMap RowWire.toRow?) := by
  induction rows with
  | nil => exact List.Forall₂.nil
  | cons a rows ih =>
      have ha := h a List.mem_cons_self
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ha
      have hr : a.toRow? = some (x.2.toRow x.1) := by
        simp [RowWire.toRow?, hx]
      rw [List.filterMap_cons, hr]
      exact List.Forall₂.cons hr (ih (fun c hc => h c (List.mem_cons_of_mem a hc)))

/-! ### The acceptance test -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ9, DQ14; Opus m3] On a checked block wire, the acceptance
test reduces to
the state tests: slot not in the future, fresh root, `F ⪯ B`. -/
theorem blockAccepted_of_wellFormed (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : FGBlock (Fin p.n))
    (hwf : wellFormed p ⟨.proposer s, .proposal N⟩ = true) :
    blockAccepted p st s N P =
      (decide (N.erase.slot ≤ st.slot p) && !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
        FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) && rowsValidForParent p P N.erase.slot
          N.rows) := by
  simp only [wellFormed, Wire.decode, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨hg, hs⟩, hps⟩, -⟩, -⟩, -⟩, hok⟩ := hwf
  simp only [blockAccepted, namedContentOk, hg, hs, hps, hok, Bool.true_and, Bool.and_true]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] Acceptance checks all rows against the parent's pre-fold
state. -/
theorem blockAccepted_rowsValid {p : Params} {st : State p.n}
  {s : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hacc : blockAccepted p st s N P = true) :
    rowsValidForParent p P N.erase.slot N.rows = true := by
  simp only [blockAccepted, Bool.and_eq_true] at hacc
  exact hacc.1.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] Invalid carried rows cause refusal before any write or
child handler. -/
theorem admitBlock_invalid_rows (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : FGBlock (Fin p.n)) (hP : parentFG st N.erase = some P)
    (hv : rowsValidForParent p P N.erase.slot N.rows = false) :
    admitBlock p st s N = st :=
  admitBlock_refused p st s N
    (Or.inr (Or.inr ⟨P, hP, by simp only [blockAccepted, hv, Bool.and_false, Bool.false_and]⟩))

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ2; Opus m4] Under a root premise on the base list and
`N.erase`,
the root test
and the block test agree (the T7 form uses `RootInjective`). -/
theorem rootTest_iff_blockTest (p : Params) (st : State p.n) (h : Inv0 p st) (b : Block)
    (hinj : ∀ c ∈ st.base.blocks, c.root = b.root → c = b) :
    (∃ Y ∈ st.fg.TF, Y.root = b.root) ↔ b ∈ st.base.blocks := by
  constructor
  · rintro ⟨Y, hY, hr⟩
    have hm : eraseFG Y ∈ st.base.blocks := (h.2.2 _).2 ⟨Y, hY, rfl⟩
    rw [← hinj _ hm (by rw [eraseFG_root, hr])]
    exact hm
  · intro hb
    obtain ⟨B, hB, rfl⟩ := (h.2.2 _).1 hb
    exact ⟨B, hB, (eraseFG_root B).symm⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The acceptance test, unpacked. -/
theorem blockAccepted_facts {p : Params} {st : State p.n} {s :
  Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hacc : blockAccepted p st s N P = true) :
    N.erase ≠ .genesis ∧ N.erase.slot ≤ st.slot p ∧ (¬ ∃ Y ∈ st.fg.TF, Y.root = N.erase.root) ∧
      FGBlock.Preceq st.fg.F (fgBlock P N.erase N.rows) ∧ N.erase.parent.slot < N.erase.slot ∧ s =
        N.erase.slot := by
  simp only [blockAccepted, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hacc
  obtain ⟨⟨⟨⟨⟨⟨⟨hg, hsl⟩, hfr⟩, hF⟩, hps⟩, hs⟩, -⟩, -⟩ := hacc
  exact ⟨hg, hsl, hfr, hF, hps, hs⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 §8.5: an accepted block has a positive slot and needs time
at least 4Δ. -/
theorem blockAccepted_slot_pos {p : Params} {st : State p.n}
  {s : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hacc : blockAccepted p st s N P = true) :
    0 < N.erase.slot ∧ 4 * p.Δ ≤ st.base.now := by
  obtain ⟨-, hslot, -, -, hparent, -⟩ := blockAccepted_facts hacc
  have hpos : 0 < N.erase.slot := Nat.zero_lt_of_lt hparent
  change N.erase.slot ≤ (st.base.now / (4 * p.Δ)).toNat at hslot
  have hn : 0 ≤ st.base.now / (4 * p.Δ) := by
    by_contra hneg
    have hz := Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hneg))
    exact (Nat.not_lt_of_ge (hslot.trans_eq hz)) hpos
  have hdiv := (Int.le_toNat hn).mp hslot
  have htime := (Int.le_ediv_iff_mul_le (by linarith [p.deltaPos])).mp hdiv
  constructor
  · exact hpos
  · have hb : (1 : Int) ≤ N.erase.slot := by exact_mod_cast hpos
    have hd : 0 ≤ 4 * p.Δ := le_of_lt (by linarith [p.deltaPos])
    exact le_trans (by simpa using mul_le_mul_of_nonneg_right hb hd) htime

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [ROOT-DIGEST W1; DC NamedBlocks] Admission checks the full
supplied content. -/
theorem blockAccepted_contentOk {p : Params} {st : State p.n} {s : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)}
    (hacc : blockAccepted p st s N P = true) :
    contentOk p N.erase N.raw N.support N.rows = true := (Bool.and_eq_true_iff.mp hacc).2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; D9] An accepted block packs its rows. -/
theorem blockAccepted_rowsOk {p : Params} {st : State p.n} {s
  : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hacc : blockAccepted p st s N P = true) : rowsOk N.erase N.rows = true
      := by
  simp only [blockAccepted, namedContentOk, contentOk, Bool.and_eq_true] at hacc
  exact hacc.2.1

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Under `Inv0`, an accepted block is not in the base
list, and its
parent is. -/
theorem accepted_base_facts (p : Params) (st : State p.n) (h :
  Inv0 p st) {s : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P =
      true) :
    P ∈ st.fg.TF ∧ eraseFG P = N.erase.parent ∧ N.erase.parent ∈ st.base.blocks ∧ N.erase ∉
      st.base.blocks := by
  obtain ⟨hPT, hPe⟩ := (parentFG_spec st N.erase P).1 hP
  obtain ⟨-, -, hfr, -⟩ := blockAccepted_facts hacc
  refine ⟨hPT, hPe, (h.2.2 _).2 ⟨P, hPT, hPe⟩, ?_⟩
  intro hb
  obtain ⟨B, hB, hBe⟩ := (h.2.2 _).1 hb
  exact hfr ⟨B, hB, by rw [← eraseFG_root, hBe]⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.frame.v1] The FG module accepts every block that the
composite accepts. -/
theorem fg_on_block_accepts (p : Params) (st : State p.n) (s :
  Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n)) (hP : parentFG st N.erase = some P) (hacc :
      blockAccepted p st s N P = true) :
    Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) =
      Window.update_finality p p.K_W { st.fg with TF := insert (fgBlock P N.erase N.rows) st.fg.TF }
        (fgBlock P N.erase N.rows) := by
  obtain ⟨hPT, hPe⟩ := pickPair_some_spec _ _ hP
  simp only [decide_eq_true_eq] at hPe
  obtain ⟨hg, -, hfr, hF, hps, -⟩ := blockAccepted_facts hacc
  apply Window.window_on_block_of_accepted
  simp only [not_or, Bool.not_eq_false, not_le]
  refine ⟨fgBlock_notMem st P N.erase N.rows hg hPe (blockAccepted_rowsOk hacc) hfr, fun hn => hn
    hPT,
    hF, ?_⟩
  rw [fgBlock_parent, fgBlock_slot, ← eraseFG_slot, hPe]
  exact hps

/-! ### The SA block admission -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `admitVote` reads no block and writes only the vote
pool and its
stamps. -/
theorem admitVote_withBlocks (q : GridCO.Params) {n : Nat} (v : GridCO.State n .root) (X : List
  Block) (D : Option (List Block))
    (o : GridCO.Wire n .root) :
    GridCO.admitVote q { v with blocks := X, headDomain := D } o = { GridCO.admitVote q v o with
      blocks := X, headDomain := D } := by
  simp only [GridCO.admitVote]
  split
  · split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  · rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The carried-vote fold commutes with a block-list
and resolution-metadata update. -/
theorem foldVotes_withBlocks (q : GridCO.Params) {n : Nat} (raw : List (GridCO.HeadWire n .root))
    (v : GridCO.State n .root) (X : List Block) (D : Option (List Block)) :
    raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) { v with
        blocks := X, headDomain := D } =
      { raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) v with
        blocks := X, headDomain := D } := by
  induction raw generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [admitVote_withBlocks, ih]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The carried-vote fold writes only the vote pool and
its stamps. -/
theorem foldVotes_fields (q : GridCO.Params) {n : Nat} (raw : List (GridCO.HeadWire n .root))
    (v : GridCO.State n .root) :
    let w := raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) v
    w.blocks = v.blocks ∧ w.blockStamp = v.blockStamp ∧ w.proposals = v.proposals ∧
      w.obligations = v.obligations ∧ w.genuine = v.genuine ∧
      w.stableRecord = v.stableRecord ∧ w.now = v.now := by
  induction raw generalizing v with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons x xs ih =>
      simp only [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (GridCO.admitVote q v (GridCO.fromHead x))
      have hv : (GridCO.admitVote q v (GridCO.fromHead x)).blocks = v.blocks ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).blockStamp = v.blockStamp ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).proposals = v.proposals ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).obligations = v.obligations ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).genuine = v.genuine ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).stableRecord = v.stableRecord ∧
          (GridCO.admitVote q v (GridCO.fromHead x)).now = v.now := by
        simp only [GridCO.admitVote]
        split
        · split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨h1.trans hv.1, h2.trans hv.2.1, h3.trans hv.2.2.1, h4.trans hv.2.2.2.1,
        h5.trans hv.2.2.2.2.1, h6.trans hv.2.2.2.2.2.1, h7.trans hv.2.2.2.2.2.2⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The accepting branch of `GridCO.admitProposal`. -/
theorem admitProposal_of_accept (q : GridCO.Params) {n : Nat} (v : GridCO.State n .root) (s : Slot)
    (w : GridCO.Msg n .root) (b : Block) (raw : List (GridCO.HeadWire n .root))
    (hslot : b.slot ≤ (v.now / (4 * q.Δ)).toNat) (hpar : b.parent ∈ v.blocks)
    (hb : b ∉ v.blocks) (hps : b.parent.slot < b.slot) (hs : s = b.slot) :
    GridCO.admitProposal q v ⟨.proposer s, w⟩ b raw =
      raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row))
        { v with
          blocks := v.blocks ++ [b]
          blockStamp := v.blockStamp ++ [(b, v.now)]
          proposals := v.proposals ++ [⟨.proposer s, w⟩] } := by
  unfold GridCO.admitProposal
  rw [ite_eq_right]
  simp only [gt_iff_lt, GridCO.blockKnown, hpar, hb, hps, hs, beq_self_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, Bool.not_eq_true',
    decide_eq_false_iff_not, not_true_eq_false, not_false_eq_true, Bool.not_true,
    Bool.false_eq_true, and_true, hslot]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp §4.3] The SA block admission accepts every block that the
composite
accepts: the block and its stamp are appended, the base wire is stored; `now`,
leases, saved results and S do not change. -/
theorem base_admitProposal_accepts (p : Params) (st : State p.n) (h : Inv0 p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true) :
    let base' := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
      N.support) N.erase
      (N.raw.map baseHead)
    base'.blocks = st.base.blocks ++ [N.erase] ∧
      base'.blockStamp = st.base.blockStamp ++ [(N.erase, st.base.now)] ∧
      base'.proposals = st.base.proposals ++ [baseProposal s N.erase N.raw N.support] ∧
      base'.obligations = st.base.obligations ∧ base'.genuine = st.base.genuine ∧
      base'.stableRecord = st.base.stableRecord ∧ base'.now = st.base.now := by
  intro base'
  obtain ⟨-, hsl, -, -, hps, hs⟩ := blockAccepted_facts hacc
  obtain ⟨-, -, hpar, hb⟩ := accepted_base_facts p st h hP hacc
  have he : base' = _ := admitProposal_of_accept p.toParams.engine st.base s _ N.erase
    (N.raw.map baseHead) hsl hpar hb hps hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := foldVotes_fields p.toParams.engine (N.raw.map baseHead)
    { st.base with
      blocks := st.base.blocks ++ [N.erase]
      blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
      proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }
  rw [he]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The accepted step -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `activeCompatible` as a function of F. -/
theorem activeCompatible_eq {n : Nat} (st : State n) :
    activeCompatible st = fun c => Block.compatible c (eraseFG st.fg.F) := rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The row fold changes only the row pool, and only by
appending. -/
theorem foldl_admitRow_eq (p : Params) (rows : List (RowWire p.n)) (X : State p.n) :
    ∃ pool, rows.foldl (admitRow p) X = { X with rowPool := pool } ∧ X.rowPool <+: pool := by
  induction rows generalizing X with
  | nil => exact ⟨X.rowPool, rfl, List.prefix_refl _⟩
  | cons a rows ih =>
      rw [List.foldl_cons]
      rcases admitRow_eq p X a with he | he
      · rw [he]
        exact ih X
      · rw [he]
        obtain ⟨pool, hp, hpre⟩ := ih { X with rowPool := X.rowPool ++ [a] }
        exact ⟨pool, hp, (List.prefix_append _ _).trans hpre⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [audit M4; Opus m2] The exact accepted step: the FG step, the
stored wire,
reconcile when F moves, and the row fold that changes only the row pool. -/
theorem admitBlock_accepted_eq (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hNamed : namedParentHeld st N = true)
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true) :
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
        N.support) N.erase
        (N.raw.map baseHead)
      fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
    let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
    ∃ pool, admitBlock p st s N = { st2 with rowPool := pool } ∧
      st2.rowPool <+: pool := by
  intro st1 st2
  unfold admitBlock
  rw [hP]
  simp only [hNamed, Bool.not_true, Bool.false_eq_true, ite_false, hacc, ite_true]
  exact foldl_admitRow_eq p N.rows st2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] An accepted block extends F: `F ⪯ P` for its stored
parent, so the
parent and the block are active. -/
theorem accepted_F_facts (p : Params) (st : State p.n) (h :
  Inv0 p st) {s : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P =
      true) :
    FGBlock.Preceq st.fg.F P ∧ Block.Preceq (eraseFG st.fg.F) N.erase.parent ∧
      Block.Preceq (eraseFG st.fg.F) N.erase := by
  obtain ⟨hg, -, hfr, hF, -, -⟩ := blockAccepted_facts hacc
  obtain ⟨hPT, hPe, -, -⟩ := accepted_base_facts p st h hP hacc
  have hne : st.fg.F ≠ fgBlock P N.erase N.rows := by
    intro he
    exact fgBlock_notMem st P N.erase N.rows hg hPe (blockAccepted_rowsOk hacc) hfr (he ▸ h.1.Fmem)
  have hFP : FGBlock.Preceq st.fg.F P := KitFG.preceq_parent_of_preceq_node hF hne
  have hFb' : Block.Preceq (eraseFG st.fg.F) N.erase.parent := by
    rw [← hPe]
    exact eraseFG_preceq hFP
  refine ⟨hFP, hFb', ?_⟩
  have := eraseFG_preceq hF
  rwa [eraseFG_fgBlock hg hPe N.rows (blockAccepted_rowsOk hacc)] at this

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The row fold keeps the active view and the FG store.
-/
theorem foldl_admitRow_view (p : Params) (rows : List (RowWire p.n)) (X : State p.n) :
    actView (rows.foldl (admitRow p) X) = actView X ∧ (rows.foldl (admitRow p) X).fg = X.fg := by
  obtain ⟨pool, hp, -⟩ := foldl_admitRow_eq p rows X
  rw [hp]
  exact ⟨rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA admission of an accepted block, on the base and
on the
active view, as the carried-vote fold over the same record with two block
lists. -/
theorem admitProposal_base_view (p : Params) (st : State p.n) (h : Inv0 p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true) :
    let W := (N.raw.map baseHead).foldl
      (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row))
      { st.base with
        blocks := st.base.blocks ++ [N.erase]
        blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
        proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }
    GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw N.support) N.erase
        (N.raw.map baseHead) = W ∧
      GridCO.admitProposal p.toParams.engine (actView st) (baseProposal s N.erase N.raw N.support)
        N.erase
        (N.raw.map baseHead) = { W with
          blocks := (actView st).blocks ++ [N.erase]
          headDomain := (actView st).headDomain } ∧
      W.blocks = st.base.blocks ++ [N.erase] := by
  intro W
  obtain ⟨-, hsl, -, -, hps, hs⟩ := blockAccepted_facts hacc
  obtain ⟨-, -, hpar, hb⟩ := accepted_base_facts p st h hP hacc
  obtain ⟨-, hFp, hFb⟩ := accepted_F_facts p st h hP hacc
  refine ⟨admitProposal_of_accept p.toParams.engine st.base s _ N.erase (N.raw.map baseHead) hsl
    hpar hb
    hps hs, ?_, (foldVotes_fields _ _ _).1⟩
  have hparv : N.erase.parent ∈ (actView st).blocks := by
    rw [actView_blocks, Block.Compatible, block_compatible_comm]
    exact ⟨hpar, block_compatible_of_preceq hFp⟩
  have hbv : N.erase ∉ (actView st).blocks := fun hv => hb ((actView_blocks st N.erase).1 hv).1
  have e := foldVotes_withBlocks p.toParams.engine (N.raw.map baseHead)
    { st.base with
      blocks := st.base.blocks ++ [N.erase]
      blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
      proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }
    ((actView st).blocks ++ [N.erase]) (actView st).headDomain
  exact (admitProposal_of_accept p.toParams.engine (actView st) s _ N.erase (N.raw.map baseHead) hsl
    hparv
    hbv hps hs).trans e

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp D3; Opus J3] A block delivery that does not move F is the
SA block
admission on the active view with updated resolution metadata. Carried rows change only the row
pool. -/
theorem actView_admitBlock_sameF (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hNamed : namedParentHeld st N = true)
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true)
    (hF : (admitBlock p st s N).fg.F = st.fg.F) :
    actView (admitBlock p st s N) =
      { GridCO.admitProposal p.toParams.engine (actView st) (baseProposal s N.erase N.raw N.support)
        N.erase
        (N.raw.map baseHead) with
        headDomain := some (st.base.headDomain.getD (st.base.blocks ++ [N.erase])) } := by
  have h0 : Inv0 p st := h.toInv0
  obtain ⟨hB, hV, hW⟩ := admitProposal_base_view p st h0 s N P hP hacc
  obtain ⟨-, -, hFb⟩ := accepted_F_facts p st h0 hP hacc
  unfold admitBlock at hF ⊢
  rw [hP] at hF ⊢
  simp only [hNamed, Bool.not_true, Bool.false_eq_true, ite_false, hacc, ite_true] at hF ⊢
  rw [(foldl_admitRow_view p N.rows _).1]
  rw [(foldl_admitRow_view p N.rows _).2] at hF
  split
  · next hc =>
    have hac : activeCompatible { st with
        base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
          N.support) N.erase
          (N.raw.map baseHead)
        fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
        proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } =
        activeCompatible st := by
      funext c
      simp only [activeCompatible]
      rw [hc]
    rw [hV]
    unfold actView
    rw [hac, hB, hW, List.filter_append]
    have hbok : activeCompatible st N.erase = true := by
      unfold activeCompatible
      rw [block_compatible_comm]
      exact block_compatible_of_preceq hFb
    simp only [List.filter_cons, List.filter_nil, hbok, ite_true]
    simp only [GridCO.resolutionTree]
    rw [foldVotes_headDomain, hW]
  · next hc =>
    rw [ite_eq_right hc, reconcile_fg] at hF
    exact absurd hF hc

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp D3; Opus J3] When F moves to `F'`, the view is the SA
admission on the
old view, with its blocks filtered by `F'` and reconcile's three writes
(`reconcile_obligations`, `reconcile_genuine`, `reconcile_stable`). -/
theorem actView_admitBlock_movedF (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hNamed : namedParentHeld st N = true)
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true)
    (hF : (admitBlock p st s N).fg.F ≠ st.fg.F) :
    let A := GridCO.admitProposal p.toParams.engine (actView st) (baseProposal s N.erase N.raw
      N.support) N.erase
      (N.raw.map baseHead)
    let st' := admitBlock p st s N
    let ok := fun c => Block.compatible c (eraseFG st'.fg.F)
    actView st' = { A with
      headDomain := some (st.base.headDomain.getD (st.base.blocks ++ [N.erase]))
      blocks := A.blocks.filter ok
      obligations := A.obligations.filter (fun row => ok row.1)
      genuine := A.genuine.map (fun row => (row.1, row.2.filter ok))
      stableRecord := if Block.preceq (eraseFG st'.fg.F) A.stableRecord then A.stableRecord
        else eraseFG st'.fg.F } := by
  have h0 : Inv0 p st := h.toInv0
  obtain ⟨hB, hV, hW⟩ := admitProposal_base_view p st h0 s N P hP hacc
  dsimp only
  unfold admitBlock at hF ⊢
  rw [hP] at hF ⊢
  simp only [hNamed, Bool.not_true, Bool.false_eq_true, ite_false, hacc, ite_true] at hF ⊢
  rw [(foldl_admitRow_view p N.rows _).1, (foldl_admitRow_view p N.rows _).2]
  rw [(foldl_admitRow_view p N.rows _).2] at hF
  split
  · next hc =>
    rw [ite_eq_left hc] at hF
    exact absurd hc hF
  · next hc =>
    have hmono : FGBlock.Preceq st.fg.F (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).F
      :=
      Window.window_on_block_F_mono p p.K_W st.fg (fgBlock P N.erase N.rows)
    rw [reconcile_fg, hV]
    rw [reconcile_eq]
    unfold actView
    simp only [activeCompatible_eq]
    rw [hB, hW, List.filter_append, List.filter_append, List.filter_filter]
    simp only [GridCO.resolutionTree]
    rw [foldVotes_headDomain]
    congr 2
    apply List.filter_congr
    intro c _
    cases hok : Block.compatible c
        (eraseFG (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).F) with
    | false => simp
    | true =>
        have hc0 : Block.compatible c (eraseFG st.fg.F) = true := by
          by_contra hn
          have hn' : ¬ Block.Compatible c (eraseFG st.fg.F) := hn
          exact block_incompatible_of_preceq hn' (eraseFG_preceq hmono) hok
        simp [hc0]

/-! ### Acceptance sufficiency (K8) -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.receiptCoverage.v1 §10.1; K8; DQ2; Opus m2] Acceptance
sufficiency: a
checked block with a stored parent, a slot that is not in the future, a fresh
root and `F ⪯ N.erase` is admitted. The blueprint premise is "absent"; the Lean
premise is the fresh root (DQ2). `admitBlock_sufficient_absent` takes the
blueprint premise with a root premise, as `rootTest_iff_blockTest` does. -/
theorem admitBlock_sufficient (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) (hNamed : namedParentHeld st N = true)
    (hwf : wellFormed p ⟨.proposer s, .proposal N⟩ = true)
    (hpar : N.erase.parent ∈ st.base.blocks) (hslot : N.erase.slot ≤ st.slot p)
    (hfresh : ∀ c ∈ st.base.blocks, c.root ≠ N.erase.root)
    (hF : Block.Preceq (eraseFG st.fg.F) N.erase)
    (hvalid : ∀ P, parentFG st N.erase = some P → rowsValidForParent p P N.erase.slot N.rows = true)
      :
    N.erase ∈ (process p st ⟨.proposer s, .proposal N⟩).base.blocks ∧
      ∃ P, parentFG st N.erase = some P ∧
        fgBlock P N.erase N.rows ∈ (process p st ⟨.proposer s, .proposal N⟩).fg.TF := by
  have h0 : Inv0 p st := h.toInv0
  have hg : N.erase ≠ .genesis := by
    intro hb
    simp [wellFormed, Wire.decode, hb] at hwf
  obtain ⟨P, hPT, hPe⟩ := (h.baseTree _).1 hpar
  have hP : parentFG st N.erase = some P := (parentFG_spec st N.erase P).2 ⟨hPT, hPe⟩
  have hfr : ¬ ∃ Y ∈ st.fg.TF, Y.root = N.erase.root := by
    rintro ⟨Y, hY, hr⟩
    exact hfresh _ ((h.baseTree _).2 ⟨Y, hY, rfl⟩) (by rw [eraseFG_root, hr])
  -- `F ⪯ fgBlock P N.erase N.rows`
  have hFm : eraseFG st.fg.F ∈ st.base.blocks := (h.baseTree _).2 ⟨_, h.fg.Fmem, rfl⟩
  have hFne : eraseFG st.fg.F ≠ N.erase := by
    intro he
    exact hfresh _ hFm (by rw [he])
  have hFpar : Block.Preceq (eraseFG st.fg.F) (eraseFG P) := by
    rw [hPe]
    generalize he : N.erase = b at hg hF hFne ⊢
    cases b with
    | genesis => exact absurd rfl hg
    | node q sl r_sl r =>
        simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hF
        rcases hF with hF | hF
        · exact absurd hF hFne
        · exact hF
  have hcl := h.fg.closed
  have hinj := viewRootInj_of_rootInj hcl h.rootInj
  have hFP : FGBlock.Preceq st.fg.F P :=
    preceq_of_eraseFG_preceq hinj ⟨_, h.fg.Fmem, KitFG.preceq_refl _⟩
      ⟨_, hPT, KitFG.preceq_refl _⟩ hFpar
  have hFB : FGBlock.Preceq st.fg.F (fgBlock P N.erase N.rows) :=
    KitFG.preceq_node_of_preceq _ _ _ _ hFP
  have hacc : blockAccepted p st s N P = true := by
    rw [blockAccepted_of_wellFormed p st s N P hwf]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨⟨⟨hslot, hfr⟩, hFB⟩, hvalid P hP⟩
  obtain ⟨pool, heq, -⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
  have hproc : process p st ⟨.proposer s, .proposal N⟩ =
      admitBlock p st s N := rfl
  obtain ⟨hbl, -⟩ := base_admitProposal_accepts p st h0 s N P hP hacc
  refine ⟨?_, P, hP, ?_⟩ <;> rw [hproc, heq] <;> dsimp only <;> split
  · rw [hbl]; exact List.mem_append_right _ (List.mem_singleton_self N.erase)
  · rw [(reconcile_frame _).2.2.2.1, hbl]; exact List.mem_append_right _ (List.mem_singleton_self
    N.erase)
  · rw [fg_on_block_accepts p st s N P hP hacc, Window.window_update_finality_TF]
    exact Finset.mem_insert_self _ _
  · rw [reconcile_fg, fg_on_block_accepts p st s N P hP hacc, Window.window_update_finality_TF]
    exact Finset.mem_insert_self _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.receiptCoverage.v1 §10.1; K8; DQ2; G10 m2]
`admitBlock_sufficient` with
the blueprint premise "absent" and a root premise on the base list and `N.erase` (the
premise of `rootTest_iff_blockTest`) in place of the fresh root. -/
theorem admitBlock_sufficient_absent (p : Params) (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (N : NamedProposal p.n) (hNamed : namedParentHeld st N = true)
    (hwf : wellFormed p ⟨.proposer s, .proposal N⟩ = true)
    (hpar : N.erase.parent ∈ st.base.blocks) (hslot : N.erase.slot ≤ st.slot p)
    (habs : N.erase ∉ st.base.blocks) (hinj : ∀ c ∈ st.base.blocks, c.root = N.erase.root → c =
      N.erase)
    (hF : Block.Preceq (eraseFG st.fg.F) N.erase)
    (hvalid : ∀ P, parentFG st N.erase = some P → rowsValidForParent p P N.erase.slot N.rows = true)
      :
    N.erase ∈ (process p st ⟨.proposer s, .proposal N⟩).base.blocks ∧
      ∃ P, parentFG st N.erase = some P ∧
        fgBlock P N.erase N.rows ∈ (process p st ⟨.proposer s, .proposal N⟩).fg.TF :=
  admitBlock_sufficient p st h s N hNamed hwf hpar hslot
    (fun c hc hr => habs (hinj c hc hr ▸ hc)) hF hvalid

end AvailableChain.FGSA
end
