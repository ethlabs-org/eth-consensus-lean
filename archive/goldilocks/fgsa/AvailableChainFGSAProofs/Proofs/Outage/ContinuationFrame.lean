module
public import AvailableChainKitFG.StoreBounds
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; the scoped contest conclusion covers
all maximum-height carriers, including those that extend J. -/
theorem outageV_contest_top (p : Params) (st : State p.n) (B : FGBlock (Fin p.n))
    (hBJ : FGBlock.Preceq B (FGSA.controls p st).J)
    (hother : ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      ¬ FGBlock.Preceq (FGSA.controls p st).J W → FGBlock.Preceq B W) :
    ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      FGBlock.Preceq B W := by
  intro W hW hh
  by_cases hJ : FGBlock.Preceq (FGSA.controls p st).J W
  · exact preceq_trans hBJ hJ
  · exact hother W hW hh hJ

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; a contested filter over any subset
of the full store contains only blocks compatible with B. -/
theorem outageV_contested_filter (p : Params) (st : State p.n)
    (hinv : CStoreInv p st) (B : FGBlock (Fin p.n))
    (htop : ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      FGBlock.Preceq B W)
    (hcontest : (FGSA.controls p st).contest = true)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ st.fg.TF)
    {X : FGBlock (Fin p.n)}
    (hX : X ∈ KitFG.filteredFromView (heightView p) (FGSA.controls p st) view) :
    FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  obtain ⟨_, _, _, W, hW, hXW, hlo⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) view X).mp hX
  have he : (FGSA.controls p st).lo = (FGSA.controls p st).H := by
    change (if (FGSA.controls p st).contest then (FGSA.controls p st).H
      else (FGSA.controls p st).H - 1) = _
    rw [hcontest]
    rfl
  rw [he] at hlo
  have hhi := KitFG.store_height_le (heightView p) (finalityView p) st.fg hinv.fg (hview hW)
  have hh : (heightView p W).h = (FGSA.controls p st).H := Nat.le_antisymm hhi hlo
  exact preceq_total_of_common hXW (htop W (hview hW) hh)

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; a compatible entry at least as high
as a retained entry Q above B must itself extend B. -/
theorem outageV_entry_above (p : Params) {B Q X : FGBlock (Fin p.n)}
    (hBQ : FGBlock.Preceq B Q) (hQ : (heightView p Q).T_h = Q)
    (hX : (heightView p X).T_h = X) (hh : (heightView p Q).h ≤ (heightView p X).h)
    (hcompat : FGBlock.Preceq X B ∨ FGBlock.Preceq B X) :
    FGBlock.Preceq B X := by
  rcases hcompat with hXB | hBX
  · have hXQ := preceq_trans hXB hBQ
    have he := (fgCertificateLaws p).height.entry_plateau hXQ
      (Nat.le_antisymm ((fgCertificateLaws p).height.h_mono hXQ) hh)
    rw [hX, hQ] at he
    exact he.symm ▸ hBQ
  · exact hBX

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; every taller carrier extends B
when its crossed entries are compatible with B. Progress crossings suffice. -/
theorem outageV_taller_carrier (p : Params) {B Q W : FGBlock (Fin p.n)}
    (hBQ : FGBlock.Preceq B Q) (hQ : (heightView p Q).T_h = Q)
    (hh : (heightView p Q).h < (heightView p W).h)
    (hcross : ∀ U, FGBlock.Preceq U W → (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h) :
    FGBlock.Preceq B W := by
  have H := (fgCertificateLaws p).height
  obtain ⟨U, hUW, hU, _⟩ := H.height_crossing W (heightView p Q).h (H.one_le_h Q) hh
  have hBU := outageV_entry_above p hBQ hQ (H.entry_idem U)
    (by rw [H.entry_same_height, hU]) (hcross U hUW (hU ▸ hh))
  exact preceq_trans hBU (preceq_trans (H.entry_preceq U) hUW)

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; receipt of a carrier raises the
selected justified height when its entry remains above F. -/
theorem outageV_received_height (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {P : FGBlock (Fin p.n)} (hP : P ∈ st.fg.TF)
    (hFP : FGBlock.Preceq st.fg.F (heightView p P).J) :
    (heightView p P).h_j ≤ st.fg.h_j :=
  KitFG.fst_le_of_lexKey_le (hinv.fg.pair.2 P hP hFP)

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; a contest supplies an actual stored
carrier at height j+1 with a nonzero justified entry. -/
theorem outageV_contest_carrier (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    (ht : (FGSA.controls p st).contest = true) :
    st.fg.h_j ≠ 0 ∧ ∃ P ∈ st.fg.TF,
      (heightView p P).h_j = st.fg.h_j ∧ (heightView p P).J = st.fg.J ∧
      (heightView p P).h = st.fg.h_j + 1 := by
  change (decide (st.fg.h_max = st.fg.h_j + 1) &&
    decide (∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
      (heightView p W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W)) = true at ht
  obtain ⟨htop, W, _, _, _, hnW⟩ :=
    (show st.fg.h_max = st.fg.h_j + 1 ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
        (heightView p W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht)
  obtain ⟨P, hP, _, hj, hJ⟩ := hinv.fg.pair.1
  have hn : st.fg.h_j ≠ 0 := by
    intro hz
    have hzero := (fgJustificationLaws p).J_zero P (hj.symm.trans hz)
    exact hnW ((hJ.trans hzero).symm ▸ genesis_preceq W)
  refine ⟨hn, P, hP, hj.symm, hJ.symm, ?_⟩
  have hlo := (fgCertificateLaws p).height.justified_below_height P
  have hhi := store_height_le (heightView p) (finalityView p) st.fg hinv.fg hP
  rw [← hj] at hlo
  rw [htop] at hhi
  change (_ : Nat) < _ at hlo
  change (_ : Nat) ≤ _ at hhi
  change (_ : Nat) = _
  omega

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; after the marker is received,
either the FG root covers B or every filtered block is compatible with B.
The view may be any subset of the cumulative store. -/
theorem outageV_marker_frame (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B Q : FGBlock (Fin p.n)} (hBQ : FGBlock.Preceq B Q)
    (hQ : (heightView p Q).T_h = Q) (hmark : (heightView p Q).h ≤ st.fg.h_j)
    (hJcomp : FGBlock.Preceq st.fg.J B ∨ FGBlock.Preceq B st.fg.J)
    (htop : (FGSA.controls p st).contest = true →
      ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H → FGBlock.Preceq B W)
    (hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ st.fg.TF) :
    FGBlock.Preceq B (FGSA.controls p st).Z ∨
      ∀ X ∈ KitFG.filteredFromView (heightView p) (FGSA.controls p st) view,
        FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  by_cases ht : (FGSA.controls p st).contest = true
  · exact Or.inr (fun _ hX => outageV_contested_filter p st hinv B (htop ht) ht view hview hX)
  have hn : (FGSA.controls p st).contest = false := Bool.eq_false_iff.mpr ht
  by_cases hnext : st.fg.h_max = st.fg.h_j + 1
  · obtain ⟨P, _, _, hheight, hentry⟩ := hinv.fg.pair.1
    have hnonzero : (heightView p P).h_j ≠ 0 := by
      have hpos := (fgCertificateLaws p).height.one_le_h Q
      change (1 : Nat) ≤ _ at hpos
      change (_ : Nat) ≤ _ at hmark
      change (_ : Nat) = _ at hheight
      change (_ : Nat) ≠ 0
      omega
    have hJ : (heightView p st.fg.J).T_h = st.fg.J := by
      rw [hentry]
      exact (fgJustificationLaws p).J_entry P
    have hhJ : (heightView p st.fg.J).h = st.fg.h_j := by
      rw [hentry, (fgJustificationLaws p).J_height P hnonzero]
      exact hheight.symm
    have hBJ := outageV_entry_above p hBQ hQ hJ (hhJ.symm ▸ hmark) hJcomp
    have hr : (FGSA.controls p st).rootIsJ = true := by
      change (decide (st.fg.h_max = st.fg.h_j + 1) && !(FGSA.controls p st).contest) = true
      simp only [hnext, hn, decide_true, Bool.not_false, Bool.and_self]
    left
    change FGBlock.Preceq B
      (if (FGSA.controls p st).rootIsJ then st.fg.J else st.fg.F)
    rw [hr]
    exact hBJ
  · right
    intro X hX
    obtain ⟨_, _, _, W, hW, hXW, hlo⟩ :=
      (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) view X).mp hX
    have hfloor : (FGSA.controls p st).lo = st.fg.h_max - 1 := by
      change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) = _
      rw [hn]
      rfl
    rw [hfloor] at hlo
    have hlt := KitFG.store_justified_lt p.E (heightView p) (finalityView p)
      (fgCertificateLaws p) st.fg hinv.fg
    have hhigh : (heightView p Q).h < (heightView p W).h := by
      change (_ : Nat) < _ at hlt ⊢
      change (_ : Nat) ≤ _ at hlo hmark
      change ¬ ((_ : Nat) = _) at hnext
      omega
    exact preceq_total_of_common hXW
      (outageV_taller_carrier p hBQ hQ hhigh (hcross W (hview hW)))

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; instantiate the subset result at
an actual honest event cut from scoped original row provenance. -/
theorem outageV_contested_frame_from_rows {p : Params} {In V : Type}
    [DecidableEq V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hstore : RStore p c E rho)
    (hframe : RFrameExactNext p c E rho) (hstrat : RStrat p c E rho)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (hx : x ∈ rho.honest)
    (hrows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) →
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e)
    (hcontest : (R_at p c E rho i x).contest = true)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ (storeAt p c E rho i x).fg.TF)
    {X : FGBlock (Fin p.n)}
    (hX : X ∈ KitFG.filteredFromView (heightView p) (R_at p c E rho i x) view) :
    FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  have _hcanonicalFrame := hframe
  have hc := (fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat i x B hx hrows).2.2.2.2
    hcontest
  exact outageV_contested_filter p (storeAt p c E rho i x) (hstore i x hx).1 B
    (outageV_contest_top p _ B hc.1 hc.2) hcontest view hview hX

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; the actual voter filter retains
path vertices with a frozen height witness. The majority and rival bounds
then instantiate the dominated walk. -/
theorem outageV_head_covers_of_witnesses (p : Params) (st : State p.n)
    (hinv : CStoreInv p st) (B : Block) {s : Slot} (hs : s ≠ 0)
    (hroot : Block.Compatible (liveRoot p st) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      ∃ X ∈ voterBlocks p st s, eraseFG X = C ∧
        ∃ W ∈ voterBlocks p st s, FGBlock.Preceq X W ∧
          (controls p st).lo ≤ (heightView p W).h)
    (hmaj : GridCO.voterCount (headVotes p st s) <
      2 * GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) B)
    (hdom : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) D <
        GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s) B) :
    Block.Preceq B (headVote p st s) := by
  change Block.Preceq B (if s = 0 then .genesis else headInTree p st _ _ _)
  rw [ite_eq_right hs]
  apply fgsa_headInTree_covers_of_transfer p st _ _ _ B hroot ?_ hmaj hdom
  intro C hAC hCB
  obtain ⟨X, hX, heX, W, hW, hXW, hlo⟩ := hpath C hAC hCB
  have hAC' : Block.Preceq (liveRoot p st) C := (Bool.and_eq_true_iff.mp hAC).2
  have hFX := eraseFG_preceq_iff.mp (heX ▸ block_preceq_trans
    (F_preceq_liveRoot p st hinv) hAC')
  have hZX := eraseFG_preceq_iff.mp (heX ▸ block_preceq_trans
    (fgsa_Z_preceq_liveRoot p st) hAC')
  apply List.mem_filter.mpr
  refine ⟨(hinv.baseTree C).mpr ⟨X, (Finset.mem_filter.mp (Finset.mem_filter.mp hX).1).1, heX⟩, ?_⟩
  exact decide_eq_true ⟨X, (mem_filteredFromView (heightView p) (controls p st)
    (voterBlocks p st s) X).mpr ⟨hX, hFX, hZX, W, hW, hXW, hlo⟩, heX⟩

/-- OUTPUT-DIRECT §§2,4. DC: INTENTIONAL; selection among a compatible
frame root and compatible live locks gives a compatible live root. -/
theorem outageV_liveRoot_compatible (p : Params) (st : State p.n) (B : Block)
    (hZ : Block.Compatible (eraseFG (controls p st).Z) B)
    (hlocks : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 B) : Block.Compatible (liveRoot p st) B := by
  rcases foldl_select_mem (fun (a b : Block) =>
    a.depth < b.depth || (a.depth == b.depth && a.root < b.root))
    (st.base.obligations.filterMap (fun row =>
      if st.base.now < row.2.2 && decide (∃ X ∈ fullTree p st, eraseFG X = row.1)
      then some row.1 else none)) (eraseFG (controls p st).Z) with he | hm
  · change liveRoot p st = _ at he
    rw [he]
    exact hZ
  · obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hm
    split at he
    · next ht =>
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp ht).1
      have he' : row.1 = liveRoot p st := Option.some.inj he
      rw [← he']
      exact hlocks row hr hl
    · cases he

/-- OUTPUT-DIRECT §§4,5. DC: INTENTIONAL; the actual walk either returns
its live root or a member of its filtered tree. -/
theorem outageV_headInTree_compatible (p : Params) (st : State p.n)
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hroot : Block.Compatible (liveRoot p st) B)
    (htree : ∀ X ∈ tree, Block.Compatible X B) :
    Block.Compatible (headInTree p st tree raw support) B := by
  rcases fgsa_headInTree_mem_or_anchor p st tree raw support with he | hm
  · rw [he]; exact hroot
  · exact htree _ hm

/-- OUTPUT-DIRECT §§4,5. DC: INTENTIONAL; connect filter compatibility
to the scheduled HEAD, including its genesis branch. -/
theorem outageV_head_of_filter (p : Params) (st : State p.n) (B : FGBlock (Fin p.n))
    (s : Slot) (hroot : Block.Compatible (liveRoot p st) (eraseFG B))
    (htree : ∀ X ∈ filteredFromView (heightView p) (controls p st) (voterBlocks p st s),
      FGBlock.Preceq X B ∨ FGBlock.Preceq B X) :
    Block.Compatible (headVote p st s) (eraseFG B) := by
  change Block.Compatible (if s = 0 then .genesis else headInTree p st _ _ _) _
  split
  · exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
  · apply outageV_headInTree_compatible p st _ _ _ _ hroot
    intro X hX
    obtain ⟨Y, hY, heY⟩ := of_decide_eq_true (List.mem_filter.mp hX).2
    rw [← heY]
    rcases htree Y hY with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (eraseFG_preceq h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq h))

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; a contested scheduled HEAD
is compatible with B for every score and every voter view. -/
theorem outageV_contested_head (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    (B : FGBlock (Fin p.n)) (s : Slot)
    (hroot : Block.Compatible (liveRoot p st) (eraseFG B))
    (htop : ∀ W ∈ st.fg.TF, (heightView p W).h = (controls p st).H → FGBlock.Preceq B W)
    (ht : (controls p st).contest = true) :
    Block.Compatible (headVote p st s) (eraseFG B) :=
  outageV_head_of_filter p st B s hroot (fun _ hX =>
    outageV_contested_filter p st hinv B htop ht _
      (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) hX)

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; the retained marker protects
all later scheduled HEAD reads, including an empty filtered view. -/
theorem outageV_marker_head (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B Q : FGBlock (Fin p.n)} (s : Slot)
    (hroot : Block.Compatible (liveRoot p st) (eraseFG B))
    (hBQ : FGBlock.Preceq B Q) (hQ : (heightView p Q).T_h = Q)
    (hmark : (heightView p Q).h ≤ st.fg.h_j)
    (hJcomp : FGBlock.Preceq st.fg.J B ∨ FGBlock.Preceq B st.fg.J)
    (htop : (controls p st).contest = true →
      ∀ W ∈ st.fg.TF, (heightView p W).h = (controls p st).H → FGBlock.Preceq B W)
    (hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h) :
    Block.Compatible (headVote p st s) (eraseFG B) := by
  rcases outageV_marker_frame p st hinv hBQ hQ hmark hJcomp htop hcross
    (voterBlocks p st s)
    (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) with hZ | htree
  · by_cases hs : s = 0
    · rw [hs, headVote_zero]
      exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
    · have hBroot := block_preceq_trans (eraseFG_preceq hZ) (fgsa_Z_preceq_liveRoot p st)
      have hh : Block.Preceq (eraseFG B) (headVote p st s) := by
        change Block.Preceq _ (if s = 0 then .genesis else headInTree p st _ _ _)
        rw [ite_eq_right hs]
        exact block_preceq_trans hBroot (liveRoot_preceq_headInTree p st _ _ _)
      exact Bool.or_eq_true_iff.mpr (Or.inr hh)
  · exact outageV_head_of_filter p st B s hroot htree

/-- OUTPUT-DIRECT §§4,5. DC: INTENTIONAL; at a real event cut, scoped
row history supplies the frame and crossing facts used by the actual HEAD.
A contest or a received marker is sufficient. Live locks remain explicit. -/
theorem outageV_head_from_rows {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hstrat : RStrat p c E rho) (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (s : Slot) (hx : x ∈ rho.honest)
    (hrows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) →
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e)
    (hlocks : ∀ row ∈ (storeAt p c E rho i x).base.obligations,
      (storeAt p c E rho i x).base.now < row.2.2 → Block.Compatible row.1 (eraseFG B))
    (hprotect : (R_at p c E rho i x).contest = true ∨
      ∃ Q, FGBlock.Preceq B Q ∧ (heightView p Q).T_h = Q ∧
        (heightView p Q).h ≤ (storeAt p c E rho i x).fg.h_j) :
    Block.Compatible (headVote p (storeAt p c E rho i x) s) (eraseFG B) := by
  have _hcanonicalFrame := hframe
  let st := storeAt p c E rho i x
  have hc := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat i x B hx hrows
  have htop : (controls p st).contest = true →
      ∀ W ∈ st.fg.TF, (heightView p W).h = (controls p st).H → FGBlock.Preceq B W := by
    intro ht
    have h := hc.2.2.2.2 ht
    exact outageV_contest_top p st B h.1 h.2
  have hZ : Block.Compatible (eraseFG (controls p st).Z) (eraseFG B) := by
    have hZfg : FGBlock.Preceq (controls p st).Z B ∨ FGBlock.Preceq B (controls p st).Z := by
      change FGBlock.Preceq (if (controls p st).rootIsJ then st.fg.J else st.fg.F) B ∨
        FGBlock.Preceq B (if (controls p st).rootIsJ then st.fg.J else st.fg.F)
      cases h : (controls p st).rootIsJ
      · exact hc.2.1
      · exact hc.2.2.1
    exact Bool.or_eq_true_iff.mpr (hZfg.imp eraseFG_preceq eraseFG_preceq)
  have hroot := outageV_liveRoot_compatible p st (eraseFG B) hZ hlocks
  rcases hprotect with ht | ⟨Q, hBQ, hQ, hmark⟩
  · exact outageV_contested_head p st (hstore i x hx).1 B s hroot (htop ht) ht
  · apply outageV_marker_head p st (hstore i x hx).1 s hroot hBQ hQ hmark hc.2.2.1 htop
    intro W hW U hUW hh
    apply hc.1 W hW
    rw [certified_def]
    exact ⟨U, hUW, Or.inr (Or.inr ⟨rfl, hh⟩)⟩


/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; previous covering honest HEADs
in the actual merged support pool supply both the raw-denominator majority
and strict rival bound. Only the frozen path witnesses remain separate. -/
theorem outageV_head_covers_from_batch {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot) (B : Block)
    {i : Nat} {y : V}
    (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card)
    (hroot : Block.Compatible
      (liveRoot p (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1)))) B)
    (hpath : ∀ C, Block.Prec
        (liveRoot p (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1)))) C →
      Block.Preceq C B → ∃ X ∈ voterBlocks p
        (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))) (r + 1),
      eraseFG X = C ∧ ∃ W ∈ voterBlocks p
        (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))) (r + 1),
      FGBlock.Preceq X W ∧
        (controls p (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1)))).lo ≤
          (heightView p W).h)
    (hheads : ∀ q, rho.seatOf (.base (.head r)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true →
      ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq B K) :
    Block.Preceq B (headVote p
      (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))) (r + 1)) := by
  obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hC r ⟨hpart⟩
  have hscores := inclusion_reader_scores E rho hE hN hC r hi H hH hbatch B
    (fun q hq => hheads q ((hH q).mp hq).1 ((hH q).mp hq).2) B (block_preceq_refl B)
  apply outageV_head_covers_of_witnesses p _
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i y) _) B (Nat.succ_ne_zero r)
    hroot hpath hscores.majority
  intro D hD
  let dst := clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (r + 1))
  have h₁ := hscores.rivals D hD
  have h₂ := hscores.majority
  change 2 * RetainedWalk.ts p dst (r + 1) D ≤ _ at h₁
  change _ < 2 * RetainedWalk.ts p dst (r + 1) B at h₂
  change RetainedWalk.ts p dst (r + 1) D < RetainedWalk.ts p dst (r + 1) B
  omega

end AvailableChain.FGSA.Run
end
