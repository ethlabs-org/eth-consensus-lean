module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist
public import AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

private theorem consumer_parent_preceq (b : Block) : Block.Preceq b.parent b := by
  cases b <;> first | exact block_preceq_refl _ |
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944; H.6-S:1012–1029. Class (iii).
DC: INTENTIONAL; prior support is measured in the actual FG-SA proposer pool.
The witness keeps the supported target in the full source domain. -/
structure RetainedPriorSupport (p : Params) (src : State p.n) (s : Slot)
    (L : Block) : Prop where
  root_compatible : Block.Compatible (z p src) L
  witness : ∃ W ∈ src.fg.TF, Block.Preceq L (eraseFG W) ∧
    (controls p src).lo ≤ (heightView p W).h
  majority : GridCO.voterCount (proposerVotes src s) < 2 * ss src s L
  rivals : ∀ B, Block.compatible L B = false → ss src s B < ss src s L

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a stored height witness supplies the supported source path. -/
private theorem consumer_source_path (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (L W : FGBlock (Fin p.n)) (hW : W ∈ src.fg.TF)
    (hLW : FGBlock.Preceq L W) (hZL : FGBlock.Preceq (controls p src).Z L)
    (hlo : (controls p src).lo ≤ (heightView p W).h) : eraseFG L ∈ S p src := by
  have hFL : FGBlock.Preceq src.fg.F L := by
    have hFZ := fgsa_F_preceq_Z p src hs
    exact KitFG.preceq_trans hFZ hZL
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hW (eraseFG_preceq hLW)
  have hL : L ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨L, hL, rfl⟩,
    decide_eq_true ⟨L, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF L).mpr ⟨hL, hFL, hZL, W, hW, hLW, hlo⟩, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:937–942; H.6-S:1027–1029. Class (iii).
DC: INTENTIONAL; prior support covers a lease target from the ordinary root. -/
private theorem consumer_supported_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  let bare : State p.n := { src with base := { src.base with obligations := [] } }
  have ha : liveRoot p bare = z p src := by rfl
  have hpath : ∀ C, Block.Prec (liveRoot p bare) C → Block.Preceq C L →
      C ∈ S p src := by
    intro C hZC hCL
    obtain ⟨W, hW, hLW, hlo⟩ := h.witness
    obtain ⟨B, hB, heB⟩ := eraseFG_ancestor_mem hs.fg.closed hW
      (block_preceq_trans hCL hLW)
    rw [← heB]
    apply consumer_source_path p src hs B W hW
    · exact eraseFG_preceq_iff.mp (heB ▸ block_preceq_trans hCL hLW)
    · apply eraseFG_preceq_iff.mp
      rw [heB]
      exact (Bool.and_eq_true_iff.mp hZC).2
    · exact hlo
  have hc := fgsa_headInTree_covers_of_transfer p bare (S p src)
    (proposerVotes src s) (proposerSupport src s) L
    (ha ▸ h.root_compatible) hpath h.majority h.rivals
  exact hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a covered target needs no fresh support below the root. -/
private theorem consumer_prior_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : Block.Preceq L (z p src) ∨ RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  rcases h with h | h
  · apply walk_covers_of_dominated_suffix _ _ _ _ _ (Bool.or_eq_true_iff.mpr (Or.inr h))
    rw [DominatedSuffix_def]
    intro C hZC hCL
    have he := block_preceq_antisymm (Bool.and_eq_true_iff.mp hZC).2
      (block_preceq_trans hCL h)
    have hn := (Bool.and_eq_true_iff.mp hZC).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  · exact consumer_supported_cover p src hs s L h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.3:748–783; H.6:947–958. Class (iii).
DC: INTENTIONAL; H.3 gives the parent height from an internal source witness.
There is no bound on the bookkeeping pivot. -/
private theorem consumer_parent_height (p : Params) (src : State p.n)
    (hr : Reachable p src) (s : Slot) (A : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = A)
    (hw : ∃ W ∈ src.fg.TF, Block.Preceq (ap p src) (eraseFG W) ∧
      (controls p src).lo ≤ (heightView p W).h) :
    ∃ B ∈ src.fg.TF, eraseFG B = A ∧ (controls p src).lo ≤ (heightView p B).h := by
  have hs := (storeBundle_of_reachable p src hr).cstore
  have hclosed : ∀ B ∈ src.fg.TF, ∀ Q, FGBlock.Preceq Q B → Q ∈ src.fg.TF := by
    intro B hB Q hQB
    obtain ⟨R, hR, heR⟩ := eraseFG_ancestor_mem hs.fg.closed hB (eraseFG_preceq hQB)
    exact (eraseFG_injective heR) ▸ hR
  have hreach := (fgsa_headReachesLo p src src.fg.TF
    (proposerVotes src s) (proposerSupport src s) hr (fun _ h => h) hclosed).1
  rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hreach
  obtain ⟨W, hW, haW, hlo⟩ := hw
  obtain ⟨B, hB, heB⟩ := eraseFG_ancestor_mem hs.fg.closed hW haW
  have hm := consumer_source_path p src hs B W hW
    (eraseFG_preceq_iff.mp (heB ▸ haW))
    (eraseFG_preceq_iff.mp (heB ▸ fgsa_Z_preceq_liveRoot p src)) hlo
  obtain ⟨Q, hQ, heQ⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  obtain ⟨H, hH, heH, hh⟩ := hreach (Or.inl ⟨Q, hQ, heQ.trans heB⟩)
  refine ⟨H, ((KitFG.mem_filteredFromView (heightView p) (controls p src)
    src.fg.TF H).mp hH).1, heH.trans hp, ?_⟩
  simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] using hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.5:877–886; H.6:953–956. Class (iii).
DC: INTENTIONAL; common height witnesses give a unique child below the source root.
Scores need not be strict on this trunk. -/
private theorem consumer_trunk_prefix (p : Params) (src dst : State p.n) (s : Slot)
    (ht : CStoreInv p dst)
    (hpath : ∀ C, Block.Preceq (ay p dst) C → Block.Preceq C (z p src) → C ∈ T p dst s)
    (hhigh : ∀ W ∈ voterBlocks p dst s, (controls p dst).lo ≤ (heightView p W).h →
      Block.Preceq (z p src) (eraseFG W))
    (hlow : ∀ P ∈ dst.fg.TF, Block.Prec (eraseFG P) (z p src) →
      (heightView p P).h < (controls p dst).lo) :
    BestAncestry (ay p dst) (z p src) (T p dst s) (ts p dst s) (et p dst s) := by
  apply fgsa_retained_prefix_of_trunk_or_support
  intro X hAX hXZ
  have hne : X ≠ z p src := by
    intro he
    have hn := (Bool.and_eq_true_iff.mp hXZ).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  obtain ⟨C, hp, hCZ⟩ := path_child X (z p src) (Bool.and_eq_true_iff.mp hXZ).2 hne
  have hXC : Block.Preceq X C := by
    cases C with
    | genesis => cases hp
    | node P s root r =>
      have he := Option.some.inj hp
      subst P
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
  have hm := hpath C (block_preceq_trans hAX hXC) hCZ
  refine ⟨C, hp, hCZ, hm, ?_, Or.inl ?_⟩
  · obtain ⟨B, hB, heB, _, _, _⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hm
    have hP := ht.fg.closed B (Next.tree_subset_TF p dst (Finset.mem_filter.mp hB).1)
    have heP : eraseFG B.parent = X := by
      rw [← eraseFG_parent, heB, fgsa_parent_eq_of_some hp]
    have hh := hlow B.parent hP (heP ▸ hXZ)
    have hb : ∃ P ∈ dst.fg.TF, eraseFG P = C.parent ∧
        (heightView p P).h < (controls p dst).lo := ⟨B.parent, hP,
      heP.trans (fgsa_parent_eq_of_some hp).symm, hh⟩
    unfold et eligible
    simp only [hb, decide_true, Bool.true_or]
  · intro B hB hpB
    obtain ⟨Q, _, heQ, _, _, W, hW, hQW, hlo⟩ := fgsa_tree_domain_witness_of_mem p dst _ B hB
    have hBW : Block.Preceq B (eraseFG W) := heQ ▸ eraseFG_preceq hQW
    have hCW := block_preceq_trans hCZ (hhigh W hW hlo)
    have hd : B.depth = C.depth := by
      cases B with
      | genesis => cases hpB
      | node P t root i =>
        cases C with
        | genesis => cases hp
        | node Q u root j =>
          have hPQ : P = Q := (Option.some.inj hpB).trans (Option.some.inj hp).symm
          subst P
          rfl
    rcases block_preceq_total_of_common hBW hCW with h | h
    · exact prefix_eq_of_depth B C h (Nat.le_of_eq hd.symm)
    · exact (prefix_eq_of_depth C B h (Nat.le_of_eq hd)).symm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:947–952. Class (iii).
DC: INTENTIONAL; split the witness's own duty-view membership.
The current-path arm uses the source parent; the frozen arm keeps its stamp. -/
private theorem consumer_reflected_witness (p : Params) (src dst : State p.n)
    (s : Slot) (b : Block) (hslot : b.slot = s)
    (hfloor : (controls p src).lo = (controls p dst).lo)
    (hparent : ∃ A ∈ src.fg.TF, eraseFG A = b.parent ∧
      (controls p src).lo ≤ (heightView p A).h)
    (hunique : ∀ P ∈ dst.fg.TF, P.slot = s → eraseFG P = b)
    (C : Block) (hm : C ∈ T p dst s) (hold : C.slot < s) :
    ReflectedDomainWitness p src dst s C := by
  obtain ⟨B, hB, heB, _, _, W, hW, hBW, hlo⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hm
  have hBd := (Next.tree_subset_TF p dst (Finset.mem_filter.mp hB).1)
  have hWd := (Next.tree_subset_TF p dst (Finset.mem_filter.mp hW).1)
  rw [ReflectedDomainWitness_def]
  rcases Bool.or_eq_true_iff.mp (Finset.mem_filter.mp hW).2 with hf | hc
  · exact ⟨B, W, hBd, heB, hBW, hfloor ▸ hlo,
      Or.inr ⟨hWd, of_decide_eq_true hf⟩⟩
  · obtain ⟨P, hP, hsP, hWP⟩ := of_decide_eq_true hc
    have hCb : Block.Preceq C b := by
      rw [← heB, ← hunique P (Next.tree_subset_TF p dst hP) hsP]
      exact eraseFG_preceq (KitFG.preceq_trans hBW hWP)
    have hCA : Block.Preceq C b.parent := by
      cases b with
      | genesis =>
        change 0 = s at hslot
        exact (Nat.not_lt_zero _ (hslot.symm ▸ hold)).elim
      | node P u root i =>
        rcases Bool.or_eq_true_iff.mp hCb with he | hp
        · have he := of_decide_eq_true he
          have hbad : (Block.node P u root i).slot < s := he ▸ hold
          exact (Nat.lt_irrefl _ (hslot ▸ hbad)).elim
        · exact hp
    obtain ⟨A, hA, heA, hh⟩ := hparent
    exact ⟨B, A, hBd, heB, eraseFG_preceq_iff.mp (by rwa [heB, heA]), hh, Or.inl hA⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:884–907; H.6:955–956. Class (iii).
DC: INTENTIONAL; common candidate storage supplies the same immutable parent. -/
private theorem consumer_band_agrees (p : Params) (src dst : State p.n)
    (hs : CStoreInv p src) (ht : CStoreInv p dst) (s : Slot)
    (hfloor : (controls p src).lo = (controls p dst).lo)
    (C : Block) (hS : C ∈ S p src) (hT : C ∈ T p dst s) :
    retainedBand p src C ↔ retainedBand p dst C := by
  obtain ⟨B, hB, heB, _, _, _⟩ := fgsa_tree_domain_witness_of_mem p src src.fg.TF C hS
  obtain ⟨Q, hQ, heQ, _, _, _⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hT
  have he : Q = B := eraseFG_injective (heQ.trans heB.symm)
  subst Q
  have hb := fgsa_band_eq_of_same_floor p src dst C B.parent
    (hs.fg.closed B hB) (ht.fg.closed B (Next.tree_subset_TF p dst (Finset.mem_filter.mp hQ).1))
    (by rw [← eraseFG_parent, heB]) hfloor
  rw [retainedBand_def, retainedBand_def]
  simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] using hb

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.3:769–775; H.5:877–886; H.6:947–958. Class (iii).
DC: INTENTIONAL; fixed-phase frame facts retain the explicit source witness.
The two trunk facts apply only when the reader starts below the source root. -/
structure RetainedH6Frame (p : Params) (src dst : State p.n) (s : Slot) : Prop where
  floor_eq : (controls p src).lo = (controls p dst).lo
  source_witness : ∃ W ∈ src.fg.TF, Block.Preceq (ap p src) (eraseFG W) ∧
    (controls p src).lo ≤ (heightView p W).h
  lower_root : Block.Prec (ay p dst) (z p src) →
    ∀ W ∈ voterBlocks p dst s, (controls p dst).lo ≤ (heightView p W).h →
      Block.Preceq (z p src) (eraseFG W)
  lower_height : Block.Prec (ay p dst) (z p src) →
    ∀ P ∈ dst.fg.TF, Block.Prec (eraseFG P) (z p src) →
      (heightView p P).h < (controls p dst).lo

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:937–958; H.6-S:1027–1031. Class (iii).
DC: INTENTIONAL; one field producer serves both repair bounds.
The source root is an ancestry-only pivot; H.3 supplies its separate witness. -/
private theorem consumer_h6_fields (p : Params) (src dst : State p.n)
    (hr : Reachable p src) (ht : CStoreInv p dst) (s : Slot) (b : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent)
    (hslot : b.slot = s) (hadm : b ∈ dst.base.blocks)
    (hunique : ∀ P ∈ dst.fg.TF, P.slot = s → eraseFG P = b)
    (hsource : Block.Preceq (ap p src) (z p src) ∨
      RetainedPriorSupport p src s (ap p src))
    (htarget : Block.Preceq (ay p dst) (z p src) ∨
      RetainedPriorSupport p src s (ay p dst) ∨
      ∀ W ∈ src.fg.TF, (controls p src).lo ≤ (heightView p W).h →
        Block.Preceq (ay p dst) (eraseFG W))
    (hf : RetainedH6Frame p src dst s) :
    ∃ Kc, RetainedReadPremises p src dst s (controls p src).Z b Kc := by
  have hs := (storeBundle_of_reachable p src hr).cstore
  have hcover := consumer_prior_cover p src hs s (ap p src) hsource
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have hordinary := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hp
  have hheight := consumer_parent_height p src hr s b.parent hp hf.source_witness
  have hy : Block.Preceq (ay p dst) b.parent := by
    rcases htarget with h | h | h
    · exact (hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h))
    · exact (hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h))
    · obtain ⟨W, hW, heW, hh⟩ := hheight
      exact heW ▸ h W hW hh
  have hz := consumer_prior_cover p src hs s (z p src) (Or.inl (block_preceq_refl _))
  rw [hordinary] at hz
  have hw : ∃ W : FGBlock (Fin p.n),
      ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
      (controls p dst).lo ≤ (heightView p W).h := by
    obtain ⟨W, hW, heW, hh⟩ := hheight
    exact ⟨W, Or.inl ⟨hW, heW⟩, hf.floor_eq ▸ hh⟩
  have href := consumer_reflected_witness p src dst s b hslot hf.floor_eq hheight hunique
  have hband := consumer_band_agrees p src dst hs ht s hf.floor_eq
  by_cases hzy : Block.Preceq (z p src) (ay p dst)
  · refine ⟨ay p dst, hz, hprefix, hy, hzy, block_preceq_refl _, hy, ?_, hw,
      fun _ C _ _ hm _ hold _ => href C hm hold,
      fun _ C _ _ hS hT _ _ => hband C hS hT⟩
    intro X hAX hXA
    have he := block_preceq_antisymm hAX (Bool.and_eq_true_iff.mp hXA).2
    have hn := (Bool.and_eq_true_iff.mp hXA).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  · have hyz : Block.Preceq (ay p dst) (z p src) :=
      (block_preceq_total_of_common hy hz).resolve_right hzy
    have hlt : Block.Prec (ay p dst) (z p src) := by
      apply Bool.and_eq_true_iff.mpr
      refine ⟨?_, hyz⟩
      have hn : ay p dst ≠ z p src := by
        intro he
        exact hzy (he ▸ block_preceq_refl (ay p dst))
      simp only [hn, decide_false, Bool.not_false]
    refine ⟨z p src, hz, hprefix, hy, block_preceq_refl _, hyz, hz, ?_, hw,
      fun _ C _ _ hm _ hold _ => href C hm hold,
      fun _ C _ _ hS hT _ _ => hband C hS hT⟩
    apply consumer_trunk_prefix p src dst s ht _ (hf.lower_root hlt) (hf.lower_height hlt)
    intro C hAC hCZ
    exact fgsa_retained_path_mem p src dst ht.baseTree ht.fg.closed
      (F_preceq_liveRoot p dst ht) s b C hadm hslot hAC
      (block_preceq_trans hCZ (block_preceq_trans hz
        (by cases b <;> first | exact block_preceq_refl _ |
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))))) hw

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–958; H.3:769–775; H.5:877–886. Class (iii).
DC: INTENTIONAL; lane inputs use prior scores and frame witnesses, not walk outputs.
The final reader case is IF.3(c)'s high-block bound for a root covered by finality. -/
structure RetainedH6Input (p : Params) (src dst : State p.n) (s : Slot) : Prop where
  frame : RetainedH6Frame p src dst s
  proposer_prior : Block.Preceq (ap p src) (z p src) ∨
    RetainedPriorSupport p src s (ap p src)
  reader_prior : Block.Preceq (ay p dst) (z p src) ∨
    RetainedPriorSupport p src s (ay p dst) ∨
    ∀ W ∈ src.fg.TF, (controls p src).lo ≤ (heightView p W).h →
      Block.Preceq (ay p dst) (eraseFG W)

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:932–963; H.3:748–783; H.5:877–907. Class (iii).
DC: INTENTIONAL; H.4's prior support and fixed-phase frame facts supply all readers.
The lane input cites each upstream fact in RetainedH6Input and RetainedH6Frame.
Emission supplies the parent by fgsa_walkRun_proposal_parent. H.3 supplies height
by fgsa_headReachesLo. Admission uses fgsa_gateReceipt_block_to_tick, and current
paths use fgsa_walkRun_current_block_eq. Sleeping readers are included.
The pivot is the ordinary root; the cut is the deeper of that root and ay. -/
theorem fgsa_retainedReads_H6
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  intro y hy ih hih
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hheight := consumer_parent_height p src hr s N.erase.parent hparent.2.2.symm
    hi.frame.source_witness
  have hcover := consumer_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have hordinary := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hparent.2.2.symm
  have hay : Block.Preceq (ay p dst) N.erase.parent := by
    rcases hi.reader_prior with h | h | h
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h)
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h)
    · obtain ⟨W, hW, heW, hh⟩ := hheight
      exact heW ▸ h W hW hh
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hc, _⟩ := hSync
  have hd : dl (SA.proposalTime p.toParams s) ≤ SA.voteTime p.toParams s := by
    have hbound := hb (SA.proposalTime p.toParams s)
    rw [max_eq_left (by linarith [p.deltaPos]), hDelta] at hbound
    exact hbound.trans (by unfold SA.proposalTime SA.voteTime; ring_nf; rfl)
  have hF : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase := by
    have hbpar := fgsa_parent_preceq N.erase
    have hh := block_preceq_trans (F_preceq_liveRoot p dst ht) (block_preceq_trans hay hbpar)
    change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
    simpa only [dst, clock_fg] using hh
  have hadm := fgsa_gateReceipt_block_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD
    (SA.proposalTime p.toParams s)
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) N.erase rfl
    (Or.inl ⟨x, hx, ip, hip, hem⟩) (hlt _) (hd.trans hc) hy hih hd hF
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_h6_fields p src dst hr ht s N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi.proposer_prior hi.reader_prior hi.frame
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2980–3001; HG.1:1557–1565; L4-R:2280–2290. Class (iii).
DC: INTENTIONAL; earlier honest support gives a majority and smaller rival scores.
No target walk or current exact HEAD is assumed. -/
structure RetainedTargetScores (p : Params) (dst : State p.n) (s : Slot) (L : Block) : Prop where
  majority : GridCO.voterCount (headVotes p dst s) < 2 * ts p dst s L
  rivals : ∀ B, Block.compatible L B = false →
    2 * ts p dst s B ≤ GridCO.voterCount (headVotes p dst s)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2958–3005; HG.1:1522–1565; L4-R:2226–2290;
L2:2149–2162. Class (iii). DC: INTENTIONAL; prior support and separate floor bounds.
The pivot is T, Q, or J as specified by the lane. Neither live start is bounded by D.
The target scores are needed only strictly below a cut component. -/
structure RetainedConeInput (p : Params) (src dst : State p.n) (s : Slot)
    (D : FGBlock (Fin p.n)) : Prop where
  proposer_prior : Block.Preceq (ap p src) (z p src) ∨
    RetainedPriorSupport p src s (ap p src)
  reader_prior : Block.Preceq (ay p dst) (z p src) ∨
    RetainedPriorSupport p src s (ay p dst) ∨
    ∀ W ∈ src.fg.TF, (controls p src).lo ≤ (heightView p W).h →
      Block.Preceq (ay p dst) (eraseFG W)
  pivot_prior : Block.Preceq (eraseFG D) (z p src) ∨
    RetainedPriorSupport p src s (eraseFG D)
  source_floor : (controls p src).lo ≤ (heightView p D).h
  target_floor : (controls p dst).lo ≤ (heightView p D).h
  target_scores : ∀ L, L = z p src ∨ L = eraseFG D → Block.Prec (ay p dst) L →
    RetainedTargetScores p dst s L

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2976–2985; HG.1:1558–1561; L4-R:2253–2257;
L2-W:2080–2081. Class (iii). DC: INTENTIONAL; immutable state-height monotonicity. -/
private theorem consumer_height_mono (p : Params) {D B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG D) (eraseFG B)) : (heightView p D).h ≤ (heightView p B).h := by
  rw [(KitFG.heightBridge_fields p.E p.cfg (heightView p) (heightView_bridge p) D).1,
    (KitFG.heightBridge_fields p.E p.cfg (heightView p) (heightView_bridge p) B).1]
  exact KitFG.h_mono p.E p.cfg (eraseFG_preceq_iff.mp h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2968–2985; HG.1:1557–1565; L4-R:2280–2290;
L2:2159–2162. Class (iii). DC: INTENTIONAL; derive starts and parent height from prior support. -/
private theorem consumer_cone_starts (p : Params) (src dst : State p.n)
    (hs : CStoreInv p src) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent)
    (h : RetainedConeInput p src dst s D) :
    BestAncestry (z p src) (ap p src) (S p src) (ss src s) (es p src s) ∧
    Block.Preceq (z p src) b.parent ∧ Block.Preceq (ay p dst) b.parent ∧
    Block.Preceq (eraseFG D) b.parent ∧
    ∃ A ∈ src.fg.TF, eraseFG A = b.parent ∧
      (controls p src).lo ≤ (heightView p A).h ∧
      (controls p dst).lo ≤ (heightView p A).h := by
  have hc := consumer_prior_cover p src hs s (ap p src) h.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hc
  have ho := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hp
  have hz := consumer_prior_cover p src hs s (z p src) (Or.inl (block_preceq_refl _))
  have hD := consumer_prior_cover p src hs s (eraseFG D) h.pivot_prior
  rw [ho] at hz hD
  have hm : b.parent ∈ src.base.blocks := by
    rw [← hp]
    rcases fgsa_headInTree_mem_or_anchor p src (S p src)
      (proposerVotes src s) (proposerSupport src s) with he | hm
    · rw [show getHead p src (proposerVotes src s) (proposerSupport src s) = ap p src from he]
      exact liveRoot_stored p src hs
    · exact (List.mem_filter.mp hm).1
  obtain ⟨A, hA, heA⟩ := (hs.baseTree _).mp hm
  have hh := consumer_height_mono p (heA.symm ▸ hD)
  have haS := h.source_floor.trans hh
  have haT := h.target_floor.trans hh
  refine ⟨hprefix, hz, ?_, hD, A, hA, heA, haS, haT⟩
  rcases h.reader_prior with h | h | h
  · exact ho ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h)
  · exact ho ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h)
  · exact heA ▸ h A hA haS

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2983–3005; HG.1:1558–1565; L4-R:2253–2257.
Class (iii). DC: INTENTIONAL; every stored parent above D disables the band arm. -/
private theorem consumer_no_band (p : Params) (st : State p.n) (D : FGBlock (Fin p.n))
    (hlo : (controls p st).lo ≤ (heightView p D).h) (X C : Block)
    (hDX : Block.Preceq (eraseFG D) X) (hp : C.parent? = some X) :
    ¬ retainedBand p st C := by
  rw [retainedBand_def]
  rintro ⟨P, _, heP, hh⟩
  have he : eraseFG P = X := heP.trans (fgsa_parent_eq_of_some hp)
  exact Nat.not_lt_of_ge (hlo.trans (consumer_height_mono p (he.symm ▸ hDX))) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2987–3007; HG.1:1562–1565; L4-R:2288–2292;
L2:2159–2162. Class (iii). DC: INTENTIONAL; frozen cone children witness themselves.
An old child on the current proposal path uses the stored source parent instead. -/
private theorem consumer_cone_reflection (p : Params) (src dst : State p.n)
    (s : Slot) (D : FGBlock (Fin p.n)) (b : Block) (hslot : b.slot = s)
    (hlo : (controls p src).lo ≤ (heightView p D).h)
    (hparent : ∃ A ∈ src.fg.TF, eraseFG A = b.parent ∧
      (controls p src).lo ≤ (heightView p A).h)
    (hunique : ∀ P ∈ dst.fg.TF, P.slot = s → eraseFG P = b)
    (X C : Block) (hDX : Block.Preceq (eraseFG D) X) (hp : C.parent? = some X)
    (hm : C ∈ T p dst s) (hold : C.slot < s) : ReflectedDomainWitness p src dst s C := by
  obtain ⟨B, hB, heB, _, _, _⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hm
  have hBd := (Next.tree_subset_TF p dst (Finset.mem_filter.mp hB).1)
  rw [ReflectedDomainWitness_def]
  rcases Bool.or_eq_true_iff.mp (Finset.mem_filter.mp hB).2 with hf | hc
  · have hXC : Block.Preceq X C := by
      cases C with
      | genesis => cases hp
      | node P t root i =>
        have he := Option.some.inj hp
        subst P
        exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
    exact ⟨B, B, hBd, heB, KitFG.preceq_refl _,
      hlo.trans (consumer_height_mono p (heB.symm ▸ block_preceq_trans hDX hXC)),
      Or.inr ⟨hBd, of_decide_eq_true hf⟩⟩
  · obtain ⟨P, hP, hsP, hBP⟩ := of_decide_eq_true hc
    have hCb : Block.Preceq C b := by
      rw [← heB, ← hunique P (Next.tree_subset_TF p dst hP) hsP]
      exact eraseFG_preceq hBP
    have hCA : Block.Preceq C b.parent := by
      cases b with
      | genesis =>
        change 0 = s at hslot
        exact (Nat.not_lt_zero _ (hslot.symm ▸ hold)).elim
      | node P u root i =>
        rcases Bool.or_eq_true_iff.mp hCb with he | hp
        · have he := of_decide_eq_true he
          have hbad : (Block.node P u root i).slot < s := he ▸ hold
          exact (Nat.lt_irrefl _ (hslot ▸ hbad)).elim
        · exact hp
    obtain ⟨A, hA, heA, hh⟩ := hparent
    exact ⟨B, A, hBd, heB, eraseFG_preceq_iff.mp (by rwa [heB, heA]), hh, Or.inl hA⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2968–3007; HG.1:1557–1565; L4-R:2280–2292;
L2:2159–2162. Class (iii). DC: INTENTIONAL; one cone assembly at the deepest cut.
Raw target scores are used only for a nonempty prefix. -/
private theorem consumer_cone_fields (p : Params) (src dst : State p.n)
    (hs : CStoreInv p src) (ht : CStoreInv p dst) (s : Slot)
    (D : FGBlock (Fin p.n)) (b : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent)
    (hslot : b.slot = s) (hadm : b ∈ dst.base.blocks)
    (hunique : ∀ P ∈ dst.fg.TF, P.slot = s → eraseFG P = b)
    (h : RetainedConeInput p src dst s D) :
    ∃ Kc, RetainedReadPremises p src dst s D b Kc := by
  obtain ⟨hprefix, hz, hy, hD, A, hA, heA, haS, haT⟩ :=
    consumer_cone_starts p src dst hs s D b hp h
  let cuts : Finset Block := {z p src, ay p dst, eraseFG D}
  have hcA : ∀ C ∈ cuts, Block.Preceq C b.parent := by
    intro C hC
    rcases (show C = z p src ∨ C = ay p dst ∨ C = eraseFG D from by simpa [cuts] using hC)
      with rfl | rfl | rfl
    · exact hz
    · exact hy
    · exact hD
  obtain ⟨Kc, hKc, hdeep⟩ := deepest_of_compatible cuts ⟨z p src, by simp [cuts]⟩
    (fun X hX Y hY => block_compatible_of_common (hcA X hX) (hcA Y hY))
  have hzK := hdeep (z p src) (by simp [cuts])
  have hyK := hdeep (ay p dst) (by simp [cuts])
  have hDK := hdeep (eraseFG D) (by simp [cuts])
  have hKA := hcA Kc hKc
  have hw : ∃ W : FGBlock (Fin p.n),
      ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
      (controls p dst).lo ≤ (heightView p W).h := ⟨A, Or.inl ⟨hA, heA⟩, haT⟩
  refine ⟨Kc, hD, hprefix, hy, hzK, hyK, hKA, ?_, hw, ?_, ?_⟩
  · by_cases he : ay p dst = Kc
    · subst Kc
      intro X hAX hXA
      have he := block_preceq_antisymm hAX (Bool.and_eq_true_iff.mp hXA).2
      have hn := (Bool.and_eq_true_iff.mp hXA).1
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
    · have hlt : Block.Prec (ay p dst) Kc := by
        apply Bool.and_eq_true_iff.mpr
        exact ⟨by simp only [he, decide_false, Bool.not_false], hyK⟩
      have hwhich : Kc = z p src ∨ Kc = eraseFG D := by
        have hm : Kc = z p src ∨ Kc = ay p dst ∨ Kc = eraseFG D := by simpa [cuts] using hKc
        exact hm.elim Or.inl (fun h => h.elim (fun hy => (he hy.symm).elim) Or.inr)
      have hscore := h.target_scores Kc hwhich hlt
      apply walk_best_ancestry_of_cover
      refine fgsa_headInTree_covers_of_transfer p dst (T p dst s)
        (headVotes p dst s) (headSupport p dst s) Kc
        (Bool.or_eq_true_iff.mpr (Or.inl hyK)) ?_ hscore.majority ?_
      · intro C hAC hCK
        have hbpar := consumer_parent_preceq b
        exact fgsa_retained_path_mem p src dst ht.baseTree ht.fg.closed
          (F_preceq_liveRoot p dst ht) s b C hadm hslot (Bool.and_eq_true_iff.mp hAC).2
          (block_preceq_trans hCK (block_preceq_trans hKA hbpar)) hw
      · intro B hB
        have hm := hscore.majority
        have hr := hscore.rivals B hB
        change ts p dst s B < ts p dst s Kc
        omega
  · intro X C hKX _ hm hp hold _
    exact consumer_cone_reflection p src dst s D b hslot h.source_floor
      ⟨A, hA, heA, haS⟩ hunique X C (block_preceq_trans hDK hKX) hp hm hold
  · intro X C hKX _ _ _ hp _
    have hs := consumer_no_band p src D h.source_floor X C (block_preceq_trans hDK hKX) hp
    have ht := consumer_no_band p dst D h.target_floor X C (block_preceq_trans hDK hKX) hp
    exact ⟨fun hh => (hs hh).elim, fun hh => (ht hh).elim⟩

private theorem consumer_retainedReads_at
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (y : V) (hy : y ∈ rho.honest) (ih : Nat)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hstarts := consumer_cone_starts p src dst hs s D N.erase hparent.2.2.symm hi
  have hay := hstarts.2.2.1
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hc, _⟩ := hSync
  have hd : dl (SA.proposalTime p.toParams s) ≤ SA.voteTime p.toParams s := by
    have hbound := hb (SA.proposalTime p.toParams s)
    rw [max_eq_left (by linarith [p.deltaPos]), hDelta] at hbound
    exact hbound.trans (by unfold SA.proposalTime SA.voteTime; ring_nf; rfl)
  have hF : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase := by
    have hbpar := consumer_parent_preceq N.erase
    have hh := block_preceq_trans (F_preceq_liveRoot p dst ht) (block_preceq_trans hay hbpar)
    change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
    simpa only [dst, clock_fg] using hh
  have hadm := fgsa_gateReceipt_block_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD
    (SA.proposalTime p.toParams s)
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) N.erase rfl
    (Or.inl ⟨x, hx, ip, hip, hem⟩) (hlt _) (hd.trans hc) hy hih hd hF
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_cone_fields p src dst hs ht s D N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2958–3012. Class (iii).
DC: INTENTIONAL; instantiate the common cone fields at the paper's T.
Choose D = C* when the maximum compared H is M+1; otherwise choose the earlier
honest source body from a maximizing crossing (2968–2977). RetainedConeInput
contains the prior support and frame facts proved there. Both band arms are
false above the deepest of z, ay, and D. The high-F competitor has no majority
by target_scores, no band arm by its parent height, and no current-slot arm.
No premise bounds either live start by D. Sleeping honest readers are included. -/
theorem fgsa_retainedReads_H17
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  intro y hy ih hih
  exact consumer_retainedReads_at E rho hE hN hDelta s hSync hx hip hseat N hem D
    hinput hroots y hy ih hih

theorem fgsa_retainedReads_H6_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  intro y hy ih hih
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hheight := consumer_parent_height p src hr s N.erase.parent hparent.2.2.symm
    hi.frame.source_witness
  have hcover := consumer_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have hordinary := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hparent.2.2.symm
  have hay : Block.Preceq (ay p dst) N.erase.parent := by
    rcases hi.reader_prior with h | h | h
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h)
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h)
    · obtain ⟨W, hW, heW, hh⟩ := hheight
      exact heW ▸ h W hW hh
  have hadm := fgsa_target_receipt_at_tick_on E rho hE hy hih N.erase
    (hServices y hy ih hih) hroots
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_h6_fields p src dst hr ht s N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi.proposer_prior hi.reader_prior hi.frame
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

private theorem consumer_retainedReads_at_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (y : V) (hy : y ∈ rho.honest) (ih : Nat)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hstarts := consumer_cone_starts p src dst hs s D N.erase hparent.2.2.symm hi
  have hay := hstarts.2.2.1
  have hadm := fgsa_target_receipt_at_tick_on E rho hE hy hih N.erase
    (hServices y hy ih hih) hroots
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_cone_fields p src dst hs ht s D N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

theorem fgsa_retainedReads_H17_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  intro y hy ih hih
  exact consumer_retainedReads_at_on E rho hE s hx hip hseat N hem D
    hinput hServices hroots y hy ih hih

/-- The H6 geometry proves the receiver floor before proposal receipt is requested. -/
theorem fgsa_retainedH6_event_floor
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {ip ih : Nat} {x y : V}
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hi : RetainedH6Input p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s) :
    Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hheight := consumer_parent_height p src hr s N.erase.parent hparent.2.2.symm
    hi.frame.source_witness
  have hcover := consumer_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have hordinary := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hparent.2.2.symm
  have hay : Block.Preceq (ay p dst) N.erase.parent := by
    rcases hi.reader_prior with h | h | h
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h)
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h)
    · obtain ⟨W, hW, heW, hh⟩ := hheight
      exact heW ▸ h W hW hh
  have hh := block_preceq_trans (F_preceq_liveRoot p dst ht)
    (block_preceq_trans hay (fgsa_parent_preceq N.erase))
  change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
  simpa only [dst, clock_fg] using hh

/-- Monotonicity pulls the H6 floor back to the strict time read. -/
theorem fgsa_retainedH6_time_floor
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (mono : RMonoAll p c E rho)
    {s : Slot} {ip ih : Nat} {x y : V} (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hi : RetainedH6Input p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s) :
    Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.voteTime p.toParams s) y).st.fg.F) N.erase := by
  have hidx : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ ih := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff
      hE.toScheduleWellFormed hih _).mp hlt
    exact (lt_irrefl _ ht).elim
  have hf := (mono _ ih y hy hidx).1
  change FGBlock.Preceq (rho.stateBefore E (V2.D.Run.idxBefore rho
    (SA.voteTime p.toParams s)) y).st.fg.F (storeAt p c E rho ih y).fg.F at hf
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed] at hf
  exact block_preceq_trans (eraseFG_preceq hf)
    (fgsa_retainedH6_event_floor E rho hip N hem hi)

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_H6_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  intro y hy ih hih hjoined
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih hjoined
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hheight := consumer_parent_height p src hr s N.erase.parent hparent.2.2.symm
    hi.frame.source_witness
  have hcover := consumer_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have hordinary := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hparent.2.2.symm
  have hay : Block.Preceq (ay p dst) N.erase.parent := by
    rcases hi.reader_prior with h | h | h
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inl h)
    · exact hordinary ▸ consumer_prior_cover p src hs s (ay p dst) (Or.inr h)
    · obtain ⟨W, hW, heW, hh⟩ := hheight
      exact heW ▸ h W hW hh
  have hadm := fgsa_target_receipt_at_tick_on E rho hE hy hih N.erase
    (hServices y hy ih hih hjoined) hroots
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_h6_fields p src dst hr ht s N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi.proposer_prior hi.reader_prior hi.frame
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

/-- Joined reader form; service is required only for that reader. -/
private theorem consumer_retainedReads_at_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (y : V) (hy : y ∈ rho.honest) (ih : Nat)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hjoined : joinedAt p E rho y s (SA.voteTime p.toParams s)) :
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hi := hinput y hy ih hih hjoined
  have hr : Reachable p src := Reachable.tick _ (reachable_stateBefore E rho ip x)
  have hs := (storeBundle_of_reachable p src hr).cstore
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hslot := (fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2).1
  have hstarts := consumer_cone_starts p src dst hs s D N.erase hparent.2.2.symm hi
  have hay := hstarts.2.2.1
  have hadm := fgsa_target_receipt_at_tick_on E rho hE hy hih N.erase
    (hServices y hy ih hih hjoined) hroots
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  apply consumer_cone_fields p src dst hs ht s D N.erase hparent.2.2.symm hslot
    (by simpa only [dst, clock_base_blocks] using hadm') _
    hi
  intro P hP hsP
  apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem
  · have hb := (ht.baseTree _).mpr ⟨P, hP, rfl⟩
    simpa only [dst, clock_base_blocks] using hb
  · exact (eraseFG_slot P).trans hsP

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_H17_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  intro y hy ih hih hjoined
  exact consumer_retainedReads_at_joined E rho hE s hx hip hseat N hem D
    hinput hServices hroots y hy ih hih hjoined

end AvailableChain.FGSA.Run
end
