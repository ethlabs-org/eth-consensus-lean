module
public import AvailableChainFGSA.Proofs.StoreLaws -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainGeneric.Proofs.AC.RootSupport
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a:4857–4859; bp02 §4.1. Class (iii), store instance.
DC: Adoption.goldfish_fork_choice_captures_supporter_majority:415.
INTENTIONAL: liveRoot and FJ eligibility replace the SG controls;
P3:4845–4853 fixes these arguments. The keep supplier is a parameter (M6). -/
theorem fgsa_getHead_covers_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (fullTree p st))
    (helig : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      eligible p st raw support C = true)
    (hdom : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      ∀ D ∈ erasedList st (fullTree p st), D.parent? = C.parent? →
        eligible p st raw support D = true → D ≠ C →
        GridCO.goldfishScore st.base.blocks raw support D <
          GridCO.goldfishScore st.base.blocks raw support C) :
    Block.Preceq B (getHead p st raw support) := by
  apply walk_covers_of_dominated_suffix _ _ _ _ _ hanchor
  rw [DominatedSuffix_def]
  exact fun C hac hcb => ⟨hkeep C hac hcb, helig C hac hcb, hdom C hac hcb⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a W3:4860–4863; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_reaches:433 and Walk.ghost_step_none:197.
INTENTIONAL: the dominated suffix packages DC's selected path; the
terminal target remains a premise, as required by P3 W3. -/
theorem fgsa_getHead_exact_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hanchor : Block.Preceq (liveRoot p st) B)
    (hkeep : DominatedSuffix (liveRoot p st) B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support))
    (hstop : NoEligibleChild (erasedList st (fullTree p st)) (eligible p st raw support) B) :
    getHead p st raw support = B :=
  walk_exact_of_dominated_suffix _ _ _ _ _ hanchor hkeep hstop

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a W6:4864–4867; bp02 §4.1. Class (iii), store instance.
DC: no same-view DC reanchor lemma; nearest: Walk.lean:433.
INTENTIONAL: P3 W6 fixes one view and moves its anchor along the dominated
suffix. No cross-view fact follows from this equality. -/
theorem fgsa_getHead_reanchor_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hanchor : Block.Preceq (liveRoot p st) B)
    (hkeep : DominatedSuffix (liveRoot p st) B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) :
    getHead p st raw support = GridCO.ghost B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support) :=
  walk_reanchor_of_dominated_suffix _ _ _ _ _ hanchor hkeep

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a:4878–4881; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_step_child:184 and Walk.ghost_eligible:281 (path ingredients).
INTENTIONAL: FJ has three eligibility arms; P3 requires exclusion of
all three, including the low-parent and current-slot arms. -/
theorem fgsa_getHead_avoids_unsupported_child
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) (B C : Block)
    (hanchor : Block.Preceq (liveRoot p st) B) (hparent : C.parent? = some B)
    (hfloor : ¬ ∃ P ∈ st.fg.TF, eraseFG P = C.parent ∧
      hOf p.E p.cfg P < (controls p st).lo)
    (hscore : 2 * GridCO.goldfishScore st.base.blocks raw support C ≤ GridCO.voterCount raw)
    (hslot : C.slot ≠ st.slot p) : ¬ Block.Preceq C (getHead p st raw support) := by
  apply walk_avoids_unsupported_child _ B _ _ _ _ hanchor hparent
  rw [fgsa_eligible_eq]
  simp only [hfloor, decide_false, Nat.not_lt.mpr hscore, Bool.false_or,
    beq_eq_false_iff_ne.mpr hslot]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] Class (iii), pivot composition. DC: Goldfish/Walk.lean:433
`ghost_reaches`.
INTENTIONAL: S1b E1 permits either start order; E2 supplies the prefix below T.
E3/E5 supply target ancestry, with E4 score/root order (bp21:789,2798–2825).
The target read is arbitrary, so E1 is required separately for each compared read.
ROOT-DIGEST W1c: require root uniqueness on the arbitrary walked tree. -/
theorem fgsa_headInTree_reanchor_of_pivot
    (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) (T P : Block)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B)
    (hstart : (Block.Preceq (liveRoot p st) T ∧
      DominatedSuffix (liveRoot p st) T tree
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) ∨
      (Block.Preceq T (liveRoot p st) ∧ Block.Preceq (liveRoot p st) P))
    (hTP : Block.Preceq T P)
    (hancestry : ∀ X, Block.Preceq T X → Block.Preceq (liveRoot p st) X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧ C ∈ tree ∧
        eligible p st raw support C = true ∧
        ∀ D ∈ tree, D.parent? = some X → eligible p st raw support D = true →
          GridCO.goldfishScore st.base.blocks raw support D ≤
            GridCO.goldfishScore st.base.blocks raw support C ∧
          (GridCO.goldfishScore st.base.blocks raw support D =
            GridCO.goldfishScore st.base.blocks raw support C → D.root ≤ C.root)) :
    headInTree p st tree raw support = GridCO.ghost P tree
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support) := by
  change GridCO.ghost (liveRoot p st) _ _ _ = _
  rcases hstart with ⟨hAT, hprefix⟩ | ⟨hTA, hAP⟩
  · rw [walk_reanchor_of_dominated_suffix _ _ _ _ _ hAT hprefix]
    exact walk_reanchor_of_best_ancestry _ _ _ _ _ hroot hTP
      (fun X hTX => hancestry X hTX (block_preceq_trans hAT hTX))
  · exact walk_reanchor_of_best_ancestry _ _ _ _ _ hroot hAP
      (fun X hAX => hancestry X (block_preceq_trans hTA hAX) hAX)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a W8:4868–4874; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_reaches:433; GSTZeroPreparedWalk.
preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero:546 (genuine test).
INTENTIONAL: the F-anchored optional result tests its final block. At the
anchor, eligibility is an explicit premise; a strict suffix supplies it (P3 W8). -/
theorem fgsa_confirmationFrom_exact_of_dominated_suffix
    (p : Params) (v : GridCO.State p.n .root) (a B : Block) (s : Slot)
    (hanchor : Block.Preceq a B)
    (hkeep : DominatedSuffix a B v.blocks (SA.Root.prefixSupport p.toParams v s)
      (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s C)))
    (hstop : NoEligibleChild v.blocks
      (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s C)) B)
    (helig : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∨ Block.Prec a B) :
    SA.Root.confirmationFrom p.toParams a v s = some B := by
  have hexact := walk_exact_of_dominated_suffix _ _ _ _ _ hanchor hkeep hstop
  have hb : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B := by
    rcases helig with ha | hab
    · by_cases he : a = B
      · simpa only [← he] using ha
      · have hab : Block.Prec a B := by
          change ((!decide (a = B)) && Block.preceq a B) = true
          simp only [he, decide_false, Bool.not_false, Bool.true_and]
          exact hanchor
        exact of_decide_eq_true (hkeep B hab (block_preceq_refl B)).2.1
    · exact of_decide_eq_true (hkeep B hab (block_preceq_refl B)).2.1
  change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s
        (GridCO.ghost a v.blocks (SA.Root.prefixSupport p.toParams v s)
          (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
            2 * SA.Root.prefixSupport p.toParams v s C))) then
      some (GridCO.ghost a v.blocks (SA.Root.prefixSupport p.toParams v s)
        (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
          2 * SA.Root.prefixSupport p.toParams v s C))) else none) = some B
  rw [hexact]
  exact ite_eq_left hb

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.4a and F2.3; bp02 §4.1–4.2. Class (iii), store instance.
DC: Adoption.goldfish_fork_choice_captures_supporter_majority:415 and
Adoption.goldfish_fork_choice_captures_of_confirmation:441.
INTENTIONAL: FJ eligibility and liveRoot replace SG controls (P3:4845–4853).
GridCO goldfishScore counts each equivocator in every subtree
(GridCO/Model/Protocol.lean:147–149). Thus score majority does not supply
the rival bound; hdominance is a separate premise.
This is the common store proof for transfer and batch callers; suffix
membership is supplied as a parameter (M6). -/
theorem fgsa_headInTree_covers_of_transfer
    (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B → C ∈ tree)
    (hmajority : GridCO.voterCount raw <
      2 * GridCO.goldfishScore st.base.blocks raw support B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks raw support D <
        GridCO.goldfishScore st.base.blocks raw support B) :
    Block.Preceq B (headInTree p st tree raw support) := by
  apply walk_covers_of_dominated_suffix _ _ _ _ _ hanchor
  rw [DominatedSuffix_def]
  intro C hac hcb
  have hm := Gen.AC.Root.goldfishScore_antitone st.base.blocks
    raw support C B hcb
  refine ⟨hpath C hac hcb, ?_, ?_⟩
  · change (_ || decide (_ < 2 * _) || _) = true
    have hmaj : GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks
          raw support C := by omega
    simp only [hmaj, decide_true, Bool.or_true, Bool.true_or]
  · intro D _ hp _ hne
    have he : D.depth = C.depth := by
      cases D with
      | genesis => cases C with
        | genesis => rfl
        | node P s r_s id => cases hp
      | node P s r_s id => cases C with
        | genesis => cases hp
        | node Q t r_t jd =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D C := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D C h (Nat.le_of_eq he.symm))
      · exact hne (prefix_eq_of_depth C D h (Nat.le_of_eq he)).symm
    have hd : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hcb)
    exact lt_of_lt_of_le (hdominance D hd) hm

/-- [ROOT-DIGEST-2 W1; DC root HEAD] ROOT-DIGEST W1b: structural erasure lifts the parent path with
the explicit root. -/
theorem geometry_lift_prefix {n : Nat} (B : FGBlock (Fin n)) (a : Block)
    (ha : Block.Preceq a (eraseFG B)) :
    ∃ A, FGBlock.Preceq A B ∧ eraseFG A = a := by
  induction B with
  | genesis =>
      have he : a = .genesis := by simpa [eraseFG, Block.Preceq, Block.preceq] using ha
      exact ⟨.genesis, KitFG.preceq_refl _, he.symm⟩
  | node P s r_s r rs ih =>
      change (decide (a = eraseFG (.node P s r_s r rs)) || Block.preceq a (eraseFG P)) = true at ha
      rcases Bool.or_eq_true_iff.mp ha with he | hp
      · exact ⟨.node P s r_s r rs, KitFG.preceq_refl _, (of_decide_eq_true he).symm⟩
      · obtain ⟨A, hA, he⟩ := ih hp
        exact ⟨A, KitFG.preceq_trans hA (KitFG.preceq_parent_node _ _ _ _ _), he⟩

private theorem geometry_Z_liveRoot (p : Params) (st : State p.n) :
    Block.Preceq (eraseFG (controls p st).Z) (liveRoot p st) :=
  fgsa_Z_preceq_liveRoot p st

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.5; bp02 §7. Class (iii), store walk instance.
DC: Goldfish/Records.lean:207 `ghost_walk_mem`. SAME conclusion after
instantiating the FG-SA anchor, score and eligibility; lists use eraseDups. -/
theorem fgsa_headInTree_mem_or_anchor (p : Params) (st : State p.n)
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    headInTree p st tree raw support = liveRoot p st ∨
      headInTree p st tree raw support ∈ tree := by
  rcases @GridCO.ghostWalk_mem GridCO.slowLeasePolicy tree.eraseDups
    (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)
    tree.eraseDups.length (liveRoot p st) with he | hm
  · exact Or.inl he
  · exact Or.inr (List.mem_eraseDups.mp hm)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.5a; bp02 §7. Class (iii), filtered store geometry.
DC: Goldfish/Walk.lean:433 `ghost_reaches` uses a path in its tree.
INTENTIONAL: FJ filtering retains the segment above the live anchor,
with the same witness in X (SYN §3; bp02 §7); it need not retain the trunk. -/
theorem fgsa_filtered_anchorClosed (p : Params) (st : State p.n)
    (hi : CStoreInv p st) (X : Finset (FGBlock (Fin p.n)))
    (hsub : X ⊆ st.fg.TF)
    (hclosed : ∀ B ∈ X, ∀ A, FGBlock.Preceq A B → A ∈ X) :
    AnchorClosed (liveRoot p st) (erasedList st (filteredFrom p.E p.cfg (controls p st) X)) := by
  intro b hb _ a haa hab
  obtain ⟨_, hb⟩ := List.mem_filter.mp hb
  obtain ⟨B, hB, rfl⟩ := of_decide_eq_true hb
  obtain ⟨hBX, hFB, hZB, W, hWX, hBW, hlo⟩ :=
    (KitFG.mem_filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mp hB
  obtain ⟨A, hAB, rfl⟩ := geometry_lift_prefix B a hab
  have hZA : FGBlock.Preceq (controls p st).Z A :=
    preceq_of_eraseFG_preceq (viewRootInj_TF p st hi)
      ⟨B, hsub hBX, hZB⟩ ⟨B, hsub hBX, hAB⟩
      (block_preceq_trans (geometry_Z_liveRoot p st) haa)
  have hFZ : FGBlock.Preceq (controls p st).F (controls p st).Z := by
    unfold Controls.Z
    split
    · exact hi.fg.FJ
    · exact KitFG.preceq_refl _
  have hAX := hclosed B hBX A hAB
  apply List.mem_filter.mpr
  refine ⟨(hi.baseTree _).mpr ⟨A, hsub hAX, rfl⟩, ?_⟩
  apply decide_eq_true
  exact ⟨A, (KitFG.mem_filteredFrom_of_bridge
    p.E p.cfg (heightView p) (heightView_bridge p) _ _ A).mpr
    ⟨hAX, KitFG.preceq_trans hFZ hZA, hZA, W, hWX,
      KitFG.preceq_trans hAB hBW, hlo⟩, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] ROOT-DIGEST W1c: use local CStoreInv root uniqueness.
P3 F1b.5; bp02 §7. Class (iii), Gen walk instance.
DC: Goldfish/Walk.lean:197 `ghost_step_none`, :433 `ghost_reaches`.
INTENTIONAL: the FJ filtered closure supplies the finite-walk terminal
condition (F1b.5a; SYN §3), for any ancestor-closed duty view X. -/
theorem fgsa_headInTree_noEligibleChild (p : Params) (st : State p.n)
    (hi : CStoreInv p st) (X : Finset (FGBlock (Fin p.n)))
    (hsub : X ⊆ st.fg.TF)
    (hclosed : ∀ B ∈ X, ∀ A, FGBlock.Preceq A B → A ∈ X)
    (raw support : List (GridCO.Wire p.n .root)) :
    let tree := erasedList st (filteredFrom p.E p.cfg (controls p st) X)
    ∀ B ∈ tree, B.parent? = some (headInTree p st tree raw support) →
      eligible p st raw support B = false := by
  apply walk_noEligibleChild_of_anchorClosed _ _ _ _ ?_
    (fgsa_filtered_anchorClosed p st hi X hsub hclosed)
  exact erasedList_rootInj p st hi _

end AvailableChain.FGSA
