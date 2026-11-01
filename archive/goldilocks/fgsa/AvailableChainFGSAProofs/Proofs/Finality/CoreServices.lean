module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSA.Proofs.Head.Walk -- shake: keep (prefix lift)
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 A.7 T-START:222–225,251–267; 22 I5:538–581. Class (iii).
DC b241081: INTENTIONAL: the FG-SA live root selects a live lease in the
FJ filtered tree, or the active root Z. The reachable lease bound supplies output. -/
theorem fgsa_tStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    TStart p c E rho := by
  constructor
  · intro i x hx row hr ht
    exact leaseBelowOutput_honest E rho i x hx row hr ht
  · intro i x _
    let st := storeAt p c E rho i x
    change liveRoot p st = _ ∨ _
    unfold liveRoot
    dsimp only
    rcases foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
        (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
    · exact Or.inl he
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · next hc =>
        obtain ⟨ht, hb⟩ := Bool.and_eq_true_iff.mp hc
        have ht := of_decide_eq_true ht
        have hb := of_decide_eq_true hb
        refine Or.inr ⟨row, hr, ht, (Option.some.inj hrow), hb, ?_⟩
        exact leaseBelowOutput_stateBefore E rho i x row hr ht
      · cases hrow

private theorem core_full_mem (st : State p.n) (B : FGBlock (Fin p.n)) :
    B ∈ fullTree p st ↔ B ∈ st.fg.TF ∧ FGBlock.Preceq (controls p st).F B ∧
      FGBlock.Preceq (controls p st).Z B ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq B W ∧ (controls p st).lo ≤ (heightView p W).h :=
  KitFG.mem_filteredFromView (heightView p) (controls p st) st.fg.TF B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 01 A.7 T-WALK:243–249,269–278; 22 I8:637. Class (iii).
DC b241081: Protocol/ForkChoice/Goldfish/Adoption.lean:415 and
Protocol/ForkChoice/Goldfish/Walk.lean:184,197,433.
INTENTIONAL: the FJ tree and live root supply the path; Batch supplies the
score bounds. An unsupported path block can use only the slot or low-parent arm. -/
theorem fgsa_tWalk (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    TWalk p c E rho := by
  intro i x s raw support Q seats m hx hb st hQ hanchor hwalk
  obtain ⟨hsub, hlabel, hseats, hother, hclean⟩ := hwalk
  have hi : CStoreInv p st := cstoreInv_stateBefore E rho i x
  have hQT := ((core_full_mem st Q).mp hQ).1
  have hinj := viewRootInj_TF p st hi
  have hbatch : ∀ a ∈ seats, Gen.AC.Root.poolSupports st.base.blocks support a (eraseFG Q) =
      true := by
    intro a ha
    obtain ⟨_, o, ho, hor, hseat, H, ht, hs, hQH⟩ := hseats a ha
    apply (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mpr
    refine ⟨o, ho, hseat, ?_⟩
    have hH := resolvedHead_mem st.base o ht
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨H, resolvedTarget_of_mem _ (baseBlocks_rootInj p st hi) o hH
        (resolvedHead_root _ o ht), hH, by simpa only [hlabel o hor, Option.getD_some] using hs,
            hQH⟩
  obtain ⟨_, _, hpath, hconflict, hunsupported⟩ := Gen.AC.Root.batch_counts
    st.base.blocks raw raw support seats seats.card m (eraseFG Q)
    (fun _ ho => ho) hsub rfl hclean hbatch hother hb
  have hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C (eraseFG Q) →
      C ∈ erasedList st (fullTree p st) := by
    intro C hac hcQ
    obtain ⟨A, hAQ, rfl⟩ := geometry_lift_prefix Q C hcQ
    have hAT := KitFG.ancestor_closed_of_parent_closed _ hi.fg.closed Q hQT A hAQ
    obtain ⟨_, hFQ, hZQ, W, hWT, hQW, hlo⟩ := (core_full_mem st Q).mp hQ
    have hZA : FGBlock.Preceq (controls p st).Z A :=
      preceq_of_eraseFG_preceq hinj ⟨Q, hQT, hZQ⟩ ⟨Q, hQT, hAQ⟩
        (block_preceq_trans (fgsa_Z_preceq_liveRoot p st) (Bool.and_eq_true_iff.mp hac).2)
    have hFZ : FGBlock.Preceq (controls p st).F (controls p st).Z :=
      fgsa_F_preceq_Z p st hi
    have hA := (core_full_mem st A).mpr
      ⟨hAT, KitFG.preceq_trans hFZ hZA, hZA, W, hWT, KitFG.preceq_trans hAQ hQW, hlo⟩
    exact List.mem_filter.mpr ⟨(hi.baseTree _).mpr ⟨A, hAT, rfl⟩,
      decide_eq_true ⟨A, hA, rfl⟩⟩
  have hcover : Block.Preceq (eraseFG Q) (getHead p st raw support) := by
    apply fgsa_headInTree_covers_of_transfer p st _ raw support (eraseFG Q)
      hanchor hkeep (hpath _ (block_preceq_refl _)).2
    intro D hd
    have := hconflict D hd
    have := (hpath _ (block_preceq_refl _)).1
    have := hb.lt
    omega
  refine ⟨hcover, ?_, ?_⟩
  · intro hmax
    have terminal (B : FGBlock (Fin p.n)) (hB : B ∈ fullTree p st)
        (he : eraseFG B = getHead p st raw support) : getHead p st raw support = eraseFG Q := by
      have hQB := preceq_of_eraseFG_preceq hinj ⟨Q, hQT, KitFG.preceq_refl _⟩
        ⟨B, ((core_full_mem st B).mp hB).1, KitFG.preceq_refl _⟩ (he.symm ▸ hcover)
      rw [← he, hmax B hB hQB]
    rcases fgsa_headInTree_mem_or_anchor p st (erasedList st (fullTree p st)) raw support
      with he | hm
    · change getHead p st raw support = liveRoot p st at he
      rcases (fgsa_tStart E rho).2 i x hx with hz | ⟨_, _, _, hr, hm, _⟩
      · have hZQ := eraseFG_preceq ((core_full_mem st Q).mp hQ).2.2.1
        exact block_preceq_antisymm (by rw [he, hz]; exact hZQ) hcover
      · obtain ⟨B, hB, hBr⟩ := hm
        exact terminal B hB (hBr.trans (hr.trans he.symm))
    · obtain ⟨B, hB, hBe⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
      exact terminal B hB hBe
  · intro B hac hBH hnone
    have hrest : ∀ a ∈ seats, Gen.AC.Root.poolSupports st.base.blocks support a B = false := by
      intro a ha
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨o, ho, hs, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mp h
      obtain ⟨H, ht, hH, _, hBH⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hv
      have hres := base_resolve_target p st hi
        (base_headDomain_none p (reachable_stateBefore E rho i x)) o hH
        (resolvedTarget_root _ o ht)
      exact hnone a ha o ho hs H hres hBH
    have hscore := hunsupported B hrest
    have hel : eligible p st raw support B = true := by
      cases B with
      | genesis =>
          have hg := (Bool.and_eq_true_iff.mp hac).2
          have he : liveRoot p st = .genesis := of_decide_eq_true hg
          have hn := (Bool.and_eq_true_iff.mp hac).1
          change (!decide (liveRoot p st = .genesis)) = true at hn
          simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
      | node P t root id =>
          have hAP : Block.Preceq (liveRoot p st) P := by
            have hne : liveRoot p st ≠ .node P t root id := by
              intro he
              have hn := (Bool.and_eq_true_iff.mp hac).1
              change (!decide (liveRoot p st = .node P t root id)) = true at hn
              simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
            have hp := (Bool.and_eq_true_iff.mp hac).2
            change (decide (liveRoot p st = .node P t root id) ||
              Block.preceq (liveRoot p st) P) = true at hp
            simp only [hne, decide_false, Bool.false_or] at hp
            exact hp
          obtain ⟨C, hp, hCB, _, hc, _⟩ := walk_best_ancestry_of_cover (liveRoot p st)
            (.node P t root id) (erasedList st (fullTree p st))
            (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)
            hBH P hAP (by
              have hne : P ≠ .node P t root id := by
                intro he
                have hd := congrArg Block.depth he
                change P.depth = P.depth + 1 at hd
                omega
              change ((!decide (P = .node P t root id)) &&
                (decide (P = .node P t root id) || Block.preceq P P)) = true
              simp only [hne, decide_false, Bool.not_false, Bool.false_or, Bool.true_and]
              exact block_preceq_refl P)
          have hdepth : C.depth = (Block.node P t root id).depth := by
            cases C with
            | genesis => cases hp
            | node D u root jd =>
                have hD := Option.some.inj hp
                subst D
                rfl
          have hC : C = .node P t root id := prefix_eq_of_depth C (.node P t root id)
            hCB (Nat.le_of_eq hdepth.symm)
          exact hC ▸ hc
    change (_ || decide (_ < 2 * _) || _) = true at hel
    have hn : ¬ GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks raw support B := by omega
    simp only [hn, decide_false, Bool.or_false, Bool.or_eq_true_iff,
      decide_eq_true_eq, beq_iff_eq] at hel
    exact hel.elim Or.inr Or.inl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 A.7 T-VOTE:235–242; 22:1233–1234.
DC: Protocol/Handlers/GoldfishVotePool.lean:320, scheduled honest HEAD. -/
theorem finality_emitted_head_form (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (y : V) (s : Slot) (a : HeadWire p.n)
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s)) :
    ∃ k, a = ⟨.seat (.head s) k, a.payload⟩ := by
  obtain ⟨j, hj, hem⟩ := he
  have haw : E.awake y (SA.voteTime p.toParams s) = true := by
    by_contra hn
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    have hh := (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho j y) y
      (SA.voteTime p.toParams s) (Bool.eq_false_iff.mpr hn)).1
    have hem' := hh ▸ hem
    exact List.not_mem_nil hem'
  have hw := honest_emit_wellFormed E rho hE.toDeliveryWellFormed hE.toScheduleWellFormed
    j y _ hj hy haw _ hem
  rcases a with ⟨auth, b⟩
  rcases auth with ⟨(_ | _), k⟩ | r | _
  · rename_i r
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    have ht := (fgsa_emits_head E rho _ y _ r k b).mp hem
    have hrs : r = s := by
      have hp := p.deltaPos
      have ht' : 4 * p.Δ * (r : Int) + p.Δ = 4 * p.Δ * (s : Int) + p.Δ := ht.2.1
      have : (r : Int) = s := by nlinarith
      exact_mod_cast this
    subst r
    exact ⟨k, rfl⟩
  all_goals cases hw

/-- Current receipts at the two exact read shapes required by public TVote.
Each read requires its previous-slot start to be at or after GST. -/
structure FinalityVoteReceipts (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  proposal : ∀ v nd, Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) v →
    E.t_GST ≤ slotStartZ p (((v - 1 : Slot) : Int) - 1) →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (v - 1)) (SA.proposalTime p.toParams v) →
    postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) v)
      (SA.proposalTime p.toParams v) = some nd →
    ∀ y (a : HeadWire p.n), y ∈ rho.honest →
      V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams (v - 1)) →
      GridCO.headLabel? (baseVote a) = some (v - 1) → baseVote a ∈ nd.st.base.votes
  action : ∀ r x nd, x ∈ rho.honest →
    E.t_GST ≤ slotStartZ p (((r * p.R + 1 : Slot) : Int) - 1) →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (r * p.R + 1)) (p.actionTime r) →
    postClock E rho x (p.actionTime r) = some nd →
    ∀ y (a : HeadWire p.n), y ∈ rho.honest →
      V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams (r * p.R + 1)) →
      GridCO.headLabel? (baseVote a) = some (r * p.R + 1) → baseVote a ∈ nd.st.base.votes

/-- True internal receipt scope for Recovery reads after the previous-slot cutoff.
The public TVote read clauses use this scope. -/
structure FinalityScopedVoteReceipts (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) : Prop where
  receipt : ∀ (s : Slot) (x : V) (t : Time) (nd : Node p), x ∈ rho.honest →
    E.t_GST ≤ slotStartZ p ((s : Int) - 1) →
    SA.earlyTime p.toParams s ≤ t → t ≤ rho.horizon →
    postClock E rho x t = some nd →
    ∀ y (a : HeadWire p.n), y ∈ rho.honest →
      V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
      GridCO.headLabel? (baseVote a) = some s → baseVote a ∈ nd.st.base.votes

/-- Exact current receipts supply the full vote service and its resolved-head filter. -/
theorem finality_full_vote_of_receipts
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (nd : Node p)
    (hReceipt : ∀ y (a : HeadWire p.n), y ∈ rho.honest →
      V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
      GridCO.headLabel? (baseVote a) = some s → baseVote a ∈ nd.st.base.votes) :
    FullVoteService p c E rho nd.st s := by
  intro y a hy he hl
  have hm := hReceipt y a hy he hl
  have hv : baseVote a ∈ GridCO.votesAt nd.st.base s :=
    List.mem_filter.mpr ⟨hm, by simp only [hl, beq_self_eq_true]⟩
  refine ⟨hv, ?_⟩
  intro H hknown hslot
  apply List.mem_filter.mpr
  refine ⟨hv, ?_⟩
  change (match GridCO.resolvedHead? _ _ with
    | some K => decide (K.slot ≤ s) | none => false) = true
  rw [hknown]
  exact decide_eq_true hslot

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 A.7 T-VOTE:235–242; 22:1233–1234 (S14). Class (ii).
DC: Generic/Conditions.lean:110,134 and
Protocol/Handlers/GoldfishVotePool.lean:320.
INTENTIONAL: FG-SA uses non-row delivery and the post-clock active view. -/
theorem fgsa_tVote (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : Base₂ p c E rho) (hR : FinalityVoteReceipts E rho) : TVote p c E rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro v st hv hcut hSync hst
    change (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) v)
      (SA.proposalTime p.toParams v)).map (·.st) = some st at hst
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact finality_full_vote_of_receipts E rho (v - 1) nd (hR.proposal v nd hv hcut hSync hnd)
  · intro r x nd hx hcut hSync hnd
    exact finality_full_vote_of_receipts E rho (r * p.R + 1) nd (hR.action r x nd hx hcut hSync hnd)
  · intro y s a hy he
    obtain ⟨k, ha⟩ := finality_emitted_head_form E rho hb.valid y s a hy he
    rw [ha] at he ⊢
    obtain ⟨j, hj, hem⟩ := he
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    have hhead := (fgsa_emits_head E rho _ y _ s k a.payload).mp hem
    refine ⟨(fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (SA.voteTime p.toParams s),
      headVote p (FGSA.clock p (rho.stateBefore E j y).st (SA.voteTime p.toParams s)) s,
      ?_, ?_, hhead.2.2.2.2.symm⟩
    · rw [postClock_def, preTick_def,
        fgsa_tickIdx_of_event p c E rho hb.valid.toScheduleWellFormed hj]
      rfl
    · exact headVote_stored p _ (storeBundle_postClock E rho j y _).cstore s

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01:126–199; 22:1228–1254. Class (iii).
DC: INTENTIONAL: assembly of the three FG-SA composition services. -/
theorem fgsa_coreServices
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : Base₂ p c E rho) (w : HealingWitness) (hR : FinalityVoteReceipts E rho) :
    CoreServices p c E rho w :=
  ⟨fgsa_tStart E rho, fgsa_tVote E rho hb hR, fgsa_tWalk E rho⟩


end AvailableChain.FGSA.Run
end
