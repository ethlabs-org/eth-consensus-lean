module
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame
public import AvailableChainFGSAProofs.Proofs.Healing.FrameSource

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 918–1012; plan S30, H-FRAME/F1.
DC: SAME proposal-parent projection; INTENTIONAL post-clock FG-SA read. -/
private theorem frame_proposal_read (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {Q : Block} {st : State p.n}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q)
    (hst : proposalStateAt p c E rho s = some st) :
    Reachable p st ∧ Q.parent = proposerHead p st s := by
  obtain ⟨_, o, ⟨j, hj, hem⟩, hb⟩ := hp
  rw [proposalTime_fgsa p c s] at hj
  have htick : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (SA.proposalTime p.toParams s) = some j := by
    obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho
        (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s) = some k := by
      rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
      exact ⟨_, List.mem_of_getElem? hj, by simp⟩
    exact (fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hk) hj) ▸ hk
  change (postClock E rho _ _).map (·.st) = some st at hst
  rw [proposalTime_fgsa p c s, postClock_def, preTick_def, htick] at hst
  have hst' := Option.some.inj hst
  subst st
  refine ⟨Reachable.tick _ (reachable_stateBefore E rho j _), ?_⟩
  obtain ⟨auth, m⟩ := o
  cases m with
  | head _ => cases hb
  | row _ => cases hb
  | proposal N =>
    have he : N.erase = Q := Option.some.inj hb
    subst Q
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    change (⟨auth, .proposal N⟩ : Obj p) ∈
      (if E.awake _ (SA.proposalTime p.toParams s) then
        (duties p (SA.proposalTime p.toParams s)).flatMap (fun d =>
          (rho.ownSeats (RunDuty.signLabel d) _).filterMap (fun i =>
            (act p c ((fgsa p c).clock _ _) d (rho.input _ _)).map
              (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
                ([] : List (Obj p)) else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, hd, hem⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
      obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
      have he : m = .proposal N := congrArg V2.Signed.payload ho
      subst m
      cases d with
      | headAction _ =>
        change (if joinedNow p _ then some (Msg.head _) else none) = some (Msg.proposal N) at hm
        split at hm <;> cases hm
      | fgAction _ =>
        change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
        obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hm
        cases he
      | propAction s' =>
        have ht := (duties_spec p _ _).mp hd
        have hss : s' = s := by
          change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
          have hΔ := p.deltaPos
          have he : (s' : Int) = s := by nlinarith
          exact_mod_cast he
        subst s'
        change (if joinedNow p _ then
          (propose p _ s).map (withApp p _) else none) = some (.proposal N) at hm
        split at hm
        · exact (fgsa_walkRun_proposal_parent p _ s _ N hm).2.2
        · cases hm
    · exact (List.not_mem_nil hem).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783; plan S30, H-FRAME/F1.
DC: INTENTIONAL the live lease selector starts inside a nonempty full FJ domain. -/
private theorem frame_liveRoot_mem (st : State p.n) (hi : CStoreInv p st)
    (hne : (fullTree p st).Nonempty) :
    ∃ B ∈ fullTree p st, eraseFG B = liveRoot p st := by
  have hZ : (controls p st).Z ∈ fullTree p st := by
    have hclosed : ∀ B ∈ st.fg.TF, ∀ A, FGBlock.Preceq A B → A ∈ st.fg.TF := by
      intro B hB A hAB
      obtain ⟨Q, hQ, he⟩ := eraseFG_ancestor_mem hi.fg.closed hB (eraseFG_preceq hAB)
      exact (eraseFG_injective he) ▸ hQ
    rw [fgsa_fullTree_eq_filtered] at hne ⊢
    apply KitFG.filteredFrom_Z_mem p.E p.cfg _ _ hclosed _ hne
    unfold Controls.Z
    split
    · exact hi.fg.FJ
    · exact KitFG.preceq_refl _
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · exact ⟨_, hZ, he.symm⟩
  · obtain ⟨row, _, hrow⟩ := List.mem_filterMap.mp hm
    split at hrow
    · rename_i hc
      have hw := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
      obtain ⟨B, hB, heB⟩ := hw
      exact ⟨B, hB, heB.trans (Option.some.inj hrow)⟩
    · cases hrow

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 918–1012; plan S30, H-FRAME/F1.
DC: SAME finite-walk membership; INTENTIONAL the full tree uses live FJ controls.
The honest proposal's parent has an exact FG witness in the full tree. -/
theorem healing_proposal_full_witness (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {Q : Block} {st : State p.n}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q)
    (hst : proposalStateAt p c E rho s = some st)
    (hne : (fullTree p st).Nonempty) :
    ∃ B ∈ fullTree p st, eraseFG B = Q.parent := by
  obtain ⟨hr, hparent⟩ := frame_proposal_read p c E rho hs hp hst
  rw [hparent]
  rcases fgsa_headInTree_mem_or_anchor p st (erasedList st (fullTree p st))
      (proposerVotes st s) (proposerSupport st s) with he | hm
  · obtain ⟨B, hB, heB⟩ := frame_liveRoot_mem p st (storeBundle_of_reachable p st hr).cstore hne
    exact ⟨B, hB, heB.trans he.symm⟩
  · exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F1.
DC: INTENTIONAL a local frontier carrier makes the full FJ domain nonempty. -/
private theorem frame_fullTree_nonempty (crossing : RXing p c E rho)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) :
    (fullTree p (storeAt p c E rho i x)).Nonempty := by
  obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho i x
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
  exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
    ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783; plan S30, H-FRAME/F1.
DC: INTENTIONAL a duty-domain member and its witness remain in the full domain. -/
private theorem frame_domain_subset_full_of_top_retained (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (hX : X ⊆ st.fg.TF)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    KitFG.storeFrameView (heightView p) st.fg X ⊆ fullTree p st := by
  change _ ⊆ KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF
  rw [KitFG.treeStoreFrameView_eq (heightView p) st.fg st.fg.TF hF]
  intro B hB
  obtain ⟨hb, hf, hz, W, hw, hbw, hlo⟩ :=
    (KitFG.mem_filteredFromView _ _ _ _).mp hB
  exact (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hX hb, hf, hz, W, hX hw, hbw, hlo⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F1.
DC: SAME walk membership; INTENTIONAL the floor belongs to a full-store witness.
An honest positive-label HEAD can return an outside anchor. Its full-domain
witness still exists; this theorem does not put the HEAD in the frozen domain. -/
theorem healing_full_witness (crossing : RXing p c E rho)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (_hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s))) (hs : 0 < s) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x)
      (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h := by
  let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [show st.fg = (storeAt p c E rho i x).fg from clock_fg p _ _]
    exact frame_fullTree_nonempty p c E rho crossing hx
  have hmem : ∃ K ∈ fullTree p st, eraseFG K = headVote p st s := by
    change ∃ K ∈ fullTree p st, eraseFG K =
      (if s = 0 then .genesis else headInTree p st
        (erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st s)))
        (headVotes p st s) (headSupport p st s))
    rw [ite_eq_right (Nat.ne_of_gt hs)]
    rcases fgsa_headInTree_mem_or_anchor p st _ (headVotes p st s) (headSupport p st s)
        with he | hm
    · exact he ▸ frame_liveRoot_mem p st (storeBundle_postClock E rho i x _).cstore hne
    · obtain ⟨K, hK, hk⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
      have htop : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
          ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W := by
        intro W hW hh _
        have hfg : st.fg = (storeAt p c E rho i x).fg := clock_fg p _ _
        rw [hfg] at hW hh ⊢
        exact (healing_phase_frontier_root p c E rho crossing hx hW hh).1
      rw [KitFG.treeStoreFrameView_eq (heightView p) st.fg _ htop] at hK
      exact ⟨K, frame_domain_subset_full_of_top_retained p st _
        ((Finset.filter_subset _ _).trans (Next.tree_subset_TF p st)) htop hK, hk⟩
  obtain ⟨K, hK, hk⟩ := hmem
  exact ⟨K, hK, hk, ((KitFG.mem_filteredFromView _ _ _ _).mp hK).2.2.2⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 918–1012, 1288–1308; plan S30, H-FRAME/F3.
DC: SAME terminal walk argument; INTENTIONAL low-parent eligibility reaches the FJ floor.
The full domain contains the live start, including a zero-step return. -/
theorem healing_proposer_floor (hs : V2.D.ScheduleWellFormed E rho)
    (s : Slot) (Q : Block) (st : State p.n)
    (hp : HonestProposal E rho (fgsaInterface p c) s Q)
    (hst : proposalStateAt p c E rho s = some st) (hne : (fullTree p st).Nonempty) :
    ∃ B ∈ fullTree p st, eraseFG B = Q.parent ∧ (frameR p st).lo ≤ (heightView p B).h := by
  obtain ⟨hr, hparent⟩ := frame_proposal_read p c E rho hs hp hst
  have hi := (storeBundle_of_reachable p st hr).cstore
  have hclosed : ∀ B ∈ st.fg.TF, ∀ A, FGBlock.Preceq A B → A ∈ st.fg.TF := by
    intro B hB A hAB
    obtain ⟨C, hC, he⟩ := eraseFG_ancestor_mem hi.fg.closed hB (eraseFG_preceq hAB)
    exact (eraseFG_injective he) ▸ hC
  obtain ⟨B, hB, heB⟩ := healing_proposal_full_witness p c E rho hs hp hst hne
  refine ⟨B, hB, heB, ?_⟩
  change (controls p st).lo ≤ (heightView p B).h
  by_contra hn
  have hlow : (heightView p B).h < (controls p st).lo := Nat.lt_of_not_ge hn
  obtain ⟨hb, hf, hz, W, hw, hbw, hlo⟩ := (KitFG.mem_filteredFromView _ _ _ _).mp hB
  change (controls p st).lo ≤ (heightView p W).h at hlo
  have hneBW : B ≠ W := by intro he; subst W; simp only [Height] at *; omega
  obtain ⟨C, hCB, hng, hCW⟩ := KitFG.child_toward hbw hneBW
  have hBC : FGBlock.Preceq B C := by
    cases C with
    | genesis => exact (hng rfl).elim
    | node P s root body rows =>
      change P = B at hCB
      subst P
      exact KitFG.preceq_parent_node _ _ _ _ _
  have hC : C ∈ fullTree p st := (KitFG.mem_filteredFromView _ _ _ _).mpr
    ⟨hclosed W hw C hCW, KitFG.preceq_trans hf hBC, KitFG.preceq_trans hz hBC,
      W, hw, hCW, hlo⟩
  have hPC : (eraseFG C).parent? = some (proposerHead p st s) := by
    cases C with
    | genesis => exact (hng rfl).elim
    | node P u root body rows =>
      change P = B at hCB
      change some (eraseFG P) = some (proposerHead p st s)
      rw [hCB, heB, hparent]
  have hband : ∃ P ∈ st.fg.TF, eraseFG P = (eraseFG C).parent ∧
      (heightView p P).h < (controls p st).lo :=
    ⟨B, hb, by rw [eraseFG_parent, hCB], hlow⟩
  have hel : eligible p st (proposerVotes st s) (proposerSupport st s) (eraseFG C) = true := by
    change (decide (∃ P ∈ st.fg.TF, eraseFG P = (eraseFG C).parent ∧
      (heightView p P).h < (controls p st).lo) || _ || _) = true
    simp only [hband, decide_true, Bool.true_or]
  have hterminal := fgsa_headInTree_noEligibleChild p st hi st.fg.TF
    (fun _ h => h) hclosed (proposerVotes st s) (proposerSupport st s)
  rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hterminal
  have hc := hterminal (eraseFG C)
    (List.mem_filter.mpr ⟨(hi.baseTree _).mpr ⟨C, (KitFG.mem_filteredFromView _ _ _ _).mp hC |>.1,
      rfl⟩, decide_eq_true ⟨C, hC, rfl⟩⟩) hPC
  rw [hel] at hc
  cases hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783, 918–1012, 1148–1252, 1288–1308; plan S30, H-FRAME/F4.
DC: INTENTIONAL the exact frozen TGeom conjunction, with both geometry and source slots.
The schedule identifies the actual proposal read. No phase or source-delivery premise is added. -/
theorem healing_tGeom (hs : V2.D.ScheduleWellFormed E rho) : TGeom p c E rho := by
  constructor
  · intro s Q st hp hst hne
    obtain ⟨B, hB, heB⟩ := healing_proposal_full_witness p c E rho hs hp hst hne
    obtain ⟨A, hA, heA, hlo⟩ := healing_proposer_floor p c E rho hs s Q st hp hst hne
    have he : A = B := eraseFG_injective (heA.trans heB.symm)
    exact ⟨B, hB, heB, he ▸ hlo⟩
  · intro x r C hx hc
    exact healing_source_slot p c E rho hx hc

end AvailableChain.FGSA.Run
end
