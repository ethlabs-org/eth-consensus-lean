module
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.CommonBodies

public section

/-! C6 CommonTree: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every held body of a positive honest proposer slot is the unique emitted proposal. -/
theorem pcsa_honest_slot_body_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (y : V) (s : Slot) (hs : 0 < s) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (B : Block) (hB : B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks)
    (hslot : B.slot = s) : B = N.erase := by
  have hg : B ≠ .genesis := by
    intro hg
    rw [hg] at hslot
    change 0 = s at hslot
    exact (Nat.ne_of_gt hs) hslot.symm
  obtain ⟨j, _, t, o, r, M, P, hj, hd, hM, _, hacc, _⟩ :=
    pcsa_body_receipt_origin E rho h.valid k y B hg hB
  have hrs : r = M.erase.slot := by
    change (_ && _ && _ && _ && _ && r == M.erase.slot && _ && _ && _) = true at hacc
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp hacc).1).1).1).2
  have hrs' : r = s := hrs.trans ((congrArg Block.slot hM).trans hslot)
  rw [hrs'] at hd
  have hobj := pcsa_decoded_proposal_object o s M hd
  subst o
  obtain ⟨u, _, hem⟩ := h.valid.unforgeable y _ t ⟨j, hj⟩ _ hx rfl
  obtain ⟨a, ha, hoa⟩ := hem
  obtain ⟨b, hb, hob⟩ := he
  have heq := (Gen.V2.Duty.emitted_unique_of_singleDuty E rho h.valid.nodup (.prop s)
    (pcsa_prop_single_duty p c m s) (0 : Fin 1) _ a b u _ _ _ ha hb hoa hob rfl rfl).2
  have hMN := Msg.proposal.inj (congrArg (fun o : Obj p => o.payload) heq)
  exact hM.symm.trans (congrArg NamedProposal.erase hMN)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: Each honest-slot voter-tree body is a proposer-tree body or an ancestor
of the proposal. -/
theorem pcsa_voter_tree_source_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (C : Block)
    (hC : C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho a y).st v)
      (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho a y).st v).fg
        (voterBlocks p (clock p (V2.D.Run.stateBefore E rho a y).st v) (s + 1)))) :
    C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1)))
      (fullTree p
        (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
          (SA.proposalTime p.toParams (s + 1)))) ∨ Block.Preceq C N.erase := by
  let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
  obtain ⟨hm, hnamed⟩ := List.mem_filter.mp hC
  obtain ⟨D, hDmem, hDC⟩ := of_decide_eq_true hnamed
  have hDv : D ∈ voterBlocks p dst (s + 1) :=
    ((KitFG.mem_filteredFromView (FGSA.heightView p) (controls p dst)
      (voterBlocks p dst (s + 1)) D).mp hDmem).1
  have arms := (Finset.mem_filter.mp hDv).2
  rcases Bool.or_eq_true_iff.mp arms with hfreeze | hancestor
  · left
    have hs : GridCO.stampBlock dst.base C < SA.freezeTime p.toParams s := by
      rw [← hDC, ← Nat.add_sub_cancel s 1]
      exact of_decide_eq_true hfreeze
    have hb := pcsa_frozen_body_in_proposer_win E rho h hF hD (hT := hT) a k y _ hy hx s C v hk hc
        hm hs
    exact pcsa_full_read_prefix_mem E rho hF k _ hx _ C C hb (Gen.Pure.block_preceq_refl _)
  · right
    obtain ⟨P, hP, hslot, hDP⟩ := of_decide_eq_true hancestor
    have hbody : eraseFG P ∈ dst.base.blocks :=
      (pcsa_tree_correspondence p dst (Reachable.tick v (pcsa_reachable_stateBefore E rho a y))
        (eraseFG P)).mpr ⟨P, hP, rfl⟩
    have hbodyPre : eraseFG P ∈ (V2.D.Run.stateBefore E rho a y).st.base.blocks := by
      change eraseFG P ∈ (clock p _ v).base.blocks at hbody
      rwa [pcsa_clock_blocks] at hbody
    have hslot' : (eraseFG P).slot = s + 1 := by
      have hp : (eraseFG P).slot = P.slot := by cases P <;> rfl
      exact hp.trans hslot
    have hPN := pcsa_honest_slot_body_unique E rho h a y (s + 1) (Nat.succ_pos s)
      N hx he (eraseFG P) hbodyPre hslot'
    rw [← hPN, ← hDC]
    simpa only [pcsa_eraseFG_eq] using (FGSA.eraseFG_preceq_iff.mpr hDP)
/-- Each honest-slot voter-tree body is a proposer-tree body or an ancestor of the proposal. -/
theorem pcsa_voter_tree_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hc : SA.proposalTime p.toParams (s + 1) ≤ cut)
    (C : Block)
    (hC : C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho a y).st v)
      (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho a y).st v).fg
        (voterBlocks p (clock p (V2.D.Run.stateBefore E rho a y).st v) (s + 1)))) :
    C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1)))
      (fullTree p
        (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
          (SA.proposalTime p.toParams (s + 1)))) ∨ Block.Preceq C N.erase :=
  pcsa_voter_tree_source_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k y hy s v N hx
    he hk (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc C hC
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A held current-slot proposal retains every ancestor in the stage-one voter tree. -/
theorem pcsa_proposal_prefix_voter_mem (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (t : Time) (s : Slot) (P C : Block)
    (hm : P ∈ (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks)
    (hs : P.slot = s) (hc : Block.Preceq C P) :
    C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k x).st t)
      (KitFG.storeFrameView (FGSA.heightView p) (clock p (V2.D.Run.stateBefore E rho k x).st t).fg
        (voterBlocks p (clock p (V2.D.Run.stateBefore E rho k x).st t) s)) := by
  let st := clock p (V2.D.Run.stateBefore E rho k x).st t
  have hreach : Reachable p st := Reachable.tick t (pcsa_reachable_stateBefore E rho k x)
  have hcm := pcsa_body_prefix_mem p st hreach P hm C hc
  obtain ⟨Q, hQ, hQP⟩ := (pcsa_tree_correspondence p st hreach P).mp hm
  obtain ⟨D, hD, hDC⟩ := (pcsa_tree_correspondence p st hreach C).mp hcm
  have hDQ : SimplexFG.FGBlock.Preceq D Q := by
    apply FGSA.eraseFG_preceq_iff.mp
    simpa only [← pcsa_eraseFG_eq, hDC, hQP] using hc
  have hqs : Q.slot = s := by
    have hq : (eraseFG Q).slot = Q.slot := by cases Q <;> rfl
    exact hq.symm.trans ((congrArg Block.slot hQP).trans hs)
  have hf : FrameVacuous p st := by
    change (clock p _ t).fg.F = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) (clock p _ t).fg).Z = .genesis ∧
      (KitFG.storeControlsView (FGSA.heightView p) (clock p _ t).fg).lo = 0
    rw [pcsa_body_clock_fg]
    exact hF x hx k
  apply List.mem_filter.mpr
  refine ⟨hcm, decide_eq_true ?_⟩
  rw [pcsa_frame_subset_of_frame p st _ hf]
  refine ⟨D, Finset.mem_filter.mpr ⟨hD, ?_⟩, hDC⟩
  exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ⟨Q, hQ, hqs, hDQ⟩))
end AvailableChain.PCSA.Run

end
