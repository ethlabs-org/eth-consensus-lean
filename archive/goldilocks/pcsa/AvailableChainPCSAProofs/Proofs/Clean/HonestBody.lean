module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody
public import AvailableChainPCSAProofs.Proofs.Shared.BodyPersistence
public import AvailableChainPCSAProofs.Proofs.Shared.BodyAdmission
public import AvailableChainPCSAProofs.Proofs.Clean.TargetCollect

public section

/-! C3 immutable-parent row validity of an emitted honest body. -/
namespace AvailableChain.PCSA
open SimplexFG
variable {p : Params}

private theorem pcsa_body_genesis_fg (p : Params) (st : State p.n) (h : Reachable p st) :
    FGBlock.genesis ∈ st.fg.TF := by
  induction h with
  | init => exact Finset.mem_singleton_self _
  | tick t _ ih => rw [pcsa_body_clock_fg]; exact ih
  | deliver o _ ih => exact pcsa_body_process_fg_mono p _ o ih

private theorem pcsa_body_head_fg (p : Params) (st : State p.n) (h : Reachable p st)
    (hf : Run.FrameVacuous p st) (view : Option (PC p.n))
    (raw sup : List (GridCO.Wire p.n .root)) :
    ∃ B ∈ fullTree p st, eraseFG B = getHead p st view raw sup := by
  have hg : FGBlock.genesis ∈ fullTree p st := by
    rw [pcsa_fullTree_of_frame p st hf]
    exact pcsa_body_genesis_fg p st h
  have hz : ∃ B ∈ fullTree p st, eraseFG B = eraseFG (controls p st).Z := by
    rw [hf.2.1]
    exact ⟨_, hg, rfl⟩
  have hb : ∃ B ∈ fullTree p st, eraseFG B = walkBase p st view := by
    cases view with
    | none => exact hz
    | some pc =>
      change ∃ B ∈ fullTree p st, eraseFG B = if frameActive p st pc then pc.target else _
      split
      · exact of_decide_eq_true (by assumption)
      · exact hz
  have hr := pcsa_liveRoot_in_tree p st view hb
  change ∃ B ∈ fullTree p st, eraseFG B =
    headInTree p st view (erasedList st (fullTree p st)) raw sup
  rcases pcsa_headInTree_mem_or_root p st view _ raw sup with he | hm
  · rwa [he]
  · exact of_decide_eq_true (List.mem_filter.mp hm).2

private theorem pcsa_body_lookup_exists (st : State p.n) (H : Block)
    (h : ∃ B ∈ fullTree p st, eraseFG B = H) :
    ∃ P, fgBlockOf st H = some P ∧ eraseFG P = H := by
  obtain ⟨B, hB, he⟩ := h
  have hm : B ∈ st.fg.TF := by
    rw [fullTree_def] at hB
    exact ((KitFG.mem_filteredFromView (FGSA.heightView p) (controls p st) st.fg.TF B).mp hB).1
  have hx : ∃! B, B ∈ st.fg.TF ∧ decide (eraseFG B = H) = true := by
    refine ⟨B, ⟨hm, decide_eq_true he⟩, ?_⟩
    intro Q hQ
    apply FGSA.eraseFG_injective
    rw [← pcsa_eraseFG_eq, ← pcsa_eraseFG_eq]
    exact (of_decide_eq_true hQ.2).trans he.symm
  have hs : (fgBlockOf st H).isSome = true := by
    delta fgBlockOf pickPair
    rw [dite_eq_left hx]
    rfl
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨P, hP, of_decide_eq_true (FGSA.pickPair_some_spec st.fg.TF _ hP).2⟩

private theorem pcsa_body_namedByErase (st : State p.n) (H : Block) (N : NamedProposal p.n)
    (h : namedByErase? st H = some N) : N.erase = H := by
  delta namedByErase? at h
  cases hl : (st.namedBodies.filter (fun N => N.erase == H)).eraseDups with
  | nil => rw [hl] at h; cases h
  | cons A rest =>
    cases rest with
    | nil =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      have hm : A ∈ (st.namedBodies.filter (fun N => N.erase == H)).eraseDups := by
        rw [hl]
        exact List.mem_singleton_self _
      exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_eraseDups.mp hm)).2
    | cons B rest => rw [hl] at h; cases h

private theorem pcsa_body_proposalRows (p : Params) (st : State p.n) (H : Block)
    (P : FGBlock (Fin p.n)) (hp : fgBlockOf st H = some P) :
    rowsValidForParent p P (st.slot p) (proposalRows p st H) = true := by
  change pickPair st.fg.TF (fun B => decide (eraseFG B = H)) = some P at hp
  delta rowsValidForParent proposalRows proposalRowsCore
  dsimp only
  rw [hp]
  apply List.all_eq_true.mpr
  intro a ha
  exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp ha).2).1

/-- A generated honest proposal has valid rows for its exact geometric parent. -/
theorem pcsa_generated_body_rows (p : Params) (st : State p.n) (s app : Nat)
    (h : Reachable p st) (hf : Run.FrameVacuous p st) (hs : st.slot p = s)
    (N : NamedProposal p.n)
    (he : (propose p st s).map (Run.withApp p app) = some (.proposal N)) :
    ∃ P, eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true := by
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp he
  delta propose at hM
  split at hM
  · cases hM
  · obtain ⟨A, hA, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p A s app _ _ _ _) = Msg.proposal N at hN
    obtain rfl := Msg.proposal.inj hN
    let H := getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s)
    have hGeom := pcsa_body_namedByErase st H A hA
    obtain ⟨P, hP, hp⟩ := pcsa_body_lookup_exists st H
      (pcsa_body_head_fg p st h hf (proposerPC p st) (proposerVotes st s) (proposerSupport st s))
    refine ⟨P, ?_, ?_⟩
    · change eraseFG P = A.erase
      exact hp.trans hGeom.symm
    · change rowsValidForParent p P s (proposalRows p st H) = true
      rw [← hs]
      exact pcsa_body_proposalRows p st H P hP
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem pcsa_body_frame_clock (st : State p.n) (t : Time) (hf : FrameVacuous p st) :
    FrameVacuous p (clock p st t) := by
  have he : controls p (clock p st t) = controls p st := by
    rw [controls_def, controls_def, pcsa_body_clock_fg]
  rw [FrameVacuous_def] at hf ⊢
  rw [pcsa_body_clock_fg, he]
  exact hf
private theorem pcsa_body_prop_label (d : RunDuty) (s : Slot) :
    d.signLabel = .prop s ↔ d = .propAction s := by
  cases d <;> dsimp only [RunDuty.signLabel] <;> simp

/-- An emitted honest proposal passes its immutable-parent row check. -/
theorem pcsa_emitted_body_rows (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (s : Slot)
    (N : NamedProposal p.n)
    (he : V2.D.Run.emits E rho x (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s)) :
    ∃ P : SimplexFG.FGBlock (Fin p.n), eraseFG P = N.erase.parent ∧
      rowsValidForParent p P N.slot N.rows = true := by
  obtain ⟨k, hk, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, _, ha⟩ := (V2.D.Engine.mem_tick_seat_iff E rho _ x
    (SA.proposalTime p.toParams s) (.prop s) (0 : Fin 1) (.proposal N)).mp ho
  obtain rfl := (pcsa_body_prop_label d s).mp hl
  have hReach := Reachable.tick (SA.proposalTime p.toParams s)
    (pcsa_reachable_stateBefore E rho k x)
  have hFrame := pcsa_body_frame_clock (V2.D.Run.stateBefore E rho k x).st
    (SA.proposalTime p.toParams s) (hF x hx k)
  have hs : (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.proposalTime p.toParams s)).slot p = s := by
    change p.slotOf (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.proposalTime p.toParams s)).base.now = s
    rw [pcsa_clock_now]
    change p.slotOf (4 * p.Δ * (s : Int)) = s
    simpa only [add_zero] using
      pcsa_slotOf_offset p s 0 le_rfl (by have hd : (0 : Int) < p.Δ := p.deltaPos; omega)
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.proposalTime p.toParams s)) s).map
      (withApp p (c.app (rho.input x _))) = some (.proposal N) at ha
  all_goals exact pcsa_generated_body_rows p _ s _ hReach hFrame hs N ha
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Formation's emitted full body is stored at every honest node before the freeze. -/
theorem pcsa_formation_body_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, N.erase ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.base.blocks := by
  let x := V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s
  let o : Obj p := ⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩
  have he : V2.D.Run.emits E rho x o (SA.proposalTime p.toParams s) := h.proposal.2
  obtain ⟨P, hP, hRows⟩ := pcsa_emitted_body_rows E rho h.frame x h.proposal.1 s N he
  have hS := h.base.valid.toScheduleWellFormed
  have hdelta : (0 : Int) < p.Δ := p.deltaPos
  have hprev : SA.freezeTime p.toParams (s - 1) ≤ SA.proposalTime p.toParams s := by
    have hs : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt h.slotPos))
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int)
    nlinarith
  have hd : max (SA.proposalTime p.toParams s) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.voteTime p.toParams s := by
    rw [max_eq_left hprev, h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    rfl
  have hvd : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvz : SA.voteTime p.toParams s < SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have ht0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    positivity
  have hslot : N.erase.slot = s := pcsa_proposal_emitted_slot E rho x s N _ he
  have hfloor : p.slotOf (SA.proposalTime p.toParams s) = s := by
    change p.slotOf (4 * p.Δ * (s : Int)) = s
    simpa only [add_zero] using pcsa_slotOf_offset p s 0 le_rfl (by omega)
  intro y hy
  have hf := (h.frame y hy (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))).1
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hf
  have hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) y) o = false :=
    pcsa_body_not_excluded p _ s N P hf hP hRows
  obtain ⟨t, htt, htd, k, parent, hk, hh⟩ := h.delivery.broadcast x h.proposal.1 o
    (by change True; trivial) _ he y hy (by simpa only [hd] using hvd)
    (by simpa only [hd] using hNX)
  rw [hd] at htd
  have hpObj : parent = o :=
    pcsa_body_handles_direct (V2.D.Run.stateBefore E rho k y).st parent s N hh
  have hko : rho.events[k]? = some (.deliver y o t) := by rwa [hpObj] at hk
  have hWF := h.base.valid.wire k y o t hko
  have hDep := h.base.valid.deps k y o t hko
  have hFresh := h.base.valid.fresh k y o t hko
  have hclock := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS h.base.noRestart
    hko hpub ht0 htt
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho k y)] at hclock
  have hlarge : N.erase.slot ≤ (V2.D.Run.stateBefore E rho k y).st.slot p := by
    rw [hslot, ← hfloor]
    exact Int.toNat_le_toNat (Int.ediv_le_ediv (by omega) hclock)
  obtain ⟨hn, Q, hQ, hAcc⟩ := pcsa_body_accepted p _ s N P (h.frame y hy k).1 hP hRows
    hWF hDep hFresh hlarge
  have hb := pcsa_admitBlock_body_mem p _ s N Q
    (pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho k y)) hn hQ hAcc
  have hb' : N.erase ∈ (V2.D.Run.stateBefore E rho (k + 1) y).st.base.blocks := by
    rw [V2.D.Run.stateBefore_succ E rho hko]
    change N.erase ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks
    rw [Function.update_self]
    change N.erase ∈ (admitBlock p (V2.D.Run.stateBefore E rho k y).st s N).base.blocks
    exact hb
  have hidx := Nat.succ_le_of_lt
    ((Gen.V2.Duty.index_lt_idxBefore_iff hS hko _).mpr (htd.trans hvz))
  have hm := pcsa_body_stateBefore_mono E rho h.base.noRestart y hidx hb'
  rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm

/-- Formation's exact hPCCollect interface, with no body-receipt hypothesis. -/
theorem pcsa_formation_collect (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card → ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase :=
  pcsa_formation_collect_of_held_body E rho s N ΔF h
    (pcsa_formation_body_before_freeze E rho s N ΔF h)
end AvailableChain.PCSA.Run
end
