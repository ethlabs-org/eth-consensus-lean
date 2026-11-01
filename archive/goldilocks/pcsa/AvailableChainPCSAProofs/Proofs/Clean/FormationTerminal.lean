module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSourceRetention

public section

/-! Formation terminal tree facts. Handler slot bounds and sorted run times
exclude children of a current-slot block at its duty read. This closes hStop
for the actual retained voter tree. -/

namespace AvailableChain.PCSA

private theorem formation_accepted_slots (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (h : blockAccepted p st s N P = true) :
    N.erase.slot ≤ st.slot p ∧ N.erase.parent.slot < N.erase.slot := by
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at h
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hSlot⟩, _⟩, _⟩, hParent⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ⟨hSlot, hParent⟩

/-- Handler slot bounds retain the slot bound of the cumulative block list. -/
theorem pcsa_formation_process_slot_bound (p : Params) (st : State p.n) (o : Wire p.n) (s : Slot)
    (hOld : ∀ b ∈ st.base.blocks, b.slot ≤ s) (hSlot : st.slot p ≤ s) :
    ∀ b ∈ (process p st o).base.blocks, b.slot ≤ s := by
  apply pcsa_formation_process_body_scope p (fun b => b.slot ≤ s) st o hOld
  intro r N _ P hAcc
  exact (formation_accepted_slots p st r N P hAcc).1.trans hSlot

/-- Every reachable non-genesis block has a parent in an earlier slot. -/
theorem pcsa_formation_parent_slots (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ b ∈ st.base.blocks, b ≠ .genesis → b.parent.slot < b.slot := by
  induction h with
  | init =>
    intro b hb hn
    exact (hn (List.mem_singleton.mp hb)).elim
  | tick t _ ih =>
    exact pcsa_clock_body_scope p (fun b => b ≠ .genesis → b.parent.slot < b.slot)
      _ t ih
  | deliver o _ ih =>
    apply pcsa_formation_process_body_scope p _ _ o ih
    intro r N _ P hAcc _
    exact (formation_accepted_slots p _ r N P hAcc).2

private theorem formation_slot_le_of_now (p : Params) (a b : Time) (hab : a ≤ b) :
    p.slotOf a ≤ p.slotOf b := by
  change (a / (4 * p.Δ)).toNat ≤ (b / (4 * p.Δ)).toNat
  have hdiv : a / (4 * p.Δ) ≤ b / (4 * p.Δ) :=
    Int.ediv_le_ediv (by have hd : (0 : Int) < p.Δ := p.deltaPos; omega) hab
  exact Int.toNat_le_toNat hdiv
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Stored blocks before a scheduled tick do not exceed the tick slot. -/
theorem pcsa_formation_slots_before_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ScheduleWellFormed E rho)
    (y : V) (i : Nat) (t : Time) (s : Slot)
    (hi : rho.events[i]? = some (.tick y t)) (hs : p.slotOf t = s) :
    ∀ b ∈ (V2.D.Run.stateBefore E rho i y).st.base.blocks, b.slot ≤ s := by
  have hz : ∀ b ∈ (initial p.n).base.blocks, b.slot ≤ s := by
    intro b hb
    obtain rfl := List.mem_singleton.mp hb
    exact Nat.zero_le s
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ∀ b ∈ nd.st.base.blocks, b.slot ≤ s) (Nat.zero_le i) y ?_ hz
  intro k e _ hki he hn hm
  cases e with
  | restart x u =>
    change x = y at hn
    subst x
    change ∀ b ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks, b.slot ≤ s
    rw [Function.update_self]
    exact hz
  | tick x u =>
    change x = y at hn
    subst x
    change ∀ b ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks, b.slot ≤ s
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y u
    rw [ht, pcsa_clock_blocks]
    exact hm
  | deliver x o u =>
    change x = y at hn
    subst x
    have hut : u ≤ t := by
      have hkl := (List.getElem?_eq_some_iff.mp he).1
      have hil := (List.getElem?_eq_some_iff.mp hi).1
      have hkey := (List.pairwise_iff_getElem.mp hv.sorted) k i hkl hil hki
      rw [(List.getElem?_eq_some_iff.mp he).2, (List.getElem?_eq_some_iff.mp hi).2] at hkey
      exact V2.D.Engine.time_le_of_key_le _ _ hkey
    have hnow := pcsa_formation_now_before_event E rho hv k (.deliver y o u) he y
    have hslot : (V2.D.Run.stateBefore E rho k y).st.slot p ≤ s := by
      change p.slotOf (V2.D.Run.stateBefore E rho k y).st.base.now ≤ s
      rw [← hs]
      exact formation_slot_le_of_now p _ _ (hnow.trans hut)
    change ∀ b ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks, b.slot ≤ s
    rw [Function.update_self]
    exact pcsa_formation_process_slot_bound p _ (toWire p o) s hm hslot

/-- A scheduled duty read has no stored block after its slot. -/
theorem pcsa_formation_read_slot_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ScheduleWellFormed E rho)
    (y : V) (t : Time) (s : Slot) (nd : Node p)
    (hr : pcsa_postClock E rho y t = some nd) (hs : p.slotOf t = s) :
    ∀ b ∈ nd.st.base.blocks, b.slot ≤ s := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  change ∀ b ∈ (clock p (V2.D.Run.stateBefore E rho k y).st t).base.blocks, b.slot ≤ s
  rw [pcsa_clock_blocks]
  exact pcsa_formation_slots_before_tick E rho hv y k t s (V2.D.Run.tickIdx?_spec hk) hs

/-- A current-slot block has no stored child at the same-slot read. -/
theorem pcsa_formation_no_child_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ScheduleWellFormed E rho)
    (y : V) (t : Time) (s : Slot) (nd : Node p) (B : Block)
    (hr : pcsa_postClock E rho y t = some nd) (hs : p.slotOf t = s) (hB : B.slot = s) :
    ∀ D ∈ nd.st.base.blocks, D.parent? ≠ some B := by
  have hbound := pcsa_formation_read_slot_bound E rho hv y t s nd hr hs
  have hReach : Reachable p nd.st := by
    rw [← pcsa_formation_read_afterTicks E rho hv y t nd hr]
    exact reachable_storeAfterTicks E rho t y
  intro D hd hp
  have hDne : D ≠ .genesis := by
    intro hg
    rw [hg] at hp
    cases hp
  have hlt := pcsa_formation_parent_slots p nd.st hReach D hd hDne
  have hpar : D.parent = B := by
    cases D with
    | genesis => cases hp
    | node parent slot root body => exact Option.some.inj hp
  rw [hpar, hB] at hlt
  exact (Nat.not_lt_of_ge (hbound D hd)) hlt
variable [Fintype V]

/-- The actual voter tree has no child of the Formation proposal. -/
theorem pcsa_formation_head_terminal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (nd : Node p)
    (hr : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd) :
    Gen.Pure.NoEligibleChild
      (erasedList nd.st (KitFG.storeFrameView (FGSA.heightView p) nd.st.fg
        (voterBlocks p nd.st s)))
      (eligible p nd.st (headVotes p nd.st s) (headSupport p nd.st s)) N.erase := by
  obtain ⟨_, _, hSlot, _, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  have ht : p.slotOf (SA.voteTime p.toParams s) = s :=
    pcsa_slotOf_offset p s p.Δ (le_of_lt p.deltaPos)
      (by have hd : (0 : Int) < p.Δ := p.deltaPos; omega)
  have hNo := pcsa_formation_no_child_at_read E rho h.base.valid.toScheduleWellFormed
    y _ s nd N.erase hr ht hSlot
  rw [Gen.Pure.NoEligibleChild_def]
  intro D hd hp
  exact (hNo D (List.mem_filter.mp hd).1 hp).elim

/-- The run slot bounds close the retained HEAD stop input. -/
theorem pcsa_formation_head_exact_of_run_terminal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.voteTime p.toParams s) = true)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hRawKeep : proposerVotes src.st s ⊆ headVotes p dst.st s)
    (hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hSupportKeep : proposerSupport src.st s ⊆ headSupport p dst.st s)
    (hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hResolution : ∀ o ∈ proposerSupport src.st s, ∀ B,
      Gen.AC.Root.voteSupports src.st.base.blocks B o =
        Gen.AC.Root.voteSupports dst.st.base.blocks B o)
    (hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)))
    (hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)))
    (hChild : N.erase ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)))
    (hUnique : ∀ B ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
      B.parent? = some N.erase.parent →
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
      B = N.erase)
    : headVote p dst.st s = N.erase := by
  exact pcsa_formation_head_exact_of_retained_inputs E rho s N ΔF h src dst y
    hSrc hy haw hDst hRawKeep hRawBack hSupportKeep hSupportBack hResolution hKeep hReflect
    hChild hUnique (pcsa_formation_head_terminal E rho s N ΔF h y dst hDst)

end AvailableChain.PCSA.Run

end
