module
public import AvailableChainPCSAProofs.Proofs.Shared.StageStore
public import AvailableChainPCSAProofs.Proofs.Clean.FormationProposal
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Shared.CleanGate
public import AvailableChainFGSA.Proofs.Head.Walk

public section

/-! Formation step 5 on resolved support counts (pcsa34-r4.3 §5.3).
OPEN: derive the path, denominator, rival, and disjoint child counts from
the early honest votes and at most a faulty votes in the PC-SA run.
Use all honest HEAD senders for h, including senders asleep at e_s; F2
counts only nodes awake at both v_s and e_s, so h can exceed h_s.
Pool equality is not a premise. -/

namespace AvailableChain.PCSA

/-- Honest support above a faulty bound makes the raw gate result exact. -/
theorem pcsa_formation_gate_exact (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (a P : Block) (h f : Nat) (hFault : f < h)
    (hAnchor : Block.Prec a P)
    (hVoters : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) ≤ h + f)
    (hPath : ∀ C, Block.Prec a C → Block.Preceq C P →
      C ∈ v.blocks ∧ h ≤ SA.Root.prefixSupport p.toParams v s C)
    (hRivals : ∀ C, Block.Prec a C → Block.Preceq C P →
      ∀ D ∈ v.blocks, D.parent? = C.parent? → D ≠ C →
        SA.Root.prefixSupport p.toParams v s D ≤ f)
    (hChildren : ∀ D ∈ v.blocks, D.parent? = some P →
      SA.Root.prefixSupport p.toParams v s D ≤ f ∧
        h + SA.Root.prefixSupport p.toParams v s D ≤
          GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s)) :
    SA.Root.confirmationFrom p.toParams a v s = some P := by
  have ha : Block.Preceq a P := (Bool.and_eq_true_iff.mp hAnchor).2
  apply FGSA.fgsa_confirmationFrom_exact_of_dominated_suffix p v a P s ha
    ?_ ?_ (Or.inr hAnchor)
  · intro C hac hCP
    obtain ⟨hm, hs⟩ := hPath C hac hCP
    refine ⟨hm, decide_eq_true (by omega), ?_⟩
    intro D hD hpar _ hne
    have hd := hRivals C hac hCP D hD hpar hne
    omega
  · intro D hD hpar
    obtain ⟨hd, hcount⟩ := hChildren D hD hpar
    apply decide_eq_false
    omega


/-- The remaining counts at the actual gate input. -/
structure FormationGateCounts (p : Params) (st : State p.n) (s : Slot) (P : Block)
    (h f : Nat) : Prop where
  hVoters : GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView st) s) ≤ h + f
  hPath : ∀ C, Block.Prec (eraseFG st.fg.F) C → Block.Preceq C P →
    C ∈ (actView st).blocks ∧ h ≤ SA.Root.prefixSupport p.toParams (actView st) s C
  hRivals : ∀ C, Block.Prec (eraseFG st.fg.F) C → Block.Preceq C P →
    ∀ D ∈ (actView st).blocks, D.parent? = C.parent? → D ≠ C →
      SA.Root.prefixSupport p.toParams (actView st) s D ≤ f
  hChildren : ∀ D ∈ (actView st).blocks, D.parent? = some P →
    SA.Root.prefixSupport p.toParams (actView st) s D ≤ f ∧
      h + SA.Root.prefixSupport p.toParams (actView st) s D ≤
        GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView st) s)

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- The longer C7 window supplies the scheduled gate input at each honest node. -/
theorem pcsa_formation_gate_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) (y : V) (hy : y ∈ rho.honest) :
    ∃ st, gateInAt p c E rho y s = some st := by
  have hpub : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.gateTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    positivity
  have hm := h.base.valid.tick_total y hy _ hpub hz h.horizon
  have hsome : (V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hm, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨clockPre p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s), ?_⟩
  rw [pcsa_gateInAt_def, pcsa_preTick_def, hk]
  rfl

/-- Stage 1 and the positive proposal slot close the gate anchor input. -/
theorem pcsa_formation_gate_anchor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) (y : V) (hy : y ∈ rho.honest)
    (st : State p.n) (hr : gateInAt p c E rho y s = some st) :
    Block.Prec (eraseFG st.fg.F) N.erase := by
  obtain ⟨_, _, hSlot, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF
    (h.toPreFreeze p c E rho)
  have hF : st.fg.F = SimplexFG.FGBlock.genesis := by
    rw [pcsa_gateInAt_def] at hr
    obtain ⟨nd, hp, hc⟩ := Option.map_eq_some_iff.mp hr
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
    subst nd
    subst st
    rw [(pcsa_clockPre_frame p _ _).2.2.2.1]
    exact (h.frame y hy k).1
  rw [hF]
  change (!decide (Block.genesis = N.erase) && Block.preceq Block.genesis N.erase) = true
  have hne : (decide (Block.genesis = N.erase) : Bool) = false := by
    apply decide_eq_false
    intro he
    rw [← he] at hSlot
    change 0 = s at hSlot
    exact (Nat.ne_of_gt h.slotPos) hSlot.symm
  rw [hne, Bool.not_false, Bool.true_and]
  exact Gen.Pure.block_genesis_preceq N.erase

/-- The named late counts give Formation's gate part at its longer horizon. -/
theorem pcsa_formation_gate_of_counts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hGateCounts : ∀ y ∈ rho.honest, ∀ st, gateInAt p c E rho y s = some st →
      ∃ H, (awakeHonestLabel p c E rho s).card ≤ H ∧
        FormationGateCounts p st s N.erase H (Gen.V2.Duty.faulty rho).card) :
    (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card →
      ∀ y ∈ rho.honest, gateResultAt p c E rho y s = some (some N.erase) := by
  intro hf y hy
  obtain ⟨st, hr⟩ := pcsa_formation_gate_read E rho s N ΔF h y hy
  obtain ⟨H, hH, hc⟩ := hGateCounts y hy st hr
  have he := pcsa_formation_gate_exact p (actView st) s (eraseFG st.fg.F) N.erase
    H (Gen.V2.Duty.faulty rho).card (lt_of_lt_of_le hf hH)
    (pcsa_formation_gate_anchor E rho s N ΔF h y hy st hr) hc.hVoters
    hc.hPath hc.hRivals hc.hChildren
  rw [pcsa_gateResultAt_def, hr, Option.map_some, he]

end AvailableChain.PCSA.Run

end
