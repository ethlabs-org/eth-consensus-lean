module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRetainedTree
public import AvailableChainPCSAProofs.Proofs.Clean.CommonRaw
public import AvailableChainPCSAProofs.Proofs.Clean.CommonSupport
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ProposerInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ResolutionDomain

public section

/-! The two retained back receipts from the frozen raw relay. The carried
arms are the proposal's own lists. A frozen support HEAD relays as a raw
HEAD, and Formation body relay gives its body at the proposer. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [Fintype V] in
private theorem back_carried (s : Slot) (l : List (GridCO.Wire p.n .root))
    (hl : ∀ w ∈ l, GridCO.headLabel? w = some s) :
    ∀ o ∈ (l.filterMap liftHead?).map baseVote, o ∈ l := by
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
  obtain ⟨w, hw, hwa⟩ := List.mem_filterMap.mp ha
  have hb := pcsa_liftHead_baseVote w s (hl w hw)
  rw [hwa] at hb
  rw [Option.some.inj hb]
  exact hw

/-- The retained input that stays open: the frozen raw relay. A slot-`(s-1)`
HEAD stamped before `z_{s-1}` at the voter read is a proposer HEAD, or its
seat is capped at the proposer. -/
structure FormationFrozenRawOpen (p : Params) (src dst : Node p) (s : Slot) : Prop where
  hFrozen : ∀ (i : Fin p.n) (r : BlockId),
    (⟨.seat (s - 1) i, .head r⟩ : GridCO.Wire p.n .root) ∈ dst.st.base.votes →
    GridCO.stampVote dst.st.base ⟨.seat (s - 1) i, .head r⟩ <
      SA.freezeTime p.toParams (s - 1) →
    (⟨.seat (s - 1) i, .head r⟩ : GridCO.Wire p.n .root) ∈ proposerVotes src.st s ∨
      GridCO.equivocates (proposerVotes src.st s) i = true

/-- The frozen raw relay gives both retained back receipts. -/
theorem pcsa_formation_retained_back_of_frozen (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hOpen : FormationFrozenRawOpen p src dst s) :
    FormationRetainedBackOpen p src dst s N := by
  have hFrozen := hOpen.hFrozen
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hlabV : ∀ w ∈ proposerVotes src.st s, GridCO.headLabel? w = some (s - 1) :=
    fun w hw => beq_iff_eq.mp (List.mem_filter.mp hw).2
  have hlabS : ∀ w ∈ proposerSupport src.st s, GridCO.headLabel? w = some (s - 1) :=
    fun w hw => hlabV w (List.mem_filter.mp hw).1
  rw [pcsa_postClock_def] at hSrc hDst
  obtain ⟨pre, hpre, hc⟩ := Option.map_eq_some_iff.mp hSrc
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hidx, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst src
  obtain ⟨pre', hpre', hc'⟩ := Option.map_eq_some_iff.mp hDst
  rw [pcsa_preTick_def] at hpre'
  obtain ⟨a, _, he'⟩ := Option.map_eq_some_iff.mp hpre'
  subst pre'
  subst dst
  have htick := V2.D.Run.tickIdx?_spec hidx
  constructor
  · intro o ho i hi
    rcases pcsa_honest_headVotes_source E rho h.base.valid a y _ s N h.proposal.1
        h.proposal.2 o ho with ⟨hm, ht⟩ | hm
    · have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hm).2
      obtain ⟨r, rfl⟩ := pcsa_count_head_shape o (s - 1) i hl hi
      exact hFrozen i r (List.mem_filter.mp hm).1 ht
    · left
      rw [hInputs.2.2.2.1] at hm
      exact back_carried (s - 1) _ hlabV o hm
  · intro o ho i hi
    rcases pcsa_honest_headSupport_source E rho h.base.valid a y _ s N h.proposal.1
        h.proposal.2 o ho with ⟨hm, hr⟩ | hm
    · have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hm).2
      obtain ⟨r, rfl⟩ := pcsa_count_head_shape o (s - 1) i hl hi
      obtain ⟨B, hres, hslot, hstamp, hbodyStamp⟩ := pcsa_frozen_support_data p _ s _ hm hr
      have hroot := FGSA.Run.resolvedHead_root _ _ hres
      change some r = some B.root at hroot
      have heq := Option.some.inj hroot
      subst r
      rcases hFrozen i B.root (List.mem_filter.mp hm).1 hstamp with hraw | hcap
      · left
        have hbody := pcsa_formation_frozen_body_in_proposer E rho s N ΔF h a k y hy _ htick B
          (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hres)).1 hbodyStamp
        have hlookup := pcsa_resolved_head_of_held_body E rho h.base h.frame k _ h.proposal.1
          (s - 1) i B (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) hbody
        change _ ∈ proposerSupport (clock p (V2.D.Run.stateBefore E rho k _).st _) s
        apply List.mem_filter.mpr
        refine ⟨hraw, ?_⟩
        rw [hlookup]
        exact decide_eq_true hslot
      · exact Or.inr hcap
    · left
      rw [hInputs.2.2.2.2] at hm
      exact back_carried (s - 1) _ hlabS o hm

/-- The pre-freeze inputs from the premise and the frozen raw relay. -/
theorem pcsa_formation_preFreeze_inputs_of_frozen (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hFrozen : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationFrozenRawOpen p src dst s) :
    FormationPreFreezeInputs E rho s N :=
  pcsa_formation_preFreeze_inputs_of_back E rho s N ΔF h (fun src dst y hs hy haw hd =>
    pcsa_formation_retained_back_of_frozen E rho s N ΔF h src dst y hs hy hd
      (hFrozen src dst y hs hy haw hd))

end AvailableChain.PCSA.Run
end
