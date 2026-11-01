module

public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair

public import AvailableChainFGCompose.Proofs.Population.HolderBaseService

public section

/-! Blueprint 21 HG.3; run 2 R2-b. Generic contest phase consumer.
The repair allowance is the published local repair service. The protocol supplies
the proposer floor, the held gate copy and the continuing local service of a
seed-qualified proposal as explicit leaves. No weak served witness builds a seed. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots : Nat)
variable (Ef : Electorate (Fin n)) (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME inclusive-prefix monotonicity. -/
theorem frontierSearch_timeIdx_mono {u v : Time} (h : u ≤ v) :
    timeIdx rho u ≤ timeIdx rho v := by
  exact frontierSearch_timeIdx_mono_core rho h

/-- Blueprint 21 HG.3. DC: SAME a shorter phase keeps the lower read cut. -/
theorem frontierSearch_phase_cut {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
    PhaseInterval R E rho O u w m J contested := by
  exact frontierSearch_phase_cut_core R E rho O hp huw hwv

/-- Blueprint 21 HG.3. DC: SAME a seed follows its phase start in both arms. -/
theorem frontierSearch_seed_after (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {GST u : Time} {q : Slot}
    (hseed : FrontierSeedQualification T leaseSlots GST u q) : u ≤ T.proposal q := by
  exact frontierSearch_seed_after_core T leaseSlots hT hk hseed

omit [DecidableEq V] in
/-- A first label after the phase start gives the seed qualification of each later
proposal of the repair window. -/
theorem frontierSearch_seed_of_start {u : Time} {l q : Slot}
    (hstart : FrontierRepairStart E T leaseSlots u l) (hlq : T.proposal l < T.proposal q) :
    FrontierSeedQualification T leaseSlots E.t_GST u q := by
  exact frontierSearch_seed_of_start_core E T leaseSlots hstart hlq

omit [DecidableEq V] in
/-- A seed-qualified proposal stays qualified for every later proposal. -/
theorem frontierSearch_seed_later {GST u : Time} {q s : Slot}
    (hseed : FrontierSeedQualification T leaseSlots GST u q)
    (hqs : T.proposal q < T.proposal s) :
    FrontierSeedQualification T leaseSlots GST u s := by
  exact frontierSearch_seed_later_core T leaseSlots hseed hqs

include obs in
/-- The phase cap read: inside the phase cut, each honest cumulative frontier is m. -/
theorem frontierSearch_phase_hmax {u v : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) {i : Nat} {x : V}
    (hui : V2.D.Run.idxBefore rho u ≤ i) (hiv : i ≤ timeIdx rho v) (hx : x ∈ rho.honest) :
    (R.core (rho.stateBefore E i x)).fg.h_max = m := by
  exact frontierSearch_phase_hmax_core R E rho O obs hp hui hiv hx

include obs in
/-- The saved seed's honest cap from the inclusive phase start through the gate. -/
theorem frontierSearch_phase_cap {u v t : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) (htv : t ≤ v) :
    ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m := by
  exact frontierSearch_phase_cap_core R E rho O obs hp htv

include obs cert inv in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3. DC: SAME the proposer floor and exact-gate cap.
The floor is the published proposal-floor leaf; the cap reads the held gate copy. -/
theorem frontierSearch_proposal_heights (floor : AttemptProposalFloor R E rho O T I Jst)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hu : u ≤ T.proposal q) (hgate : T.gate q ≤ D)
    (hQ : HonestProposal E rho I q Q) (heq : R.erase Qfg = Q)
    (hcopy : ∃ i x, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho D ∧
      x ∈ rho.honest ∧ Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF) :
    (if contested then m else m - 1) ≤ (O.height Qfg).h ∧ (O.height Qfg).h ≤ m := by
  exact frontierSearch_proposal_heights_core R E rho O T I Jst Ef obs cert inv floor hready hp hu
    hgate hQ heq hcopy

include obs in
/-- Blueprint 21 HG.3. DC: SAME save a complete seed at its actual gate.
The HEAD service and the local service at the gate are explicit leaves. -/
theorem frontierSearch_save_seed (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q)
    (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hh : (O.height Qfg).h = m) (hs : FrontierProposalService R E rho T q Q)
    (hg : T.gate q ≤ D)
    (hlocal : FrontierLocalService R S E rho O T I pair q Q Qfg m (T.gate q)) :
    StrongServed R S E rho O T I pair Jst leaseSlots m (T.gate q) := by
  exact frontierSearch_save_seed_holder_local_core R S E rho O T I pair Jst leaseSlots obs hT hk
    hready hp hseed hQ he hh hs hg hlocal

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 contest; plan R2-b.
DC: SAME stop at the finite first event, or save the repaired height-m seed.
The horizon is closed. The repair allowance is the published local repair service;
the gate copy and the continuing local service are leaves of a seed-qualified proposal. -/
theorem frontier_hg3_contest (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (crossing : RXing R E rho O) (hs : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R) (hdelta : E.Δ = T.delta) (gst : E.t_GST ≤ Jst)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (Prot.clock (rho.stateBefore E iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
    {G ρbar : Time} (hG : 4 * T.delta ≤ G)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalService R S E rho O T I pair q Q Qfg m v)
    {i m : Nat} {ev : V2.Event V Prot.Object}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m .contest)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar
      (ev.time + 3 * T.delta))
    (hhor : ev.time + (ρbar + 3 * T.delta) ≤ rho.horizon) :
    FrontierHG3Result R S E rho O T I pair Jst leaseSlots i m ev.time
      (ev.time + (ρbar + 3 * T.delta)) := by
  have result := frontier_hg3_contest_holder R S E rho O T I pair Jst leaseSlots Ef obs cert inv
    justif keep positive coreLaws erasePreceq joined receipt hT hk crossing hs mono hdelta gst
    awake joinedTick readyCut hServices receiptHeld hG floor gateCopy (fun u v m J c q Q Qfg hr hQ
    he hh hs hseed hu hp hg ht hc => frontierLocalService_to_holder_core (service u v m J c q Q Qfg
    hr hQ he hh hs hseed hu hp hg ht hc)) hstart allowance hhor
  rcases result with h | h | ⟨t, hlo, hhi, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨t, hlo, hhi, strongServed_of_holder_service_core service hs⟩)

end AvailableChain.FGCompose
end
