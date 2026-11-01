module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGCompose.Proofs.Healing.PhaseSettle
public import AvailableChainFGCompose.Proofs.Population.HolderBaseRepair
public import AvailableChainFGCompose.Proofs.Population.HolderBaseService
public import AvailableChainFGCompose.Statements.Population.FrontierSearch

public section

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

include obs in
/-- The holder construction exposes its selected seed so an existing service can be restored. -/
theorem frontierSearch_save_seed_holder_witness_core (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q)
    (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hh : (O.height Qfg).h = m) (hs : FrontierProposalService R E rho T q Q)
    (hg : T.gate q ≤ D)
    (hlocal : FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m (T.gate q)) :
    ∃ u' J' contested' q' Q' Qfg',
      q' = q ∧ Q' = Q ∧ Qfg' = Qfg ∧
      Jst ≤ u' ∧ HonestProposal E rho I q' Q' ∧ R.erase Qfg' = Q' ∧
      (O.height Qfg').h = m ∧ FrontierProposalService R E rho T q' Q' ∧
      FrontierSeedQualification T leaseSlots E.t_GST u' q' ∧ u' ≤ T.proposal q' ∧
      PhaseInterval R E rho O u' (T.gate q') m J' contested' ∧ T.gate q' ≤ T.gate q ∧
      T.gate q ≤ rho.horizon ∧
      (∀ i x, timeIdx rho u' ≤ i → i ≤ timeIdx rho (T.gate q) → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) ∧
      FrontierLocalServiceFG R S E rho O T I pair q' Q' Qfg' m (T.gate q) := by
  obtain ⟨hu, hphase, hcap⟩ :=
    frontierSearch_save_seed_fields_core R E rho O T leaseSlots obs hT hk hp hseed hg
  exact ⟨u, J, contested, q, Q, Qfg, rfl, rfl, rfl, hready, hQ, he, hh, hs, hseed, hu,
    hphase, le_rfl, hg.trans hp.2.1, hcap, hlocal⟩

include obs in
/-- Blueprint 21 HG.3. DC: SAME save a complete seed at its actual gate.
The HEAD service and the local service at the gate are explicit leaves. -/
theorem frontierSearch_save_seed_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q)
    (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hh : (O.height Qfg).h = m) (hs : FrontierProposalService R E rho T q Q)
    (hg : T.gate q ≤ D)
    (hlocal : FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m (T.gate q)) :
    StrongServedFG R S E rho O T I pair Jst leaseSlots m (T.gate q) := by
  obtain ⟨u', J', c', q', Q', Qfg', _, _, _, h⟩ :=
    frontierSearch_save_seed_holder_witness_core R S E rho O T I pair Jst leaseSlots obs hT hk
      hready hp hseed hQ he hh hs hg hlocal
  exact ⟨u', J', c', q', Q', Qfg', h⟩

include obs in
/-- Restore the given all-node service for the exact seed selected by the holder construction. -/
theorem frontierSearch_save_seed_holder_local_core (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q)
    (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hh : (O.height Qfg).h = m) (hs : FrontierProposalService R E rho T q Q)
    (hg : T.gate q ≤ D)
    (hlocal : FrontierLocalService R S E rho O T I pair q Q Qfg m (T.gate q)) :
    StrongServed R S E rho O T I pair Jst leaseSlots m (T.gate q) := by
  obtain ⟨u', J', c', q', Q', Qfg', rfl, rfl, rfl,
    hr, hQ', he', hh', hs', hseed', hu, hp', hg', ht, hc, _⟩ :=
    frontierSearch_save_seed_holder_witness_core R S E rho O T I pair Jst leaseSlots obs hT hk
      hready hp hseed hQ he hh hs hg (frontierLocalService_to_holder_core hlocal)
  exact ⟨u', J', c', q', Q', Qfg', hr, hQ', he', hh', hs', hseed', hu, hp', hg', ht, hc,
    hlocal⟩

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 contest; plan R2-b.
DC: SAME stop at the finite first event, or save the repaired height-m seed.
The horizon is closed. The repair allowance is the published local repair service;
the gate copy and the continuing local service are leaves of a seed-qualified proposal. -/
theorem frontier_hg3_contest_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
      FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v)
    {i m : Nat} {ev : V2.Event V Prot.Object}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m .contest)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar
      (ev.time + 3 * T.delta))
    (hhor : ev.time + (ρbar + 3 * T.delta) ≤ rho.horizon) :
    FrontierHG3ResultFG R S E rho O T I pair Jst leaseSlots i m ev.time
      (ev.time + (ρbar + 3 * T.delta)) := by
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (FrontierSearchStart_def R E rho O T Jst i ev m .contest).mp hstart
  obtain ⟨_, l, hl, hrep⟩ := allowance
  rcases frontierSearch_first_effective_split R E rho O hs i
      (ev.time + (ρbar + 3 * T.delta)) with hstop | hquiet
  · rcases frontierSearch_classify_stop R E rho O mono hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (R := R) (E := E) (rho := rho) (O := O)
    (Ef := Ef) (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
    (Jst := Jst) (T := T) (positive := positive) (coreLaws := coreLaws)
    (erasePreceq := erasePreceq) (joined := joined) (receipt := receipt)
    crossing hs mono hdelta gst awake joinedTick readyCut hServices receiptHeld
    i ev _ m .contest hi hgst0 (by linarith) hhor hm hfront hkind hquiet
  have hready : Jst ≤ ev.time + 3 * T.delta := by linarith [hT.delta_pos]
  obtain ⟨_, hseedEx⟩ := hrep hG _ m none true hready hp
  obtain ⟨q, Q, hlq, hgate, hQ, hsvc⟩ := hseedEx (by linarith)
  have hseed := frontierSearch_seed_of_start_core E T leaseSlots hl hlq
  have hu := frontierSearch_seed_after_core T leaseSlots hT hk hseed
  have hgateD : T.gate q ≤ ev.time + (ρbar + 3 * T.delta) := by linarith
  obtain ⟨j, x, Qfg, hj0, hj1, hx, hmem, hErase⟩ :=
    gateCopy _ _ m none true q Q hready hp hseed hgateD hQ
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights_core R E rho O T I Jst Ef obs cert inv
    floor hready hp hu hgateD hQ hErase ⟨j, x, hj0, hj1, hx, hmem⟩
  have hh : (O.height Qfg).h = m := Nat.le_antisymm hhi hlo
  have ht : ev.time ≤ T.gate q := by
    rw [hT.gate_eq]
    linarith [hT.delta_pos]
  have hpq := frontierSearch_phase_cut_core R E rho O hp (hu.trans (by
    rw [hT.gate_eq]; linarith [hT.delta_pos])) hgateD
  exact Or.inr (Or.inr ⟨_, ht, hgateD,
    frontierSearch_save_seed_holder R S E rho O T I pair Jst leaseSlots obs hT hk hready hp hseed hQ
      hErase hh hsvc hgateD
      (service _ _ m none true q Q Qfg hready hQ hErase hh hsvc hseed hu hpq le_rfl
        (hgateD.trans hhor) (frontierSearch_phase_cap_core R E rho O obs hp hgateD))⟩)

end AvailableChain.FGCompose
end
