module
public import AvailableChainFGCompose.Statements.FrontierSearch
public import AvailableChainFGCompose.Proofs.Healing.PhaseFrame
public import Mathlib.Tactic.Linarith -- shake: keep (arithmetic tactics)
public import Mathlib.Tactic.Ring -- shake: keep (ring tactic)

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
theorem frontierSearch_timeIdx_mono_core {u v : Time} (h : u ≤ v) :
    timeIdx rho u ≤ timeIdx rho v := by
  rw [timeIdx_def, timeIdx_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    ((of_decide_eq_true he).trans h))

/-- Blueprint 21 HG.3. DC: SAME a shorter phase keeps the lower read cut. -/
theorem frontierSearch_phase_cut_core {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
    PhaseInterval R E rho O u w m J contested :=
  ⟨huw, hwv.trans hp.2.1, hp.2.2.1, fun i x hui hiw hx =>
    hp.2.2.2 i x hui (hiw.trans (frontierSearch_timeIdx_mono_core rho hwv)) hx⟩

/-- Blueprint 21 HG.3. DC: SAME a seed follows its phase start in both arms. -/
theorem frontierSearch_seed_after_core (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {GST u : Time} {q : Slot}
    (hseed : FrontierSeedQualification T leaseSlots GST u q) : u ≤ T.proposal q := by
  have hd := hT.delta_pos
  rcases (FrontierSeedQualification_def T leaseSlots GST u q).mp hseed with
    ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
  · have hl : β ≤ β + 2 * leaseSlots - 1 :=
      Nat.le_sub_of_add_le (Nat.add_le_add_left (show 1 ≤ 2 * leaseSlots by omega) β)
    have hli : (β : Time) ≤ ((β + 2 * leaseSlots - 1 : Nat) : Time) := by exact_mod_cast hl
    have ht : T.proposal β ≤ T.proposal (β + 2 * leaseSlots - 1) := by
      rw [hT.proposal_eq, hT.proposal_eq]
      nlinarith
    exact hβ.le.trans (ht.trans hlt.le)
  · rw [hT.vote_eq, hT.proposal_eq] at hb
    rw [hT.proposal_eq, hT.proposal_eq] at hlt
    rw [hT.proposal_eq]
    have hqN : b + 1 ≤ q := by
      by_contra hn
      have hle : (q : Time) ≤ ((b + leaseSlots : Nat) : Time) := by
        exact_mod_cast (Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_of_not_le hn))
          (Nat.le_add_right b leaseSlots))
      nlinarith
    have hq : (b : Time) + 1 ≤ q := by exact_mod_cast hqN
    nlinarith

omit [DecidableEq V] in
/-- A first label after the phase start gives the seed qualification of each later
proposal of the repair window. -/
theorem frontierSearch_seed_of_start_core {u : Time} {l q : Slot}
    (hstart : FrontierRepairStart E T leaseSlots u l) (hlq : T.proposal l < T.proposal q) :
    FrontierSeedQualification T leaseSlots E.t_GST u q := by
  cases hstart with
  | two β after least => exact Or.inl ⟨β, after, least, hlq⟩
  | one b after least window sync => exact Or.inr ⟨b, after, least, window, sync, hlq⟩

omit [DecidableEq V] in
/-- A seed-qualified proposal stays qualified for every later proposal. -/
theorem frontierSearch_seed_later_core {GST u : Time} {q s : Slot}
    (hseed : FrontierSeedQualification T leaseSlots GST u q)
    (hqs : T.proposal q < T.proposal s) :
    FrontierSeedQualification T leaseSlots GST u s := by
  rcases hseed with ⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, hw, hsync, hlt⟩
  · exact Or.inl ⟨β, hβ, hmin, hlt.trans hqs⟩
  · exact Or.inr ⟨b, hb, hmin, hw, hsync, hlt.trans hqs⟩

omit [DecidableEq V] in
private theorem p0d5c_rep_idx_le (t : Time) :
    V2.D.Run.idxBefore rho t ≤ timeIdx rho t := by
  change (rho.events.filter (fun e => decide (e.time < t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he => decide_eq_true (of_decide_eq_true he).le

include obs in
/-- The phase cap read: inside the phase cut, each honest cumulative frontier is m. -/
theorem frontierSearch_phase_hmax_core {u v : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) {i : Nat} {x : V}
    (hui : V2.D.Run.idxBefore rho u ≤ i) (hiv : i ≤ timeIdx rho v) (hx : x ∈ rho.honest) :
    (R.core (rho.stateBefore E i x)).fg.h_max = m := by
  have h := (hp.2.2.2 i x hui hiv hx).1
  rw [obs.controls_eq] at h
  exact h

include obs in
/-- The saved seed's honest cap from the inclusive phase start through the gate. -/
theorem frontierSearch_phase_cap_core {u v t : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) (htv : t ≤ v) :
    ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m := by
  intro i x hui hit hx
  exact (frontierSearch_phase_hmax_core R E rho O obs hp ((p0d5c_rep_idx_le rho u).trans hui)
    (hit.trans (frontierSearch_timeIdx_mono_core rho htv)) hx).le

include obs cert inv in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3. DC: SAME the proposer floor and exact-gate cap.
The floor is the published proposal-floor leaf; the cap reads the held gate copy. -/
theorem frontierSearch_proposal_heights_core (floor : AttemptProposalFloor R E rho O T I Jst)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hu : u ≤ T.proposal q) (hgate : T.gate q ≤ D)
    (hQ : HonestProposal E rho I q Q) (heq : R.erase Qfg = Q)
    (hcopy : ∃ i x, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho D ∧
      x ∈ rho.honest ∧ Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF) :
    (if contested then m else m - 1) ≤ (O.height Qfg).h ∧ (O.height Qfg).h ≤ m := by
  have hlo := floor u D m J contested q Q Qfg hready hp hu hgate hQ heq
  have hparent : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  refine ⟨hlo.trans (cert.height.h_mono hparent), ?_⟩
  obtain ⟨i, x, hui, hiD, hx, hK⟩ := hcopy
  have hh := healing_phase_height_le (R := R) (E := E) (rho := rho) (O := O) (inv := inv) hK
  rw [frontierSearch_phase_hmax_core R E rho O obs hp hui hiD hx] at hh
  exact hh

include obs in
/-- The fixed seed's shared bounds, before choosing a population for its local service. -/
theorem frontierSearch_save_seed_fields_core (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q) (hg : T.gate q ≤ D) :
    u ≤ T.proposal q ∧ PhaseInterval R E rho O u (T.gate q) m J contested ∧
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho (T.gate q) → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) := by
  have hu := frontierSearch_seed_after_core T leaseSlots hT hk hseed
  have huq : u ≤ T.gate q := by
    rw [hT.gate_eq]
    linarith [hT.delta_pos]
  exact ⟨hu, frontierSearch_phase_cut_core R E rho O hp huq hg,
    frontierSearch_phase_cap_core R E rho O obs hp hg⟩

end AvailableChain.FGCompose
end
