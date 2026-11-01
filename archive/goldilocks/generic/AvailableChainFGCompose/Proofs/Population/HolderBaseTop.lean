module
public import AvailableChainFGCompose.Statements.Channels
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import Mathlib.Tactic.Linarith -- shake: keep (arithmetic tactics)

public section

/-! Blueprint 21 HG.3 top J. The fixed entry age comes from the accepted top carrier
at the actual start, with the inclusive cut. The proposer frame, the justified source
and the seed-qualified repair facts are explicit leaves. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (Ef : Electorate (Fin n)) (cert : FGCertificateLaws Ef O.height O.finality)

omit [DecidableEq V] in
private theorem p0d5c_top_idx_le (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {e : V2.Event V Prot.Object} (hj : rho.events[j]? = some e) {u : Time}
    (hu : u ≤ e.time) : V2.D.Run.idxBefore rho u ≤ j := by
  by_contra hn
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj u).mp (Nat.lt_of_not_ge hn)
  exact (not_lt.mpr hu) hlt

include cert in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME an accepted nonzero J has an
actual earlier honest source; its slot is at least 6Δ before the start.
The earlier source is the justified-source leaf of the protocol's QC origin. -/
theorem frontierSearch_initial_J_age_core (hT : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho)
    (justifiedSource : ∀ i x, x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
        actionSourceFG R E rho T y r = some (some K) ∧
        (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    {i : Nat} {ev : V2.Event V Prot.Object} {x : V}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest)
    (hj : (R.core (rho.stateBefore E (i + 1) x)).fg.h_j ≠ 0) :
    T.proposal (R.core (rho.stateBefore E (i + 1) x)).fg.J.slot ≤ ev.time - 6 * T.delta := by
  obtain ⟨j, y, r, a, K, hji, ha, hK, hT'⟩ := justifiedSource (i + 1) x hx hj
  have hle := ancestorSlot r y _ _ ha.1 hK (cert.height.entry_preceq _)
  rw [hT'] at hle
  have hslot := sourceSlot r y _ ha.1 hK
  have htime : T.action r ≤ ev.time := by
    by_contra hn
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi (T.action r)).mpr (lt_of_not_ge hn)
    have hle' := p0d5c_top_idx_le E rho hs ha.2.1 (le_refl (T.action r))
    omega
  have hslotI : ((R.core (rho.stateBefore E (i + 1) x)).fg.J.slot : Time) ≤
      ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hle.trans hslot
  rw [hT.action_eq, hT.gate_eq, hT.proposal_eq] at htime
  rw [hT.proposal_eq]
  nlinarith [hT.delta_pos]

end AvailableChain.FGCompose
end
