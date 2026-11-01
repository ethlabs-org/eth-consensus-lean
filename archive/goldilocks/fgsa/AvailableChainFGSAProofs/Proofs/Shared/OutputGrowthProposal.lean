module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp -- shake: keep (source declarations)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan A2: a scheduled joined positive-slot proposer emits an actual
proposal. The block includes the application value and keeps slot s. -/
theorem fgsa_proposal_emission_exists_of_awake_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) {s : Slot}
    (hh : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (ha : E.awake (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) = true)
    (hJ : ∀ w, 0 ≤ w → w ≤ V2.D.proposalTime (fgsaInterface p c) s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ 4 * p.Δ * ((s : Int) - 1))
    (hhor : V2.D.proposalTime (fgsaInterface p c) s ≤ rho.horizon) :
    ∃ o B, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
      (V2.D.proposalTime (fgsaInterface p c) s) ∧
      (fgsaInterface p c).block o.payload = some B ∧ B.slot = s := by
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let t := V2.D.proposalTime (fgsaInterface p c) s
  have he : ((4 * s : Nat) : Time) * p.Δ = t := by
    change ((4 * s : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int)
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hΔ v hh.2 (4 * s) (he ▸ hhor)
    (by simpa only [he] using ha)
  rw [he] at hi
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t
  let raw := proposerVotes st s
  let sup := proposerSupport st s
  let H := getHead p st raw sup
  let rows := proposalRows p st H
  obtain ⟨P, hP, _, _⟩ := propose_parent_lookup p
    (Reachable.tick t (reachable_stateBefore E rho i v)) s
  let N := namedProposal p P s (c.app (rho.input v t))
    (raw.filterMap liftHead?) (sup.filterMap liftHead?) rows
  let m := Msg.proposal N
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩
  have hm : o ∈ (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).2 := by
    apply (fgsa_emits_proposal E rho _ v t s m).mpr
    refine ⟨ha, rfl, rfl, ?_, ?_⟩
    · apply fgsa_joinedNow_of_joinedEnv E rho hs hi
      intro w hw ht hr
      have hslot : p.slotOf t = s :=
        (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i v) _).2.symm.trans
          (fgsa_proposal_slot (c := c) (V2.D.Run.stateBefore E rho i v) s)
      rw [hslot]
      exact hJ w hw ht hr
    · delta propose
      simp only [Nat.ne_of_gt hh.1, ↓reduceIte, hP, Option.map_some]
      rfl
  refine ⟨o, N.erase, ⟨i, hi, ?_⟩, rfl, rfl⟩
  rw [(V2.D.Run.step_tick_eq E rho hi).2]
  exact hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A2: adapt the raw emission to HonestProposal and retain its slot. -/
theorem fgsa_honestProposal_exists_of_awake_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) {s : Slot}
    (hh : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (ha : E.awake (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) = true)
    (hJ : ∀ w, 0 ≤ w → w ≤ V2.D.proposalTime (fgsaInterface p c) s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ 4 * p.Δ * ((s : Int) - 1))
    (hhor : V2.D.proposalTime (fgsaInterface p c) s ≤ rho.horizon) :
    ∃ B, HonestProposal E rho (fgsaInterface p c) s B ∧ B.slot = s := by
  obtain ⟨o, B, ho, hb, hslot⟩ :=
    fgsa_proposal_emission_exists_of_awake_slot E rho hs hΔ hh ha hJ hhor
  exact ⟨B, ⟨hh, o, ho, hb⟩, hslot⟩

end AvailableChain.FGSA.Run
end
