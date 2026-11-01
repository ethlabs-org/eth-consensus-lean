module
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBody
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalStore

public section

/-! C6 ProposalDelivery: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- From the window floor, every honest emitted proposal is stored, with its exact
metadata, before the voter read. -/
theorem pcsa_honest_proposal_before_vote_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (s : Slot)
    (N : NamedProposal p.n)
    (he : V2.D.Run.emits E rho x (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s))
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.voteTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k) :
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals ∧
      N.erase ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks := by
  let obj : Obj p := ⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩
  obtain ⟨P, hP, hRows⟩ := pcsa_emitted_body_rows E rho hF x hx s N he
  have hS := h.valid.toScheduleWellFormed
  have hp := p.deltaPos
  have hdeadline : SA.proposalTime p.toParams s + E.Δ = SA.voteTime p.toParams s := by
    rw [h.delta]
    rfl
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    positivity
  have hslot : N.erase.slot = s := pcsa_proposal_emitted_slot E rho x s N _ he
  have hfloor : p.slotOf (SA.proposalTime p.toParams s) = s := by
    change p.slotOf (4 * p.Δ * (s : Int)) = s
    simpa only [add_zero] using pcsa_slotOf_offset p s 0 le_rfl (mul_pos (by norm_num) p.deltaPos)
  have hf := (hF y hy (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))).1
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hf
  have hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s + E.Δ) y) obj = false := by
    rw [hdeadline]
    exact pcsa_body_not_excluded p _ s N P hf hP hRows
  obtain ⟨t, hlo, hhi, j, parent, hj, hh⟩ := pcsa_strict_broadcast_win E rho hD obj
    (by intro body heq; cases heq) x y _ hx hy he hT (by rwa [hdeadline]) hNX
  rw [hdeadline] at hhi
  have hpObj : parent = obj :=
    pcsa_body_handles_direct (V2.D.Run.stateBefore E rho j y).st parent s N hh
  have hjo : rho.events[j]? = some (.deliver y obj t) := by rwa [hpObj] at hj
  have hw := h.valid.wire j y obj t hjo
  have hd := h.valid.deps j y obj t hjo
  have hFresh := h.valid.fresh j y obj t hjo
  have hclock := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS h.noRestart
    hjo hpub hz hlo
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j y)] at hclock
  have hlarge : N.erase.slot ≤ (V2.D.Run.stateBefore E rho j y).st.slot p := by
    rw [hslot, ← hfloor]
    have hden : (0 : Int) < 4 * p.Δ := mul_pos (by norm_num) p.deltaPos
    exact Int.toNat_le_toNat (Int.ediv_le_ediv hden hclock)
  obtain ⟨hn, Q, hQ, hAcc⟩ := pcsa_body_accepted p _ s N P (hF y hy j).1 hP hRows
    hw hd hFresh hlarge
  have hpMem : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.proposals := by
    rw [V2.D.Run.stateBefore_succ E rho hjo]
    change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.proposals
    rw [Function.update_self]
    change _ ∈ (admitBlock p (V2.D.Run.stateBefore E rho j y).st s N).proposals
    rw [pcsa_clean_admitBlock_proposals p _ s N Q hn hQ hAcc]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hbMem : N.erase ∈ (V2.D.Run.stateBefore E rho (j + 1) y).st.base.blocks := by
    rw [V2.D.Run.stateBefore_succ E rho hjo]
    change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.base.blocks
    rw [Function.update_self]
    exact pcsa_admitBlock_body_mem p _ s N Q
      (pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho j y)) hn hQ hAcc
  have hidx : j + 1 ≤ k := (Nat.succ_le_of_lt
    ((Gen.V2.Duty.index_lt_idxBefore_iff hS hjo _).mpr hhi)).trans hk
  exact ⟨pcsa_proposals_stateBefore_mono E rho h.noRestart (j + 1) k y hidx hpMem,
    pcsa_body_stateBefore_mono E rho h.noRestart y hidx hbMem⟩
/-- Every honest emitted proposal is stored, with its exact metadata, before the voter read. -/
theorem pcsa_honest_proposal_before_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (s : Slot)
    (N : NamedProposal p.n)
    (he : V2.D.Run.emits E rho x (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s))
    (hc : SA.voteTime p.toParams s ≤ cut) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k) :
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals ∧
      N.erase ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks := by
  have hT : (0 : Time) ≤ SA.proposalTime p.toParams s := by
    have hd := p.deltaPos
    change (0 : Time) ≤ 4 * p.Δ * (s : Int)
    positivity
  exact pcsa_honest_proposal_before_vote_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0)
    x y hx hy s N he hT hc k hk
end AvailableChain.PCSA.Run

end
