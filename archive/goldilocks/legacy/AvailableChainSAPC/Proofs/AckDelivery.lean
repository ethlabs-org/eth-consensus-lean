module
public import AvailableChainSAPC.Proofs.Assembly
public import AvailableChainSAPC.Proofs.TimelyDelivery

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A quorum of usable archived acks produces a valid PC and a stored
certificate of at least that rank. The targets need not yet be compatible. -/
theorem archived_ack_quorum_complete (p : Params) {n : Nat} (st : State n)
    (hcomplete : PCComplete p st) (s : Slot) (b : Block)
    (hs : 0 < s) (hb : b ≠ .genesis) (hslot : b.slot = s)
    (hpath : pathKnown st b = true) (seats : Finset (Fin n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, ∃ data, (⟨.seat (s + 1) i, data⟩ : HeadWire n) ∈ st.receivedHeads ∧
      data.ack = some (s, b) ∧ Block.Preceq b data.target ∧ data.target.slot ≤ s + 1 ∧
      pathKnown st data.target = true) :
    (∃ c, c.slot = s ∧ c.target = b ∧ pcValid p st c = true) ∧
      ∃ d, st.bestPC = some d ∧ s ≤ d.slot := by
  have hcount : pcQuorum p ≤ ((st.receivedHeads.filter (fun o =>
      pcWitness s b o && pathKnown st o.payload.target)).filterMap headSeat?).toFinset.card := by
    apply hq.trans
    apply Finset.card_le_card
    intro i hi
    obtain ⟨data, hm, ha, he, ht, hp⟩ := hheads i hi
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    refine ⟨⟨.seat (s + 1) i, data⟩, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩
    simpa [pcWitness, headLabel?, ha, Block.Preceq, ht, hp] using he
  obtain ⟨c, _, hcs, hct, hc⟩ := assemblePC_complete p st s b hs hb hslot hpath hcount
  obtain ⟨d, hd, hcd⟩ := hcomplete c hc
  exact ⟨⟨c, hcs, hct, hc⟩, d, hd, by simpa only [hcs] using hcd⟩

theorem ack_early_eq_gate (p : Params) (s : Slot) : earlyTime p (s + 1) = gateTime p s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Time) + 2 * p.Δ = 4 * p.Δ * (s : Time) + 6 * p.Δ
  push_cast
  ring

/-- Timely ack calls and admitted target paths complete the certificate
strictly before the genuine gate. Neither the cap nor a gossip tick is needed. -/
theorem delivered_ack_quorum_complete {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hsched : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (v : V) (s : Slot) (b : Block) (hs : 0 < s) (hb : b ≠ .genesis) (hslot : b.slot = s)
    (hpath : b ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base.blocks)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, ∃ data index t,
      data.ack = some (s, b) ∧ Block.Preceq b data.target ∧ data.target.slot ≤ s + 1 ∧
      voteTime p (s + 1) ≤ t ∧ t < gateTime p s ∧
      Run.handlesAt (sapc p) rho index v (fromHead ⟨.seat (s + 1) i, data⟩) t ∧
      data.target ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base.blocks) :
    (∃ c, c.slot = s ∧ c.target = b ∧
      pcValid p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v) c = true) ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).bestPC = some d ∧ s ≤ d.slot := by
  apply archived_ack_quorum_complete p _ (PCComplete_at_fold p _ v) s b hs hb hslot
    (stored_pathKnown_at_fold p _ v b hpath) seats hq
  intro i hi
  obtain ⟨data, index, t, ha, he, ht, hlo, hhi, hh, hp⟩ := hheads i hi
  have hraw := early_handled_head_at_cut p E rho hsched hΔ index v (s + 1) i data t
    (gateTime p s) hlo (by rwa [ack_early_eq_gate]) (by rw [ack_early_eq_gate]) hh
  exact ⟨data, hraw.1, ha, he, ht, stored_pathKnown_at_fold p _ v data.target hp⟩

/-- Synchronous honest ack emissions give PC completion before the same
6Δ gate, once their paths are admitted. This is the delivery part of
strong inclusion; exact preparation and choice remain separate proofs. -/
theorem synchronous_ack_quorum_complete {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hsched : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (v : V) (hv : v ∈ rho.honest)
    (s : Slot) (b : Block) (hs : 0 < s) (hb : b ≠ .genesis) (hslot : b.slot = s)
    (hsync : E.t_GST ≤ voteTime p (s + 1)) (horizon : gateTime p s ≤ rho.horizon)
    (hpath : b ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base.blocks)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, rho.seatOf (s + 1) i ∈ rho.honest ∧ ∃ data,
      data.ack = some (s, b) ∧ Block.Preceq b data.target ∧ data.target.slot ≤ s + 1 ∧
      Run.emits (sapc p) E rho (rho.seatOf (s + 1) i)
        (fromHead ⟨.seat (s + 1) i, data⟩) (voteTime p (s + 1)) ∧
      data.target ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base.blocks) :
    (∃ c, c.slot = s ∧ c.target = b ∧
      pcValid p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v) c = true) ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).bestPC = some d ∧ s ≤ d.slot := by
  apply delivered_ack_quorum_complete p E rho hsched hΔ v s b hs hb hslot hpath seats hq
  intro i hi
  obtain ⟨honest, data, ha, he, ht, hem, hp⟩ := hheads i hi
  have htime : max (voteTime p (s + 1)) E.t_GST + E.Δ = gateTime p s := by
    rw [max_eq_left hsync, hΔ, ← ack_early_eq_gate]
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ + p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Time) + 2 * p.Δ
    ring
  obtain ⟨t, hlo, hhi, index, hh⟩ := hnet.broadcast _ honest _ _ hem v hv
    (by rwa [htime]) rfl
  exact ⟨data, index, t, ha, he, ht, hlo, by rwa [htime] at hhi, hh, hp⟩

end AvailableChain.SAPC
end
