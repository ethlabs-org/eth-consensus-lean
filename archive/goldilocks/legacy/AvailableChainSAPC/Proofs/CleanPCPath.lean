module
public import AvailableChainSAPC.Proofs.GenuineHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The cap supplies an honest certificate witness without participation
or synchrony. -/
theorem capped_quorum_above_faults {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p))
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) :
    (faulty rho).card < pcQuorum p := by
  have h := (cap_bounds p).1
  have q := (quorum_bounds p).2.2
  change (faulty rho).card ≤ pcFaultCap p at cap
  omega

/-- A valid PC is already sourced before its use. This does not assume
the clean invariant or infer an order from certificate rank. -/
theorem validPC_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (c : PC p.n)
    (hc : pcValid p (Run.stateBefore (sapc p) rho i reader) c = true) :
    cleanRunPath p rho i c.target := by
  obtain ⟨v, hv, j, hj, ht, hn⟩ := validPC_prior_timely p E rho hx
    (capped_quorum_above_faults p rho cap) i reader c hc
  exact Or.inr ⟨c.target, .timely c.slot c.target cap
    ⟨v, hv, j, by omega, ht, hn⟩, GridCO.block_preceq_self _⟩

theorem installedPC_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (c : PC p.n)
    (hc : (Run.stateBefore (sapc p) rho i reader).bestPC = some c) :
    cleanRunPath p rho i c.target :=
  validPC_on_cleanRunPath p E rho hx cap i reader c
    (installedPC_valid_before p rho reader i c hc)

/-- A clock changes neither the archive nor admitted paths. Frozen or
carried selection after the clock therefore has a source before it. -/
theorem selectedPC_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (t : Time) (r : Slot) (c : PC p.n)
    (hc : selectedPC p (clock p (Run.stateBefore (sapc p) rho i reader) t) r = some c) :
    cleanRunPath p rho i c.target := by
  set_option backward.isDefEq.respectTransparency false in
  have valid := certificates_valid_at_fold p (rho.events.take i) reader
  have hc' := selectedPC_valid p _ (clock_frozenPC_valid p _ t valid.2 valid.1) r c hc
  rw [pcValid_eq_of_data p _ _ (clock_blocks p _ t) (clock_archive p _ t)] at hc'
  exact validPC_on_cleanRunPath p E rho hx cap i reader c hc'

/-- All selected PC targets are compatible with the current canonical
path once its comparability has been proved. No live-lease/S order is used. -/
theorem selectedPC_compatible_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (t : Time) (r : Slot) (c : PC p.n)
    (chain : CleanPath (cleanRunPath p rho i)) (b : Block)
    (hb : cleanRunPath p rho i b)
    (hc : selectedPC p (clock p (Run.stateBefore (sapc p) rho i reader) t) r = some c) :
    Block.Compatible c.target b :=
  chain.comparable _ _ (selectedPC_on_cleanRunPath p E rho hx cap i reader t r c hc) hb

/-- A PC visible at the strict HEAD input needs an earlier honest ack.
Thus the pending label cannot supply a PC to its own next HEAD. This
uses q>a, not the cap or the clean invariant. -/
theorem selectedPC_slot_lt_at_nextHead {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (reader : V) (r : Slot) (c : PC p.n)
    (hc : selectedPC p (headState p rho (r + 1) reader) (r + 1) = some c) :
    c.slot < r := by
  set_option backward.isDefEq.respectTransparency false in
  have valid := certificates_valid_at_fold p
    (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader
  have hc' := selectedPC_valid p _
    (clock_frozenPC_valid p _ _ valid.2 valid.1) (r + 1) c hc
  rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc'
  obtain ⟨seat, data, honest, hm, _, _⟩ := pc_honest_witness p rho _ c hc' ha
  have he : Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) =
      Run.readAt (sapc p) rho (voteTime p (r + 1) - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  change _ ∈ (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).receivedHeads at hm
  rw [he] at hm
  have ht := archived_honest_head_time_le_read p E rho hx.toUnforgeableSignatures reader _
    (c.slot + 1) seat data hm honest
  by_contra hn
  have hle : (r : Time) ≤ c.slot := by exact_mod_cast le_of_not_gt hn
  change 4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ ≤
    4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ - 1 at ht
  push_cast at ht
  nlinarith [p.deltaPos]

/-- Under the cap, authority uses introduce no extra branches. The
canonical path is generated only by raw gates and honest timely saves. -/
theorem cleanRunPath_capped_sources {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) (i : Nat) (b : Block) :
    cleanRunPath p rho i b ↔ b = .genesis ∨
      (∃ j < i, ∃ v ∈ rho.honest, ∃ r c,
        rho.events[j]? = some (.tick v (gateTime p r)) ∧
        SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some c ∧
        Block.Preceq b c) ∨
      (∃ r c, HonestTimelySource p rho i r c ∧ Block.Preceq b c) := by
  set_option backward.isDefEq.respectTransparency false in
  have pcsource (j : Nat) (hj : j < i) (v : V) (c : PC p.n)
      (hc : pcValid p (Run.stateBefore (sapc p) rho j v) c = true)
      (hb : Block.Preceq b c.target) :
      ∃ r c, HonestTimelySource p rho i r c ∧ Block.Preceq b c := by
    obtain ⟨w, hw, k, hk, ht, hn⟩ := validPC_prior_timely p E rho hx
      (capped_quorum_above_faults p rho cap) j v c hc
    exact ⟨c.slot, c.target, ⟨w, hw, k, by omega, ht, hn⟩, hb⟩
  constructor
  · rintro (hg | ⟨c, hc, hb⟩)
    · exact Or.inl hg
    · apply Or.inr
      cases hc with
      | genuine j hj v hv r c ht hc => exact Or.inl ⟨j, hj, v, hv, r, c, ht, hc, hb⟩
      | timely r c _ source => exact Or.inr ⟨r, c, source, hb⟩
      | gate j hj v _ r c _ _ hc =>
        exact Or.inr (pcsource j hj v c (installedPC_valid_before p rho v j c hc) hb)
      | proposal j hj v _ r c _ _ hc =>
        rw [clock_bestPC] at hc
        exact Or.inr (pcsource j hj v c (installedPC_valid_before p rho v j c hc) hb)
      | head j hj v _ r c _ _ hc =>
        have valid := certificates_valid_at_fold p (rho.events.take j) v
        have hc' := selectedPC_valid p _
          (clock_frozenPC_valid p _ _ valid.2 valid.1) r c hc
        rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc'
        exact Or.inr (pcsource j hj v c hc' hb)
  · rintro (hg | ⟨j, hj, v, hv, r, c, ht, hc, hb⟩ | ⟨r, c, source, hb⟩)
    · exact Or.inl hg
    · exact Or.inr ⟨c, .genuine j hj v hv r c ht hc, hb⟩
    · exact Or.inr ⟨c, .timely r c cap source, hb⟩

/-- HEAD/release has no new capped path source. Its selected PC has
an earlier timely source, and release only removes finite rows. -/
theorem cleanRunPath_eq_at_head_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r))) :
    cleanRunPath p rho (i + 1) = cleanRunPath p rho i := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (ht : rho.events[j]? = some (.tick v t)) (hn : voteTime p r ≠ t) : j < i := by
    have hne : j ≠ i := by
      rintro rfl
      exact hn (congrArg Event.time (Option.some.inj (he.symm.trans ht)))
    omega
  funext b
  apply propext
  rw [cleanRunPath_capped_sources p E rho hx cap (i + 1) b,
    cleanRunPath_capped_sources p E rho hx cap i b]
  constructor
  · rintro (hg | ⟨j, hj, v, hv, s, c, ht, hc, hb⟩ | ⟨s, c, ⟨v, hv, j, hj, ht, hc⟩, hb⟩)
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨j, old j hj v _ ht
        (voteTime_ne_gateTime p r s), v, hv, s, c, ht, hc, hb⟩)
    · exact Or.inr (Or.inr ⟨s, c, ⟨v, hv, j,
        old j hj v _ ht (voteTime_ne_earlyTime p r s), ht, hc⟩, hb⟩)
  · rintro (hg | ⟨j, hj, v, hv, s, c, ht, hc, hb⟩ | ⟨s, c, ⟨v, hv, j, hj, ht, hc⟩, hb⟩)
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨j, by omega, v, hv, s, c, ht, hc, hb⟩)
    · exact Or.inr (Or.inr ⟨s, c, ⟨v, hv, j, by omega, ht, hc⟩, hb⟩)

end AvailableChain.SAPC
end
