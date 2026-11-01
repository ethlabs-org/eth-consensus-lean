module
public import AvailableChainSAPC.Proofs.BaseViews

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Proposer authentication identifies the exact engine action, including
the clock before emission. Gossip cannot emit a proposer signature. -/
theorem emittedAt_proposal_action {V : Type} [DecidableEq V] {n : Nat}
    (P : ProtocolSpec n) (E : Env V) (rho : Run V P) (index : Nat)
    (v : V) (t : Time) (s : Slot) (payload : P.Payload)
    (ho : (⟨.proposer s, payload⟩ : P.Object) ∈ Run.emittedAt P E rho index v t) :
    t = P.proposalTime s ∧ rho.proposerOf s = v ∧
      P.propose (P.clock (Run.stateBefore P rho index v) t) s = some payload := by
  unfold Run.emittedAt at ho
  split at ho
  · simp only [List.mem_append] at ho
    rcases ho with (hact | hprop) | hgossip
    · obtain ⟨label, _, ha⟩ := List.mem_filterMap.mp hact
      obtain ⟨msg, _, he⟩ := Option.map_eq_some_iff.mp ha
      have heauth := congrArg Signed.auth he
      cases heauth
    · obtain ⟨slot, hl, hp⟩ := List.mem_filterMap.mp hprop
      split at hp
      · rename_i hv
        obtain ⟨msg, hm, he⟩ := Option.map_eq_some_iff.mp hp
        have heauth := congrArg Signed.auth he
        have hepayload := congrArg Signed.payload he
        have hslot : slot = s := Auth.proposer.inj heauth
        subst slot
        change msg = payload at hepayload
        subst msg
        exact ⟨((P.slotsAt_spec s t).mp hl).symm, hv, hm⟩
      · simp at hp
    · obtain ⟨msg, _, he⟩ := List.mem_map.mp hgossip
      have heauth := congrArg Signed.auth he
      cases heauth
  · simp at ho

def proposalState {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) : State p.n :=
  clock p (Run.stateBeforeTime (sapc p) rho (proposalTime p s) (rho.proposerOf s))
    (proposalTime p s)

/-- The actual proposal carries original signatures and the live PC.
No equality of different readers' choices is assumed. -/
theorem honest_proposal_views {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b) :
    let st := proposalState p rho s
    let parent := choice p st st.base.blocks (GridCO.proposerView st.base s)
      (GridCO.proposerSupportView st.base s) s st.bestPC
    0 < s ∧ b = .node parent s (nodeRoot parent.root s 0) 0 ∧
      Run.emits (sapc p) E rho (rho.proposerOf s)
        ⟨.proposer s, .proposal b (originalHeads st (GridCO.proposerView st.base s))
          (originalHeads st (GridCO.proposerSupportView st.base s)) st.bestPC⟩
        (proposalTime p s) := by
  obtain ⟨_, msg, hblock, i, hi, ho⟩ := hb
  have hp := (emittedAt_proposal_action (sapc p) E rho i _ _ s msg ho).2.2
  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hp
  change propose p (proposalState p rho s) s = some msg at hp
  cases msg with
  | head data => simp [sapcInterface, block] at hblock
  | pc c => simp [sapcInterface, block] at hblock
  | proposal target raw support c =>
      have heq : target = b := by simpa [sapcInterface, block] using hblock
      subst target
      simp only [propose] at hp
      split at hp
      · simp at hp
      · rename_i hpos
        have hn : 0 < s := Nat.pos_of_ne_zero (by simpa using hpos)
        have hm := Option.some.inj hp
        cases hm
        exact ⟨hn, rfl, i, hi, ho⟩

theorem honest_proposal_slot {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b) :
    0 < s ∧ b ≠ .genesis ∧ b.slot = s := by
  obtain ⟨hpos, rfl, _⟩ := honest_proposal_views p E rho hs s b hb
  exact ⟨hpos, by simp, rfl⟩

/-- The fixed schedule supplies proposal emission for every positive
opening with an awake honest proposer, independently of fork choice. -/
theorem honest_proposal_exists {V : Type} [DecidableEq V]
    {p : Params} {E : Env V} {rho : Run V (sapc p)}
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hs : 0 < s) (hawake : HonestAwakeProposer E rho s)
    (hh : proposalTime p s ≤ rho.horizon) :
    ∃ b, HonestProposalAt E (sapcInterface p).toInterface rho s b := by
  have hpub : PublicTime E (proposalTime p s) := by
    refine ⟨4 * s, ?_⟩
    change 4 * p.Δ * (s : Time) = (4 * s : Nat) * E.Δ
    rw [hΔ]
    push_cast
    ring
  have ht : 0 ≤ proposalTime p s :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt p.deltaPos)) (Int.natCast_nonneg s)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hx.tick_total _ hawake.1 _ hpub ht hh)
  let st := clock p (Run.stateBefore (sapc p) rho i (rho.proposerOf s)) (proposalTime p s)
  let parent := choice p st st.base.blocks (GridCO.proposerView st.base s)
    (GridCO.proposerSupportView st.base s) s st.bestPC
  let b := Block.node parent s (nodeRoot parent.root s 0) 0
  let msg := Msg.proposal b (originalHeads st (GridCO.proposerView st.base s))
    (originalHeads st (GridCO.proposerSupportView st.base s)) st.bestPC
  have hp : propose p st s = some msg := by simp [propose, Nat.ne_of_gt hs, msg, b, parent]
  refine ⟨b, hawake.1, msg, rfl, i, hi, ?_⟩
  change _ ∈ Run.emittedAt (sapc p) E rho i (rho.proposerOf s) (proposalTime p s)
  simp only [Run.emittedAt, show E.awake (rho.proposerOf s) (proposalTime p s) = true from hawake.2,
    ↓reduceIte, List.mem_append]
  apply Or.inl
  apply Or.inr
  apply List.mem_filterMap.mpr
  refine ⟨s, ((sapc p).slotsAt_spec s _).mpr rfl, ?_⟩
  simp only [↓reduceIte]
  change (propose p st s).map _ = _
  rw [hp]
  rfl

end AvailableChain.SAPC
end
