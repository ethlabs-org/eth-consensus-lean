module
public import AvailableChainSAPC.Proofs.CleanDelivery

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- No early duty means no new timely save. -/
theorem clock_timely_of_no_early (p : Params) {n : Nat} (st : State n) (t : Time)
    (hn : ∀ r, t ≠ earlyTime p r) : (clock p st t).timely = st.timely := by
  rw [clock_timely]
  dsimp only
  split
  · rename_i ht
    exact (hn _ (by simpa using (Bool.and_eq_true_iff.mp ht).2)).elim
  · rfl

theorem clock_eq_preGate_of_no_gate (p : Params) {n : Nat} (st : State n) (t : Time)
    (hn : ∀ r, t ≠ gateTime p r) : clock p st t = clockPreGate p st t := by
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rename_i ht
    exact (hn _ (by simpa using (Bool.and_eq_true_iff.mp ht).2)).elim
  · rfl

/-- Reuse the receipt and finite-row steps for any clock with no early
save or gate. At a HEAD, only authority and genuine continuation remain. -/
theorem cleanPathFacts_tick_of_no_early_no_gate {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (reader : V) (t : Time)
    (he : rho.events[index]? = some (.tick reader t))
    (hne : ∀ r, t ≠ earlyTime p r) (hng : ∀ r, t ≠ gateTime p r)
    {path : Block → Prop} (h : CleanPathFacts p E rho index path)
    (hproposal : ∀ r c, t = proposalTime p r → reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho index reader) t) = false →
      (clock p (Run.stateBefore (sapc p) rho index reader) t).bestPC = some c →
      path c.target)
    (hhead : ∀ r c, t = voteTime p r → reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho index reader) t) = false →
      selectedPC p (clock p (Run.stateBefore (sapc p) rho index reader) t) r = some c →
      path c.target)
    (htransfer : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
      rho.events[j]? = some (.tick v (gateTime p r)) →
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
      ∀ s, r < s → t = voteTime p s → reader ∈ rho.honest →
        Block.Preceq b (headTarget p
          (clock p (Run.stateBefore (sapc p) rho index reader) t) s)) :
    CleanPathFacts p E rho (index + 1) path := by
  have oldTick (j : Nat) (v : V) (time : Time) (hj : j < index + 1)
      (ht : rho.events[j]? = some (.tick v time)) (hn : t ≠ time) : j < index := by
    have hneq : j ≠ index := by
      intro heq
      subst j
      rw [he] at ht
      exact hn (congrArg Event.time (Option.some.inj ht))
    omega
  have data (v : V) :
      (Run.stateBefore (sapc p) rho (index + 1) v).base.blocks =
        (Run.stateBefore (sapc p) rho index v).base.blocks ∧
      (Run.stateBefore (sapc p) rho (index + 1) v).receivedHeads =
        (Run.stateBefore (sapc p) rho index v).receivedHeads ∧
      (Run.stateBefore (sapc p) rho (index + 1) v).timely =
        (Run.stateBefore (sapc p) rho index v).timely ∧
      capBroken p (Run.stateBefore (sapc p) rho (index + 1) v) =
        capBroken p (Run.stateBefore (sapc p) rho index v) := by
    rw [stateBefore_succ_event he]
    by_cases hv : v = reader
    · subst v
      simp only [World.step, sapc, Function.update_self, clock_blocks, clock_archive,
        clock_timely_of_no_early p _ t hne, capBroken_clock, and_self]
    · simp only [World.step, Function.update_of_ne hv, and_self]
  refine ⟨h.chain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v hv
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · rw [stateBefore_succ_event he]
      by_cases heq : v = reader
      · subst v
        simpa only [World.step, sapc, Function.update_self] using
          (clock_clean p _ t h.chain (h.states index (le_refl _) reader hv)
            (base_receiptStamped_at_fold p _ reader)
            (fun r _ ht _ => (hng r ht).elim)).1
      · simpa only [World.step, Function.update_of_ne heq] using
          h.states index (le_refl _) v hv
    · exact h.states i (by omega) v hv
  · intro b hb
    rcases h.accessible b hb with hg | ⟨v, hv, i, hi, hk⟩
    · exact Or.inl hg
    · exact Or.inr ⟨v, hv, i, by omega, hk⟩
  · intro v hv b g d hm
    have hold : (b, g, d) ∈ (Run.stateBefore (sapc p) rho index v).base.obligations := by
      rw [stateBefore_succ_event he] at hm
      by_cases heq : v = reader
      · subst v
        simp only [World.step, sapc, Function.update_self,
          clock_eq_preGate_of_no_gate p _ t hng, clockPreGate_base] at hm
        exact GridCO.clockPreGate_obligations_subset p.engine _ t _ hm
      · simpa only [World.step, Function.update_of_ne heq] using hm
    obtain ⟨j, hj, rest⟩ := h.finiteSources v hv b g d hold
    exact ⟨j, by omega, rest⟩
  · intro j hj v hv r b ht hb
    exact h.genuine j (oldTick j v _ hj ht (hng r)) v hv r b ht hb
  · intro j hj v hv r b ht hb k hk w hw s hrs hhead
    have hj' := oldTick j v _ hj ht (hng r)
    by_cases hk' : k < index
    · exact h.transferred j hj' v hv r b ht hb k hk' w hw s hrs hhead
    · have hki : k = index := by omega
      subst k
      have eq := Option.some.inj (he.symm.trans hhead)
      have hw' : reader = w := congrArg Event.node eq
      have ht' : t = voteTime p s := congrArg Event.time eq
      subst w
      exact ht' ▸ htransfer j hj' v hv r b ht hb s hrs ht' hw
  · intro i hi v hv c hc
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · rw [pcValid_eq_of_data p _ _ (data v).1 (data v).2.1] at hc
      obtain ⟨⟨w, hw, j, hj, ht, hs⟩, hp⟩ := h.certificates index (le_refl _) v hv c hc
      exact ⟨⟨w, hw, j, by omega, ht, hs⟩, hp⟩
    · exact h.certificates i (by omega) v hv c hc
  · intro i hi v hv r b hn
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · have hold : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b) := by
        simpa only [savedTimely, (data v).2.2.1] using hn
      obtain ⟨⟨w, hw, j, hj, ht, hs⟩, hp⟩ := h.timely index (le_refl _) v hv r b hold
      exact ⟨⟨w, hw, j, by omega, ht, hs⟩, hp⟩
    · exact h.timely i (by omega) v hv r b hn
  · intro cap i _ v _
    exact capBroken_false_before p E rho hx cap v i
  · intro i _ v _
    exact archive_authenticated_before p E rho hx.toUnforgeableSignatures i v
  · intro i hi v hv r c ht hm hc
    exact h.gateAuthorities i (oldTick i v _ hi ht (hng r)) v hv r c ht hm hc
  · intro i hi v hv r c ht hm hc
    by_cases hi' : i < index
    · exact h.headAuthorities i hi' v hv r c ht hm hc
    · have hei : i = index := by omega
      subst i
      have eq := Option.some.inj (he.symm.trans ht)
      have hv' : reader = v := congrArg Event.node eq
      have ht' : t = voteTime p r := congrArg Event.time eq
      subst v
      exact hhead r c ht' hv (ht'.symm ▸ hm) (ht'.symm ▸ hc)
  · intro i hi v hv r c ht hm hc
    by_cases hi' : i < index
    · exact h.proposalAuthorities i hi' v hv r c ht hm hc
    · have hei : i = index := by omega
      subst i
      have hevent := Option.some.inj (he.symm.trans ht)
      have hev : reader = v := congrArg Event.node hevent
      have het : t = proposalTime p r := congrArg Event.time hevent
      subst v
      exact hproposal r c het hv (het.symm ▸ hm) (het.symm ▸ hc)

/-- Between duties, the HEAD inputs of the shared clock step are empty. -/
theorem cleanPathFacts_tick_between_duties {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (reader : V) (t : Time)
    (he : rho.events[index]? = some (.tick reader t))
    (hne : ∀ r, t ≠ earlyTime p r) (hnh : ∀ r, t ≠ voteTime p r)
    (hng : ∀ r, t ≠ gateTime p r)
    {path : Block → Prop} (h : CleanPathFacts p E rho index path)
    (hproposal : ∀ r c, t = proposalTime p r → reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho index reader) t) = false →
      (clock p (Run.stateBefore (sapc p) rho index reader) t).bestPC = some c →
      path c.target) : CleanPathFacts p E rho (index + 1) path := by
  apply cleanPathFacts_tick_of_no_early_no_gate p E rho hx index reader t he hne hng h hproposal
  · intro r c ht
    exact (hnh r ht).elim
  · intro j hj v hv r b ht hb s hrs hs
    exact (hnh s hs).elim

theorem duty_phase_ne (p : Params) (r s a b : Nat)
    (ha : a < 4) (hb : b < 4) (hne : a ≠ b) :
    4 * p.Δ * (r : Time) + (a : Time) * p.Δ ≠
      4 * p.Δ * (s : Time) + (b : Time) * p.Δ := by
  intro he
  have hm : (4 * (r : Time) + a) * p.Δ = (4 * (s : Time) + b) * p.Δ := by
    nlinarith
  have hc : 4 * (r : Time) + (a : Time) = 4 * (s : Time) + (b : Time) :=
    mul_right_cancel₀ (ne_of_gt p.deltaPos) hm
  have hnat : 4 * r + a = 4 * s + b := by exact_mod_cast hc
  omega

theorem voteTime_ne_gateTime (p : Params) (r s : Slot) :
    voteTime p r ≠ gateTime p s := by
  intro he
  apply voteTime_ne_earlyTime p r (s + 1)
  change 4 * p.Δ * (r : Time) + p.Δ =
    4 * p.Δ * ((s + 1 : Nat) : Time) + 2 * p.Δ
  change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (s : Time) + 6 * p.Δ at he
  push_cast
  linarith

theorem cleanPathFacts_freeze {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (index : Nat) (reader : V) (r : Slot)
    (he : rho.events[index]? = some (.tick reader (freezeTime p r)))
    {path : Block → Prop} (h : CleanPathFacts p E rho index path) :
    CleanPathFacts p E rho (index + 1) path := by
  refine cleanPathFacts_tick_between_duties p E rho hx index reader _ he ?_ ?_ ?_ h ?_
  · intro s; exact duty_phase_ne p r s 3 2 (by decide) (by decide) (by decide)
  · intro s; simpa only [Nat.cast_one, one_mul] using!
      duty_phase_ne p r s 3 1 (by decide) (by decide) (by decide)
  · intro s heq
    apply duty_phase_ne p r (s + 1) 3 2 (by decide) (by decide) (by decide)
    change 4 * p.Δ * (r : Time) + 3 * p.Δ = 4 * p.Δ * (s : Time) + 6 * p.Δ at heq
    push_cast
    nlinarith
  · intro s c ht _ _ _
    apply False.elim
    apply duty_phase_ne p r s 3 0 (by decide) (by decide) (by decide)
    simpa only [Nat.cast_zero, zero_mul, add_zero] using! ht

/-- A proposal tick preserves the joint state invariant. The emitted
proposal's later common HEAD is deliberately not asserted here. -/
theorem cleanPathFacts_proposal_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (index : Nat) (reader : V) (r : Slot)
    (he : rho.events[index]? = some (.tick reader (proposalTime p r)))
    {path : Block → Prop} (h : CleanPathFacts p E rho index path) :
    CleanPathFacts p E rho (index + 1) path := by
  set_option backward.isDefEq.respectTransparency false in
  refine cleanPathFacts_tick_between_duties p E rho hx index reader _ he ?_ ?_ ?_ h ?_
  · intro s; simpa only [Nat.cast_zero, zero_mul, add_zero] using!
      duty_phase_ne p r s 0 2 (by decide) (by decide) (by decide)
  · intro s; simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] using!
      duty_phase_ne p r s 0 1 (by decide) (by decide) (by decide)
  · intro s heq
    apply duty_phase_ne p r (s + 1) 0 2 (by decide) (by decide) (by decide)
    change 4 * p.Δ * (r : Time) = 4 * p.Δ * (s : Time) + 6 * p.Δ at heq
    push_cast
    nlinarith
  · intro s c _ hv _ hc
    rw [clock_bestPC] at hc
    exact (h.certificates index (le_refl _) reader hv c
      (installedPC_valid_before p rho reader index c hc)).2 hcap

end AvailableChain.SAPC
end
