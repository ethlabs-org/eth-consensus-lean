module
public import AvailableChainGridCO.Proofs.Votes
public import AvailableChainKit.Engine.ProtectionInduction

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A row with this block and level has a deadline at least `d`. -/
def ProtectsUntil {n : Nat} (st : State n) (B : Block) (g : Nat) (d : Time) : Prop :=
  ∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations

theorem process_protectsUntil (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (g : Nat) (d : Time) (h : ProtectsUntil st B g d) :
    ProtectsUntil (process p st o) B g d := by
  simpa only [ProtectsUntil, process_obligations] using h

theorem expire_protectsUntil {n : Nat} (st : State n) (B : Block) (g : Nat)
    (d t : Time) (h : ProtectsUntil st B g d) (ht : t < d) :
    ProtectsUntil (expire st t) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  exact ⟨deadline, hd, List.mem_filter.mpr ⟨hr, decide_eq_true (lt_of_lt_of_le ht hd)⟩⟩

theorem release_protectsUntil (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (g : Nat) (d : Time) (h : ProtectsUntil st B g d)
    (hc : releaseCount p st r B < g) : ProtectsUntil (release p st r) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  exact ⟨deadline, hd, List.mem_filter.mpr ⟨hr, decide_eq_true hc⟩⟩

private theorem deadlineOf_eq_of_row {n : Nat} (st : State n)
    (B : Block) (g : Nat) (d : Time) (hu : UniqueObligationKeys st)
    (hr : (B, g, d) ∈ st.obligations) : deadlineOf st B g = some d := by
  unfold deadlineOf
  cases hf : st.obligations.find? (fun (target, level, _) => target == B && level == g) with
  | none =>
      have := List.find?_eq_none.mp hf (B, g, d) hr
      simp at this
  | some row =>
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have hk : obligationKey row = obligationKey (B, g, d) := by
        simpa [obligationKey] using hp
      have he := hu row hm (B, g, d) hr hk
      simp [he]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A write at any block or level cannot shorten a protected deadline.
In particular, a lower-level renewal cannot change the protected key. -/
theorem write_protectsUntil {n : Nat} (st : State n) (B C : Block) (g k : Nat)
    (d limit : Time) (hu : UniqueObligationKeys st) (h : ProtectsUntil st B g d) :
    ProtectsUntil (writeObligation st C k limit) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  by_cases hk : (B, g) = (C, k)
  · have ⟨hB, hg⟩ := Prod.mk.inj hk
    subst C; subst k
    refine ⟨max deadline limit, le_trans hd (le_max_left _ _), ?_⟩
    simp [writeObligation, deadlineOf_eq_of_row st B g deadline hu hr]
  · refine ⟨deadline, hd, List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hr, ?_⟩))⟩
    simpa only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      Prod.mk.injEq, not_and_or] using hk

theorem fold_write_protectsUntil {n : Nat} {α : Type} (xs : List α)
    (f : State n → α → State n) (st : State n) (B : Block) (g : Nat) (d : Time)
    (hstep : ∀ acc x, UniqueObligationKeys acc → ProtectsUntil acc B g d →
      UniqueObligationKeys (f acc x) ∧ ProtectsUntil (f acc x) B g d)
    (hu : UniqueObligationKeys st) (hp : ProtectsUntil st B g d) :
    UniqueObligationKeys (xs.foldl f st) ∧ ProtectsUntil (xs.foldl f st) B g d := by
  induction xs generalizing st with
  | nil => exact ⟨hu, hp⟩
  | cons x xs ih =>
      obtain ⟨hu', hp'⟩ := hstep st x hu hp
      exact ih (f st x) hu' hp'

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A gate can renew a key but cannot delete it or shorten its deadline. -/
theorem gate_protectsUntil (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (g : Nat) (d : Time) (hu : UniqueObligationKeys st)
    (h : ProtectsUntil st B g d) : ProtectsUntil (gate p st r) B g d := by
  unfold gate
  split
  · exact h
  · dsimp only
    split
    · exact h
    · refine (fold_write_protectsUntil _ _ _ B g d ?_ ?_ ?_).2
      · intro acc b hu hp
        apply fold_write_protectsUntil
        · intro acc level hu hp
          exact ⟨write_unique_keys acc b level _ hu,
            write_protectsUntil acc B b g level d _ hu hp⟩
        · exact hu
        · exact hp
      · exact hu
      · exact h

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The unique-key invariant also holds through all clock phases. -/
theorem clock_unique_keys (p : Params) {n : Nat} (st : State n) (t : Time)
    (hu : UniqueObligationKeys st) : UniqueObligationKeys (clock p st t) := by
  have hpre : UniqueObligationKeys (clockPreGate p st t) := by
    intro a ha b hb hk
    exact hu a (clockPreGate_obligations_subset p st t a ha)
      b (clockPreGate_obligations_subset p st t b hb) hk
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact gate_unique_keys p _ _ hpre
  · exact hpre

private theorem fold_unique_keys {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object)) (w : World V (gridCO p))
    (h : ∀ v, UniqueObligationKeys (w v)) :
    ∀ v, UniqueObligationKeys ((events.foldl World.step w) v) := by
  set_option backward.isDefEq.respectTransparency false in
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
      apply ih
      intro v
      cases e with
      | tick u t =>
          by_cases hv : v = u
          · subst v; simpa [World.step] using! clock_unique_keys p (w u) t (h u)
          · simpa [World.step, hv] using h v
      | deliver u o t =>
          by_cases hv : v = u
          · subst v; simpa [World.step, gridCO, UniqueObligationKeys, process_obligations] using h u
          · simpa [World.step, hv] using h v

theorem run_unique_keys {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (i : Nat) (v : V) :
    UniqueObligationKeys (Run.stateBefore (gridCO p) rho i v) :=
  fold_unique_keys p _ World.init (fun _ => initial_unique_keys p.n) v

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Compatibility with a protected prefix prevents `advance` from losing it. -/
theorem advance_preserves_prefix (B old candidate : Block)
    (hold : Block.Preceq B old) (hc : Block.Compatible B candidate) :
    Block.Preceq B (advance old candidate) := by
  unfold advance
  split
  · exact hold
  · rename_i hn
    rcases Bool.or_eq_true_iff.mp hc with hforward | hback
    · exact hforward
    · exact (hn (prefix_trans candidate B old hback hold)).elim

theorem writeKeys_stable {n : Nat} (st : State n) (keys : List (Block × Nat))
    (limit : Time) : (writeKeys st keys limit).stableRecord = st.stableRecord := by
  induction keys generalizing st with
  | nil => rfl
  | cons key keys ih => exact ih _

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A protected row prevents the gate from losing an already stored prefix.
This includes a pending gate and a sleeping reader. -/
theorem gate_preserves_protected_prefix (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (g : Nat) (d : Time)
    (hp : ProtectsUntil st B g d) (hold : Block.Preceq B (stable st)) :
    Block.Preceq B (stable (gate p st r)) := by
  obtain ⟨deadline, _, hrow⟩ := hp
  cases hc : confirmation p st r with
  | none => simpa only [gate, hc] using! hold
  | some C =>
      by_cases hcomp : Block.compatible B C = true
      · cases hg : st.obligations.any (fun (target, _, _) => !Block.compatible target C) with
        | true =>
            change Block.Preceq B (gate p st r).stableRecord
            rw [(gate_veto p st r C hc hg).1]; exact hold
        | false =>
            change Block.Preceq B (gate p st r).stableRecord
            rw [gate_eq_writeKeys p st r C hc hg, writeKeys_stable]
            exact advance_preserves_prefix B st.stableRecord C hold hcomp
      · have hfalse : Block.compatible B C = false := Bool.eq_false_iff.mpr hcomp
        change Block.Preceq B (gate p st r).stableRecord
        rw [(gate_veto_of_live_target p st r C B g deadline hc hrow hfalse).1]
        exact hold

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
All clock phases before the gate retain a row before its deadline
when the strict input's scheduled release count is below its level. -/
theorem clockPreGate_protectsUntil (p : Params) {n : Nat} (st : State n) (t : Time)
    (B : Block) (g : Nat) (d : Time) (hs : ReceiptStamped st)
    (hp : ProtectsUntil st B g d) (ht : t < d)
    (hc : ∀ r, t = releaseTime p r → releaseCount p st r B < g) :
    ProtectsUntil (clockPreGate p st t) B g d := by
  have hc' : ∀ st' r, receiptData st' = receiptData st → t = releaseTime p r →
      releaseCount p st' r B < g := by
    intro st' r he hr
    rw [releaseCount_eq_of_receiptData p st' st he hs r B]
    exact hc r hr
  unfold clockPreGate
  dsimp only
  split <;> split <;> split
  all_goals first
    | exact expire_protectsUntil { st with now := t } B g d t hp ht
    | have hrelease : (decide (0 ≤ t - 5 * p.Δ) &&
          t == releaseTime p ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) = true := by assumption
      apply release_protectsUntil
      · exact expire_protectsUntil { st with now := t } B g d t hp ht
      · apply hc'
        · rfl
        · simpa using (Bool.and_eq_true_iff.mp hrelease).2

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
One clock step retains both a strong row and its record prefix.
The release-count premise is the only participation-dependent input. -/
theorem clock_preserves_protection (p : Params) {n : Nat} (st : State n) (t : Time)
    (B : Block) (g : Nat) (d : Time) (hs : ReceiptStamped st)
    (hu : UniqueObligationKeys st) (hp : ProtectsUntil st B g d)
    (hold : Block.Preceq B (stable st)) (ht : t < d)
    (hc : ∀ r, t = releaseTime p r → releaseCount p st r B < g) :
    ProtectsUntil (clock p st t) B g d ∧ Block.Preceq B (stable (clock p st t)) := by
  have hpre := clockPreGate_protectsUntil p st t B g d hs hp ht hc
  have horder : UniqueObligationKeys (clockPreGate p st t) := by
    intro a ha b hb hk
    exact hu a (clockPreGate_obligations_subset p st t a ha)
      b (clockPreGate_obligations_subset p st t b hb) hk
  have hrecord : Block.Preceq B (stable (clockPreGate p st t)) := by
    simpa only [stable, clockPreGate_stable] using hold
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact ⟨gate_protectsUntil p _ _ B g d horder hpre,
      gate_preserves_protected_prefix p _ _ B g d hpre hrecord⟩
  · exact ⟨hpre, hrecord⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A live protected row constrains each emitted honest HEAD. -/
theorem emitted_head_compatible_of_protection
    {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (i : Nat) (v : V) (t : Time) (hi : rho.events[i]? = some (.tick v t))
    (B : Block) (g : Nat) (d : Time)
    (hp : ProtectsUntil (Run.stateBefore (gridCO p) rho (i + 1) v) B g d)
    (ht : t < d) (o : Wire p.n) (r : Slot) (target : Block)
    (hem : o ∈ Run.emittedAt (gridCO p) E rho i v t)
    (hr : headLabel? o = some r) (hb : headTarget? o = some target) :
    Block.Compatible target B := by
  set_option backward.isDefEq.respectTransparency false in
  have ha := (emitted_head_action p E rho i v t o r target hem hr hb).2
  by_cases hz : r = 0
  · subst r
    have heq : target = .genesis := by simpa [act, targetOfBlock] using ha.symm
    subst target
    exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix B))
  · have hstate : Run.stateBefore (gridCO p) rho (i + 1) v =
        clock p (Run.stateBefore (gridCO p) rho i v) t := by
      rw [stateBefore_succ_event hi]
      simp [World.step, gridCO]
    obtain ⟨deadline, hd, hrow⟩ := hp
    have hlive : (Run.stateBefore (gridCO p) rho (i + 1) v).now < deadline := by
      rw [hstate, clock_now]
      exact lt_of_lt_of_le ht hd
    have hroot := liveTarget_preceq_liveRoot _
      (run_map_reachable p E rho hs (i + 1) v).comparable g B deadline hrow hlive
    rw [hstate] at hroot
    simp only [act, beq_iff_eq, hz, ↓reduceIte, Option.some.injEq, Msg.head.injEq] at ha
    have hprefix : Block.Preceq B target := by
      rw [← ha]
      exact prefix_trans B _ _ hroot
        (forkChoice_extends_liveRoot (clock p (Run.stateBefore (gridCO p) rho i v) t)
          _ _ _ r)
    exact Bool.or_eq_true_iff.mpr (Or.inr hprefix)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The batch in flight at arming must be compatible with the protected
prefix. Only labels with a release after U occur in this premise. -/
def ArmingHeadsCompatible {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (U : Time) (B : Block) : Prop :=
  ∀ r, ∀ u ∈ rho.honest, ∀ o t, t ≤ U → U < releaseTime p r →
    Run.emits (gridCO p) E rho u o t → headLabel? o = some r →
    ∀ target, headTarget? o = some target → Block.Compatible target B

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
First-loss induction from armed rows. New honest HEADs follow the live
rows, so a release has at most the faulty count. A gate preserves both the
row and the record prefix. No synchrony or awake-count premise is used. -/
theorem protection_from_armed_index
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hexec : ExecutionValid (gridCO p) E rho)
    (B : Block) (g : V → Nat) (U d : Time) (start finish : Nat)
    (hstrong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (hbase : ∀ v ∈ rho.honest,
      ProtectsUntil (Run.stateBefore (gridCO p) rho start v) B (g v) d ∧
      Block.Preceq B (stable (Run.stateBefore (gridCO p) rho start v)))
    (hseed : ArmingHeadsCompatible p E rho U B)
    (hbefore : ∀ j v t, j < start → rho.events[j]? = some (.tick v t) → t ≤ U)
    (hafter : ∀ j v t, start ≤ j → rho.events[j]? = some (.tick v t) → U < t)
    (hdeadline : ∀ j e, start ≤ j → j < finish → rho.events[j]? = some e → e.time < d)
    (hfinish : start ≤ finish) :
    ∀ v ∈ rho.honest,
      ProtectsUntil (Run.stateBefore (gridCO p) rho finish v) B (g v) d ∧
      Block.Preceq B (stable (Run.stateBefore (gridCO p) rho finish v)) := by
  set_option backward.isDefEq.respectTransparency false in
  apply AvailableChain.Engine.state_interval_induction (gridCO p) rho
    (fun v st => ProtectsUntil st B (g v) d ∧ Block.Preceq B (stable st))
    start finish hfinish hbase
  · intro v hv st o hp
    exact ⟨process_protectsUntil p st o B (g v) d hp.1,
      by simpa only [gridCO, stable, process_stable] using! hp.2⟩
  · intro i u t hsi hif hi hu hp hpast
    have htd := hdeadline i _ hsi hif hi
    apply clock_preserves_protection p _ t B (g u) d
      (run_receiptStamped p rho i u) (run_unique_keys p rho i u) hp.1 hp.2 htd
    intro r hr
    rw [stateBefore_tick_eq_stateBeforeTime hexec.toScheduleWellFormed hi]
    apply lt_of_le_of_lt (releaseCount_le_faults_of_emissions p E rho
      hexec.toUnforgeableSignatures t u r B ?_) (hstrong u hu)
    intro voter hhonest o t' ht' hem hlabel target htarget
    obtain ⟨j, hj, hmem⟩ := hem
    have hji := eventIndex_lt_of_time_lt hexec.toScheduleWellFormed hj hi ht'
    by_cases hjstart : j < start
    · exact hseed r voter hhonest o t' (hbefore j voter t' hjstart hj)
        (hr ▸ hafter i u t hsi hi) ⟨j, hj, hmem⟩ hlabel target htarget
    · exact emitted_head_compatible_of_protection p E rho hexec.toScheduleWellFormed
        j voter t' hj B (g voter) d (hpast j (by omega) hji voter hhonest).1
        (lt_trans ht' htd) o r target hmem hlabel htarget

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Strong rows protect every later public read until their deadlines,
provided the batch in flight at arming is compatible. The selected level
can differ between readers. Expiry at the endpoint is deliberately excluded. -/
theorem protection_from_armed_read
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hexec : ExecutionValid (gridCO p) E rho)
    (B : Block) (g : V → Nat) (U d : Time)
    (hstrong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (hbase : ∀ v ∈ rho.honest,
      ProtectsUntil (Run.readAt (gridCO p) rho U v) B (g v) d ∧
      Block.Preceq B (stable (Run.readAt (gridCO p) rho U v)))
    (hseed : ArmingHeadsCompatible p E rho U B)
    (t : Time) (hUt : U ≤ t) (htd : t < d) :
    ∀ v ∈ rho.honest,
      ProtectsUntil (Run.readAt (gridCO p) rho t v) B (g v) d ∧
      Block.Preceq B (stable (Run.readAt (gridCO p) rho t v)) := by
  let start := (rho.events.filter (fun e => decide (e.time ≤ U))).length
  let finish := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hbase' : ∀ v ∈ rho.honest,
      ProtectsUntil (Run.stateBefore (gridCO p) rho start v) B (g v) d ∧
      Block.Preceq B (stable (Run.stateBefore (gridCO p) rho start v)) := by
    simpa only [readAt_eq_stateBefore hexec.toScheduleWellFormed U] using hbase
  rw [readAt_eq_stateBefore hexec.toScheduleWellFormed t]
  apply protection_from_armed_index p E rho hexec B g U d start finish hstrong hbase' hseed
  · intro j v t' hj he
    exact (index_lt_read_length_iff hexec.toScheduleWellFormed U he).mp hj
  · intro j v t' hj he
    have hn : ¬ t' ≤ U := by
      intro ht'
      have := (index_lt_read_length_iff hexec.toScheduleWellFormed U he).mpr ht'
      omega
    exact lt_of_not_ge hn
  · intro j e _ hj he
    exact lt_of_le_of_lt ((index_lt_read_length_iff hexec.toScheduleWellFormed t he).mp hj) htd
  · exact read_length_mono U t hUt

end AvailableChain.GridCO
end
