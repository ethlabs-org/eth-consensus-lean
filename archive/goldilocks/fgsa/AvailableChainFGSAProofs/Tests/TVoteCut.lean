module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers -- shake: keep
public import Mathlib.Tactic.FinCases -- shake: keep (fin_cases tests)
public import Mathlib.Tactic.IntervalCases -- shake: keep (interval_cases tests)

set_option linter.privateModule false

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.TVoteCut
open AvailableChain.SimplexFG

/-- The repaired run has two signing seats and two honest nodes. -/
abbrev p : Params :=
  { Δ := 1, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 3, δt := 6,
    RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def env : Generic.Env (Fin 2) :=
  ⟨1, by decide, 6, by decide, fun x t => decide (x = 0 ∨ t < 5 ∨ 6 ≤ t)⟩

abbrev Object := (fgsa p unitCodec).Object
abbrev Event := V2.Event (Fin 2) Object
abbrev World := V2.D.World (Fin 2) (fgsa p unitCodec)

def mkRun (es : List Event) : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 62
  events := es
  seatOf := fun l i => match l with
    | .base .fg => i
    | .base (.head _) => i
    | .prop _ => 0
  input := fun _ _ => ()

/-- Restart, then both awake ticks, then the actual released objects in order.
At 5 only node zero receives; the saved HEAD reaches node one after the ticks at 6. -/
def batch (acc : List Event × World × List Object) (n : Nat) :
    List Event × World × List Object :=
  let t : Time := n
  let restart : List Event := if n = 6 then [.restart 1 t] else []
  let w := restart.foldl (V2.D.World.step env (mkRun [])) acc.2.1
  let o₀ := V2.D.tick env (mkRun []) (w 0) 0 t
  let w := Function.update w 0 o₀.1
  let o₁ := V2.D.tick env (mkRun []) (w 1) 1 t
  let ticks : List Event := [.tick 0 t] ++ if n = 5 then [] else [.tick 1 t]
  let w := if n = 5 then w else Function.update w 1 o₁.1
  let released := o₀.2 ++ if n = 5 then [] else o₁.2
  let deliveries := released.flatMap fun o =>
    [.deliver 0 o t] ++ if n = 5 then [] else [.deliver 1 o t]
  let delayed := if n = 6 then acc.2.2.map (fun o => .deliver 1 o t) else []
  (acc.1 ++ restart ++ ticks ++ deliveries ++ delayed,
    (deliveries ++ delayed).foldl (V2.D.World.step env (mkRun [])) w,
    if n = 5 then released else [])

def early := (List.range 7).foldl batch ([], V2.D.World.init, [])
def late := ((List.range 56).map (· + 7)).foldl batch ([], early.2.1, early.2.2)
def run := mkRun (early.1 ++ late.1)

theorem batch_time (acc : List Event × World × List Object) (n : Nat) :
    ∀ e ∈ (batch acc n).1, e ∈ acc.1 ∨ e.time = (n : Time) := by
  intro e he
  simp only [batch, List.mem_append, List.mem_flatMap] at he
  split_ifs at he <;> simp_all <;> aesop

/-- Every generated suffix event is after the failed read. -/
theorem late_time : ∀ e ∈ late.1, (7 : Time) ≤ e.time := by
  have step (acc : List Event × World × List Object) (n : Nat)
      (ha : ∀ e ∈ acc.1, (7 : Time) ≤ e.time) (hn : 7 ≤ n) :
      ∀ e ∈ (batch acc n).1, (7 : Time) ≤ e.time := by
    intro e he
    rcases batch_time acc n e he with he | ht
    · exact ha e he
    · rw [ht]
      exact_mod_cast hn
  have fold (ns : List Nat) (acc : List Event × World × List Object)
      (hn : ∀ n ∈ ns, 7 ≤ n) (ha : ∀ e ∈ acc.1, (7 : Time) ≤ e.time) :
      ∀ e ∈ (ns.foldl batch acc).1, (7 : Time) ≤ e.time := by
    induction ns generalizing acc with
    | nil => exact ha
    | cons n ns ih =>
      exact ih (batch acc n) (fun m hm => hn m (List.mem_cons_of_mem n hm))
        (step acc n ha (hn n List.mem_cons_self))
  exact fold _ _ (by simp) (by simp)

def head₁ : HeadWire p.n := ⟨.seat (.head 1) 0, ⟨2⟩⟩
def read₆ : Node p :=
  (fgsa p unitCodec).clock (V2.D.Run.stateBefore env run 20 1) 6

def head₀ (i : Fin 2) : HeadWire p.n := ⟨.seat (.head 0) i, ⟨0⟩⟩
def prop₁ : Obj p :=
  ⟨.seat (.prop 1) ⟨0, by decide⟩,
    .proposal (namedProposal p .genesis 1 0 [head₀ 0, head₀ 1] [head₀ 0, head₀ 1] [])⟩

theorem early_events : early.1 =
    [.tick 0 0, .tick 1 0, .tick 0 1, .tick 1 1,
      .deliver 0 (ofHead p (head₀ 0)) 1, .deliver 1 (ofHead p (head₀ 0)) 1,
      .deliver 0 (ofHead p (head₀ 1)) 1, .deliver 1 (ofHead p (head₀ 1)) 1,
      .tick 0 2, .tick 1 2, .tick 0 3, .tick 1 3, .tick 0 4, .tick 1 4,
      .deliver 0 prop₁ 4, .deliver 1 prop₁ 4, .tick 0 5,
      .deliver 0 (ofHead p head₁) 5, .restart 1 6, .tick 0 6, .tick 1 6,
      .deliver 1 (ofHead p head₁) 6] := by
  decide +kernel

theorem early_index {i : Nat} {e : Event} (he : run.events[i]? = some e)
    (ht : e.time ≤ 6) : i < 22 := by
  have hlen : early.1.length = 22 := by rw [early_events]; rfl
  by_contra hn
  change (early.1 ++ late.1)[i]? = some e at he
  rw [List.getElem?_append_right (by dsimp [Time] at *; omega)] at he
  have hl := late_time e (List.mem_of_getElem? he)
  dsimp [Time] at *; omega

/-- Only four actual objects can trigger local service through time 5. -/
def EarlyObject (o : Obj p) (t : Time) : Prop :=
  (o = ofHead p (head₀ 0) ∧ 1 ≤ t) ∨
  (o = ofHead p (head₀ 1) ∧ 1 ≤ t) ∨
  (o = prop₁ ∧ 4 ≤ t) ∨ (o = ofHead p head₁ ∧ 5 ≤ t)

theorem early_emission {i : Nat} {v : Fin 2} {t : Time} {o : Obj p}
    (hi : run.events[i]? = some (.tick v t)) (ht : t ≤ 5)
    (ho : o ∈ V2.D.Run.emitsAt env run i) : EarlyObject o t := by
  have hib := early_index hi (by change t ≤ 6; dsimp [Time] at *; omega)
  have hi' := hi
  change (early.1 ++ late.1)[i]? = some (.tick v t) at hi'
  rw [List.getElem?_append_left (by rw [early_events]; simpa using hib), early_events] at hi'
  interval_cases i <;> simp at hi'
  all_goals rcases hi' with ⟨rfl, rfl⟩
  all_goals first
    | change o ∈ [] at ho; cases ho
    | change o ∈ [ofHead p (head₀ 0)] at ho
      rcases List.mem_singleton.mp ho with rfl
      exact Or.inl ⟨rfl, le_rfl⟩
    | change o ∈ [ofHead p (head₀ 1)] at ho
      rcases List.mem_singleton.mp ho with rfl
      exact Or.inr (Or.inl ⟨rfl, le_rfl⟩)
    | have hp : V2.D.Run.emitsAt env run 12 = [prop₁] := by
        exact @of_decide_eq_true _
          ((inferInstance : DecidableEq (List (Obj p))) _ _) (by decide +kernel)
      rw [hp] at ho
      rcases List.mem_singleton.mp ho with rfl
      exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl⟩))
    | change o ∈ [ofHead p head₁] at ho
      rcases List.mem_singleton.mp ho with rfl
      exact Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl⟩))

theorem early_acceptance {i : Nat} {v : Fin 2} {t : Time} {o : Obj p}
    (hi : V2.D.Run.acceptsAt env run i v o t) (ht : t ≤ 5) : EarlyObject o t := by
  obtain ⟨outer, he, hh⟩ := hi.1
  have hib := early_index he (by change t ≤ 6; dsimp [Time] at *; omega)
  change (early.1 ++ late.1)[i]? = some (.deliver v outer t) at he
  rw [List.getElem?_append_left (by rw [early_events]; simpa using hib), early_events] at he
  interval_cases i <;> simp at he
  all_goals rcases he with ⟨rfl, rfl, rfl⟩
  all_goals first
    | dsimp [Time] at *; omega
    | change ofHead p (head₀ 0) = o ∨ False at hh
      rcases hh with rfl | hh
      · exact Or.inl ⟨rfl, le_rfl⟩
      · cases hh
    | change ofHead p (head₀ 1) = o ∨ False at hh
      rcases hh with rfl | hh
      · exact Or.inr (Or.inl ⟨rfl, le_rfl⟩)
      · cases hh
    | change ofHead p head₁ = o ∨ False at hh
      rcases hh with rfl | hh
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl⟩))
      · cases hh
    | change prop₁ = o ∨ (_ ∧ (o ∈ [ofHead p (head₀ 0), ofHead p (head₀ 1)] ∨
        o ∈ ([] : List (Obj p)))) at hh
      rcases hh with rfl | ⟨_, hh⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl⟩))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl
        · exact Or.inl ⟨rfl, by decide⟩
        · exact Or.inr (Or.inl ⟨rfl, by decide⟩)

theorem early_cut (a : Time) :
    (early.1.filter (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length ≤
      V2.D.Run.actionCut run a := by
  change _ ≤ ((early.1 ++ late.1).filter _).length
  rw [List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

theorem early_service {o : Obj p} {t a : Time} (ho : EarlyObject o t)
    (hta : t ≤ a) (ha : a ≤ 5) : V2.D.DeliveryService env run 0 o a 6 := by
  rcases ho with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩
  · by_cases h : a = 1
    · subst a
      exact Or.inr ⟨1, le_rfl, by decide, 4, ofHead p (head₀ 0), by decide +kernel,
        Or.inl rfl⟩
    · refine Or.inl ⟨5, ?_, by decide +kernel⟩
      apply le_trans _ (early_cut a)
      rw [early_events]
      have hlo : 2 ≤ a := by dsimp [Time] at *; omega
      interval_cases a <;> decide
  · by_cases h : a = 1
    · subst a
      exact Or.inr ⟨1, le_rfl, by decide, 6, ofHead p (head₀ 1), by decide +kernel,
        Or.inl rfl⟩
    · refine Or.inl ⟨7, ?_, by decide +kernel⟩
      apply le_trans _ (early_cut a)
      rw [early_events]
      have hlo : 2 ≤ a := by dsimp [Time] at *; omega
      interval_cases a <;> decide
  · by_cases h : a = 4
    · subst a
      exact Or.inr ⟨4, le_rfl, by decide, 14, prop₁, by decide +kernel, Or.inl rfl⟩
    · have h : a = 5 := by dsimp [Time] at *; omega
      subst a
      refine Or.inl ⟨15, ?_, by decide +kernel⟩
      apply le_trans _ (early_cut 5)
      rw [early_events]
      decide
  · have h : a = 5 := by dsimp [Time] at *; omega
    subst a
    exact Or.inr ⟨5, le_rfl, by decide, 17, ofHead p head₁, by decide +kernel,
      Or.inl rfl⟩

/-- The local sync deadline has no ready receiver link to the sleeping node at 5. -/
theorem action_sync : Gen.V2.Duty.LabelSyncOn env run (fun o => ¬ isRowObject o)
    (SA.voteTime p.toParams 1) (p.actionTime 0) := by
  let dl : Time → Time := fun a => max a 5 + 1
  have hbound (a : Time) (hc : dl a ≤ 6) : a ≤ 5 := by
    dsimp [dl, Time] at *
    omega
  have hNoLink (v : Fin 2) (a : Time) (hc : dl a ≤ 6)
      (hl : V2.D.LinkReadyOn env run v 1 a (dl a)) : False := by
    have ha := hbound a hc
    have hd : (5 : Time) < dl a := by dsimp [dl, Time] at *; omega
    have h := hl 5 ha hd
    have hf : env.awake 1 5 = false := by decide
    rw [hf] at h
    cases h
  refine ⟨dl, 6, ⟨?_, ?_⟩, ?_, ?_, (fun _ => le_rfl), by decide, le_rfl, by decide⟩
  · intro v hv o hQ t hem w hw a hta ha hlt hc hh hlink hNX
    have hab := hbound a hc
    have hdl : dl a = 6 := by dsimp [dl, Time] at *; omega
    rw [hdl]
    fin_cases w
    · obtain ⟨i, hi, ho⟩ := hem
      exact early_service (early_emission hi (hta.trans hab) ho) hta hab
    · exact (hNoLink v a hc hlink).elim
  · intro v hv i o hQ t hem w hw a hta ha hlt hc hh hlink hNX
    have hab := hbound a hc
    have hdl : dl a = 6 := by dsimp [dl, Time] at *; omega
    rw [hdl]
    fin_cases w
    · exact early_service (early_acceptance hem (hta.trans hab)) hta hab
    · exact (hNoLink v a hc hlink).elim
  · intro a b hab
    dsimp [dl, Time] at *
    have hm : max a (5 : Int) ≤ max b 5 := max_le_max hab le_rfl
    omega
  · intro a
    exact (le_max_left a 5).trans_lt (lt_add_of_pos_right _ (by decide))

/-- The exact old public TVote, with neither GST antecedent. -/
def LegacyTVote : Prop :=
  (∀ v st, Gen.V2.Duty.HonestSlot run (fgsaInterface p unitCodec) v →
    Gen.V2.Duty.LabelSyncOn env run (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (v - 1)) (SA.proposalTime p.toParams v) →
    proposalStateAt p unitCodec env run v = some st →
    FullVoteService p unitCodec env run st (v - 1)) ∧
  (∀ r x nd, x ∈ run.honest →
    Gen.V2.Duty.LabelSyncOn env run (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (r * p.R + 1)) (p.actionTime r) →
    postClock env run x (p.actionTime r) = some nd →
    FullVoteService p unitCodec env run nd.st (r * p.R + 1)) ∧
  (∀ y s (a : HeadWire p.n), y ∈ run.honest →
    V2.D.Run.emits env run y (ofHead p a) (SA.voteTime p.toParams s) →
    ∃ nd H, postClock env run y (SA.voteTime p.toParams s) = some nd ∧
      H ∈ nd.st.base.blocks ∧ H.root = a.payload)

/-- Both committee families use the identity seat map, as required by the repair. -/
theorem committees :
    V2.D.CStar (fgsaFamilies p unitCodec).fresh run ∧
      V2.D.Linked (fgsaFamilies p unitCodec).linked run := by
  constructor
  · intro l hl
    cases l with
    | base l => cases l <;> exact Function.bijective_id
    | prop s => cases hl
  · refine ⟨2, Equiv.refl (Fin 2), ?_⟩
    intro l hl
    cases l with
    | base l => cases l with
      | fg => exact ⟨rfl, fun _ => rfl⟩
      | head s => cases hl
    | prop s => cases hl

/-- The new public action antecedent is false at the failed read. -/
theorem action_cut_false :
    ¬ env.t_GST ≤ slotStartZ p (((0 * p.R + 1 : Slot) : Int) - 1) := by decide

/-- The generated read is the actual post-clock node at time 6. -/
theorem read_at : postClock env run 1 (p.actionTime 0) = some read₆ := by
  have hi : V2.D.Run.tickIdx? run 1 6 = some 20 := by decide +kernel
  rw [postClock_def, preTick_def]
  change ((V2.D.Run.tickIdx? run 1 6).map _).map _ = some read₆
  rw [hi]
  rfl

/-- The full vote conclusion is false at the post-clock read before the delayed HEAD. -/
theorem read_missing : ¬ FullVoteService p unitCodec env run read₆.st 1 := by
  intro h
  have hem : V2.D.Run.emits env run 0 (ofHead p head₁) (SA.voteTime p.toParams 1) := by
    refine ⟨16, by decide +kernel, ?_⟩
    change ofHead p head₁ ∈ [ofHead p head₁]
    exact List.mem_singleton_self _
  have hv := (h 0 head₁ (by decide) hem (by decide)).1
  have hp : GridCO.votesAt read₆.st.base 1 = [] := by decide +kernel
  rw [hp] at hv
  exact List.not_mem_nil hv

/-- The full legacy service fails in the repaired two-seat execution. -/
theorem unscoped_tVote_false : ¬ LegacyTVote := by
  intro h
  exact read_missing (h.2.1 0 1 read₆ (by decide) action_sync read_at)

/-- The amended clause has no obligation at this actual read. -/
theorem amended_action_at_read :
    (1 : Fin 2) ∈ run.honest →
    env.t_GST ≤ slotStartZ p (((0 * p.R + 1 : Slot) : Int) - 1) →
    Gen.V2.Duty.LabelSyncOn env run (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (0 * p.R + 1)) (p.actionTime 0) →
    postClock env run 1 (p.actionTime 0) = some read₆ →
    FullVoteService p unitCodec env run read₆.st (0 * p.R + 1) := by
  intro _ hcut
  exact (action_cut_false hcut).elim

end AvailableChain.FGSA.Run.Tests.TVoteCut

#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.p
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.env
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.Object
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.Event
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.World
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.mkRun
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.batch
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.late
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.run
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.batch_time
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.late_time
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.head₁
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.read₆
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.head₀
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.prop₁
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_events
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_index
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.EarlyObject
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_emission
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_acceptance
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_cut
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.early_service
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.action_sync
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.LegacyTVote
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.committees
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.action_cut_false
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.read_at
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.read_missing
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.unscoped_tVote_false
#print axioms AvailableChain.FGSA.Run.Tests.TVoteCut.amended_action_at_read
