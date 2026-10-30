module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Service
public import ConsensusLeanTest.GoldilocksNode
@[expose] public section

/-! # Witnesses for the Goldilocks run model and the run-level Compose statements

On `Spec/Run` with the AC `rootAC` of `ConsensusLeanTest/GoldilocksNode` (one validator,
`Δ = 1`, slot `s` starts at `s`), labelled by kind (CONTRIBUTING "Statements"):

* (a) `oneTickRun_localRun`: the run whose only top-level event is the tick of time `0` of the
  validator (two cuts, `ac_on_tick` and `ac_to_fg`; the node is awake at `0` only) is a
  `Node.LocalRun`: the hypothesis of `EventOrder`, `ACProjection`, `FGProjection`,
  `GroupStatesReachable` and `SyncProjection` is satisfiable by a run with a non-empty group, so
  the group law (`GroupAt`: the handler's cuts at consecutive indices under one event id), the
  cut law, the tick laws and the awake clamp hold together.
* (a) `tickCuts_eq`: that tick's cuts are the two AC cuts in C0.4's order (the shape the
  `tick_steps` clause of `RunOrder` reads).

On `idleAC` (`rootAC` with `ac_proposal = ⊥`), the infinite periodic run `periodicRun` (a tick
of the validator at every time `t ≥ 0`, the initial node state throughout):

* (a) `periodicRun_localRun`: it is a `Node.LocalRun`, so an infinite run satisfies the awake
  clamp `awake_in_horizon` and the tick laws together;
* (a) `periodicRun_healthy`, `periodicRun_sleepy`: `Healthy(0)` and `Sleepy` hold on it, so the
  regime premises of `Spec/Run/Premises` are satisfiable by a `Node.LocalRun` (they force an
  infinite run; see the module docstring there). The witness is over an AC that never proposes,
  not over `GoldilocksRun`: a `Sleepy` or `Healthy` run of the SA itself would carry its
  proposals and votes, a larger witness left to the Healing/Regimes milestone. -/

namespace Consensus.Goldilocks.Compose.Test

/-- The initial frame of `rootAC`'s node. -/
noncomputable abbrev Φ₀ : rootAC.Frm := Node.frame (Node.init rootAC)

/-- The cuts of the tick of time `0` from the initial node state. -/
noncomputable def tickCuts : List (Cut rootAC) := (Node.exec dg₁ v₀ (Node.init rootAC) 0 .tick).2

/-- The slot of time `0` is `0`. -/
theorem slotOf_zero : P₁.slotOf 0 = 0 := by decide

/-- (a) The tick of time `0` makes two cuts, `ac_on_tick` and `ac_to_fg`, both with the initial
frame and no emissions: the validator does not propose at `0` and `rootAC` returns
`fg_confirmed = ⊥`. -/
theorem tickCuts_eq :
    tickCuts = [.ac ⟨.tick, Φ₀, []⟩, .ac ⟨.toFG, Φ₀, []⟩] := by
  have hnp : ¬ Node.Proposes (P := P₁) v₀ 0 := fun h => by
    have := h.1; rw [slotOf_zero] at this; exact absurd this (lt_irrefl 0)
  simp only [tickCuts, Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep, hnp,
    Node.acCall, Node.acToFG, rootAC, ACInterface.step, List.foldl, ite_false]
  rfl

/-- The one-tick run: the validator's tick at time `0` at cuts `0` and `1` (one event id, the
positions `0` and `1`), no other cut; every node state is the initial one (`rootAC` keeps no
state); the validator is awake at time `0` only. -/
noncomputable def oneTickRun : RunTrace rootAC where
  init _ := Node.init rootAC
  node _ := v₀
  time _ := 0
  event i := i - 1
  pos i := i
  label i := tickCuts[i]?
  post _ := Node.init rootAC
  awake _ t := t = 0

/-- Every state of the one-tick run is the initial node state. -/
theorem oneTickRun_state (y : Fin P₁.n) (i : Nat) : oneTickRun.state y i = Node.init rootAC := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Trace.state]; split_ifs <;> first | rfl | exact ih

/-- A labelled cut of the one-tick run is cut `0`, `ac_on_tick`, or cut `1`, `ac_to_fg`. -/
theorem oneTickRun_label {i : Nat} {c : Cut rootAC} (h : oneTickRun.label i = some c) :
    (i = 0 ∧ c = .ac ⟨.tick, Φ₀, []⟩) ∨ (i = 1 ∧ c = .ac ⟨.toFG, Φ₀, []⟩) := by
  simp only [oneTickRun, tickCuts_eq] at h
  rcases i with _ | _ | i
  · exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  · simp at h

/-- Every labelled cut of the one-tick run is an AC cut whose call is `tick` or `toFG`. -/
theorem oneTickRun_label_ac {i : Nat} {c : Cut rootAC} (h : oneTickRun.label i = some c) :
    ∃ ℓ : ACLabel rootAC, c = .ac ℓ ∧ (ℓ.call = .tick ∨ ℓ.call = .toFG) := by
  rcases oneTickRun_label h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨_, rfl, Or.inl rfl⟩
  · exact ⟨_, rfl, Or.inr rfl⟩

/-- A labelled cut of the one-tick run has index `< 2`. -/
theorem oneTickRun_label_lt {i : Nat} (h : oneTickRun.label i ≠ none) : i < 2 := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h
  rcases oneTickRun_label hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega

/-- The handler of a delivery makes no cut or starts with an FG cut. -/
theorem exec_delivery_head (st : NodeState rootAC) (t : Time) (e : Node.Event rootAC)
    (he : e ≠ .tick) (hr : e ≠ .restart) :
    (Node.exec dg₁ v₀ st t e).2 = [] ∨
      ∃ ℓ l, (Node.exec dg₁ v₀ st t e).2 = .fg ℓ :: l := by
  cases e with
  | tick => exact absurd rfl he
  | restart => exact absurd rfl hr
  | message m => exact m.elim
  | attestation a => exact Or.inr ⟨_, _, rfl⟩
  | block B =>
    simp only [Node.exec, Node.onBlock]
    split_ifs
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inr ⟨_, _, rfl⟩

/-- A group of the one-tick run starts at cut `0`, at time `0`, and is a tick or a restart. -/
theorem oneTickRun_groupAt {y : Fin P₁.n} {j : Nat} {t : Time} {e : Node.Event rootAC}
    (h : oneTickRun.GroupAt dg₁ y j t e) : j = 0 ∧ t = 0 ∧ (e = .tick ∨ e = .restart) := by
  obtain ⟨hne, hk, hev⟩ := h
  have hlen : 0 < (Node.exec dg₁ y (oneTickRun.state y j) t e).2.length :=
    List.length_pos_of_ne_nil hne
  obtain ⟨-, ht, -, -, hl⟩ := hk 0 hlen
  have hj : j < 2 :=
    oneTickRun_label_lt (by rw [Nat.add_zero] at hl; rw [hl]; exact Option.some_ne_none _)
  have ht0 : t = 0 := by simpa [oneTickRun] using ht.symm
  have hj0 : j = 0 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h0 | h1
    · exact Nat.lt_one_iff.mp h0
    · exact absurd (hev 0 (by simp [oneTickRun, h1])).1 (by omega)
  refine ⟨hj0, ht0, ?_⟩
  have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
  subst hy
  by_cases hte : e = .tick
  · exact Or.inl hte
  by_cases hre : e = .restart
  · exact Or.inr hre
  exfalso
  rcases exec_delivery_head (oneTickRun.state v₀ j) t e hte hre with h0 | ⟨ℓ, l, hl'⟩
  · exact hne h0
  · have h0 : (Node.exec dg₁ v₀ (oneTickRun.state v₀ j) t e).2[0] = .fg ℓ := by
      rw [List.getElem_of_eq hl' hlen]; rfl
    rw [Nat.add_zero, h0] at hl
    obtain ⟨ℓ', hℓ', -⟩ := oneTickRun_label_ac hl
    cases hℓ'

/-- (a) The tick of time `0` is a group of the one-tick run, at cut `0`. -/
theorem oneTickRun_tickAt (y : Fin P₁.n) : oneTickRun.TickAt dg₁ y 0 0 := by
  have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
  subst hy
  have hcs : (Node.exec dg₁ v₀ (oneTickRun.state v₀ 0) 0 .tick).2 = tickCuts := rfl
  refine ⟨by rw [hcs, tickCuts_eq]; exact List.cons_ne_nil _ _, fun k hk => ?_, fun i hi => ?_⟩
  · have hk2 : k < 2 := by rw [hcs, tickCuts_eq] at hk; simpa using hk
    refine ⟨rfl, rfl, ?_, Nat.zero_add k, ?_⟩
    · change (0 + k) - 1 = 0 - 1
      omega
    · change tickCuts[0 + k]? = some (tickCuts[k]'hk)
      rw [Nat.zero_add]
      exact List.getElem?_eq_getElem hk
  · rw [hcs, tickCuts_eq]
    change i - 1 = 0 - 1 at hi
    simp only [List.length_cons, List.length_nil]
    omega

/-- (a) The one-tick run is a `Node.LocalRun` for the honest set `{0}` (every message signer
map; `rootAC` has no messages). -/
theorem oneTickRun_localRun (sg : rootAC.Msg → Fin P₁.n) :
    Node.LocalRun dg₁ Set.univ sg oneTickRun where
  init _ _ := rfl
  grouped y _ i c hc := by
    have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
    subst hy
    refine ⟨0, .tick, oneTickRun_tickAt v₀, Nat.zero_le _, ?_⟩
    have hi := oneTickRun_label_lt (by rw [hc.2]; exact Option.some_ne_none _)
    change i < 0 + tickCuts.length
    rw [tickCuts_eq]; simpa using hi
  cutLaw y _ i c hc := by
    rw [oneTickRun_state]
    rcases oneTickRun_label hc.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  wire y _ j t e h := by
    rcases (oneTickRun_groupAt h).2.2 with rfl | rfl <;> trivial
  time_nonneg _ := le_rfl
  time_mono _ _ _ := le_rfl
  finite _ := (Set.finite_Iio 2).subset fun i hi => oneTickRun_label_lt hi.1
  phase_order y _ y' _ j j' t e e' h h' hlt := by
    obtain ⟨rfl, -, -⟩ := oneTickRun_groupAt h
    obtain ⟨rfl, -, -⟩ := oneTickRun_groupAt h'
    exact absurd hlt (lt_irrefl 0)
  tick_public y _ j t h := by
    obtain ⟨-, rfl, -⟩ := oneTickRun_groupAt h
    exact public_zero
  tick_unique y _ j j' t h h' := by
    rw [(oneTickRun_groupAt h).1, (oneTickRun_groupAt h').1]
  tick_of_awake y _ t _ _ ht := ⟨0, by cases ht; exact oneTickRun_tickAt y⟩
  awake_in_horizon y _ t ht := ⟨0, by rw [oneTickRun, tickCuts_eq]; exact Option.some_ne_none _,
    by cases ht; exact le_rfl⟩
  awake_of_call _ _ _ _ := rfl
  restart_of_sleep y _ i u _ hu hlt _ _ := absurd (lt_of_le_of_lt hu hlt) (lt_irrefl 0)
  restart_at_wake y _ u v hu huv hnu hv := by
    change v = 0 at hv; subst hv
    exact absurd (lt_of_le_of_lt hu huv) (lt_irrefl 0)
  sleep_of_restart y _ i h := by
    obtain ⟨ℓ, hc, hr⟩ := h
    obtain ⟨ℓ', hℓ', hcall⟩ := oneTickRun_label_ac hc.2
    cases hℓ'
    rcases hcall with h | h <;> rw [h] at hr <;> cases hr
  block_unforgeable y _ i B h _ := by
    obtain ⟨_, hc⟩ := h
    obtain ⟨_, hℓ, -⟩ := oneTickRun_label_ac hc.2
    cases hℓ
  att_unforgeable y _ i a h _ := by
    rcases h with hc | ⟨B, ⟨_, hc⟩, -⟩ <;>
    · obtain ⟨_, hℓ, -⟩ := oneTickRun_label_ac hc.2
      cases hℓ
  msg_unforgeable y _ i m _ _ := m.elim

end Consensus.Goldilocks.Compose.Test

/-! ## An infinite periodic run: `Healthy` and `Sleepy` are satisfiable

`Spec/Run/Premises`: under `Healthy(g)` or `Sleepy`, `awake_in_horizon` makes a run infinite.
`idleAC` is `rootAC` with `ac_proposal = ⊥`, so the one validator never proposes, keeps the
initial node state for ever and ticks at every time: the tick at `0` is the two cuts
`ac_on_tick`, `ac_to_fg`, the tick at `t ≥ 1 = t_t` the three cuts `ac_on_tick`, `ac_proposal`,
`ac_to_fg`. `periodicRun` records the tick of time `t` at the cuts `3t`, `3t + 1`, `3t + 2`
(cut `2` unlabelled, under its own event id); the validator is awake at every `t ≥ 0`. -/

namespace Consensus.Goldilocks.Compose.Test

/-- `rootAC` with `ac_proposal = ⊥`: the validator never proposes. -/
def idleAC : NodeAC P₁ := { rootAC with proposal s _ _ := (s, none) }

/-- The initial frame of `idleAC`'s node. -/
noncomputable abbrev Φ₀' : idleAC.Frm := Node.frame (Node.init idleAC)

/-- The cuts of the tick of time `t` from the initial node state of `idleAC`. -/
noncomputable def idleTickCuts (t : Time) : List (Cut idleAC) :=
  (Node.exec dg₁ v₀ (Node.init idleAC) t .tick).2

/-- `slot(t) = t` for `t ≥ 0` in `P₁`. -/
theorem P₁_slotOf {t : Time} (ht : 0 ≤ t) : P₁.slotOf t = t.toNat := by
  unfold Params.slotOf
  rw [Nat.findGreatest_eq_iff]
  refine ⟨le_rfl, fun _ => ?_, fun k hk hk' => absurd (lt_of_lt_of_le hk hk') (lt_irrefl _)⟩
  change ((t.toNat : Nat) : Int) ≤ t
  rw [Int.toNat_of_nonneg ht]

/-- The validator proposes at every `t ≥ 1` in `P₁`. -/
theorem P₁_proposes {t : Time} (ht : 1 ≤ t) : Node.Proposes (P := P₁) v₀ t := by
  have h0 : 0 ≤ t := le_trans zero_le_one ht
  refine ⟨?_, ?_, rfl⟩
  · rw [P₁_slotOf h0]
    exact Int.lt_toNat.mpr (by simpa using lt_of_lt_of_le zero_lt_one ht)
  · change t = ((P₁.slotOf t : Nat) : Int)
    rw [P₁_slotOf h0, Int.toNat_of_nonneg h0]

/-- The tick of time `0`: `ac_on_tick`, `ac_to_fg`. -/
theorem idleTickCuts_zero : idleTickCuts 0 = [.ac ⟨.tick, Φ₀', []⟩, .ac ⟨.toFG, Φ₀', []⟩] := by
  have hnp : ¬ Node.Proposes (P := P₁) v₀ 0 := fun h => by
    have := h.1; rw [slotOf_zero] at this; exact absurd this (lt_irrefl 0)
  simp only [idleTickCuts, Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
    hnp, Node.acCall, Node.acToFG, idleAC, rootAC, ACInterface.step, List.foldl, ite_false]
  rfl

/-- The tick of time `t ≥ 1`: `ac_on_tick`, `ac_proposal`, `ac_to_fg`. -/
theorem idleTickCuts_pos {t : Time} (ht : 1 ≤ t) :
    idleTickCuts t = [.ac ⟨.tick, Φ₀', []⟩, .ac ⟨.proposal, Φ₀', []⟩, .ac ⟨.toFG, Φ₀', []⟩] := by
  have hp := P₁_proposes ht
  simp only [idleTickCuts, Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
    hp, Node.acCall, Node.acProposal, Node.acToFG, idleAC, rootAC, ACInterface.step, List.foldl,
    ite_true]
  rfl


/-- The tick of every `t ≥ 0` has cuts. -/
theorem idleTickCuts_ne_nil {t : Time} (ht : 0 ≤ t) : idleTickCuts t ≠ [] := by
  rcases eq_or_lt_of_le ht with rfl | h
  · rw [idleTickCuts_zero]; exact List.cons_ne_nil _ _
  · rw [idleTickCuts_pos h]; exact List.cons_ne_nil _ _

/-- The tick of `t ≥ 0` has three cuts, or `t = 0` and it has two. -/
theorem idleTickCuts_length {t : Time} (ht : 0 ≤ t) :
    (idleTickCuts t).length = 3 ∨ (t = 0 ∧ (idleTickCuts t).length = 2) := by
  rcases eq_or_lt_of_le ht with rfl | h
  · exact Or.inr ⟨rfl, by rw [idleTickCuts_zero]; rfl⟩
  · exact Or.inl (by rw [idleTickCuts_pos h]; rfl)

/-- Every cut of a tick of `t ≥ 0` is an AC cut at the initial frame with no emissions, of the
call `tick`, `proposal` or `toFG`. -/
theorem idleTickCuts_mem {t : Time} (ht : 0 ≤ t) {c : Cut idleAC} (hc : c ∈ idleTickCuts t) :
    ∃ ℓ : ACLabel idleAC, c = .ac ℓ ∧ ℓ.frame = Φ₀' ∧ ℓ.emits = [] ∧
      (ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG) := by
  rcases eq_or_lt_of_le ht with rfl | h
  · rw [idleTickCuts_zero] at hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, rfl, rfl, Or.inr (Or.inr rfl)⟩
  · rw [idleTickCuts_pos h] at hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨_, rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, rfl, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, rfl, rfl, rfl, Or.inr (Or.inr rfl)⟩

/-- The periodic run: the tick of time `t` of the validator at the cuts `3t`, `3t + 1`, `3t + 2`
(event id `2t`, positions `0, 1, 2`; at `t = 0` cut `2` is unlabelled, under the event id `1`);
every node state is the initial one; the validator is awake at every `t ≥ 0`. -/
noncomputable def periodicRun : RunTrace idleAC where
  init _ := Node.init idleAC
  node _ := v₀
  time i := ((i / 3 : Nat) : Int)
  event i := if i = 2 then 1 else 2 * (i / 3)
  pos i := i % 3
  label i := (idleTickCuts ((i / 3 : Nat) : Int))[i % 3]?
  post _ := Node.init idleAC
  awake _ t := 0 ≤ t

/-- Every state of the periodic run is the initial node state. -/
theorem periodicRun_state (y : Fin P₁.n) (i : Nat) :
    periodicRun.state y i = Node.init idleAC := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Trace.state]; split_ifs <;> first | rfl | exact ih

/-- The time of the cuts `3t', 3t' + 1, 3t' + 2` is `t'`. -/
theorem periodicRun_time (t' k : Nat) (hk : k < 3) :
    periodicRun.time (3 * t' + k) = (t' : Int) := by
  change (((3 * t' + k) / 3 : Nat) : Int) = (t' : Int)
  congr 1; omega

/-- The labels of the cuts `3t', 3t' + 1, 3t' + 2` are the cuts of the tick of time `t'`. -/
theorem periodicRun_label_eq (t' k : Nat) (hk : k < 3) :
    periodicRun.label (3 * t' + k) = (idleTickCuts (t' : Int))[k]? := by
  change (idleTickCuts (((3 * t' + k) / 3 : Nat) : Int))[(3 * t' + k) % 3]? = _
  have h1 : (3 * t' + k) / 3 = t' := by omega
  have h2 : (3 * t' + k) % 3 = k := by omega
  rw [h1, h2]

/-- Cut `2` is unlabelled. -/
theorem periodicRun_label_two : periodicRun.label 2 = none := by
  change (idleTickCuts ((2 / 3 : Nat) : Int))[2 % 3]? = none
  rw [show ((2 / 3 : Nat) : Int) = 0 from rfl, idleTickCuts_zero]
  rfl

/-- A labelled cut of the periodic run is not cut `2` and is an AC cut at the initial frame with
no emissions, of the call `tick`, `proposal` or `toFG`. -/
theorem periodicRun_label {i : Nat} {c : Cut idleAC} (h : periodicRun.label i = some c) :
    i ≠ 2 ∧ ∃ ℓ : ACLabel idleAC, c = .ac ℓ ∧ ℓ.frame = Φ₀' ∧ ℓ.emits = [] ∧
      (ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG) := by
  refine ⟨fun h2 => ?_, ?_⟩
  · rw [h2, periodicRun_label_two] at h; cases h
  have hmem : c ∈ idleTickCuts ((i / 3 : Nat) : Int) := List.mem_of_getElem? h
  exact idleTickCuts_mem (Int.natCast_nonneg _) hmem

/-- The event id of a cut other than `2` is `2 ⌊i/3⌋`. -/
theorem periodicRun_event {i : Nat} (hi : i ≠ 2) : periodicRun.event i = 2 * (i / 3) := by
  change (if i = 2 then 1 else 2 * (i / 3)) = _
  simp only [hi, ↓reduceIte]

/-- A labelled cut of the periodic run has index `< 3 ⌊i/3⌋ + 3`, and `< 2` when `⌊i/3⌋ = 0`. -/
theorem periodicRun_label_bound {i : Nat} (h : periodicRun.label i ≠ none) (h0 : i / 3 = 0) :
    i < 2 := by
  have h2 : i ≠ 2 := fun h2 => h (by rw [h2]; exact periodicRun_label_two)
  omega

/-- (a) The tick of time `t ≥ 0` is a group of the periodic run, at cut `3t`. -/
theorem periodicRun_tickAt {t : Time} (ht : 0 ≤ t) :
    periodicRun.TickAt dg₁ v₀ (3 * t.toNat) t := by
  have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
  have hcs : (Node.exec dg₁ v₀ (periodicRun.state v₀ (3 * t.toNat)) t .tick).2 =
      idleTickCuts t := by rw [periodicRun_state]; rfl
  have hlen : ∀ k, k < (idleTickCuts t).length → k < 3 ∧ (3 * t.toNat + k ≠ 2) := by
    intro k hk
    rcases idleTickCuts_length ht with h3 | ⟨rfl, h2⟩
    · rw [h3] at hk
      refine ⟨hk, fun h => ?_⟩
      have h1 : 1 ≤ t := by
        rcases eq_or_lt_of_le ht with rfl | h1
        · rw [idleTickCuts_zero] at h3; simp at h3
        · exact h1
      have : 1 ≤ t.toNat := (Int.le_toNat (le_trans zero_le_one h1)).mpr (by simpa using h1)
      omega
    · rw [h2] at hk
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_zero]; omega
  refine ⟨by rw [hcs]; exact idleTickCuts_ne_nil ht, fun k hk0 => ?_, fun i hi => ?_⟩
  · have hk : k < (idleTickCuts t).length := hcs ▸ hk0
    obtain ⟨hk3, hne⟩ := hlen k hk
    have hpos : periodicRun.pos (3 * t.toNat + k) = k := by
      change (3 * t.toNat + k) % 3 = k
      omega
    refine ⟨rfl, by rw [periodicRun_time _ _ hk3, htt], ?_, hpos, ?_⟩
    · rw [periodicRun_event hne, periodicRun_event (by omega)]
      congr 1; omega
    · rw [periodicRun_label_eq _ _ hk3, htt, List.getElem_of_eq hcs hk0]
      exact List.getElem?_eq_getElem hk
  · rw [hcs]
    have h2 : i ≠ 2 := by
      intro h2; subst h2
      have h21 : periodicRun.event 2 = 1 := rfl
      rw [h21, periodicRun_event (i := 3 * t.toNat) (by omega)] at hi
      omega
    rw [periodicRun_event h2, periodicRun_event (by omega)] at hi
    have hdiv : i / 3 = t.toNat := by omega
    rcases idleTickCuts_length ht with h3 | ⟨rfl, hl⟩
    · rw [h3]; omega
    · rw [hl]; simp only [Int.toNat_zero] at hdiv ⊢; omega

/-- A group of the periodic run starts at a cut `3t'`, at time `t'`, and is a tick or a
restart (the only events whose handler can start with an AC cut). -/
theorem periodicRun_groupAt {y : Fin P₁.n} {j : Nat} {t : Time} {e : Node.Event idleAC}
    (h : periodicRun.GroupAt dg₁ y j t e) :
    j % 3 = 0 ∧ t = ((j / 3 : Nat) : Int) ∧ (e = .tick ∨ e = .restart) := by
  obtain ⟨hne, hk, hev⟩ := h
  have hlen : 0 < (Node.exec dg₁ y (periodicRun.state y j) t e).2.length :=
    List.length_pos_of_ne_nil hne
  obtain ⟨-, ht, -, -, hl⟩ := hk 0 hlen
  rw [Nat.add_zero] at hl ht
  have hj2 : j ≠ 2 := (periodicRun_label hl).1
  have hmod : j % 3 = 0 := by
    have hev' : periodicRun.event (3 * (j / 3)) = periodicRun.event j := by
      rw [periodicRun_event (by omega), periodicRun_event hj2]
      congr 1; omega
    have := (hev (3 * (j / 3)) hev').1
    omega
  refine ⟨hmod, ht.symm, ?_⟩
  have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
  subst hy
  by_cases hte : e = .tick
  · exact Or.inl hte
  by_cases hre : e = .restart
  · exact Or.inr hre
  exfalso
  have hdel : (Node.exec dg₁ v₀ (periodicRun.state v₀ j) t e).2 = [] ∨
      ∃ ℓ l, (Node.exec dg₁ v₀ (periodicRun.state v₀ j) t e).2 = .fg ℓ :: l := by
    cases e with
    | tick => exact absurd rfl hte
    | restart => exact absurd rfl hre
    | message m => exact m.elim
    | attestation a => exact Or.inr ⟨_, _, rfl⟩
    | block B =>
      simp only [Node.exec, Node.onBlock]
      split_ifs
      · exact Or.inl rfl
      · split
        · exact Or.inr ⟨_, _, rfl⟩
        · exact Or.inr ⟨_, _, rfl⟩
  rcases hdel with h0 | ⟨ℓ, l, hl'⟩
  · exact hne h0
  · have h0 : (Node.exec dg₁ v₀ (periodicRun.state v₀ j) t e).2[0] = .fg ℓ := by
      rw [List.getElem_of_eq hl' hlen]; rfl
    rw [h0] at hl
    obtain ⟨ℓ', hℓ', -⟩ := (periodicRun_label hl).2
    cases hℓ'

/-- Two groups of the periodic run at one time start at the same cut. -/
theorem periodicRun_groupAt_unique {y y' : Fin P₁.n} {j j' : Nat} {t : Time}
    {e e' : Node.Event idleAC} (h : periodicRun.GroupAt dg₁ y j t e)
    (h' : periodicRun.GroupAt dg₁ y' j' t e') : j = j' := by
  obtain ⟨hm, ht, -⟩ := periodicRun_groupAt h
  obtain ⟨hm', ht', -⟩ := periodicRun_groupAt h'
  have : j / 3 = j' / 3 := by rw [ht] at ht'; exact_mod_cast ht'
  omega

/-- The periodic run has no restart cut. -/
theorem periodicRun_no_restart (y : Fin P₁.n) (k : Nat) : ¬ periodicRun.RestartAt y k := by
  rintro ⟨ℓ, hc, hr⟩
  obtain ⟨ℓ', hℓ', -, -, hcall⟩ := (periodicRun_label hc.2).2
  cases hℓ'
  rcases hcall with h | h | h <;> rw [h] at hr <;> cases hr

/-- The periodic run has no FG cut. -/
theorem periodicRun_no_fg (y : Fin P₁.n) (k : Nat) (ℓ : FGLabel P₁ idleAC.Payload) :
    ¬ periodicRun.CallAt y k (.fg ℓ) := by
  intro hc
  obtain ⟨ℓ', hℓ', -⟩ := (periodicRun_label hc.2).2
  cases hℓ'

/-- (a) The periodic run is a `Node.LocalRun` for the honest set `{0}`: an infinite run, with a
tick of the validator at every time `t ≥ 0`. -/
theorem periodicRun_localRun (sg : idleAC.Msg → Fin P₁.n) :
    Node.LocalRun dg₁ Set.univ sg periodicRun where
  init _ _ := rfl
  grouped y _ i c hc := by
    have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
    subst hy
    have hi2 : i ≠ 2 := (periodicRun_label hc.2).1
    refine ⟨3 * (i / 3), .tick, ?_⟩
    have htick := periodicRun_tickAt (t := ((i / 3 : Nat) : Int)) (Int.natCast_nonneg _)
    rw [Int.toNat_natCast] at htick
    refine ⟨htick, by omega, ?_⟩
    rw [periodicRun_state]
    change _ < 3 * (i / 3) + (idleTickCuts ((i / 3 : Nat) : Int)).length
    rcases idleTickCuts_length (t := ((i / 3 : Nat) : Int)) (Int.natCast_nonneg _) with
      h3 | ⟨h0, h2⟩
    · rw [h3]; omega
    · rw [h2]
      have : i / 3 = 0 := by exact_mod_cast h0
      omega
  cutLaw y _ i c hc := by
    rw [periodicRun_state]
    obtain ⟨ℓ, rfl, hf, he, hcall⟩ := (periodicRun_label hc.2).2
    refine ⟨hf, ?_, rfl, rfl⟩
    rw [he]
    rcases hcall with h | h | h <;> rw [h] <;> rfl
  wire y _ j t e h := by
    rcases (periodicRun_groupAt h).2.2 with rfl | rfl <;> trivial
  time_nonneg _ := Int.natCast_nonneg _
  time_mono _ _ h := Int.ofNat_le.mpr (Nat.div_le_div_right h)
  finite T := (Set.finite_Iio (3 * (T.toNat + 1))).subset fun i hi => by
    obtain ⟨-, hT⟩ := hi
    change ((i / 3 : Nat) : Int) ≤ T at hT
    have h0 : 0 ≤ T := le_trans (Int.natCast_nonneg _) hT
    have : i / 3 ≤ T.toNat := (Int.le_toNat h0).mpr hT
    change i < 3 * (T.toNat + 1)
    omega
  phase_order y _ y' _ j j' t e e' h h' hlt :=
    absurd (periodicRun_groupAt_unique h h') (Nat.ne_of_lt hlt)
  tick_public y _ j t h := by
    obtain ⟨-, rfl, -⟩ := periodicRun_groupAt h
    exact one_dvd _
  tick_unique y _ j j' t h h' := periodicRun_groupAt_unique h h'
  tick_of_awake y _ t h0 _ _ := by
    have hy : y = v₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)
    subst hy
    exact ⟨_, periodicRun_tickAt h0⟩
  awake_in_horizon y _ t ht := by
    have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
    refine ⟨3 * t.toNat, ?_, ?_⟩
    · rw [show 3 * t.toNat = 3 * t.toNat + 0 from rfl, periodicRun_label_eq _ _ (by omega), htt]
      exact List.getElem?_eq_getElem (List.length_pos_of_ne_nil (idleTickCuts_ne_nil ht)) ▸
        Option.some_ne_none _
    · rw [show 3 * t.toNat = 3 * t.toNat + 0 from rfl, periodicRun_time _ _ (by omega), htt]
  awake_of_call _ _ _ _ := Int.natCast_nonneg _
  restart_of_sleep _ _ _ u _ hu _ hnu _ := absurd hu hnu
  restart_at_wake _ _ u _ hu _ hnu _ := absurd hu hnu
  sleep_of_restart y _ i h := absurd h (periodicRun_no_restart y i)
  block_unforgeable y _ i B h _ := by
    obtain ⟨_, hc⟩ := h
    exact absurd hc (periodicRun_no_fg y i _)
  att_unforgeable y _ i a h _ := by
    rcases h with hc | ⟨B, ⟨_, hc⟩, -⟩ <;> exact absurd hc (periodicRun_no_fg y i _)
  msg_unforgeable y _ i m _ _ := m.elim

/-- The periodic run satisfies `Sync` for every window and effective time: no AC message exists
(`idleAC.Msg` is empty), and the run has no FG cut, so nothing is sent, accepted, admitted or
signed. -/
theorem periodicRun_syncOn (W : Time → Prop) (eff : Time → Time) :
    periodicRun.SyncOn Set.univ 1 W eff where
  deltaF := le_rfl
  message _ _ _ m _ := m.elim
  block x _ i B h := by
    rcases h with h | ⟨⟨_, h⟩, -⟩ <;> exact absurd h (periodicRun_no_fg x i _)
  relay x _ i B h := absurd h (periodicRun_no_fg x i _)
  attestation x _ i a h := by
    rcases h with ⟨_, h⟩ | ⟨_, h, -⟩ <;> exact absurd h (periodicRun_no_fg x i _)

/-- `f < h_t` at every `t ≥ 0` on the periodic run: the validator is honest, awake and joined. -/
theorem periodicRun_faultBound {t : Time} (ht : 0 ≤ t) : periodicRun.FaultBound Set.univ t := by
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  have huniv : {y : Fin P₁.n | y ∈ Set.univ ∧ periodicRun.awake y t ∧ periodicRun.JoinedAt y t} =
      Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, iff_true]
    exact ⟨ht, fun k hk => absurd hk (periodicRun_no_restart y k)⟩
  rw [huniv, Set.compl_univ, Set.ncard_empty, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  exact Nat.one_pos

/-- (a) `Healthy(0)` holds on the periodic run (with `Δ_F = 1`): the regime premise of the
`Healing`/`Regimes` statements is satisfiable by a `Node.LocalRun`, infinite as
`awake_in_horizon` requires. -/
theorem periodicRun_healthy : periodicRun.HealthyRun Set.univ 1 0 :=
  ⟨periodicRun_syncOn _ _, fun _ _ t ht => show (0 : Int) ≤ t by simpa using ht, by simp⟩

/-- (a) `Sleepy` holds on the periodic run (with `Δ_F = 1`): the premise of `Service` and of
C1.1's `PersistPremises` is satisfiable by a `Node.LocalRun`. -/
theorem periodicRun_sleepy : periodicRun.SleepyRun Set.univ 1 := by
  refine ⟨periodicRun_syncOn _ _, fun s => ⟨?_, ?_, ?_⟩⟩
  · exact periodicRun_faultBound (Int.natCast_nonneg s)
  · exact periodicRun_faultBound (by change (0 : Int) ≤ (s : Int) + 1; omega)
  · exact periodicRun_faultBound (by change (0 : Int) ≤ (s : Int) + 2 * 1; omega)

end Consensus.Goldilocks.Compose.Test

end
