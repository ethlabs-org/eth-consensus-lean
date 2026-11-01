module
public import AvailableChainWitnesses.Sanity

@[expose] public section

namespace AvailableChain.Witnesses.Accumulation

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- Honest votes for the parent do not choose either child. -/
def parentBlock : Block := .node .genesis 0 (nodeRoot (.genesis : Block).root 0 0) 0
def visibleChild : Block := .node parentBlock 1 (nodeRoot (parentBlock : Block).root 1 0) 0
def hiddenChild : Block := .node parentBlock 1 (nodeRoot (parentBlock : Block).root 1 1) 1

inductive Vote where
  | parent | visible | hidden
  deriving DecidableEq, Repr

abbrev Wire := Signed (Fin 4) 3 Vote
abbrev VoteState := Bool × List Wire

/-- All received seat votes count. Parent votes are wasted at the fork. -/
def pooledHead (st : VoteState) : Vote :=
  if !st.1 then .parent
  else if (st.2.filter (fun o => o.payload == Vote.hidden)).length >
      (st.2.filter (fun o => o.payload == Vote.visible)).length then
    .hidden else .visible

def headBlock (st : VoteState) : Block :=
  match pooledHead st with
  | .parent => parentBlock
  | .visible => visibleChild
  | .hidden => hiddenChild

def labelTime (ℓ : Fin 4) : Time := ℓ.val

def labelsAt (t : Time) : List (Fin 4) :=
  if t = 0 then [0] else if t = 1 then [1] else
  if t = 2 then [2] else if t = 3 then [3] else []

theorem labels_spec (ℓ : Fin 4) (t : Time) :
    ℓ ∈ labelsAt t ↔ labelTime ℓ = t := by
  fin_cases ℓ <;> simp [labelsAt, labelTime] <;> split_ifs <;> simp_all [eq_comm]

theorem labels_nodup (t : Time) : (labelsAt t).Nodup := by
  unfold labelsAt
  split_ifs <;> decide

/-- The public clock reveals Y at time 3. Honest labels 0, 1, 2 vote B;
label 3 votes Y. The tally pools votes from every label. -/
def pooledLMD : ProtocolSpec 3 where
  State := VoteState
  Label := Fin 4
  Payload := Vote
  init := (false, [])
  clock := fun st t => (st.1 || decide (3 ≤ t), st.2)
  actTime := labelTime
  duties := labelsAt
  duties_spec := labels_spec
  duties_nodup := labels_nodup
  act := fun _ ℓ => some (if ℓ = 3 then .visible else .parent)
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := (Sanity.alwaysGenesis 3).slotsAt_spec
  slotsAt_nodup := (Sanity.alwaysGenesis 3).slotsAt_nodup
  propose := fun _ _ => none
  gossip := fun _ _ => []
  process := fun st o => (st.1, o :: st.2)
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun st o => st.2.contains o
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def interface : Interface pooledLMD where
  confirmed := headBlock
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => False

def env : Env (Fin 3) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

def honestVote (ℓ : Fin 4) (v : Fin 3) : Wire :=
  ⟨.seat ℓ v, if ℓ = 3 then .visible else .parent⟩
def faultyVote (ℓ : Fin 4) : Wire := ⟨.seat ℓ 2, .hidden⟩

/-- Faulty signing is outside `Run.emits`. This witness records that each
withheld X vote is signed at its own label's act time. -/
structure WithheldFaultyVote where
  label : Fin 4
  signedAt : Time
  object : Wire
  afterAct : pooledLMD.actTime label ≤ signedAt

def withheldVote (ℓ : Fin 4) : WithheldFaultyVote where
  label := ℓ
  signedAt := labelTime ℓ
  object := faultyVote ℓ
  afterAct := le_refl _

@[simp] theorem withheldVote_object (ℓ : Fin 4) :
    (withheldVote ℓ).object = faultyVote ℓ := rfl

theorem withheldVote_signedAtAct (ℓ : Fin 4) :
    (withheldVote ℓ).signedAt = pooledLMD.actTime ℓ := rfl

/-- Three prior faulty seats withhold X votes. Honest seats spend six votes
on B before the two label-3 seats vote Y. The three X votes arrive at 4. -/
def attackRun : Run (Fin 3) pooledLMD where
  honest := {0, 1}
  horizon := 5
  events :=
    [
     .tick 0 0, .tick 1 0, .deliver 0 (honestVote 0 0) 0,
     .deliver 0 (honestVote 0 1) 0, .deliver 1 (honestVote 0 0) 0, .deliver 1 (honestVote 0 1) 0,
     .tick 0 1, .tick 1 1, .deliver 0 (honestVote 1 0) 1,
     .deliver 0 (honestVote 1 1) 1, .deliver 1 (honestVote 1 0) 1, .deliver 1 (honestVote 1 1) 1,
     .tick 0 2, .tick 1 2, .deliver 0 (honestVote 2 0) 2,
     .deliver 0 (honestVote 2 1) 2, .deliver 1 (honestVote 2 0) 2, .deliver 1 (honestVote 2 1) 2,
     .tick 0 3, .tick 1 3, .deliver 0 (honestVote 3 0) 3,
     .deliver 0 (honestVote 3 1) 3, .deliver 1 (honestVote 3 0) 3, .deliver 1 (honestVote 3 1) 3,
     .tick 0 4, .tick 1 4, .deliver 0 (withheldVote 0).object 4,
     .deliver 0 (withheldVote 1).object 4, .deliver 0 (withheldVote 2).object 4,
     .deliver 1 (withheldVote 0).object 4, .deliver 1 (withheldVote 1).object 4,
     .deliver 1 (withheldVote 2).object 4,
     .tick 0 5, .tick 1 5
    ]
  seatOf := fun _ => Equiv.refl (Fin 3)
  proposerOf := fun _ => 0

/-- This interface names no proposal blocks, so its root scope is genesis. -/
theorem rootInjective : RootInjective env interface attackRun := by
  have hseen : ∀ B, BlockInRun env interface attackRun B → B = .genesis := by
    intro B hB
    rcases hB with hB | ⟨v, o, t, tip, _, htip, _⟩
    · exact hB
    · cases htip
  intro B C hB hC _
  exact (hseen B hB).trans (hseen C hC).symm

private theorem event_mem (i : Nat) (e : Event (Fin 3) pooledLMD.Object)
    (h : attackRun.events[i]? = some e) : e ∈ attackRun.events :=
  List.mem_iff_getElem?.2 ⟨i, h⟩

private theorem delivery_cases {v : Fin 3} {o : pooledLMD.Object} {t : Time}
    (h : Run.processes pooledLMD attackRun v o t) :
    (∃ ℓ : Fin 4, (o = honestVote ℓ 0 ∨ o = honestVote ℓ 1) ∧
      t = labelTime ℓ) ∨
    (∃ ℓ : Fin 4, ℓ.val < 3 ∧ o = faultyVote ℓ ∧ t = 4) := by
  set_option backward.isDefEq.respectTransparency false in
  rcases h with ⟨i, hi⟩
  have hm := event_mem i _ hi
  simp [attackRun] at hm
  aesop (add simp [labelTime])

/-- No faulty vote is delivered before its own label's act time. -/
theorem noFaultyEarly (ℓ : Fin 4) (v : Fin 3) (t : Time)
    (h : Run.processes pooledLMD attackRun v (faultyVote ℓ) t) :
    pooledLMD.actTime ℓ ≤ t := by
  have ht : t = 4 := by
    rcases delivery_cases h with ⟨ℓ', (he | he), _⟩ | ⟨ℓ', _, _, ht⟩
    · have hp := congrArg Signed.payload he
      simp [faultyVote, honestVote] at hp
      split_ifs at hp
    · have hp := congrArg Signed.payload he
      simp [faultyVote, honestVote] at hp
      split_ifs at hp
    · exact ht
  change (ℓ.val : Time) ≤ t
  have hl : (ℓ.val : Time) < 4 := by exact_mod_cast ℓ.isLt
  rw [ht]
  exact hl.le

theorem noFaultySeatDeliveryEarly (ℓ : Fin 4) (v : Fin 3)
    (o : pooledLMD.Object) (t : Time)
    (hp : Run.processes pooledLMD attackRun v o t)
    (ha : o.auth = .seat ℓ 2) : pooledLMD.actTime ℓ ≤ t := by
  rcases delivery_cases hp with ⟨ℓ', (he | he), _⟩ | ⟨ℓ', _, he, _⟩
  · simp [he, honestVote] at ha
    injection ha with hlabel hseat
    cases hseat
  · simp [he, honestVote] at ha
    injection ha with hlabel hseat
    cases hseat
  · simp [he, faultyVote] at ha
    injection ha with hℓ hseat
    subst ℓ'
    rw [he] at hp
    exact noFaultyEarly ℓ v t hp

theorem honestSeatsOutnumberFaulty (ℓ : Fin 4) :
    (Finset.univ.filter (fun i : Fin 3 =>
      attackRun.seatOf ℓ i ∈ attackRun.honest)).card = 2 ∧
    (Finset.univ.filter (fun i : Fin 3 =>
      attackRun.seatOf ℓ i ∉ attackRun.honest)).card = 1 := by
  fin_cases ℓ <;> constructor <;> decide

private theorem emitsHonest (ℓ : Fin 4) (v : Fin 3)
    (hv : v ∈ attackRun.honest) :
    Run.emits pooledLMD env attackRun v (honestVote ℓ v) (labelTime ℓ) := by
  refine ⟨6 * ℓ.val + v.val, ?_, ?_⟩
  · fin_cases ℓ <;> fin_cases v <;> simp [attackRun, labelTime] at hv ⊢
  · fin_cases ℓ <;> fin_cases v <;> simp [attackRun] at hv
    all_goals change honestVote _ _ ∈ [honestVote _ _]
    all_goals simp [attackRun]

theorem attackExecution : ExecutionValid pooledLMD env attackRun := by
  set_option backward.isDefEq.respectTransparency false in
  refine { horizon_nonneg := by decide
           sorted := by decide
           nodup := by
             simp [attackRun, honestVote, faultyVote]
           in_horizon := ?_
           honest_only := ?_
           tick_public := ?_
           tick_total := ?_
           wire := ?_
           deps := ?_
           fresh := ?_
           unforgeable := ?_
           carried := ?_ }
  · intro e he
    simp [attackRun] at he
    rcases he with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h
    all_goals (subst e; decide)
  · intro e he
    simp [attackRun] at he
    rcases he with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h |
      h | h
    all_goals (subst e; decide)
  · intro v t h
    have ht : 0 ≤ t := by
      simp [attackRun] at h
      aesop
    exact ⟨t.toNat, by simpa [env] using (Int.toNat_of_nonneg ht).symm⟩
  · intro v hv t ht h0 hh
    rcases ht with ⟨k, hk⟩
    have hv' : v = 0 ∨ v = 1 := by simpa [attackRun] using hv
    have htk : t = (k : Time) := by simpa [env] using hk
    change t ≤ 5 at hh
    have hk' : k ≤ 5 := by
      rw [htk] at hh
      exact_mod_cast hh
    rcases hv' with rfl | rfl
    · interval_cases k <;> simp [attackRun, htk]
    · interval_cases k <;> simp [attackRun, htk]
  · intro i v o t h; rfl
  · intro i v o t h; rfl
  · intro i v o t h
    rcases List.getElem?_eq_some_iff.mp h with ⟨hb, he⟩
    change i < 34 at hb
    interval_cases i <;> simp [attackRun] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩
    all_goals decide
  · intro v o t hp u hu holder
    rcases delivery_cases hp with ⟨ℓ, (rfl | rfl), rfl⟩ |
      ⟨ℓ, hℓ, rfl, rfl⟩
    · have hu0 : u = 0 := by simpa [Run.holder, attackRun, honestVote] using holder.symm
      subst u
      exact ⟨labelTime ℓ, le_refl _, emitsHonest ℓ 0 (by decide)⟩
    · have hu1 : u = 1 := by simpa [Run.holder, attackRun, honestVote] using holder.symm
      subst u
      exact ⟨labelTime ℓ, le_refl _, emitsHonest ℓ 1 (by decide)⟩
    · have hu2 : u = 2 := by simpa [Run.holder, attackRun, faultyVote] using holder.symm
      subst u
      simp [attackRun] at hu
  · intro v o t hp o' hc u hu holder
    exact False.elim hc

private theorem emission_cases (v : Fin 3) (o : pooledLMD.Object) (t : Time)
    (h : Run.emits pooledLMD env attackRun v o t) :
    ∃ ℓ : Fin 4, t = labelTime ℓ ∧ o = honestVote ℓ v := by
  rcases h with ⟨i, hi, ho⟩
  have hm := event_mem i _ hi
  simp [attackRun] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals simp [Run.emittedAt, pooledLMD, env, labelsAt, attackRun] at ho
  all_goals try (exact False.elim (List.not_mem_nil
    (show o ∈ ([] : List pooledLMD.Object) from ho)))
  all_goals first
    | exact ⟨0, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 0 0] from ho)⟩
    | exact ⟨0, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 0 1] from ho)⟩
    | exact ⟨1, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 1 0] from ho)⟩
    | exact ⟨1, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 1 1] from ho)⟩
    | exact ⟨2, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 2 0] from ho)⟩
    | exact ⟨2, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 2 1] from ho)⟩
    | exact ⟨3, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 3 0] from ho)⟩
    | exact ⟨3, rfl, List.mem_singleton.mp
        (show o ∈ [honestVote 3 1] from ho)⟩

private theorem delivered (ℓ : Fin 4) (v w : Fin 3)
    (hv : v ∈ attackRun.honest) (hw : w ∈ attackRun.honest) :
    ∃ j, Run.handlesAt pooledLMD attackRun j w (honestVote ℓ v)
      (labelTime ℓ) := by
  refine ⟨6 * ℓ.val + 2 + 2 * w.val + v.val, honestVote ℓ v, ?_, rfl⟩
  fin_cases ℓ <;> fin_cases v <;> fin_cases w <;>
    simp [attackRun, labelTime] at hv hw ⊢

private theorem deliveredFaulty (ℓ : Fin 4) (w : Fin 3)
    (hℓ : ℓ.val < 3) (hw : w ∈ attackRun.honest) :
    ∃ j, Run.handlesAt pooledLMD attackRun j w (faultyVote ℓ) 4 := by
  refine ⟨26 + ℓ.val + 3 * w.val, faultyVote ℓ, ?_, rfl⟩
  fin_cases ℓ <;> fin_cases w <;> simp [attackRun] at hℓ hw ⊢

theorem attackSynchrony : PartialSynchrony pooledLMD env attackRun := by
  constructor
  · intro v hv o t hem w hw hd _
    rcases emission_cases v o t hem with ⟨ℓ, rfl, rfl⟩
    refine ⟨labelTime ℓ, le_refl _, ?_, delivered ℓ v w hv hw⟩
    fin_cases ℓ <;> decide
  · intro v hv i o t ha w hw hp hd _
    rcases ha.1 with ⟨o', hi, hh⟩
    have heq : o' = o := hh
    subst o'
    have hproc : Run.processes pooledLMD attackRun v o t := ⟨i, hi⟩
    rcases delivery_cases hproc with ⟨ℓ, (rfl | rfl), rfl⟩ |
      ⟨ℓ, hℓ, rfl, rfl⟩
    · exact ⟨labelTime ℓ, le_refl _, by fin_cases ℓ <;> decide,
        delivered ℓ 0 w (by decide) hw⟩
    · exact ⟨labelTime ℓ, le_refl _, by fin_cases ℓ <;> decide,
        delivered ℓ 1 w (by decide) hw⟩
    · exact ⟨4, by decide, by decide, deliveredFaulty ℓ w hℓ hw⟩

theorem attackValidSynchronous :
    ExecutionValid pooledLMD env attackRun ∧ PartialSynchrony pooledLMD env attackRun :=
  ⟨attackExecution, attackSynchrony⟩

theorem attackHasFault : (faulty attackRun).Nonempty := by
  refine ⟨2, ?_⟩
  decide

theorem wastedHonestVotes :
    ∀ ℓ : Fin 4, ℓ.val < 3 →
      (honestVote ℓ 0).payload = .parent ∧
      (honestVote ℓ 1).payload = .parent := by
  intro ℓ hℓ
  fin_cases ℓ <;> simp [honestVote] at hℓ ⊢

theorem honestParentVotes (ℓ : Fin 4) (hℓ : ℓ.val < 3) :
    ∀ v ∈ attackRun.honest,
      Run.emits pooledLMD env attackRun v (honestVote ℓ v) (labelTime ℓ) ∧
      (honestVote ℓ v).payload = .parent := by
  intro v hv
  refine ⟨emitsHonest ℓ v hv, ?_⟩
  fin_cases ℓ <;> simp [honestVote] at hℓ ⊢

theorem honestVisibleVotes :
    ∀ v ∈ attackRun.honest,
      Run.emits pooledLMD env attackRun v (honestVote 3 v) (labelTime 3) ∧
      (honestVote 3 v).payload = .visible := by
  intro v hv
  exact ⟨emitsHonest 3 v hv, by simp [honestVote]⟩

theorem atLastLabel :
    (honestVote 3 0).payload = .visible ∧
    (honestVote 3 1).payload = .visible := by decide

theorem visibleBeforeRelease :
    readAt pooledLMD attackRun interface.confirmed 0 3 = visibleChild := by
  decide

theorem hiddenAfterRelease :
    readAt pooledLMD attackRun interface.confirmed 0 4 = hiddenChild := by
  decide

theorem pooledCounts :
    ((Run.readAt pooledLMD attackRun 3 0).2.filter
      (fun o => o.payload == Vote.parent)).length = 6 ∧
    ((Run.readAt pooledLMD attackRun 3 0).2.filter
      (fun o => o.payload == Vote.visible)).length = 2 ∧
    ((Run.readAt pooledLMD attackRun 4 0).2.filter
      (fun o => o.payload == Vote.hidden)).length = 3 := by
  decide

theorem reorg :
    Block.Preceq visibleChild (readAt pooledLMD attackRun interface.confirmed 0 3) ∧
    ¬ Block.Preceq visibleChild (readAt pooledLMD attackRun interface.confirmed 0 4) := by
  rw [visibleBeforeRelease, hiddenAfterRelease]
  constructor <;> decide

theorem faultyVotesReleased :
    Run.processes pooledLMD attackRun 0 (faultyVote 0) 4 ∧
    Run.processes pooledLMD attackRun 0 (faultyVote 1) 4 ∧
    Run.processes pooledLMD attackRun 0 (faultyVote 2) 4 :=
  ⟨⟨26, rfl⟩, ⟨27, rfl⟩, ⟨28, rfl⟩⟩

theorem accumulationWitness :
    ExecutionValid pooledLMD env attackRun ∧
    PartialSynchrony pooledLMD env attackRun ∧
    (faulty attackRun).Nonempty ∧
    ∃ v ∈ attackRun.honest, ∃ t t' : Time, t < t' ∧
      Block.Preceq visibleChild (readAt pooledLMD attackRun interface.confirmed v t) ∧
      ¬ Block.Preceq visibleChild (readAt pooledLMD attackRun interface.confirmed v t') := by
  exact ⟨attackExecution, attackSynchrony, attackHasFault,
    0, by decide, 3, 4, by decide, reorg.1, reorg.2⟩

end AvailableChain.Witnesses.Accumulation
end
