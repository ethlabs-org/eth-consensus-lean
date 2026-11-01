module
public import AvailableChainFGCompose.Proofs.SafetyOrigin

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0Origin
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! P0-origin controls (pure data). One node holds a queue of one body. A child body that
arrives before its parent waits in the queue. The delivery of the parent then admits the
parent and the queued child: one delivery adds two blocks. The frozen
`FGSafetyStoreLaws.process_new` is false in this model for every `Good`. The origin record
holds, with the queue as the pending reader. -/

private abbrev Obj : Type := V2.Signed Unit (fun _ : Unit => 1) Nat

/-- The queue and the stage. Stage 0: genesis only; 1: the parent; 2: the parent and the
child. -/
private abbrev TB : Type := Option Obj × Nat

private def tbProcess (st : TB) (o : Obj) : TB :=
  if o.payload = 0 then
    (if st.2 = 0 then ⟨none, st.1.elim 1 (fun _ => 2)⟩ else st)
  else if o.payload = 1 then
    (if st.2 = 1 then ⟨none, 2⟩
      else if st.2 = 0 ∧ st.1.isNone then ⟨some o, 0⟩ else st)
  else st

private abbrev twoBody : V2.ProtocolSpecD Unit where
  State := TB
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := ⟨none, 0⟩
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := tbProcess
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => ⟨none, 0⟩
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private def tbA : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def tbB : FGBlock (Fin 1) := .node tbA 2 ⟨2⟩ 0 []

private def tbTF (k : Nat) : Finset (FGBlock (Fin 1)) :=
  if k = 0 then {.genesis} else if k = 1 then {.genesis, tbA} else {.genesis, tbA, tbB}

private def tbErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (tbErase p) s r (encFGBody x rs)

private theorem tbErase_inj : Function.Injective tbErase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [tbErase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [tbErase] at h
    | node q t u y ts =>
      simp only [tbErase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private noncomputable abbrev tbR : FGCoreReads twoBody 1 Unit Unit Unit where
  core st := ⟨(), ⟨tbTF st.2, .genesis, .genesis, 0, 1⟩, [], []⟩
  erase := tbErase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private noncomputable abbrev tbS : FGSafetyReads twoBody 1 Unit where
  proposalErase := fun o =>
    if o.payload = 0 then some (tbErase tbA)
    else if o.payload = 1 then some (tbErase tbB) else none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, 2⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

private abbrev tbH : FGHeightView (Fin 1) :=
  fun _ => ⟨.genesis, 0, 0, .genesis, ∅, ∅, 0, .genesis⟩
private abbrev tbF : FGFinalityView (Fin 1) := fun _ => ⟨.genesis, 0⟩

/-- A queued object is a child body, and the parent is not yet held. -/
private def tbGood (st : TB) : Prop := ∀ q, st.1 = some q → q.payload = 1 ∧ st.2 = 0
private def tbPending (st : TB) (q : Obj) : Prop := st.1 = some q

private def parentObj : Obj := ⟨.none, 0⟩
private def childObj : Obj := ⟨.none, 1⟩

private theorem tbTF_genesis (k : Nat) : FGBlock.genesis ∈ tbTF k := by
  unfold tbTF; split_ifs <;> simp

private theorem tbTF_parent (k : Nat) (X : FGBlock (Fin 1)) (h : X ∈ tbTF k) :
    X.parent ∈ tbTF k := by
  unfold tbTF at h ⊢
  split_ifs at h ⊢ <;> simp at h ⊢ <;> rcases h with rfl | rfl | rfl <;>
    simp [FGBlock.parent, tbA, tbB]

private theorem tbInvariant (st : TB) : FGStoreInvariant tbH tbF (tbR.core st).fg where
  closed := tbTF_parent st.2
  gen := tbTF_genesis st.2
  Fmem := tbTF_genesis st.2
  hmax := by
    have h0 : (tbTF st.2).sup (fun _ => (0 : Nat)) = 0 :=
      Nat.eq_zero_of_le_zero (Finset.sup_le (fun _ _ => le_rfl))
    change 1 = (tbTF st.2).sup (fun _ => (0 : Nat)) ⊔ 1
    rw [h0]; rfl
  pair := ⟨⟨.genesis, tbTF_genesis st.2,
    by change FGBlock.Preceq .genesis .genesis; decide, rfl, rfl⟩, fun _ _ _ => le_rfl⟩
  FJ := by change FGBlock.Preceq .genesis .genesis; decide
  Fcar := ⟨.genesis, tbTF_genesis st.2, rfl⟩

private theorem tbGood_process (st : TB) (o : Obj) (h : tbGood st) : tbGood (tbProcess st o) := by
  unfold tbProcess
  split_ifs with h0 hs h1 hs1 hq
  · intro q hq; cases hq
  · exact h
  · intro q hq; cases hq
  · intro q hq'; cases hq'; exact ⟨h1, rfl⟩
  · exact h
  · exact h

/-- CONTROL: the delivery of the parent to a node with a queued child adds two blocks. -/
private theorem two_blocks_one_delivery :
    (tbR.core ⟨some childObj, 0⟩).fg.TF = {.genesis} ∧
      (tbR.core (twoBody.process ⟨some childObj, 0⟩ parentObj)).fg.TF =
        {.genesis, tbA, tbB} ∧ tbA ≠ tbB ∧ tbA ≠ .genesis ∧ tbB ≠ .genesis := by
  refine ⟨rfl, rfl, by decide, by decide, by decide⟩

private theorem tbProcessOrigin : FGProcessOrigin tbR tbS tbGood tbPending := by
  rw [FGProcessOrigin_def]
  intro st o B hg hB hold
  change B ∈ tbTF (tbProcess st o).2 at hB
  change B ∉ tbTF st.2 at hold
  unfold tbProcess at hB
  split_ifs at hB with h0 hs h1 hs1 hq
  · cases hqd : st.1 with
    | none =>
      rw [hqd] at hB
      rw [hs] at hold
      simp [tbTF] at hB hold
      rcases hB with rfl | rfl
      · exact absurd rfl hold
      · exact ⟨o, Or.inl rfl, by simp [h0], rfl⟩
    | some q =>
      rw [hqd] at hB
      rw [hs] at hold
      simp [tbTF] at hB hold
      rcases hB with rfl | rfl | rfl
      · exact absurd rfl hold
      · exact ⟨o, Or.inl rfl, by simp [h0], rfl⟩
      · exact ⟨q, Or.inr hqd, by simp [(hg q hqd).1], rfl⟩
  · exact absurd hB hold
  · rw [hs1] at hold
    simp [tbTF] at hB hold
    rcases hB with rfl | rfl | rfl
    · exact absurd rfl hold.1
    · exact absurd rfl hold.2
    · exact ⟨o, Or.inl rfl, by simp [h1], rfl⟩
  · rw [hq.1] at hold
    exact absurd hB hold
  · exact absurd hB hold
  · exact absurd hB hold

private theorem tbPendingOrigin : FGPendingOrigin (P := twoBody) tbGood tbPending := by
  rw [FGPendingOrigin_def]
  refine ⟨fun o h => (by cases h), fun _ _ _ _ h => h, fun st o q _ h => ?_,
    fun _ _ _ _ h => h, fun _ _ o _ h => (by cases h)⟩
  change (tbProcess st o).1 = some q at h
  unfold tbProcess at h
  split_ifs at h with h0 hs h1 hs1 hq
  · exact Or.inl h
  · exact Or.inr (Option.some.inj h).symm
  · exact Or.inl h
  · exact Or.inl h

private theorem tbCore : FGCoreLaws tbR where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st o := by
    change tbTF st.2 ⊆ tbTF (tbProcess st o).2
    unfold tbProcess
    split_ifs with h0 hs h1 hs1 hq
    · rw [hs]; intro X hX; simp [tbTF] at hX; subst hX; exact tbTF_genesis _
    · exact Finset.Subset.refl _
    · rw [hs1]; intro X hX; simp [tbTF] at hX ⊢; rcases hX with rfl | rfl <;> simp
    · rw [hq.1]
    · exact Finset.Subset.refl _
    · exact Finset.Subset.refl _
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := tbErase_inj

/-- premises_sat for the origin consumers on the two-body model: the core laws and the
origin record, with the queue as the pending reader. -/
private theorem twoBody_premises_sat :
    FGCoreLaws tbR ∧ FGSafetyStoreOriginLaws tbR tbS tbH tbF tbGood tbPending :=
  ⟨tbCore,
   { initial_good := fun q h => by cases h
     clock_good := fun _ _ h => h
     process_good := tbGood_process
     own_good := fun _ _ h => h
     restart_good := fun _ _ _ q h => by cases h
     invariant := fun st _ => tbInvariant st
     initial_tf := fun B hB => by simpa [tbTF] using hB
     restart_tf := fun st _ B _ hB => by
       have : B = .genesis := by simpa [tbTF] using hB
       subst this
       exact tbTF_genesis _
     process_origin := tbProcessOrigin
     pending_origin := tbPendingOrigin }⟩

/-- NEGATIVE: the pending reader is necessary. With no pending object the origin record is
false in this model, for every `Good`. -/
private theorem twoBody_no_pending_false (Good : TB → Prop) :
    ¬ FGSafetyStoreOriginLaws tbR tbS tbH tbF Good (fun _ _ => False) := by
  intro L
  have hg : Good ⟨some childObj, 0⟩ := L.process_good _ childObj L.initial_good
  have ho := L.process_origin
  rw [FGProcessOrigin_def] at ho
  obtain ⟨origin, hsrc, he, -⟩ := ho ⟨some childObj, 0⟩ parentObj tbB hg
    (by rw [two_blocks_one_delivery.2.1]; simp)
    (by rw [two_blocks_one_delivery.1]; simp [tbB])
  rcases hsrc with rfl | hf
  · have hAB : tbA = tbB := tbErase_inj (Option.some.inj he)
    exact two_blocks_one_delivery.2.2.1 hAB
  · exact hf

/-- NEGATIVE: the frozen record, with `process_new`, is false in this model for every
`Good`. The frozen record would give the origin record with no pending object. -/
private theorem twoBody_frozen_false (Good : TB → Prop) :
    ¬ FGSafetyStoreLaws tbR tbS tbH tbF Good :=
  fun L => twoBody_no_pending_false Good (safetyStoreOriginLaws_of_storeLaws L)

private abbrev tbEnv : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

/-- The child arrives first; the parent arrives second. -/
private noncomputable abbrev tbRun : V2.D.Run Unit twoBody where
  honest := {()}
  horizon := 2
  events := [.deliver () childObj 1, .deliver () parentObj 2]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem tbRun_states :
    V2.D.Run.stateBefore tbEnv tbRun 1 () = ⟨some childObj, 0⟩ ∧
      V2.D.Run.stateBefore tbEnv tbRun 2 () = ⟨none, 2⟩ := by decide

/-- POSITIVE: the generic origin lemma on the run. The second delivery adds the child
block, and its origin is the first delivery, not the delivery that added it. -/
private theorem tbRun_child_origin :
    tbB ∉ (tbR.core (V2.D.Run.stateBefore tbEnv tbRun 1 ())).fg.TF ∧
      tbB ∈ (tbR.core (V2.D.Run.stateBefore tbEnv tbRun 2 ())).fg.TF ∧
      ∃ o t, V2.Event.deliver () o t ∈ tbRun.events ∧
        tbS.proposalErase o = some (tbR.erase tbB) ∧ o = childObj ∧ t = 1 := by
  rw [tbRun_states.1, tbRun_states.2]
  refine ⟨by simp [tbTF, tbB], by simp [tbTF], ?_⟩
  have hB : tbB ∈ (tbR.core (V2.D.Run.stateBefore tbEnv tbRun 2 ())).fg.TF := by
    rw [tbRun_states.2]; simp [tbTF]
  obtain ⟨o, t, hd, he, -⟩ :=
    ((safety_origin_stateBefore twoBody_premises_sat.1 twoBody_premises_sat.2 tbEnv tbRun 2
      ()).2.1 tbB hB).resolve_left two_blocks_one_delivery.2.2.2.2
  refine ⟨o, t, hd, he, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd
  · cases hd; exact ⟨rfl, rfl⟩
  · cases hd
    exact absurd (tbErase_inj (Option.some.inj he)) two_blocks_one_delivery.2.2.1

/-- POSITIVE: the public run-block variant on the same prefix. -/
private theorem tbRun_child_runBlock : safetyRunBlock tbR tbS tbEnv tbRun tbB :=
  safety_stored_runBlock_origin twoBody_premises_sat.1 twoBody_premises_sat.2 tbEnv tbRun 2 ()
    tbB (by rw [tbRun_states.2]; simp [tbTF]) two_blocks_one_delivery.2.2.2.2

#print axioms two_blocks_one_delivery
#print axioms twoBody_premises_sat
#print axioms twoBody_no_pending_false
#print axioms twoBody_frozen_false
#print axioms tbRun_states
#print axioms tbRun_child_origin
#print axioms tbRun_child_runBlock

end AvailableChain.FGCompose.Tests.P0Origin
end
