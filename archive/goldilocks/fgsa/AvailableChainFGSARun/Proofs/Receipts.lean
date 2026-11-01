module
public import AvailableChainFGSARun.Proofs.Roots
public import AvailableChainFGSARun.Proofs.NamedDelivery
public import AvailableChainFGSARun.Proofs.Interface -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainFGSARun.Proofs.Readiness
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSARun.Proofs.RowHistory -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.StampOrigins
public import AvailableChainFGSARun.Proofs.ReadyAcceptance
public import AvailableChainFGSARun.Statements.Receipts
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSARun.Proofs.EmissionWellFormed
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy -- shake: keep (re-export)

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def hygiene_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

private theorem receipt_admitBlock_hygiene_eq : @admitBlock = @hygiene_admitBlock := rfl

end AvailableChain.FGSA

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The clock of every run state is nonnegative, including after restore. -/
theorem fgsa_clockOf_nonneg (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (k : Nat) (x : V) :
    0 ≤ (fgsaTimelyClock p c).clockOf (V2.D.Run.stateBefore E rho k x) := by
  rw [fgsaTimelyClock_clockOf p c (V2.D.Run.stateBefore E rho k x),
    ← fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)]
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun st => 0 ≤ (fgsaClock p c).now st) (Nat.zero_le k) x ?_ ?_
  · intro j e _ _ he hx hj
    cases e with
    | restart v t =>
      change v = x at hx
      subst v
      simp only [V2.D.World.step, Function.update_self]
      have hNow := fgsa_restore_now p c
        ((fgsa p c).durable (V2.D.Run.stateBefore E rho j x)) t
      exact hNow.symm ▸ (hS.in_horizon _ (List.mem_of_getElem? he)).1
    | tick v t =>
      change v = x at hx
      subst v
      simp only [V2.D.World.step, Function.update_self, V2.D.Engine.ClockLaws.now_tick]
      exact (hS.in_horizon _ (List.mem_of_getElem? he)).1
    | deliver v o t =>
      change v = x at hx
      subst v
      simpa only [V2.D.World.step, Function.update_self, (fgsaClock p c).process] using hj
  · simp only [V2.D.Run.stateBefore, List.take_zero, List.foldl_nil]
    dsimp only [V2.D.World.init]
    simpa only [(fgsaClock p c).init] using (le_refl (0 : Time))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A processed object stays processed on each restart-free interval. -/
theorem processed_stable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (v : V) (o : Obj p) (i j : Nat)
    (hij : i ≤ j) (hrf : V2.D.restartFree rho v i j)
    (h : (fgsa p c).processed (V2.D.Run.stateBefore E rho i v) o = true) :
    (fgsa p c).processed (V2.D.Run.stateBefore E rho j v) o = true :=
  (fgsaHooks p c).processed_stable E rho hS v o i j hij hrf h

private theorem t78_vote_stamp_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (v : GridCO.Wire p.n .root)
    (hm : v ∈ (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    (v, GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base v) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp := by
  have hm' := hm
  rw [← fgsa_vote_stamp_keys E rho k x] at hm'
  obtain ⟨⟨v', t⟩, ht, he⟩ := List.mem_map.mp hm'
  dsimp only at he
  subst v'
  unfold GridCO.stampVote
  cases hf : (V2.D.Run.stateBefore E rho k x).st.base.voteStamp.find? (fun row => row.1 == v) with
  | none => have h := List.find?_eq_none.mp hf (v, t) ht; simp at h
  | some row =>
    have he : row.1 = v := by simpa using List.find?_some hf
    have hh := List.mem_of_find?_eq_some hf
    simpa only [Option.map_some, Option.getD_some, ← he] using hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A HEAD stamp below a public cutoff gives acceptance strictly before it. -/
theorem fgsa_vote_accepted_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hNoRestart : V2.D.NoRestart rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (b : BlockId) (X : Time)
    (hpub : V2.PublicTime E X) (hzero : 0 ≤ X)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes)
    (ht : GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base
      ⟨.seat s i, .head b⟩ < X) :
    ∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j x (ofHead p ⟨.seat (.head s) i, b⟩) t ∧ t < X := by
  have hS := hV.toScheduleWellFormed
  obtain ⟨j, hj, t, ha, he⟩ := fgsa_vote_stamp_source E rho hNoRestart k x s i b _
    (t78_vote_stamp_mem E rho k x _ hm)
  refine ⟨j, hj, t, ha, ?_⟩
  by_contra hn
  obtain ⟨parent, hd, -⟩ := ha.1
  have hb := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c) (fgsaRestoreTimeLaw p c)
    E rho hV hd hpub hzero (le_of_not_gt hn)
  rw [he] at ht
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hb
  exact (not_lt.mpr hb) ht

private theorem t78_block_stamp_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (b : Block)
    (hm : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    (b, GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base b) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.blockStamp := by
  rw [← (metaInv_stateBefore E rho k x).stampKeys] at hm
  obtain ⟨⟨b', t⟩, ht, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b'
  unfold GridCO.stampBlock
  cases hf : (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.find? (fun row => row.1 == b) with
  | none => have h := List.find?_eq_none.mp hf (b, t) ht; simp at h
  | some row =>
    have he : row.1 = b := by simpa using List.find?_some hf
    have hh := List.mem_of_find?_eq_some hf
    simpa only [Option.map_some, Option.getD_some, ← he] using hh

private theorem t78_block_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ s N, (toWire p o).decode = some (.block s N) ∧ N.erase = b := by
  dsimp only [blockOf?] at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    subst b
    exact ⟨_, _, rfl, rfl⟩

private theorem t78_proposal_direct (st : State p.n) (parent o : Obj p)
    (b : Block) (hb : blockOf? p o = some b) (hh : handlesS p st parent o) : parent = o := by
  obtain ⟨s, N, hd, heN⟩ := t78_block_decode hb
  rcases hh with h | h
  · exact h
  · -- A proposal is never a carried HEAD or row.
    cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r N =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[R6] A newly accepted proposal passed the parent-state row check. -/
theorem fgsa_accepted_rowsValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (x : V) (o : Obj p) (t : Time) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N))
    (ha : V2.D.Run.acceptsAt E rho j x o t) :
    ∃ P, parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      rowsValidForParent p P N.erase.slot N.rows = true := by
  obtain ⟨parent, he, hh⟩ := ha.1
  have hp := t78_proposal_direct _ parent o N.erase (by dsimp only [blockOf?]; rw [hd]) hh
  subst parent
  have hpost := ha.2.2
  rw [V2.D.Run.stateBefore_succ E rho he] at hpost
  simp only [V2.D.World.step, Function.update_self] at hpost
  change processedS p (FGSA.process p (V2.D.Run.stateBefore E rho j x).st
    (toWire p o)) o = true at hpost
  dsimp only [FGSA.process] at hpost
  rw [hd] at hpost
  dsimp only at hpost
  cases hNamed : namedParentHeld (V2.D.Run.stateBefore E rho j x).st N with
  | false =>
    rw [admitBlock_refused p _ s N (Or.inl hNamed)] at hpost
    cases ha.2.1.symm.trans hpost
  | true =>
    cases hP : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase with
    | none =>
        rw [admitBlock_refused p _ s N (Or.inr (Or.inl hP))] at hpost
        cases ha.2.1.symm.trans hpost
    | some P =>
        cases hacc : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P with
        | false =>
            rw [admitBlock_refused p _ s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))] at hpost
            cases ha.2.1.symm.trans hpost
        | true => exact ⟨P, rfl, blockAccepted_rowsValid hacc⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[R6] An emitted or accepted proposal has immutable parent validity.
Any store that holds its parent resolves the same exact parent content. -/
theorem fgsa_trigger_rowsValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (t : Time) (s : Slot) (N : NamedProposal p.n) (hT : Gen.V2.Duty.Trigger E rho o t)
    (hd : (toWire p o).decode = some (.block s N))
    (st : State p.n) (P : FGBlock (Fin p.n)) (hP : parentFG st N.erase = some P) :
    rowsValidForParent p P N.erase.slot N.rows = true := by
  have hPe := ((parentFG_spec st N.erase P).mp hP).2
  rcases hT with ⟨v, _, k, he, hem⟩ | ⟨v, _, k, ha⟩
  · have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    rw [ho, (V2.D.Run.step_tick_eq E rho he).2] at hem
    have hemit := (fgsa_emits_proposal E rho _ v t s (.proposal N)).mp hem
    have hs : (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st t).slot p = s := by
      rw [← hemit.2.1]
      exact fgsa_proposal_slot (c := c) _ s
    have hInv := (storeBundle_postClock E rho k v t).cstore
    obtain ⟨Q, hQ, hv⟩ := propose_rowsValid _ hInv s (c.app (rho.input v t)) hs
      N hemit.2.2.2.2
    have hQe := ((fgBlockOf_spec p _ hInv N.erase.parent Q).mp hQ).2
    have hQP : Q = P := eraseFG_injective (hQe.trans hPe.symm)
    simpa only [hQP] using hv
  · obtain ⟨Q, hQ, hv⟩ := fgsa_accepted_rowsValid E rho k v o t s N hd ha
    have hQe := ((parentFG_spec _ N.erase Q).mp hQ).2
    have hQP : Q = P := eraseFG_injective (hQe.trans hPe.symm)
    simpa only [hQP] using hv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[R6] A triggered proposal cannot fail the permanent invalidity test. -/
theorem fgsa_trigger_invalid_false (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (t : Time) (s : Slot) (N : NamedProposal p.n) (hT : Gen.V2.Duty.Trigger E rho o t)
    (hd : (toWire p o).decode = some (.block s N)) (st : State p.n) :
    invalidForParent p st N = false := by
  unfold invalidForParent
  split
  · rfl
  · rw [← named_erase_slot]
    cases hP : parentFG st N.erase with
    | none => rfl
    | some P =>
        change (!rowsValidForParent p P N.erase.slot N.rows) = false
        rw [fgsa_trigger_rowsValid E rho o t s N hT hd st P hP, Bool.not_true]

private theorem t78_block_accept_clock_pos (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (j : Nat) (x : V) (o : Obj p) (t : Time)
    (b : Block) (hb : blockOf? p o = some b) (ha : V2.D.Run.acceptsAt E rho j x o t) :
    0 < (V2.D.Run.stateBefore E rho j x).st.base.now := by
  obtain ⟨parent, he, hh⟩ := ha.1
  obtain ⟨s, N, hd, heN⟩ := t78_block_decode hb
  subst b
  have hp := t78_proposal_direct _ parent o N.erase hb hh
  subst parent
  have hpost := ha.2.2
  rw [V2.D.Run.stateBefore_succ E rho he] at hpost
  simp only [V2.D.World.step, Function.update_self] at hpost
  change processedS p (FGSA.process p (V2.D.Run.stateBefore E rho j x).st
    (toWire p o)) o = true at hpost
  dsimp only [FGSA.process] at hpost
  rw [hd] at hpost
  dsimp only at hpost
  cases hNamed : namedParentHeld (V2.D.Run.stateBefore E rho j x).st N with
  | false =>
    rw [admitBlock_refused p _ s N (Or.inl hNamed)] at hpost
    cases ha.2.1.symm.trans hpost
  | true =>
    cases hP : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase with
    | none =>
      rw [admitBlock_refused p _ s N (Or.inr (Or.inl hP))] at hpost
      cases ha.2.1.symm.trans hpost
    | some P =>
      cases hacc : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P with
      | false =>
        rw [admitBlock_refused p _ s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))] at hpost
        cases ha.2.1.symm.trans hpost
      | true =>
        have hf := blockAccepted_facts hacc
        have hbs := hf.2.1
        have hps := hf.2.2.2.2.1
        have hslot : 1 ≤ (V2.D.Run.stateBefore E rho j x).st.slot p :=
          (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hps)).trans hbs
        have hclock := (fgsa_slot_threshold_iff p _
          (by rw [← fgsaTimelyClock_clockOf p c (V2.D.Run.stateBefore E rho j x)]
              exact fgsa_clockOf_nonneg E rho hS j x) 1).1 hslot
        simp only [Nat.cast_one, mul_one] at hclock
        exact lt_of_lt_of_le (mul_pos (by decide) p.deltaPos) hclock

private theorem t78_block_clock_cut (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {j : Nat} {x : V} {o : Obj p} {t X : Time}
    (he : rho.events[j]? = some (.deliver x o t)) (hpub : V2.PublicTime E X)
    (hzero : 0 ≤ X) (hle : X ≤ t) :
    X ≤ (fgsaClock p c).now (V2.D.Run.stateBefore E rho j x) :=
  V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c) (fgsaRestoreTimeLaw p c)
    E rho hV he hpub hzero hle

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A non-genesis block stamp below a public cutoff gives an earlier acceptance.
No restart premise is needed: block admission requires a positive store clock. -/
theorem fgsa_block_accepted_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (k : Nat) (x : V) (b : Block) (X : Time)
    (hgen : b ≠ .genesis) (hpub : V2.PublicTime E X) (hzero : 0 ≤ X)
    (hm : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks)
    (ht : GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base b < X) :
    ∃ j < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t ∧ t < X := by
  have hS := hV.toScheduleWellFormed
  rcases fgsa_block_stamp_source_or_restart E rho k x b _
      (t78_block_stamp_mem E rho k x b hm) with hg | ⟨j, hj, t, o, hb, ha, hs⟩ |
      ⟨j, hj, wake, he, _, hheld, hs⟩
  · exact (hgen hg.1).elim
  · refine ⟨j, hj, t, o, hb, ha, ?_⟩
    by_contra hn
    obtain ⟨parent, he, -⟩ := ha.1
    have hc := t78_block_clock_cut E rho hV he hpub hzero (le_of_not_gt hn)
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hc
    rw [hs] at ht
    exact (not_lt.mpr hc) ht
  · obtain ⟨q, hq, t, o, hb, ha⟩ := fgsa_block_accepted_origin E rho j x b hgen hheld
    refine ⟨q, by omega, t, o, hb, ha, ?_⟩
    obtain ⟨parent, hd, -⟩ := ha.1
    obtain ⟨hql, hqe⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
    have hk := List.pairwise_iff_getElem.mp hS.sorted q j hql hjl hq
    rw [hqe, hje] at hk
    have htime := V2.D.Engine.time_le_of_key_le _ _ hk
    rw [hs] at ht
    exact htime.trans_lt ht

private theorem t78_vote_read_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (x : V) (D : Time)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBeforeTime E rho D x).st.base.votes) :
    GridCO.stampVote (V2.D.Run.stateBeforeTime E rho D x).st.base ⟨.seat s i, .head b⟩ < D := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hm ⊢
  rcases fgsa_vote_stamp_source_or_restart E rho _ x s i b _
      (t78_vote_stamp_mem E rho _ x _ hm) with ⟨j, hj, t, ha, hs⟩ |
      ⟨j, hj, w, he, hs, _⟩
  · obtain ⟨o, he, -⟩ := ha.1
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).1 hj
    have hc := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS he x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hc
    rw [hs]
    exact hc.trans_lt ht
  · rw [hs]
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).1 hj

private theorem t78_head_keys (v : GridCO.Wire p.n .root) (s : Slot) (i : Fin p.n)
    (hl : GridCO.headLabel? v = some s) (hi : GridCO.headSeat? v = some i) :
    ∃ b, v = ⟨.seat s i, .head b⟩ := by
  obtain ⟨auth, payload⟩ := v
  cases auth with
  | seat r j =>
    cases payload with
    | head B =>
      have hs : r = s := Option.some.inj hl
      have hj : j = i := Option.some.inj hi
      subst r j
      exact ⟨B, rfl⟩
    | proposal B raw sup => cases hl
  | proposer r => cases payload <;> cases hl
  | none => cases payload <;> cases hl

private theorem t78_cap_pair (st : GridCO.State p.n .root) (s : Slot) (i : Fin p.n)
    (hx : GridCO.equivocates (GridCO.votesAt st s) i = true) :
    ∃ v₁ ∈ st.votes, ∃ v₂ ∈ st.votes, v₁ ≠ v₂ ∧
      GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
      GridCO.headSeat? v₁ = some i ∧ GridCO.headSeat? v₂ = some i := by
  have hlen : 2 ≤ (GridCO.seatVotes (GridCO.votesAt st s) i).eraseDups.length :=
    of_decide_eq_true hx
  have hnodup := Internal.eraseDups_nodup' (GridCO.seatVotes (GridCO.votesAt st s) i)
  cases hl : (GridCO.seatVotes (GridCO.votesAt st s) i).eraseDups with
  | nil => rw [hl] at hlen; contradiction
  | cons v₁ vs =>
    cases vs with
    | nil => rw [hl] at hlen; contradiction
    | cons v₂ vs =>
      have hmem (v) (hv : v ∈ v₁ :: v₂ :: vs) : v ∈ st.votes ∧
          GridCO.headLabel? v = some s ∧ GridCO.headSeat? v = some i := by
        rw [← hl] at hv
        obtain ⟨hm, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp hv)
        obtain ⟨hm, hs⟩ := List.mem_filter.mp hm
        exact ⟨hm, beq_iff_eq.mp hs, beq_iff_eq.mp hi⟩
      have h₁ := hmem v₁ (List.mem_cons_self ..)
      have h₂ := hmem v₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      refine ⟨v₁, h₁.1, v₂, h₂.1, ?_, h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2⟩
      rw [hl] at hnodup
      exact fun he => (List.nodup_cons.mp hnodup).1
        (List.mem_cons.mpr (Or.inl he))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An in-window HEAD exclusion has two distinct witnesses with strict stamps. -/
theorem fgsa_head_excluded_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (x : V) (D : Time)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hwindow : (V2.D.Run.stateBeforeTime E rho D x).st.slot p ≤ s + 1)
    (hx : excludesS p (V2.D.Run.stateBeforeTime E rho D x).st
      (ofHead p ⟨.seat (.head s) i, b⟩) = true) :
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
      v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
      GridCO.headSeat? v₁ = some i ∧ GridCO.headSeat? v₂ = some i ∧
      GridCO.stampVote st.base v₁ < D ∧ GridCO.stampVote st.base v₂ < D := by
  dsimp only
  have hx' : GridCO.excludes p.toParams.engine
      (V2.D.Run.stateBeforeTime E rho D x).st.base ⟨.seat s i, .head b⟩ = true := hx
  have heq := (Internal.grid_excludes_head_iff _ s i b).1 hx'
  have hold : ¬ s + 1 <
      ((V2.D.Run.stateBeforeTime E rho D x).st.base.now / (4 * p.toParams.engine.Δ)).toNat :=
    not_lt.mpr hwindow
  obtain ⟨v₁, h₁, v₂, h₂, hne, hl₁, hl₂, hi₁, hi₂⟩ :=
    t78_cap_pair _ s i (heq.2.resolve_left hold)
  refine ⟨v₁, h₁, v₂, h₂, hne, hl₁, hl₂, hi₁, hi₂, ?_, ?_⟩
  · obtain ⟨B, rfl⟩ := t78_head_keys v₁ s i hl₁ hi₁
    exact t78_vote_read_stamp E rho hS x D s i B h₁
  · obtain ⟨B, rfl⟩ := t78_head_keys v₂ s i hl₂ hi₂
    exact t78_vote_read_stamp E rho hS x D s i B h₂

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Both delivery forms retain an in-window HEAD or two strictly stamped cap witnesses.
The trigger can be an honest emission or acceptance, including a carried HEAD.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_head_receipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hDelta : E.Δ = p.Δ) (hExecution : V2.D.ExecutionValid E rho)
    (hNoRestart : V2.D.NoRestart rho) (dl : Time → Time) (cut : Time)
    (s : Slot) (i : Fin p.n) (b : BlockId) (t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho (ofHead p ⟨.seat (.head s) i, b⟩) t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hwindow : (V2.D.Run.stateBeforeTime E rho (dl t) w).st.slot p ≤ s + 1)
    (hhor : dl t ≤ rho.horizon) (hAwake : V2.D.AwakeOn E w t (dl t)) :
    let st := (V2.D.Run.stateBeforeTime E rho (dl t) w).st
    let v := baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n)
    (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some i ∧ GridCO.headSeat? v₂ = some i ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t := by
  let o := ofHead p (⟨.seat (.head s) i, b⟩ : HeadWire p.n)
  let C := fgsaTimelyClock p c
  have hS := hExecution.toScheduleWellFormed
  dsimp only
  by_cases hx : excludesS p (V2.D.Run.stateBeforeTime E rho (dl t) w).st o = true
  · exact Or.inr (fgsa_head_excluded_before E rho hS w (dl t) s i b hwindow hx)
  · left
    have htime : 0 ≤ t ∧ t ≤ rho.horizon ∧ C.actTime o ≤ Gen.V2.Duty.pubFloor E t := by
      rcases hT with ⟨v, _, k, he, hem⟩ | ⟨v, _, k, ha⟩
      · have ht := hS.in_horizon _ (List.mem_of_getElem? he)
        rw [(V2.D.Run.step_tick_eq E rho he).2] at hem
        have hemit := (fgsa_emits_head E rho _ v t s i b).1 hem
        have hthreshold : C.actTime o = 4 * p.Δ * (s : Int) := by
          rw [fgsaTimelyClock_actTime p c o]
          rfl
        refine ⟨ht.1, ht.2, Gen.V2.Duty.timely_of_emit E rho C o t ht.1 ?_ ?_⟩
        · rw [hthreshold]
          refine ⟨4 * s, ?_⟩
          rw [hDelta]
          push_cast
          ring
        · rw [hthreshold, ← hemit.2.1]
          exact le_add_of_nonneg_right (le_of_lt p.deltaPos)
      · obtain ⟨parent, he, -⟩ := ha.1
        have ht := hS.in_horizon _ (List.mem_of_getElem? he)
        refine ⟨ht.1, ht.2, timely_of_relay_retained E rho C (fgsaAdmitSound p c)
          hS (by dsimp only [C]
                 rw [fgsaTimelyClock_clock]
                 exact fgsaRestoreTimeLaw p c)
          (fun obj => by dsimp only [C]
                         exact (fgsaTimelyClock_actTime p c obj).symm ▸
                           (fgsa_admissionTime_public p E hDelta obj)) v k o t ha⟩
    have hAct : fgsaAdmissionTime p o ≤ Gen.V2.Duty.pubFloor E t := by
      have h := htime.2.2
      rw [fgsaTimelyClock_actTime] at h
      exact h
    have hprocessed := fgsa_processed_by_deadline_ready E rho hExecution hNoRestart dl cut
      o t w hD (by change ¬ False; exact not_false) hT hw htime.1 htime.2.1 hcut hlt hhor
      hAwake hAct (by
        intro j t' _ htd hh
        have hcall := hh
        obtain ⟨parent, he, -⟩ := hh
        have hj := (Gen.V2.Duty.index_lt_idxBefore_iff hS he (dl t)).2 htd
        exact fgsa_hReady_of_not_block (by intro s' N h; cases h)
          (fgsa_hWF_of_delivery hExecution.wire) j t' hj hcall)
      (Bool.eq_false_iff.mpr hx)
    have hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBeforeTime E rho (dl t) w).st.base.votes := of_decide_eq_true hprocessed
    exact ⟨hm, t78_vote_read_stamp E rho hS w (dl t) s i b hm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Each source cap witness has its own earlier acceptance for the relay trigger. -/
theorem fgsa_head_cap_sources (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hNoRestart : V2.D.NoRestart rho)
    (x : V) (D : Time)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hwindow : (V2.D.Run.stateBeforeTime E rho D x).st.slot p ≤ s + 1)
    (hx : excludesS p (V2.D.Run.stateBeforeTime E rho D x).st
      (ofHead p ⟨.seat (.head s) i, b⟩) = true) :
    ∃ b₁ b₂, b₁ ≠ b₂ ∧ ∃ j₁ j₂ t₁ t₂,
      j₁ < V2.D.Run.idxBefore rho D ∧ j₂ < V2.D.Run.idxBefore rho D ∧
      V2.D.Run.acceptsAt E rho j₁ x (ofHead p ⟨.seat (.head s) i, b₁⟩) t₁ ∧
      V2.D.Run.acceptsAt E rho j₂ x (ofHead p ⟨.seat (.head s) i, b₂⟩) t₂ ∧
      t₁ < D ∧ t₂ < D := by
  obtain ⟨v₁, h₁, v₂, h₂, hne, hl₁, hl₂, hi₁, hi₂, -, -⟩ :=
    fgsa_head_excluded_before E rho hS x D s i b hwindow hx
  obtain ⟨b₁, rfl⟩ := t78_head_keys v₁ s i hl₁ hi₁
  obtain ⟨b₂, rfl⟩ := t78_head_keys v₂ s i hl₂ hi₂
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at h₁ h₂
  obtain ⟨j₁, hj₁, t₁, ha₁, -⟩ := fgsa_vote_stamp_source E rho hNoRestart _ x s i b₁ _
    (t78_vote_stamp_mem E rho _ x _ h₁)
  obtain ⟨j₂, hj₂, t₂, ha₂, -⟩ := fgsa_vote_stamp_source E rho hNoRestart _ x s i b₂ _
    (t78_vote_stamp_mem E rho _ x _ h₂)
  refine ⟨b₁, b₂, (fun h => hne (by rw [h])), j₁, j₂, t₁, t₂,
    hj₁, hj₂, ha₁, ha₂, ?_, ?_⟩
  · obtain ⟨o, he, -⟩ := ha₁.1
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).1 hj₁
  · obtain ⟨o, he, -⟩ := ha₂.1
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).1 hj₂

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every decoded fixed-FG row has a false exclusion result. -/
theorem excludesS_honestRow_false (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (i : Fin p.n) (body : RowPayload) (t : Time) (w : V) :
    excludesS p (V2.D.Run.stateBeforeTime E rho (dl t) w).st
      (ofRow p ⟨.seat .fg i, body⟩) = false := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. A required compatible proposal is stored at its own receipt deadline.
This transports its block only; each carried HEAD uses its own trigger.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_proposal_receipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (hDelta : E.Δ = p.Δ) (hExecution : V2.D.ExecutionValid E rho)
    (hNoRestart : V2.D.NoRestart rho) (dl : Time → Time) (cut : Time)
    (s : Slot) (N : NamedProposal p.n)
    (t : Time) (w : V) (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer s, .proposal N⟩) t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hCompat : Block.Compatible N.erase (eraseFG (V2.D.Run.stateBeforeTime E rho (dl t)
        w).st.fg.F))
    (hhor : dl t ≤ rho.horizon) (hAwake : V2.D.AwakeOn E w t (dl t)) :
    ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) w).st.fg.TF, eraseFG Y = N.erase := by
  let o := ofWire p (⟨.proposer s, .proposal N⟩ : Wire p.n)
  let C := fgsaTimelyClock p c
  have hS := hExecution.toScheduleWellFormed
  have hReceiptScope := proposal_trigger_in_receipt_scope E rho s N t hT
  have hd : (toWire p o).decode = some (.block s N) := by
    rw [toWire_ofWire]
    rfl
  have htime : 0 ≤ t ∧ t ≤ rho.horizon ∧ C.actTime o ≤ Gen.V2.Duty.pubFloor E t := by
    rcases hT with ⟨v, _, k, he, hem⟩ | ⟨v, _, k, ha⟩
    · have ht := hS.in_horizon _ (List.mem_of_getElem? he)
      rw [(V2.D.Run.step_tick_eq E rho he).2] at hem
      have hemit := (fgsa_emits_proposal E rho _ v t s (.proposal N)).1 hem
      have hthreshold : C.actTime o = 4 * p.Δ * (s : Int) := by
        rw [fgsaTimelyClock_actTime p c o]
        rfl
      refine ⟨ht.1, ht.2, Gen.V2.Duty.timely_of_emit E rho C o t ht.1 ?_ ?_⟩
      · rw [hthreshold]
        refine ⟨4 * s, ?_⟩
        rw [hDelta]
        push_cast
        ring
      · rw [hthreshold, ← hemit.2.1]
        exact le_refl _
    · obtain ⟨parent, he, -⟩ := ha.1
      have ht := hS.in_horizon _ (List.mem_of_getElem? he)
      refine ⟨ht.1, ht.2, timely_of_relay_retained E rho C (fgsaAdmitSound p c)
        hS (by dsimp only [C]
               rw [fgsaTimelyClock_clock]
               exact fgsaRestoreTimeLaw p c)
        (fun obj => by dsimp only [C]
                       exact (fgsaTimelyClock_actTime p c obj).symm ▸
                         (fgsa_admissionTime_public p E hDelta obj)) v k o t ha⟩
  have hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
      V2.D.Run.handlesAt E rho i w o t' →
      namedParentHeld (V2.D.Run.stateBefore E rho i w).st N = true ∧
        (parentFG (V2.D.Run.stateBefore E rho i w).st N.erase).isSome = true := by
    rintro i t' _ ⟨parent, he, hh⟩
    have hp := t78_proposal_direct _ parent o N.erase (by dsimp only [blockOf?]; rw [hd]) hh
    subst parent
    have hdeps := hExecution.deps i w o t' he
    change depsS p (V2.D.Run.stateBefore E rho i w).st o = true at hdeps
    dsimp only [depsS] at hdeps
    rw [hd] at hdeps
    exact Bool.and_eq_true_iff.mp hdeps
  have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false := by
    change excludesS p (V2.D.Run.stateBeforeTime E rho (dl t) w).st o = false
    change N.erase.compatible (eraseFG (V2.D.Run.stateBeforeTime E rho (dl t) w).st.fg.F) = true
      at hCompat
    dsimp only [excludesS]
    rw [hd]
    simp only [blockExcluded, activeCompatible, hCompat, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho o t s N hT hd _
  have hAct : fgsaAdmissionTime p o ≤ Gen.V2.Duty.pubFloor E t := by
    have h := htime.2.2
    rw [fgsaTimelyClock_actTime] at h
    exact h
  have hp := fgsa_processed_by_deadline_ready E rho hExecution hNoRestart dl cut o t w hD
    (by change ¬ False; exact not_false) hT hw htime.1 htime.2.1 hcut hlt hhor hAwake hAct
    (by
      intro j t' _ htd hh
      have hcall := hh
      obtain ⟨parent, he, -⟩ := hh
      have hj := (Gen.V2.Duty.index_lt_idxBefore_iff hS he (dl t)).2 htd
      exact fgsa_hReady_of_parentStored hd (fgsa_hWF_of_delivery hExecution.wire) hParent
        j t' hj hcall) hNX
  have hScope : NamedProposalInRun p c E rho N := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hp
    exact proposal_processed_in_scope E rho hRoots hw _ s N hReceiptScope hp
  change processedS p (V2.D.Run.stateBeforeTime E rho (dl t) w).st o = true at hp
  dsimp only [processedS] at hp
  rw [hd] at hp
  simp only [decide_eq_true_eq] at hp
  obtain ⟨Y, hY, hroot⟩ := hp
  have hbScope : RootBlockInRun p c E rho N.erase := ⟨N, hScope, rfl⟩
  have hYscope : RootBlockInRun p c E rho (eraseFG Y) := by
    have hm := (storeBundle_stateBeforeTime E rho (dl t) w).cstore.baseTree (eraseFG Y)
      |>.mpr ⟨Y, hY, rfl⟩
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hm
    exact rootBlockInRun_held E rho hw _ hm
  exact ⟨Y, hY, rootBlockInRun_eq E rho (hRoots.toNamedRootCollisionFree E rho) hYscope hbScope
    (by simpa using (eraseFG_root Y).trans hroot)⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An honest HEAD in the receipt window is retained with a strict stamp.
The HEAD family can satisfy CStar independently of the linked FG family.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_honest_head_receipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hDelta : E.Δ = p.Δ) (hExecution : V2.D.ExecutionValid E rho)
    (hNoRestart : V2.D.NoRestart rho)
    (_hCStar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (dl : Time → Time) (cut : Time) (s : Slot) (i : Fin p.n) (b : BlockId)
    (t : Time) (v w : V) (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hv : v ∈ rho.honest)
    (hEmit : V2.D.Run.emits E rho v (ofHead p ⟨.seat (.head s) i, b⟩) t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hwindow : (V2.D.Run.stateBeforeTime E rho (dl t) w).st.slot p ≤ s + 1)
    (hhor : dl t ≤ rho.horizon) (hAwake : V2.D.AwakeOn E w t (dl t)) :
    let st := (V2.D.Run.stateBeforeTime E rho (dl t) w).st
    let o := baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n)
    o ∈ st.base.votes ∧ GridCO.stampVote st.base o < dl t := by
  have hS := hExecution.toScheduleWellFormed
  have hT : Gen.V2.Duty.Trigger E rho (ofHead p ⟨.seat (.head s) i, b⟩) t :=
    Or.inl ⟨v, hv, hEmit⟩
  rcases fgsa_head_receipt E rho hDelta hExecution hNoRestart dl cut s i b t w
    hD hT hw hcut hlt hwindow hhor hAwake with hm | ⟨v₁, h₁, v₂, h₂, hne, hl₁, hl₂, hi₁, hi₂, -, -⟩
  · exact hm
  · obtain ⟨k, he, hem⟩ := hEmit
    rw [(V2.D.Run.step_tick_eq E rho he).2] at hem
    have hEm := (fgsa_emits_head E rho _ v t s i b).1 hem
    have hstored (B : BlockId) (hm : (⟨.seat s i, .head B⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBeforeTime E rho (dl t) w).st.base.votes) : B = b := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hm
      obtain ⟨j, _, u, ha, -⟩ := fgsa_vote_stamp_source E rho hNoRestart _ w s i B _
        (t78_vote_stamp_mem E rho _ w _ hm)
      obtain ⟨parent, hd, hh⟩ := ha.1
      have hholder : V2.D.Run.holder rho (ofHead p ⟨.seat (.head s) i, B⟩).auth = some v :=
        congrArg some hEm.2.2.1
      have hsig : ∃ u', u' ≤ u ∧
          V2.D.Run.emits E rho v (ofHead p ⟨.seat (.head s) i, B⟩) u' := by
        rcases (fgsaHooks p c).handles_carries _ parent _ hh with hp | hc
        · subst parent
          exact hExecution.unforgeable w _ u ⟨j, hd⟩ v hv hholder
        · exact hExecution.carried w parent u ⟨j, hd⟩ _ hc v hv hholder
      obtain ⟨u', _, j', he', hem'⟩ := hsig
      rw [(V2.D.Run.step_tick_eq E rho he').2] at hem'
      have hEm' := (fgsa_emits_head E rho _ v u' s i B).1 hem'
      have ht : u' = t := hEm'.2.1.symm.trans hEm.2.1
      subst u'
      have hk : j' = k := fgsa_tick_unique E rho hS he' he
      subst j'
      exact hEm'.2.2.2.2.trans hEm.2.2.2.2.symm
    obtain ⟨b₁, rfl⟩ := t78_head_keys v₁ s i hl₁ hi₁
    obtain ⟨b₂, rfl⟩ := t78_head_keys v₂ s i hl₂ hi₂
    exact (hne (by rw [hstored b₁ h₁, hstored b₂ h₂])).elim

end AvailableChain.FGSA.Run
end
