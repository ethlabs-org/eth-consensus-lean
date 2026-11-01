module
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers
public import Mathlib.Tactic.IntervalCases -- shake: keep (interval_cases tests)
public import Mathlib.Tactic.FinCases -- shake: keep (fin_cases tests)

set_option linter.privateModule false

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.FinalityEpochs
open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
def proposal : Obj p :=
  ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 1 0 [] [] [])⟩

-- SleepTests.ownRun, with the HEAD-2 seat assigned to its honest sender.
def ownEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 31 ∨ 35 ≤ t)⟩

def ownHead : Obj p := ⟨.seat (.base (.head 2)) ⟨0, by decide⟩, .head ⟨0⟩⟩

def ownRun : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := {0}
  horizon := 38
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16,
    .tick 0 18, .deliver 0 ownHead 18, .tick 0 20, .tick 0 22, .tick 0 24,
    .tick 0 26, .tick 0 28, .tick 0 30, .restart 0 35, .tick 0 36, .tick 0 38]
  seatOf := fun l _ => match l with | .base .fg => 0 | .base (.head 2) => 0 | _ => 1
  input := fun _ _ => ()

theorem head_emitted : ownHead ∈ V2.D.Run.emitsAt ownEnv ownRun 10 := by
  change ownHead ∈ [ownHead]
  exact List.mem_singleton_self _

/-- Full validity includes the honest own-row emission and exact non-public wake. -/
theorem fgp_own_valid : V2.D.ExecutionValid ownEnv ownRun := by
  refine { toSleepWellFormed := ?_, toScheduleWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e h
      simp [ownRun] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e h
      simp [ownRun] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro v t h
      simp [ownRun] at h
      refine ⟨(t / 2).toNat, ?_⟩
      simp [ownEnv]; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t ≤ 38 at hh
      simp [ownEnv] at hk ha
      simp [ownRun]; dsimp [Time] at *; omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [ownRun] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [ownRun] at hib
    all_goals interval_cases i <;> first | contradiction | decide +kernel
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [ownRun] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      all_goals have hu0 : u = 0 := Finset.mem_singleton.mp hu
      all_goals subst u
      · simp [V2.D.Run.holder, proposal, ownRun] at hh
      · exact ⟨18, le_rfl, 10, by decide +kernel, head_emitted⟩
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [ownRun] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · change carriesS p proposal o' at hc
        change o' ∈ ([] : List (Obj p)) ∨ o' ∈ [] ∨ o' ∈ [] at hc
        simp at hc
        cases hc
      · change carriesS p ownHead o' at hc
        simp [carriesS, ownHead] at hc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v t h
      simp [ownRun] at h
      have hv : v = 0 := by tauto
      subst v
      simp [ownEnv]; dsimp [Time] at *; omega
    · intro v o t h
      simp [ownRun] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    · intro v t h
      simp [ownRun] at h
      rcases h with ⟨rfl, rfl⟩; decide
    · intro v hv t _ _ h
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      have ht : t = 35 := by simp [V2.D.Wakes, ownEnv] at h; dsimp [Time] at *; omega
      subst t; simp [ownRun]

/-- A fresh honest HEAD is lost when the receiver wakes in a later epoch. -/
theorem fresh_head_erased :
    ownHead ∈ V2.D.Run.emitsAt ownEnv ownRun 10 ∧
    (fgsa p unitCodec).processed (V2.D.Run.stateBefore ownEnv ownRun 12 0) ownHead = true ∧
    ownEnv.awake 0 36 = true ∧
    (fgsa p unitCodec).processed (V2.D.Run.stateBefore ownEnv ownRun 19 0) ownHead = false := by
  exact ⟨head_emitted, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- FullVoteService needs a current receiver service scope after a wake. -/
theorem full_vote_service_fails :
    ¬ FullVoteService p unitCodec ownEnv ownRun
      ((fgsa p unitCodec).clock (V2.D.Run.stateBefore ownEnv ownRun 19 0) 36).st 2 := by
  intro h
  have hm := (h 0 ⟨.seat (.head 2) 0, ⟨0⟩⟩ (by decide)
    ⟨10, by decide +kernel, head_emitted⟩ (by decide)).1
  have hempty : GridCO.votesAt
      ((fgsa p unitCodec).clock (V2.D.Run.stateBefore ownEnv ownRun 19 0) 36).st.base 2 = [] := by
    decide +kernel
  rw [hempty] at hm
  exact List.not_mem_nil hm

end AvailableChain.FGSA.Run.Tests.FinalityEpochs

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.fgp_own_valid
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.fresh_head_erased
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.full_vote_service_fails

namespace AvailableChain.FGSA.Run.Tests.FinalityEpochs

abbrev q : Params := { p with δt := 4 }
def shortEnv : Generic.Env (Fin 1) :=
  ⟨2, by decide, 7, by decide, fun _ t => decide (t < 3 ∨ 7 ≤ t)⟩
def shortRun : V2.D.Run (Fin 1) (fgsa q unitCodec) where
  honest := {0}
  horizon := 8
  events := [.tick 0 0, .tick 0 2, .restart 0 7, .tick 0 8]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

theorem short_valid : V2.D.ExecutionValid shortEnv shortRun := by
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_, toSleepWellFormed := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp [shortRun] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    · intro e he
      simp [shortRun] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    · intro v t ht
      fin_cases v
      simp [shortRun] at ht
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
    · intro v hv t ⟨k, hk⟩ ht hh ha
      fin_cases v
      change t ≤ 8 at hh
      simp [shortEnv] at hk ha
      simp [shortRun]; dsimp [Time] at *; omega
  · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t he <;>
      have hm := List.mem_of_getElem? he <;> simp [shortRun] at hm
  · refine ⟨?_, ?_⟩
    · intro v o t ⟨i, hi⟩ u hu hh
      have hm := List.mem_of_getElem? hi
      simp [shortRun] at hm
    · intro v o t ⟨i, hi⟩ o' hc u hu hh
      have hm := List.mem_of_getElem? hi
      simp [shortRun] at hm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v t ht
      simp [shortRun] at ht
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · intro v o t ht
      simp [shortRun] at ht
    · intro v t ht
      simp [shortRun] at ht
      rcases ht with ⟨rfl, rfl⟩; decide
    · intro v hv t ht hh hw
      fin_cases v
      have he : t = 7 := by simp [V2.D.Wakes, shortEnv] at hw; dsimp [Time] at *; omega
      subst t
      simp [shortRun]

theorem short_named_bodies (i : Nat) (x : Fin 1) :
    (V2.D.Run.stateBefore shortEnv shortRun i x).st.namedBodies = [.genesis] := by
  fin_cases x
  by_cases hi : i < 4
  · interval_cases i <;> decide +kernel
  · have htake : shortRun.events.take i = shortRun.events :=
      List.take_of_length_le (by change 4 ≤ i; omega)
    change ((shortRun.events.take i).foldl (V2.D.World.step shortEnv shortRun)
      V2.D.World.init 0).st.namedBodies = [.genesis]
    rw [htake]
    decide +kernel

theorem short_no_proposal (i : Nat) (o : Obj q) (N : NamedProposal q.n)
    (ho : o ∈ V2.D.Run.emitsAt shortEnv shortRun i) (hp : o.payload = .proposal N) : False := by
  by_cases hi : i < 4
  · interval_cases i
    · change o ∈ [] at ho; exact List.not_mem_nil ho
    · change o ∈ [⟨.seat (.base (.head 0)) ⟨0, by decide⟩, .head ⟨0⟩⟩] at ho
      have he := List.mem_singleton.mp ho
      subst o
      cases hp
    · change o ∈ [] at ho; exact List.not_mem_nil ho
    · change o ∈ [] at ho; exact List.not_mem_nil ho
  · have hn : shortRun.events[i]? = none := List.getElem?_eq_none (by change 4 ≤ i; omega)
    rw [V2.D.Run.emitsAt, hn] at ho
    exact List.not_mem_nil ho

theorem short_scope_genesis (A : NamedProposal q.n)
    (h : NamedProposalReceiptScope q unitCodec shortEnv shortRun A) : A = .genesis := by
  rcases h with ⟨B, (hd | ⟨x, hx, i, hi⟩), hAB⟩ | ⟨v, hv, o, t, N, ⟨i, he, ho⟩, hp, hAN⟩
  · obtain ⟨x, o, t, he, hp⟩ := hd
    simp [shortRun] at he
  · rw [short_named_bodies i x] at hi
    have hB := List.mem_singleton.mp hi
    subst B
    simpa [NamedProposal.Preceq, NamedProposal.preceq] using hAB
  · exact (short_no_proposal i o N ho hp).elim

theorem short_base : Base₂ q unitCodec shortEnv shortRun := by
  have hL : V2.D.Linked (fun _ => True) shortRun := by
    refine ⟨1, Equiv.refl (Fin 1), ?_⟩
    intro l hl
    have hs : (fgsa q unitCodec).seats l = 1 := by cases l <;> rfl
    refine ⟨hs, ?_⟩
    intro i
    apply Fin.ext
    change 0 = i.val
    have hi := i.isLt
    have hi1 : i.val < 1 := hs ▸ hi
    omega
  refine ⟨short_valid, ?_, ?_, ?_, rfl, ?_⟩
  · obtain ⟨n, e, h⟩ := hL
    exact ⟨n, e, fun l _ => h l trivial⟩
  · intro l hl
    exact hL.toCStar l trivial
  · intro v t ht
    simp [shortRun] at ht
    rcases ht with ⟨rfl, rfl⟩
    change 0 < (7 : Time) ∧ shortEnv.awake 0 7 = true ∧
      shortEnv.awake 0 6 = false
    decide
  · intro A B hA hB he
    exact (short_scope_genesis A hA).trans (short_scope_genesis B hB).symm

theorem short_sync : Gen.V2.Duty.LabelSyncOn shortEnv shortRun
    (fun o => ¬ isRowObject o) (SA.voteTime q.toParams 0) (SA.proposalTime q.toParams 1) := by
  let dl : Time → Time := fun a => max a 2 + 2
  have hNoLink (src dst : Fin 1) (a : Time) (hd : dl a ≤ 8)
      (hlink : V2.D.LinkReadyOn shortEnv shortRun src dst a (dl a)) : False := by
    have hb : max a 3 < dl a := by dsimp [dl, Time] at *; omega
    have hu := hlink (max a 3) (le_max_left _ _) hb
    have hf : shortEnv.awake dst (max a 3) = false := by
      simp [shortEnv]; dsimp [dl, Time] at *; omega
    rw [hf] at hu
    cases hu
  refine ⟨dl, 8, ⟨?_, ?_⟩, ?_, ?_, (fun _ => le_rfl), by decide, le_rfl, le_rfl⟩
  · intro v hv o hQ t hem w hw a hta ha hlt hc hh hlink hNX
    exact (hNoLink v w a hc hlink).elim
  · intro v hv i o hQ t hem w hw a hta ha hlt hc hh hlink hNX
    exact (hNoLink v w a hc hlink).elim
  · intro a b hab
    have hmax : max a 2 ≤ max b 2 := max_le_max hab le_rfl
    change max a 2 + 2 ≤ max b 2 + 2
    dsimp [Time] at *
    omega
  · intro a
    exact (le_max_left a 2).trans_lt (lt_add_of_pos_right _ (by decide))

/-- Legacy unscoped TVote, retained only for the pre-cutoff regression. -/
def LegacyTVote : Prop :=
  (∀ v st, Gen.V2.Duty.HonestSlot shortRun (fgsaInterface q unitCodec) v →
    Gen.V2.Duty.LabelSyncOn shortEnv shortRun (fun o => ¬ isRowObject o)
      (SA.voteTime q.toParams (v - 1))
      (SA.proposalTime q.toParams v) →
    proposalStateAt q unitCodec shortEnv shortRun v = some st →
    FullVoteService q unitCodec shortEnv shortRun st (v - 1)) ∧
  (∀ r x nd, x ∈ shortRun.honest →
    Gen.V2.Duty.LabelSyncOn shortEnv shortRun
      (fun o => ¬ isRowObject o) (SA.voteTime q.toParams (r * q.R + 1)) (q.actionTime r) →
    postClock shortEnv shortRun x (q.actionTime r) = some nd →
    FullVoteService q unitCodec shortEnv shortRun nd.st (r * q.R + 1)) ∧
  (∀ y s (a : HeadWire q.n), y ∈ shortRun.honest →
    V2.D.Run.emits shortEnv shortRun y (ofHead q a) (SA.voteTime q.toParams s) →
    ∃ nd H, postClock shortEnv shortRun y (SA.voteTime q.toParams s) = some nd ∧
      H ∈ nd.st.base.blocks ∧ H.root = a.payload)

/-- Base₂ and label synchrony do not supply an unjoined proposer's current vote pool. -/
theorem base_not_tVote : Base₂ q unitCodec shortEnv shortRun ∧
    ¬ LegacyTVote := by
  refine ⟨short_base, ?_⟩
  intro h
  let st := ((fgsa q unitCodec).clock (V2.D.Run.stateBefore shortEnv shortRun 3 0) 8).st
  have hprop : proposalStateAt q unitCodec shortEnv shortRun 1 = some st := by rfl
  have hslot : Gen.V2.Duty.HonestSlot shortRun (fgsaInterface q unitCodec) 1 := by
    change 0 < 1 ∧ (0 : Fin 1) ∈ ({0} : Finset (Fin 1))
    decide
  have hfull := h.1 1 st hslot short_sync hprop
  have hem : ofHead q ⟨.seat (.head 0) 0, ⟨0⟩⟩ ∈
      V2.D.Run.emitsAt shortEnv shortRun 1 := by
    change _ ∈ [ofHead q ⟨.seat (.head 0) 0, ⟨0⟩⟩]
    exact List.mem_singleton_self _
  have hv := (hfull 0 ⟨.seat (.head 0) 0, ⟨0⟩⟩ (by decide)
    ⟨1, by decide, hem⟩ (by decide)).1
  have hp : GridCO.votesAt st.base 0 = [] := by decide +kernel
  rw [hp] at hv
  exact List.not_mem_nil hv


theorem short_recovery : Recovery₂ q unitCodec shortEnv shortRun 8 2 := by
  refine {
    sync := ⟨?_, ?_⟩
    deltaF := by decide
    gap := ?_
    base := short_base
    fault := by decide
    awake := ?_
    gapPos := by decide }
  · intro v hv o t he w hw a hta ha hlt hc hh hlink hNX
    have hd : fgsaDelay shortEnv.Δ 2 o = 2 := by
      unfold fgsaDelay
      split <;> rfl
    rw [hd] at hc
    change max a 7 + 2 ≤ 8 at hc
    have hm := le_max_right a (7 : Time)
    dsimp [Time] at *
    omega
  · intro v hv i o t he w hw a hta ha hlt hc hh hlink hNX
    have hd : fgsaDelay shortEnv.Δ 2 o = 2 := by
      unfold fgsaDelay
      split <;> rfl
    rw [hd] at hc
    change max a 7 + 2 ≤ 8 at hc
    have hm := le_max_right a (7 : Time)
    dsimp [Time] at *
    omega
  · intro t ht hh
    change 7 ≤ t at ht
    change t + 8 ≤ 8 at hh
    dsimp [Time] at *
    omega
  · intro v hv t ht hh
    simp [shortEnv, shortEnv]
    right
    exact ht

/-- Recovery supplies the amended receipt record. -/
theorem recovery_vote_receipts : FinalityVoteReceipts shortEnv shortRun :=
  finality_vote_receipts short_recovery

/-- Recovery supplies the amended public TVote. -/
theorem recovery_tVote : TVote q unitCodec shortEnv shortRun :=
  fgsa_tVote shortEnv shortRun short_base recovery_vote_receipts

/-- The same run has the public Recovery sleep guards; its joined suffix is beyond horizon. -/
theorem short_recovery_sleep : RecoverySleep₂ q unitCodec shortEnv shortRun 8 2 := by
  refine { toRecovery₂ := short_recovery, suffixNoRestart := ?_, joinedGap := ?_ }
  · intro v hv i t he ht hh
    have hm := List.mem_of_getElem? he
    simp [shortRun] at hm
    rcases hm with ⟨rfl, rfl⟩
    change 7 < (7 : Time) at ht
    exact (lt_irrefl _ ht).elim
  · intro t ht hh
    change 20 ≤ t at ht
    change t + 8 ≤ 8 at hh
    dsimp [Time] at *
    omega

/-- Sleep Recovery and the amended public service hold in the same short run. -/
theorem recovery_sleep_tVote :
    RecoverySleep₂ q unitCodec shortEnv shortRun 8 2 ∧ TVote q unitCodec shortEnv shortRun :=
  ⟨short_recovery_sleep, recovery_tVote⟩

end AvailableChain.FGSA.Run.Tests.FinalityEpochs

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_valid
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_base
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_sync
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.base_not_tVote

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.head_emitted

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_named_bodies

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_no_proposal

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_scope_genesis

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.recovery_vote_receipts
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_recovery
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.recovery_tVote

#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.short_recovery_sleep
#print axioms AvailableChain.FGSA.Run.Tests.FinalityEpochs.recovery_sleep_tVote
