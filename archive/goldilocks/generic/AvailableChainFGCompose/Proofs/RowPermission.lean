module
public import AvailableChainFGCompose.Statements.RowPermission
public import AvailableChainFGCompose.Proofs.SourceHead -- shake: keep (re-export)
public import AvailableChainKitFG.ClientOnceSafety -- shake: keep (re-export)
public import Mathlib.Tactic.Linarith -- shake: keep (re-export)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- SAME permitted-lock case split for the computed height pair. -/
theorem p0d2_pair_of_lock (Λ : Record) (h : Height) (T : BlockId)
    (fp : Option FinalityPair) (hl : own_lock Λ h fp = none ∨ own_lock Λ h fp = some T) :
    namedEntry (height_pair Λ (some (h, T)) fp) = some (h, T) := by
  change namedEntry (if Λ.timeout h then .vote h T true else
    match own_lock Λ h fp with
    | some locked => if locked = T then .vote h T false else .empty
    | none => match Λ.target h with
      | some recorded => if recorded = T then .vote h T false else .vote h T true
      | none => .vote h T false) = _
  by_cases ht : Λ.timeout h = true
  · rw [ht, ite_eq_left (rfl : true = true)]
    rfl
  · have ht' : Λ.timeout h = false := Bool.eq_false_of_not_eq_true ht
    rw [ht', ite_eq_right Bool.false_ne_true]
    rcases hl with hn | he
    · rw [hn]
      cases Λ.target h with
      | none => rfl
      | some recorded => by_cases he : recorded = T <;>
          simp only [he, ite_true, ite_false] <;> rfl
    · rw [he]
      simp only [ite_true]
      rfl

/-- SAME pair algebra; the concrete protocol supplies the permitted lock. -/
theorem rowPermission_pair {In : Type} {P : V2.ProtocolSpecD In} {n : Nat} {Wire : Type}
    (S : FGSafetyReads P n Wire) (H : FGHeightView (Fin n))
    (nd : P.State) (C : FGBlock (Fin n)) (h : FGRowPermissionInputs S H nd C) :
    namedEntry (height_pair (S.record nd).toRecord
      ((S.inputs nd).1.map (fun C => ((H C).h, (H C).T_h.root)))
      (finality_pair (S.record nd).toRecord (S.inputs nd).2)) =
        some ((H C).h, (H C).T_h.root) := by
  rw [h.source_eq]
  exact p0d2_pair_of_lock _ _ _ _ h.permitted_lock

/-- INTENTIONAL send-once split: a release or an earlier matching named entry. -/
theorem p0d2_once_coverage {n : Nat} (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (Λ : RecordOnce) (seat : Fin n) (source : Option (FGBlock (Fin n))) (hd : HeadFields)
    (h : Height) (T : BlockId)
    (hInv : RecordInv Λ.toRecord)
    (hHist : ∀ g U timeout fp, (.vote g U timeout, fp) ∈ Λ.sent →
      (timeout = false → Λ.target g = some U) ∧ (timeout = true → Λ.timeout g = true))
    (hp : namedEntry (height_pair Λ.toRecord
      (source.map (fun C => ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root)))
      (finality_pair Λ.toRecord hd)) = some (h, T)) :
    (∃ a, (createRowOnce Ef cfg Λ seat source hd).1 = some a ∧
      namedEntry a.height_pair = some (h, T)) ∨
      ∃ b ∈ Λ.sent, namedEntry b.1 = some (h, T) := by
  cases hpair : height_pair Λ.toRecord
      (source.map (fun C => ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root)))
      (finality_pair Λ.toRecord hd) with
  | empty => rw [hpair] at hp; cases hp
  | vote g U timeout =>
    rw [hpair] at hp
    delta namedEntry at hp
    have he := Option.some.inj hp
    have hg : g = h := congrArg Prod.fst he
    have hU : U = T := congrArg Prod.snd he
    subst h
    subst T
    by_cases hs : sameHeightOnce Λ g U timeout = true
    · right
      obtain ⟨⟨pair, fp⟩, hm, hg⟩ := List.any_eq_true.mp hs
      cases pair with
      | empty => cases hg
      | vote k W oldTimeout =>
        change (decide (k = g) && (!timeout || decide (W = U))) = true at hg
        obtain ⟨hk, he⟩ := Bool.and_eq_true_iff.mp hg
        have hk : k = g := of_decide_eq_true hk
        subst k
        have hWU : W = U := by
          cases timeout with
          | true => simpa using he
          | false =>
            have old := hHist g W oldTimeout fp hm
            cases oldTimeout with
            | true =>
              have ht := old.2 rfl
              have fields := KitFG.height_pair_vote_fields hpair
              rw [fields] at hpair
              change (if Λ.timeout g then NamedHeightPair.vote g U true else _) = _ at hpair
              rw [ht] at hpair
              cases hpair
            | false =>
              have ht := old.1 rfl
              rcases KitFG.height_pair_target_compat hInv hpair with hn | he
              · rw [ht] at hn; cases hn
              · exact Option.some.inj (ht.symm.trans he)
        subst W
        exact ⟨(.vote g U oldTimeout, fp), hm, rfl⟩
    · let a : Row (Fin n) := ⟨seat, .vote g U timeout,
        (finality_pair Λ.toRecord hd).filter (fun fp => decide (fp.height < g))⟩
      by_cases hm : a.onceKey ∈ Λ.sent
      · exact Or.inr ⟨a.onceKey, hm, rfl⟩
      · left
        refine ⟨a, ?_, rfl⟩
        rw [createRowOnce_def]
        dsimp only
        rw [hpair]
        simp only [hs, Bool.false_eq_true, ite_false]
        change (if a.onceKey ∈ Λ.sent then (none, Λ) else
          (some a, record_row_once Λ a)).1 = some a
        rw [ite_eq_right hm]

/-- INTENTIONAL durable send-once coverage at the actual enabled action.
The prior-origin leaf preserves the node, full wire, and strict earlier index. -/
theorem rowPermission_covered {In V : Type} {P : V2.ProtocolSpecD In}
    [DecidableEq V] {n : Nat} {Wire : Type}
    (S : FGSafetyReads P n Wire) (H : FGHeightView (Fin n))
    (Ef : Electorate (Fin n)) (cfg : FGConfig) (T : FGTiming) (hT : FGTimingLaws T)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (J : FGSafetyClientLaws S Ef cfg) (entry : Wire → Option (Height × BlockId))
    (W : FGRowPermissionWireLaws S entry)
    (e : Fin n ≃ V) (he : ∀ k, rho.seatOf S.fgLabel (S.fgSeats k) = e k)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hheight : ∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
      ((H C).h, (H C).T_h.root))
    (x : V) (hx : x ∈ rho.honest) (r i : Nat) (nd : P.State)
    (htick : rho.events[i]? = some (.tick x (T.action r)))
    (hnd : P.clock (V2.D.Run.stateBefore E rho i x) (T.action r) = nd)
    (C : FGBlock (Fin n)) (hperm : FGRowPermissionInputs S H nd C)
    (hhist : FGRowRecordHistory (S.record nd))
    (horigin : ∀ b ∈ (S.record (V2.D.Run.stateBefore E rho i x)).sent,
      ∃ j rSent a, j < i ∧ HonestRowAt S E rho T j x rSent a ∧
        entry a = namedEntry b.1)
    (hawake : E.awake x (T.action r) = true) (henabled : S.enabled (T.action r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      entry a = some ((H C).h, (H C).T_h.root) := by
  have hrec : S.record nd = S.record (V2.D.Run.stateBefore E rho i x) := by
    rw [← hnd, J.clock_record]
  have hp := rowPermission_pair S H nd C hperm
  have hsrc : (S.inputs nd).1.map
      (fun C => ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root)) =
      (S.inputs nd).1.map (fun C => ((H C).h, (H C).T_h.root)) := by
    congr 1
    funext C
    exact hheight C
  rw [← hsrc] at hp
  rcases p0d2_once_coverage Ef cfg (S.record nd) (e.symm x)
      (S.inputs nd).1 (S.inputs nd).2 _ _ hhist.invariant hhist.sent_history hp with
      ⟨u, hu, hn⟩ | ⟨b, hb, hn⟩
  · have hrows := J.tick_rows E rho e he (V2.D.Run.stateBefore E rho i x) x (T.action r)
    rw [hnd, ← hrec] at hrows
    rw [ite_eq_left ⟨hawake, henabled⟩, hu] at hrows
    have hm : u ∈ ((V2.D.tick E rho (V2.D.Run.stateBefore E rho i x) x
        (T.action r)).2.filter P.objSelfVisible).filterMap S.decodeObject := by
      rw [hrows]
      exact List.mem_singleton_self _
    obtain ⟨o, ho, hd⟩ := List.mem_filterMap.mp hm
    obtain ⟨a, ha, _, hentry⟩ := W.decoded_wire o u hd
    refine ⟨i, r, a, le_rfl, ⟨hx, htick, ?_⟩, hentry.trans hn⟩
    rw [ha, (V2.D.Run.step_tick_eq E rho htick).2]
    exact (List.mem_filter.mp ho).1
  · rw [hrec] at hb
    obtain ⟨j, rSent, a, hji, hj, ha⟩ := horigin b hb
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj.2.1
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp htick
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have htime := V2.D.Engine.time_le_of_key_le _ _ hk
    change T.action rSent ≤ T.action r at htime
    have hr : rSent ≤ r := by
      by_contra h
      have hcast : ((r * T.roundSlots : Nat) : Time) <
          ((rSent * T.roundSlots : Nat) : Time) := by
        exact_mod_cast (Nat.mul_lt_mul_of_pos_right (show r < rSent by omega)
          (show 0 < T.roundSlots by have := hT.rounds; omega))
      rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq,
        hT.proposal_eq, hT.proposal_eq] at htime
      have := hT.delta_pos
      nlinarith
    exact ⟨j, rSent, a, hr, hj, ha.trans hn⟩

end AvailableChain.FGCompose
end
