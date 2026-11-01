module
public import AvailableChainFGSARun.Statements.Emission
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainFGSA.Proofs.RowSelection

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

-- ROOT-DIGEST-2: private unfolding facts and matcher copies (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def hygiene_wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ body) => body.valid
  | some (.block s N) =>
      let b := N.erase
      let raw := N.raw
      let support := N.support
      let rows := N.rows
      b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
        raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == b.slot
          | none => false) &&
        support.all (fun v => decide (v ∈ raw)) &&
        rows.all RowWire.valid &&
        contentOk p b raw support rows
  | none => false

private theorem hygiene_wellFormed_eq : @wellFormed = @hygiene_wellFormed := rfl

private theorem hygiene_raw_eq {n : Nat} (N : NamedProposal n) :
    N.raw = (match N with
      | .genesis => []
      | .node _ _ _ _ xs _ _ => xs : List (HeadWire n)) := rfl

private theorem hygiene_support_eq {n : Nat} (N : NamedProposal n) :
    N.support = (match N with
      | .genesis => []
      | .node _ _ _ _ _ xs _ => xs : List (HeadWire n)) := rfl

private theorem hygiene_rows_eq {n : Nat} (N : NamedProposal n) :
    N.rows = (match N with
      | .genesis => []
      | .node _ _ _ _ _ _ xs => xs : List (RowWire n)) := rfl

private def hygiene_root {n : Nat} : NamedProposal n → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

private theorem hygiene_root_match_eq :
    hygieneEq% (@NamedProposal.root) (@hygiene_root) := rfl

end AvailableChain.FGSA

attribute [local simp↓] AvailableChain.FGSA.hygiene_root_match_eq

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The application codec recovers the input of each emitted proposal. -/
theorem decode_honest (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    HonestProposalDecodes p c E rho := by
  intro i v s hi _ _ _ N hm
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hm
  have ha := (fgsa_emits_proposal E rho _ v _ s _).mp hm
  obtain ⟨H, raw', sup', rows', he, -, happ⟩ := rowsOk_withApp _ _ _ ha.2.2.2.2
  cases he
  exact (congrArg c.unapp happ).trans (c.unapp_app _)

private theorem emission_rows_clock (st : State p.n) (t : Time)
    (h : EmissionRowsValid st) : EmissionRowsValid (FGSA.clock p st t) := by
  constructor
  · rw [clock_rowPool]; exact h.1
  · rw [clock_proposals]; exact h.2

private theorem emission_rows_admit (st : State p.n) (a : RowWire p.n)
    (h : EmissionRowsValid st) (ha : a.valid = true) :
    EmissionRowsValid (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

private theorem emission_rows_fold (rows : List (RowWire p.n)) (st : State p.n)
    (h : EmissionRowsValid st) (hr : ∀ a ∈ rows, a.valid = true) :
    EmissionRowsValid (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (emission_rows_admit st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

private theorem emission_rows_process (st : State p.n) (o : Obj p)
    (h : EmissionRowsValid st) (hw : (fgsa p c).wellFormed o = true) :
    EmissionRowsValid (FGSA.process p st (toWire p o)) := by
  change FGSA.wellFormed p (toWire p o) = true at hw
  unfold FGSA.process
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row i body =>
      have he := decode_eq_row.mp hd
      rw [he] at hw ⊢
      exact emission_rows_admit _ _ h hw
    | block s N =>
      have hr : ∀ a ∈ N.rows, a.valid = true := by
        unfold FGSA.wellFormed at hw
        rw [hd] at hw
        intro a ha
        exact List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 a ha
      change EmissionRowsValid (admitBlock p st s N)
      unfold admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply emission_rows_fold _ _ _ hr
            have hs : EmissionRowsValid
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } := by
              refine ⟨h.1, ?_⟩
              intro w hw s' M hd'
              rcases List.mem_append.mp hw with hm | hm
              · exact h.2 w hm s' M hd'
              · have hew := List.mem_singleton.mp hm
                subst w
                change some (Input.block s N) = some (Input.block s' M) at hd'
                cases hd'
                exact hr
            split
            · exact hs
            · constructor
              · rw [(reconcile_frame _).2.2.1]; exact hs.1
              · rw [(reconcile_frame _).2.1]; exact hs.2
          · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Delivery wire checks keep all pool and stored-proposal rows valid.
Restarts keep both lists. No schedule or restart premise is needed. -/
theorem fgsa_emissionRowsValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hd : V2.D.DeliveryWellFormed E rho) (i : Nat) (v : V) :
    EmissionRowsValid (V2.D.Run.stateBefore E rho i v).st := by
  have hinit : ∀ v, EmissionRowsValid (V2.D.Run.stateBefore E rho 0 v).st := by
    intro v
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  apply Gen.V2.Duty.interval_induction_all E rho (fun _ nd => EmissionRowsValid nd.st)
    hinit (j := i) ?_ i (Nat.zero_le i) le_rfl v
  intro v k e _ _ he hv h
  cases e with
  | restart u t =>
    change u = v at hv; subst u
    simp only [V2.D.World.step, Function.update_self]
    change EmissionRowsValid (acRestart p (V2.D.Run.stateBefore E rho k v).st t)
    constructor
    · rw [acRestart_rowPool]; exact h.1
    · rw [acRestart_proposals]; exact h.2
  | tick u t =>
    change u = v at hv; subst u
    simp only [V2.D.World.step, Function.update_self]
    exact (tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k v) v t).symm ▸
      emission_rows_clock _ _ h
  | deliver u o t =>
    change u = v at hv; subst u
    simp only [V2.D.World.step, Function.update_self]
    exact emission_rows_process _ o h (hd.wire k v o t he)

private theorem emission_attest_valid (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (body : RowPayload) (hbody : (attest p st Λ j).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh := congrArg Prod.fst hc
  change (derive p.E p.cfg C).h = h at heh
  have hpos : 1 ≤ h := heh ▸ KitFG.one_le_h p.E p.cfg C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < h))
      |>.map (fun fp => decide (fp.height < h))).getD true) = true
  cases hfp : finality_pair Λ.toRecord (fgInputs p st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

private theorem emission_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, N, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s N hd a hm

private theorem emission_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The parent chosen at a proposal tick is stored and has a smaller slot. -/
theorem fgsa_propose_parent_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s))) (hs0 : 0 < s) :
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i v).st (SA.proposalTime p.toParams s)
    (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s := by
  exact (fgsa_stored_block_slots E rho hs hi hs0).2.1 _
    (getHead_stored p _ (storeBundle_postClock E rho i v _).cstore _ _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Emission checks the exact digest and the BODY encoding. -/
private theorem emission_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  rw [hygiene_wellFormed_eq]
  dsimp only [hygiene_wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, hygiene_raw_eq, hygiene_support_eq, hygiene_rows_eq]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := emission_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (emission_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[R6/R7] A proposal carries only rows valid for its exact held parent. -/
theorem propose_rowsValid (st : State p.n) (hInv : CStoreInv p st) (s : Slot) (app : Nat)
    (hs : st.slot p = s) (N : NamedProposal p.n)
    (hm : (propose p st s).map (withApp p app) = some (.proposal N)) :
    ∃ P, fgBlockOf st N.erase.parent = some P ∧
      rowsValidForParent p P N.erase.slot N.rows = true := by
  unfold propose at hm
  split at hm
  · simp at hm
  · simp only [Option.map_map] at hm
    obtain ⟨M, hM, he⟩ := Option.map_eq_some_iff.mp hm
    have heN := Msg.proposal.inj he
    change namedProposal p M s app _ _ _ = N at heN
    subst N
    let H := getHead p st (proposerVotes st s) (proposerSupport st s)
    have heM : M.erase = H := (namedByErase?_sound st H M hM).2
    rw [namedProposal_erase]
    obtain ⟨P, hP, he⟩ := (hInv.baseTree H).mp (getHead_stored p st hInv _ _)
    have hlookup := (fgBlockOf_spec p st hInv H P).mpr ⟨hP, he⟩
    refine ⟨P, ?_, ?_⟩
    · simpa only [proposalBlock, Block.parent, heM] using hlookup
    · change rowsValidForParent p P s (proposalRows p st H) = true
      rw [proposalRows_eq_proposalRowsFor, ← hs]
      exact proposalRowsFor_valid p st (st.slot p) H P hlookup

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every honest awake emission passes the wire check. -/
theorem honest_emit_wellFormed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hd : V2.D.DeliveryWellFormed E rho) (hs : V2.D.ScheduleWellFormed E rho) :
    HonestEmissionWellFormed p c E rho := by
  intro i v t hi _ hawake o ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at ho
  obtain ⟨auth, m⟩ := o
  cases auth with
  | none =>
    have hu : ∀ m, (⟨.none, m⟩ : Obj p) ∉
        (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).2 := by
      intro m hm
      change (⟨.none, m⟩ : Obj p) ∈ (if E.awake v t then
        (duties p t).flatMap (fun l => (rho.ownSeats (RunDuty.signLabel l) v).filterMap (fun j =>
          ((fgsa p c).act ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v) t) l
            (rho.input v t)).map
              (fun m => ⟨.seat (RunDuty.signLabel l) j, m⟩))) ++ [] else []) at hm
      rw [ite_eq_left hawake, List.append_nil] at hm
      obtain ⟨l, _, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨j, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    exact (hu m ho).elim
  | seat l j =>
    obtain ⟨_, _, d, hl, ht, ha⟩ := (mem_tick_seat_iff E rho _ v t l j m).mp ho
    change RunDuty.signLabel d = l at hl
    cases d with
    | headAction s =>
      change RunLabel.base (.head s) = l at hl
      subst l
      change (if joinedNow p _ then (some (Msg.head _) : Option (Msg p.n)) else none) =
        some m at ha
      split at ha <;> try contradiction
      have he : .head (headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t) s).root =
          m :=
        Option.some.inj ha
      subst m
      rfl
    | fgAction r =>
      change RunLabel.base .fg = l at hl
      subst l
      change (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t)
        (V2.D.Run.stateBefore E rho i v).record ⟨0, p.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact emission_attest_valid _ _ _ _ hb
    | propAction s =>
      change RunLabel.prop s = l at hl
      subst l
      change SA.proposalTime p.toParams s = t at ht
      subst t
      change (if joinedNow p _ then (propose p _ s).map (withApp p _) else none) =
        some m at ha
      split at ha <;> try contradiction
      have hm : (propose p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st
          (SA.proposalTime p.toParams s)) s).map
          (withApp p (c.app (rho.input v (SA.proposalTime p.toParams s)))) = some m := ha
      have hs0 : 0 < s := by
        by_contra hn
        have he : s = 0 := Nat.eq_zero_of_not_pos hn
        subst s
        change none = some m at hm
        cases hm
      exact emission_proposal_wf _ s _
        (emission_rows_clock _ _ (fgsa_emissionRowsValid E rho hd i v))
        (fgsa_propose_parent_lt E rho hs hi hs0) hm

end AvailableChain.FGSA.Run
end
