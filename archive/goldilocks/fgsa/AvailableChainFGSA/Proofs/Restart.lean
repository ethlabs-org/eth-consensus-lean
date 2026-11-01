module
public import AvailableChainFGSA.Proofs.StoreBundle -- shake: keep (re-export)

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

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

private def hygiene_decode {n : Nat} (o : Wire n) : Option (Input n) :=
  match o.auth, o.payload with
  | .seat (.head s) i, .head b => some (.vote s i b)
  | .seat .fg i, .row body => some (.row i body)
  | .proposer s, .proposal N => some (.block s N)
  | _, _ => none

private def hygiene_block {n : Nat} (o : Wire n) : Option Block :=
  match o.decode with
  | some (.block _ N) => some N.erase
  | _ => none

private def hygiene_restartSources (p : Params) (st : State p.n) :
    List (NamedProposal p.n) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) =>
        if N.erase != .genesis && decide (∃ B ∈ Next.tree p st, eraseFG B = N.erase) then
          some N else none
    | _ => none)

private theorem hygiene_decode_match_eq :
    hygieneEq% (@Wire.decode) (@hygiene_decode) := rfl
private theorem hygiene_block_match_eq :
    hygieneEq% (@Wire.block?) (@hygiene_block) := rfl
private theorem hygiene_sources_match_eq :
    hygieneEq% (@restartSources) (@hygiene_restartSources) := rfl

end AvailableChain.FGSA

attribute [local simp↓]
  AvailableChain.FGSA.hygiene_decode_match_eq
  AvailableChain.FGSA.hygiene_block_match_eq
  AvailableChain.FGSA.hygiene_sources_match_eq

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

variable {n : Nat}

/-- [Sleep v6; plan §14.3] Nesting makes normalization leave the state unchanged. -/
theorem normalizeS_eq_of_nestOK {n : Nat} (st : State n) (h : NestOK st) :
    normalizeS st = st := by
  exact ite_eq_left h

/-- [Sleep v6; plan §14.3] The `now` field after wipe. -/
theorem wipe_now (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).base.now = w := rfl

/-- [Sleep v6; plan §14.3] The `restartTime` field after wipe. -/
theorem wipe_restartTime (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).restartTime = some w := rfl

/-- [Sleep v6; plan §14.3] The `fg` field after wipe. -/
theorem wipe_fg (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).fg = st.fg := rfl

/-- [Sleep v6; plan §14.3] The `proposals` field after wipe. -/
theorem wipe_proposals (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).proposals = st.proposals := rfl

/-- [Sleep v6; plan §14.3] The `rowPool` field after wipe. -/
theorem wipe_rowPool (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).rowPool = st.rowPool := rfl

/-- [Sleep v6; plan §14.3] The `blocks` field after wipe. -/
theorem wipe_blocks (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).base.blocks = st.base.blocks := rfl

/-- [Sleep v6; plan §14.3] The `obligations` field after wipe. -/
theorem wipe_obligations (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).base.obligations = st.base.obligations := rfl

/-- [Sleep v6; plan §14.3] The `stableRecord` field after wipe. -/
theorem wipe_stableRecord (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).base.stableRecord = st.base.stableRecord := rfl

/-- [Sleep v6; plan §14.3] The `fastWrite` field after wipe. -/
theorem wipe_fastWrite (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).fastWrite = [] := rfl

/-- [Sleep v6; plan §14.3] Genesis keeps stamp zero; every other block gets w. -/
theorem wipe_blockStamp (p : Params) (st : State p.n) (w : Time) :
    (wipe p st w).base.blockStamp =
      st.base.blocks.map (fun b => (b, if b = .genesis then 0 else w)) := rfl

private def replayHead {n : Nat} (h : HeadWire n) : Wire n := ⟨h.auth, .head h.payload⟩

/-- [Sleep v6; plan §14.3] The replay list is exactly the selected raw HEAD lists. -/
theorem restartVotes_eq (p : Params) (st : State p.n) :
    restartVotes p st = (restartSources p st).flatMap
      (fun N => N.raw.map (fun h => (⟨h.auth, .head h.payload⟩ : Wire p.n))) := by
  rw [restartSources, List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
  unfold restartVotes
  apply List.flatMap_congr
  intro o _
  cases hd : o.decode with
  | none => rfl
  | some input =>
    cases input <;> dsimp only
    · rfl
    · rfl
    · split <;> simp only [Option.toList_some, Option.toList_none, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]


private theorem replayHeads (p : Params) (st : State p.n) :
    ∀ o ∈ restartVotes p st, ∃ h : HeadWire p.n, o = replayHead h := by
  rw [restartVotes_eq]
  intro o ho
  obtain ⟨N, _, ho⟩ := List.mem_flatMap.mp ho
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp ho
  exact ⟨h, rfl⟩

private def ReplayFields (a b : State n) : Prop :=
  b.base.now = a.base.now ∧ b.restartTime = a.restartTime ∧ b.fg = a.fg ∧
  b.proposals = a.proposals ∧ b.rowPool = a.rowPool ∧ b.base.blocks = a.base.blocks ∧
  b.base.obligations = a.base.obligations ∧ b.base.stableRecord = a.base.stableRecord ∧
  b.base.blockStamp = a.base.blockStamp ∧ b.fastWrite = a.fastWrite ∧
  b.base.genuine = a.base.genuine

private theorem process_replay_fields (p : Params) (st : State p.n) (h : HeadWire p.n) :
    ReplayFields st (process p st (replayHead h)) := by
  unfold process replayHead Wire.decode
  cases h with
  | mk auth payload =>
    cases auth with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | proposer s => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | seat label i =>
      cases label with
      | fg => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | head s =>
        dsimp only
        dsimp only [ReplayFields, admitHead]
        simp only [GridCO.admitVote]
        split_ifs <;> simp only [and_self]

private theorem replay_fields_fold (p : Params) (xs : List (Wire p.n))
    (heads : ∀ o ∈ xs, ∃ h : HeadWire p.n, o = replayHead h) (st : State p.n) :
    ReplayFields st (xs.foldl (process p) st) := by
  induction xs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons o xs ih =>
      obtain ⟨h, rfl⟩ := heads o List.mem_cons_self
      have a := process_replay_fields p st h
      have b := ih (fun o ho => heads o (List.mem_cons_of_mem _ ho))
        (process p st (replayHead h))
      rcases a with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
      rcases b with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
      exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5,
        b6.trans a6, b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10,
        b11.trans a11⟩

private theorem acRestart_fields (p : Params) (st : State p.n) (w : Time) :
    ReplayFields (wipe p st w) (acRestart p st w) :=
  replay_fields_fold p _ (replayHeads p st) _

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `now`. -/
theorem acRestart_now (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.now = w :=
  (acRestart_fields p st w).1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `restartTime`. -/
theorem acRestart_restartTime (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).restartTime = some w :=
  (acRestart_fields p st w).2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `fg`. -/
theorem acRestart_fg (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).fg = st.fg :=
  (acRestart_fields p st w).2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `proposals`. -/
theorem acRestart_proposals (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).proposals = st.proposals :=
  (acRestart_fields p st w).2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `rowPool`. -/
theorem acRestart_rowPool (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).rowPool = st.rowPool :=
  (acRestart_fields p st w).2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `blocks`. -/
theorem acRestart_blocks (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.blocks = st.base.blocks :=
  (acRestart_fields p st w).2.2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `obligations`. -/
theorem acRestart_obligations (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.obligations = st.base.obligations :=
  (acRestart_fields p st w).2.2.2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `stableRecord`. -/
theorem acRestart_stableRecord (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.stableRecord = st.base.stableRecord :=
  (acRestart_fields p st w).2.2.2.2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `blockStamp`. -/
theorem acRestart_blockStamp (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.blockStamp =
      st.base.blocks.map (fun b => (b, if b = .genesis then 0 else w)) :=
  (acRestart_fields p st w).2.2.2.2.2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `fastWrite`. -/
theorem acRestart_fastWrite (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).fastWrite = [] :=
  (acRestart_fields p st w).2.2.2.2.2.2.2.2.2.1

/-- [Sleep v6; plan §14.3] HEAD-only replay keeps `genuine`. -/
theorem acRestart_genuine (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.genuine = [] :=
  (acRestart_fields p st w).2.2.2.2.2.2.2.2.2.2

private theorem eraseDups_eq_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (h : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : xs.filter (fun b => !b == a) = xs := by
      apply List.filter_eq_self.mpr
      intro b hb
      have he : (b == a) = false := beq_false_of_ne (fun he => ha (he ▸ hb))
      simp only [he, Bool.not_false]
    rw [hf, ih hn]

private def ReplayPool (w : Time) (v : GridCO.State n .root) : Prop :=
  v.now = w ∧ v.voteStamp.map Prod.fst = v.votes ∧ v.votes.Nodup ∧
  (∀ row ∈ v.voteStamp, row.2 = w) ∧
  ∀ s i, (GridCO.seatVotes (GridCO.votesAt v s) i).length ≤ 2

private theorem replayPool_admitVote (p : GridCO.Params) (v : GridCO.State n .root)
    (w : Time) (o : GridCO.Wire n .root) (h : ReplayPool w v) :
    ReplayPool w (GridCO.admitVote p v o) := by
  rcases h with ⟨hw, hk, hn, hs, hc⟩
  unfold GridCO.admitVote
  cases o with
  | mk auth payload =>
    cases auth with
    | none => exact ⟨hw, hk, hn, hs, hc⟩
    | proposer r => exact ⟨hw, hk, hn, hs, hc⟩
    | seat r i =>
      cases payload with
      | proposal b raw support => exact ⟨hw, hk, hn, hs, hc⟩
      | head b =>
        dsimp only
        split
        · exact ⟨hw, hk, hn, hs, hc⟩
        · next ha =>
          have hnot : (⟨.seat r i, .head b⟩ : GridCO.Wire n .root) ∉ v.votes := by
            intro hm
            exact ha (by simp [hm])
          have he : GridCO.equivocates (GridCO.votesAt v r) i = false := by
            cases he : GridCO.equivocates (GridCO.votesAt v r) i with
            | false => rfl
            | true => exact False.elim (ha (by simp [he]))
          have hfilter : (GridCO.seatVotes (GridCO.votesAt v r) i).Nodup :=
            (hn.filter (fun o => GridCO.headLabel? o == some r)).filter
            (fun o => GridCO.headSeat? o == some i)
          have hsmall : (GridCO.seatVotes (GridCO.votesAt v r) i).length < 2 := by
            have he' : ¬ 2 ≤ (GridCO.seatVotes (GridCO.votesAt v r) i).eraseDups.length :=
              of_decide_eq_false he
            rw [eraseDups_eq_of_nodup _ hfilter] at he'
            exact Nat.lt_of_not_ge he'
          refine ⟨hw, ?_, ?_, ?_, ?_⟩
          · simp only [List.map_append, List.map_cons, List.map_nil, hk]
          · apply List.nodup_append.mpr
            refine ⟨hn, List.nodup_singleton _, ?_⟩
            intro a hm c hm' hac
            have heq := List.mem_singleton.mp hm'
            exact hnot ((hac.trans heq) ▸ hm)
          · intro row hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hs row hm
            · have heq := List.mem_singleton.mp hm
              subst row
              exact hw
          · intro s j
            have hl : GridCO.headLabel?
                (⟨.seat r i, .head b⟩ : GridCO.Wire n .root) = some r := rfl
            have hseat : GridCO.headSeat?
                (⟨.seat r i, .head b⟩ : GridCO.Wire n .root) = some i := rfl
            change ((v.votes ++ [(⟨.seat r i, .head b⟩ : GridCO.Wire n .root)]).filter
              (fun o => GridCO.headLabel? o == some s) |>.filter
              (fun o => GridCO.headSeat? o == some j)).length ≤ 2
            by_cases hr : r = s <;> by_cases hi : i = j
            · subst s; subst j
              have heq : ((v.votes ++ [(⟨.seat r i, .head b⟩ : GridCO.Wire n .root)]).filter
                  (fun o => GridCO.headLabel? o == some r) |>.filter
                  (fun o => GridCO.headSeat? o == some i)).length =
                  (GridCO.seatVotes (GridCO.votesAt v r) i).length + 1 := by
                dsimp only [GridCO.seatVotes, GridCO.votesAt]
                simp [List.filter_append, hl, hseat]
              rw [heq]
              omega
            · dsimp only [GridCO.seatVotes, GridCO.votesAt] at hc ⊢
              simpa [List.filter_append, hl, hseat, hi] using hc s j
            · dsimp only [GridCO.seatVotes, GridCO.votesAt] at hc ⊢
              simpa [List.filter_append, hl, hr] using hc s j
            · dsimp only [GridCO.seatVotes, GridCO.votesAt] at hc ⊢
              simpa [List.filter_append, hl, hr] using hc s j

private theorem replayPool_process (p : Params) (st : State p.n) (w : Time)
    (h : ReplayPool w st.base) (o : HeadWire p.n) :
    ReplayPool w (process p st (replayHead o)).base := by
  unfold process replayHead Wire.decode
  cases o with
  | mk auth payload =>
    cases auth with
    | none => exact h
    | proposer s => exact h
    | seat label i =>
      cases label with
      | fg => exact h
      | head s => exact replayPool_admitVote p.toParams.engine st.base w _ h

private theorem acRestart_pool (p : Params) (st : State p.n) (w : Time) :
    ReplayPool w (acRestart p st w).base := by
  have fold : ∀ (xs : List (Wire p.n)),
      (∀ o ∈ xs, ∃ h : HeadWire p.n, o = replayHead h) →
      ∀ acc, ReplayPool w acc.base → ReplayPool w (xs.foldl (process p) acc).base := by
    intro xs
    induction xs with
    | nil => exact fun _ _ h => h
    | cons o xs ih =>
      intro heads acc h
      obtain ⟨head, rfl⟩ := heads o List.mem_cons_self
      exact ih (fun o ho => heads o (List.mem_cons_of_mem _ ho)) _
        (replayPool_process p acc w h head)
  apply fold _ (replayHeads p st)
  refine ⟨rfl, rfl, List.nodup_nil, ?_, ?_⟩
  · simp [wipe, GridCO.initial]
  · simp [GridCO.seatVotes, GridCO.votesAt, wipe, GridCO.initial]

/-- [Sleep v6; plan §14.3] Accepted stamp keys are exactly the accepted votes. -/
theorem acRestart_voteStamp_keys (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.voteStamp.map Prod.fst = (acRestart p st w).base.votes :=
  (acRestart_pool p st w).2.1

/-- [Sleep v6; plan §14.3] The replay handler stores no duplicate vote. -/
theorem acRestart_votes_nodup (p : Params) (st : State p.n) (w : Time) :
    (acRestart p st w).base.votes.Nodup := (acRestart_pool p st w).2.2.1

/-- [Sleep v6; plan §14.3] The replay handler stores no duplicate stamp key. -/
theorem acRestart_voteStamp_nodup (p : Params) (st : State p.n) (w : Time) :
    ((acRestart p st w).base.voteStamp.map Prod.fst).Nodup := by
  rw [acRestart_voteStamp_keys]
  exact acRestart_votes_nodup p st w

/-- [Sleep v6; plan §14.3] Each label and seat has at most two stored votes. -/
theorem acRestart_two_per_seat (p : Params) (st : State p.n) (w : Time) (s : Slot)
    (i : Fin p.n) :
    (GridCO.seatVotes (GridCO.votesAt (acRestart p st w).base s) i).length ≤ 2 :=
  (acRestart_pool p st w).2.2.2.2 s i

/-- [Sleep v6; plan §14.3] Every accepted replay vote has the exact wake stamp. -/
theorem acRestart_replay_stamp (p : Params) (st : State p.n) (w : Time)
    (o : GridCO.Wire p.n .root) (_ho : o ∈ (acRestart p st w).base.votes) :
    GridCO.stampVote (acRestart p st w).base o = w := by
  have hs := (acRestart_pool p st w).2.2.2.1
  unfold GridCO.stampVote
  cases hf : (acRestart p st w).base.voteStamp.find? (fun row => row.1 == o) with
  | none => exact acRestart_now p st w
  | some row =>
      exact hs row (List.mem_of_find?_eq_some hf)

private def BodyOrder (st : State n) : Prop :=
  (st.proposals.filterMap Wire.proposal?).Pairwise (fun N M => N.parent ≠ M) ∧
  ∀ N ∈ st.proposals.filterMap Wire.proposal?, N.parent ≠ N

private theorem bodyOrder_append (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) (ord : BodyOrder st) (s : Slot) (N : NamedProposal p.n)
    (P : FGBlock (Fin p.n)) (ha : blockAccepted p st s N P = true) :
    BodyOrder { st with proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } := by
  have fresh : N ∉ st.namedBodies := by
    intro hm
    have hb := (namedBodies_erase_domain p st h m N.erase).mpr ⟨N, hm, rfl⟩
    obtain ⟨B, hB, he⟩ := (h.baseTree N.erase).mp hb
    exact (blockAccepted_facts ha).2.2.1 ⟨B, hB, by rw [← eraseFG_root, he]⟩
  have self : N.parent ≠ N := by
    intro he
    have hs := (blockAccepted_facts ha).2.2.2.2.1
    rw [named_erase_parent, he] at hs
    exact (Nat.lt_irrefl _) hs
  dsimp only [BodyOrder]
  have hd : Wire.proposal? (⟨.proposer s, .proposal N⟩ : Wire p.n) = some N := rfl
  simp only [List.filterMap_append, List.filterMap_cons_some hd, List.filterMap_nil]
  refine ⟨List.pairwise_append.mpr ⟨ord.1, List.pairwise_singleton _ _, ?_⟩, ?_⟩
  · intro M hm Q hQ
    have he := List.mem_singleton.mp hQ
    subst Q
    intro he
    have hM : M ∈ st.namedBodies := List.mem_cons_of_mem _ hm
    exact fresh (he ▸ namedBodies_parent p st m hM)
  · intro M hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ord.2 M hm
    · have he := List.mem_singleton.mp hm
      subst M
      exact self

private theorem bodyOrder_process (p : Params) (st : State p.n) (hr : Reachable p st)
    (ord : BodyOrder st) (o : Wire p.n) : BodyOrder (process p st o) := by
  have h := storeInvariant p st hr
  have m := metadataInvariant p st hr
  unfold process
  cases hd : o.decode with
  | none => exact ord
  | some input =>
    cases input with
    | vote s i b => exact ord
    | row i body =>
      change BodyOrder (admitRow p st ⟨o.auth, body⟩)
      rcases admitRow_eq p st ⟨o.auth, body⟩ with he | he <;> rw [he] <;> exact ord
    | block s N =>
      change BodyOrder (admitBlock p st s N)
      by_cases hNamed : namedParentHeld st N = true
      swap
      · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
        exact ord
      cases hP : parentFG st N.erase with
      | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
        exact ord
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, ha⟩))]
          exact ord
        | true =>
          obtain ⟨pool, he, _⟩ := admitBlock_accepted_eq p st s N P hNamed hP ha
          have hp : (admitBlock p st s N).proposals =
              st.proposals ++ [⟨.proposer s, .proposal N⟩] := by
            rw [he]
            exact (accepted_st2 p st h s N P hP ha).1
          have ord' := bodyOrder_append p st h m ord s N P ha
          dsimp only [BodyOrder] at ord' ⊢
          rw [hp]
          exact ord'


private theorem bodyOrder_reachable (p : Params) {st : State p.n} (hr : Reachable p st) :
    BodyOrder st := by
  induction hr with
  | init => exact ⟨List.Pairwise.nil, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | restart w _ ih => exact ih
  | tick t _ ih =>
    dsimp only [BodyOrder] at ih ⊢
    simpa only [clock_proposals] using ih
  | deliver o hr ih => exact bodyOrder_process p _ hr ih o

/-- [Sleep v6; plan §14.3] Selection filters the admitted bodies without changing their order. -/
theorem restartSources_eq (p : Params) (st : State p.n) :
    restartSources p st = (st.proposals.filterMap Wire.proposal?).filter
      (fun N => N.erase != .genesis && decide (∃ B ∈ Next.tree p st, eraseFG B = N.erase)) := by
  rw [List.filter_filterMap]
  unfold restartSources
  apply List.filterMap_congr
  intro o _
  unfold Wire.proposal?
  cases hd : o.decode with
  | none => rfl
  | some input => cases input <;> rfl

/-- [Sleep v6; plan §14.3] A selected parent occurs before its selected child. -/
theorem restartSources_parent_order (p : Params) (st : State p.n) (hr : Reachable p st)
    (i j : Nat) (hi : i < (restartSources p st).length)
    (hj : j < (restartSources p st).length)
    (hp : (restartSources p st)[j].parent = (restartSources p st)[i]) : i < j := by
  have ord := bodyOrder_reachable p hr
  have pair : (restartSources p st).Pairwise (fun N M => N.parent ≠ M) := by
    rw [restartSources_eq]
    exact ord.1.filter _
  have self : ∀ N ∈ restartSources p st, N.parent ≠ N := by
    rw [restartSources_eq]
    exact fun N hm => ord.2 N (List.mem_filter.mp hm).1
  by_contra hn
  have hji : j ≤ i := Nat.le_of_not_gt hn
  rcases Nat.lt_or_eq_of_le hji with hji | he
  · exact (pair.rel_getElem_of_lt hj hi hji) hp
  · subst i
    exact self _ (List.getElem_mem hj) hp

/-- [Sleep v6; D0c] Replay uses the same block order and raw-list order as the source. -/
theorem acRestart_replay_order (p : Params) (st : State p.n) (w : Time) :
    acRestart p st w = (restartSources p st).foldl
      (fun acc N => N.raw.foldl
        (fun acc h => process p acc (⟨h.auth, .head h.payload⟩ : Wire p.n)) acc)
      (wipe p st w) := by
  rw [acRestart, restartVotes_eq, List.foldl_flatMap]
  simp only [List.foldl_map]

/-- [Sleep v6; D0c] Each non-genesis block has the exact wake stamp after replay. -/
theorem acRestart_block_stamp (p : Params) (st : State p.n) (w : Time)
    (b : Block) (hb : b ≠ .genesis) : GridCO.stampBlock (acRestart p st w).base b = w := by
  have stamp : ∀ row ∈ (acRestart p st w).base.blockStamp, row.1 = b → row.2 = w := by
    rw [acRestart_blockStamp]
    intro row hm he
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hm
    dsimp only at he ⊢
    rw [he, ite_eq_right hb]
  unfold GridCO.stampBlock
  cases hf : (acRestart p st w).base.blockStamp.find? (fun row => row.1 == b) with
  | none => exact acRestart_now p st w
  | some row =>
      have he : (row.1 == b) = true :=
        List.find?_some (p := fun r : Block × Time => r.1 == b) (a := row) hf
      exact stamp row (List.mem_of_find?_eq_some hf) (beq_iff_eq.mp he)

/-- [Sleep v6; P24] Wipe and the existing delivery constructor give restart reachability. -/
theorem reachable_acRestart (p : Params) (st : State p.n) (w : Time)
    (h : Reachable p st) : Reachable p (acRestart p st w) := by
  have fold : ∀ (xs : List (Wire p.n)) (acc : State p.n), Reachable p acc →
      Reachable p (xs.foldl (process p) acc) := by
    intro xs
    induction xs with
    | nil => exact fun _ h => h
    | cons o xs ih => exact fun _ h => ih _ (.deliver o h)
  exact fold _ _ (.restart w h)

end AvailableChain.FGSA
end
