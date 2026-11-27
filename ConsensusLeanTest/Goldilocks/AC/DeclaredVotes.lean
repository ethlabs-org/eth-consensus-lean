module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Restart
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Block
@[expose] public section

/-! # Golden cases of declared head votes

A slot-`s` block declares previous-slot head votes, with a support list (the Lean form of the
support bits). A declaration is not a vote: block receipt and restart stamping pool nothing, a
block carries no vote object, and a voter counts a declaration only when its pool holds the exact
vote or two distinct votes of its validator (`ShouldCountDeclaredVote`). An early vote needs every
declaration of every slot-`s` proposal counted (`voteReady`); at `t_s + Δ` the voter votes and
omits the rest.

Three validators `v0`, `v1`, `v2`, `Δ = 1`, `t_s = 4s` (so the slot-`1` vote freeze of a slot-`2`
voter is `t_1 + 3Δ = 7`). Genesis `g` (root `0`), the slot-`1` siblings `X` (root `1`) and `Y`
(root `2`), and slot-`2` proposals on `X` (`prop`). The slot-`1` votes are `a = (v0, X)`,
`b = (v1, X)`, `b' = (v1, Y)`, `c = (v2, Y)`, and `z = (v1, g)`, a vote nobody signed. A reader
state `st f l` holds the slot-`1` votes `f` stamped `5` (before the freeze) and `l` stamped `8`
(after it), and nothing else. Labelled by case:

* digest and association: `decodeInfo_encodeInfo`, `encodeInfo_seat_head`,
  `encodeInfo_support`, `root_ne_of_support`;
* rejection and omission: `invalid_duplicate`, `invalid_three_of_one_seat`, `invalid_slot`,
  `invalid_support`, `valid_unsigned_pair`, `unsigned_omitted_at_timeout`;
* no pool insertion or replay: `blockReceipt_admits_nothing`, `message_admits`,
  `acRestart_pools_empty`, `payloadObjs_no_vote`;
* responsive path: `ready_all_counted`, `early_vote_all_counted`;
* timeout path: `not_ready_missing`, `no_early_vote_missing`, `timeout_vote_missing`,
  `missing_omitted`;
* conflicting frozen evidence: `frozen_conflict_kept`;
* missing vote: `missing_omitted`, `single_conflict_omitted`;
* genuine pair: `pair_counts_unsigned`, `pair_ready`;
* support bits: `support_marked`, `support_unmarked`, `support_unresolved`,
  `ready_one_resolved`;
* already-frozen pair: `frozen_pair_kept`;
* several same-slot proposals: `not_ready_other_proposal`, `no_early_vote_other_proposal`,
  `declared_twice_counts_once`. -/

namespace Consensus.Goldilocks.AC.Test.DeclaredVotes

/-- Three validators, `Δ = 1`, `t_s = 4s`, genesis root `0`. -/
abbrev P3 : Params where
  n := 3
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 0

/-- The AC parameters: `P3` with `k = c = 2`. -/
abbrev sp3 : ACParams where
  toParams := P3
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

abbrev v0 : Fin sp3.n := 0
abbrev v1 : Fin sp3.n := 1
abbrev v2 : Fin sp3.n := 2

/-- The slot-`1` votes. -/
def a : Vote sp3.n := ⟨v0, 1, 1⟩
def b : Vote sp3.n := ⟨v1, 1, 1⟩
def b' : Vote sp3.n := ⟨v1, 1, 2⟩
def c : Vote sp3.n := ⟨v2, 1, 2⟩
/-- A declared vote nobody signed. -/
def z : Vote sp3.n := ⟨v1, 1, 0⟩

/-- Blocks (FG payload `Unit`). -/
def g : Blk sp3.n Unit := ⟨0, none, 0, v0, 0, (), ([], [])⟩
def X : Blk sp3.n Unit := ⟨1, some 0, 1, v1, 0, (), ([], [])⟩
def Y : Blk sp3.n Unit := ⟨2, some 0, 1, v1, 0, (), ([], [])⟩

/-- A slot-`2` proposal on `X` with root `r` and payload `p`. -/
def prop (r : Nat) (p : Payload sp3.n) : Blk sp3.n Unit := ⟨r, some 1, 2, v2, 0, (), p⟩

/-- The frame whose tree is `g`, `X`, `Y` and the proposals `ps`. -/
def frm (ps : List (Blk sp3.n Unit)) : Frm sp3.n Unit :=
  ⟨{B | B = g ∨ B = X ∨ B = Y ∨ B ∈ ps}, g, g, ∅⟩

/-- A reader holding the slot-`1` votes `f` stamped `5` and `l` stamped `8`. -/
def st (f l : List (Vote sp3.n)) : ACState sp3.n :=
  { ACState.initial (n := sp3.n) 0 with
    pool := fun s => if s = 1 then f ++ l else []
    voteStamp := fun v => if v ∈ f then ETime.of 5 else if v ∈ l then ETime.of 8 else ⊤ }

/-! ## The fixture's arithmetic -/

theorem slot_8 : sp3.slot 8 = 2 := by decide
theorem slot_9 : sp3.slot 9 = 2 := by decide
theorem ts_2 : sp3.ts (2 : Nat) = 8 := rfl
theorem freeze_2 : freeze sp3 2 = 7 := rfl

theorem joined_st (f l : List (Vote sp3.n)) (t : Time) : joined sp3 (st f l) t := by
  unfold joined; exact (bot_le : (⊥ : WithBot Time) ≤ _)

/-- At `t ∈ {8, 9}` a slot-`2` voter of `st f l` passes the first guard of `try_vote`. -/
theorem guard_st (f l : List (Vote sp3.n)) (t : Time) (ht : t = 8 ∨ t = 9) :
    ¬ (¬ joined sp3 (st f l) t ∨ (st f l).votedSlot = ((2 : Nat) : Int) ∨
      sp3.ts (2 : Nat) + sp3.Δ < t) := by
  rintro (h | h | h)
  · exact h (joined_st _ _ _)
  · simp [st, ACState.initial] at h
  · rw [ts_2] at h; rcases ht with rfl | rfl <;> exact absurd h (by decide)

/-- Not ready at `t_2 = 8`: no vote, nothing changes. -/
theorem tryVote_wait {f l : List (Vote sp3.n)} {Φ : Frm sp3.n Unit} (self : Fin sp3.n)
    (hr : ¬ voteReady sp3 (st f l) Φ 2) : tryVote sp3 self (st f l) Φ 8 = (st f l, []) := by
  unfold tryVote
  rw [slot_8, ite_eq_right (fun h => absurd h (guard_st f l 8 (Or.inl rfl))),
    ite_eq_left ⟨by rw [ts_2]; decide, Or.inr hr⟩]

/-- Ready at `t_2 = 8`, or at `t_2 + Δ = 9` with no test: the voter casts. -/
theorem tryVote_cast {f l : List (Vote sp3.n)} {Φ : Frm sp3.n Unit} (self : Fin sp3.n) {t : Time}
    (ht : (t = 8 ∧ voteReady sp3 (st f l) Φ 2) ∨ t = 9) :
    (tryVote sp3 self (st f l) Φ t).2 ≠ [] := by
  have hs : sp3.slot t = 2 := by rcases ht with ⟨rfl, -⟩ | rfl <;> decide
  have h1 := guard_st f l t (by rcases ht with ⟨h, -⟩ | h <;> simp [h])
  have h2 : ¬ (t < sp3.ts (2 : Nat) + sp3.Δ ∧ ((2 : Nat) = 0 ∨ ¬ voteReady sp3 (st f l) Φ 2)) := by
    rintro ⟨hlt, h | h⟩
    · exact absurd h (by decide)
    · rcases ht with ⟨-, hr⟩ | rfl
      · exact h hr
      · rw [ts_2] at hlt; exact absurd hlt (by decide)
  unfold tryVote
  rw [hs, ite_eq_right (fun h => absurd h h1), ite_eq_right (fun h => absurd h h2)]
  simp [st, ACState.initial]

/-- The proposals of slot `2` in `frm ps` are those of `ps` (all of slot `2`). -/
theorem slot_two {ps : List (Blk sp3.n Unit)} {B : Blk sp3.n Unit} (hB : B ∈ (frm ps).tree)
    (hs : B.slot = 2) : B ∈ ps := by
  rcases hB with rfl | rfl | rfl | h
  · simp [g] at hs
  · simp [X] at hs
  · simp [Y] at hs
  · exact h

theorem mem_frm {ps : List (Blk sp3.n Unit)} {B : Blk sp3.n Unit} (h : B ∈ ps) :
    B ∈ (frm ps).tree := Or.inr (Or.inr (Or.inr h))

theorem X_mem (ps : List (Blk sp3.n Unit)) : X ∈ (frm ps).tree := Or.inr (Or.inl rfl)

/-- A slot-`1` vote should be counted by `st f l` iff `f ++ l` holds it or two distinct votes of
its validator. -/
theorem shouldCount_st {f l : List (Vote sp3.n)} {v : Vote sp3.n} (hv : v.slot = 1) :
    ShouldCountDeclaredVote sp3 (st f l) v ↔
      v ∈ f ++ l ∨ v.val ∈ equivocators {y | y ∈ f ++ l} := by
  simp [ShouldCountDeclaredVote, ACState.poolAt, st, hv]

/-- The frozen base of a slot-`2` voter of `st f l` is `f`. -/
theorem base_st (f l : List (Vote sp3.n)) (Φ : Frm sp3.n Unit) (v : Vote sp3.n) :
    v ∈ (voteView (st f l) Φ (((2 : Nat) : Int) - 1) (ETime.of (freeze sp3 2))).votes ↔ v ∈ f := by
  simp only [voteView, View.ofLists, voteViewList, Set.mem_ofPred_eq, List.mem_filter, freeze_2]
  simp only [ACState.poolAt, st]
  constructor
  · rintro ⟨-, h⟩
    by_contra hf
    simp only [hf, ↓reduceIte] at h
    split_ifs at h <;> simp only [ETime.of] at h <;> exact absurd h (by decide)
  · intro hf
    refine ⟨by simp [hf], ?_⟩
    simp only [hf, ↓reduceIte]
    simp only [ETime.of]; decide

/-- The votes of the merged view of a slot-`2` voter of `st f l` in `frm ps`. -/
theorem merged_votes {f l : List (Vote sp3.n)} {ps : List (Blk sp3.n Unit)} {v : Vote sp3.n}
    (hps : ∀ B ∈ ps, B.slot = 2) :
    v ∈ (mergedVoteView sp3 (st f l) (frm ps) 2).votes ↔
      v ∈ f ∨ ∃ B ∈ ps, v ∈ declaredHeadVotes B ∧ ShouldCountDeclaredVote sp3 (st f l) v := by
  simp only [mergedVoteView, Set.mem_union, Set.mem_ofPred_eq]
  rw [base_st]
  constructor
  · rintro (h | ⟨B, hB, hs, hv, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨B, slot_two hB hs, hv, hc⟩
  · rintro (h | ⟨B, hB, hv, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨B, mem_frm hB, hps B hB, hv, hc⟩

/-! ## Digest and association -/

/-- A payload: `a` and `b` declared, `a` marked. -/
def pAB : Payload sp3.n := ([a, b], [a])

/-- The header data round-trips: the decoded payload is the declared one, seat by seat, head by
head, with the same support. -/
theorem decodeInfo_encodeInfo :
    AsChainShape.decodeInfo 3 (AsChainShape.encodeInfo (n := 3) [] pAB) = some ([], pAB) := by
  decide

/-- The same seats and the same heads, associated differently, encode differently. -/
theorem encodeInfo_seat_head :
    AsChainShape.encodeInfo (n := 3) [] (([⟨v0, 1, 1⟩, ⟨v1, 1, 2⟩], []) : Payload sp3.n) ≠
      AsChainShape.encodeInfo (n := 3) [] (([⟨v0, 1, 2⟩, ⟨v1, 1, 1⟩], []) : Payload sp3.n) := by
  decide

/-- The same declarations with different support encode differently. -/
theorem encodeInfo_support :
    AsChainShape.encodeInfo (n := 3) [] (([a, b], [a]) : Payload sp3.n) ≠
      AsChainShape.encodeInfo (n := 3) [] (([a, b], [b]) : Payload sp3.n) ∧
    AsChainShape.encodeInfo (n := 3) [] (([a, b], [a]) : Payload sp3.n) ≠
      AsChainShape.encodeInfo (n := 3) [] (([a, b], []) : Payload sp3.n) := by
  decide

/-- Under a digest injective in the AC payload, two blocks that differ only in their support have
different roots. -/
theorem root_ne_of_support (dg : Digest Unit (Payload sp3.n))
    (hdg : ∀ p s i f q q', dg p s i f q = dg p s i f q' → q = q') {B B' : Blk sp3.n Unit}
    (h : B.RootOk dg) (h' : B'.RootOk dg) (hp : B.parent = B'.parent) (hs : B.slot = B'.slot)
    (hi : B.input = B'.input) (hpay : B.acPayload = ([a, b], [a]))
    (hpay' : B'.acPayload = ([a, b], [])) : B.root ≠ B'.root := by
  intro hr
  unfold Block.RootOk at h h'
  have hf : B.fgPayload = B'.fgPayload := rfl
  rw [h, h', hp, hs, hi, hf] at hr
  have := hdg _ _ _ _ _ _ hr
  rw [hpay, hpay'] at this
  simp at this

/-! ## Rejection and omission -/

/-- A repeated declaration is rejected. -/
theorem invalid_duplicate : ¬ validPayload (prop 3 ([a, a], [])) :=
  fun h => by simpa [prop, declaredHeadVotes, a] using h.2.2.1

/-- A third declaration of one validator is rejected. -/
theorem invalid_three_of_one_seat : ¬ validPayload (prop 3 ([b, b', z], [])) :=
  fun h => absurd (h.2.2.2 v1) (by decide)

/-- A declaration of another slot than the previous one is rejected. -/
theorem invalid_slot : ¬ validPayload (prop 3 ([⟨v0, 2, 1⟩], [])) :=
  fun h => absurd (h.1 _ List.mem_cons_self) (by decide)

/-- A support entry that is not declared is rejected. -/
theorem invalid_support : ¬ validPayload (prop 3 ([a], [b])) :=
  fun h => absurd (h.2.1.subset List.mem_cons_self) (by decide)

/-- A pair of declarations of one validator, one of them a vote nobody signed, is valid: the
payload check reads no signature. -/
theorem valid_unsigned_pair : validPayload (prop 3 ([a, b, z], [a, z])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; simp [prop, declaredHeadVotes] at hv; rcases hv with rfl | rfl | rfl <;> rfl
  · decide
  · decide
  · decide

/-- At the timeout, a reader with nothing of `v1` omits the unsigned declaration `z`. -/
theorem unsigned_omitted_at_timeout :
    z ∉ (mergedVoteView sp3 (st [] [a]) (frm [prop 3 ([a, z], [])]) 2).votes := by
  rw [merged_votes (by simp [prop])]
  rintro (h | ⟨B, hB, -, hc⟩)
  · simp at h
  · rw [shouldCount_st rfl] at hc
    rcases hc with h | ⟨x, hx, y, hy, hne, hx1, hy1⟩
    · simp [z, a] at h
    · simp only [Set.mem_ofPred_eq, List.nil_append, List.mem_singleton] at hx hy
      exact hne (hx.trans hy.symm)

/-! ## No pool insertion or replay -/

/-- A block receipt pools none of the block's declarations (under the former rule it would pool
`a`, `b'` and `z`). -/
theorem blockReceipt_admits_nothing :
    (blockReceipt sp3 (ACState.initial 0) 8 (prop 3 ([a, b', z], [a]))).pool 1 = [] := rfl

/-- A vote received as a message is still admitted. -/
theorem message_admits : (admitVote sp3 (ACState.initial 0) 8 a).pool 1 = [a] := by
  simp [admitVote, slot_8, ACState.initial, a]

/-- A restart admits no declaration, whatever the frame and the retained replay order:
the pools are empty and nothing is emitted. -/
theorem acRestart_pools_empty (self : Fin sp3.n) (A : ACState sp3.n)
    (Φ : Frm sp3.n Unit) :
    (acRestart sp3 self A Φ 10).1.pool = (fun _ => []) ∧
      (acRestart sp3 self A Φ 10).2 = [] := by
  exact ⟨rfl, rfl⟩

/-- A block's AC payload carries no vote object: only its attestations are carried (under the
former rule a block declaring `a`, `b'` and `z` would carry their vote objects). -/
theorem payloadObjs_no_vote :
    AsChainShape.payloadObjs (binding := AsChainShape.stock) (n := sp3.n) []
      (([a, b', z], [a]) : Payload sp3.n) = [] := rfl

/-! ## The responsive path: every declaration counted, an early vote -/

/-- The proposal declaring and marking `a` and `b`. -/
def P : Blk sp3.n Unit := prop 3 ([a, b], [a, b])

/-- `a` and `b` held (after the freeze): ready. -/
theorem ready_all_counted : voteReady sp3 (st [] [a, b]) (frm [P]) 2 := by
  refine ⟨⟨P, mem_frm (by simp), rfl, fun x hx _ => ?_⟩, fun B hB hs x hx => ?_⟩
  · simp [P, prop, declaredSupportVotes] at hx
    rcases hx with rfl | rfl <;> exact ⟨X, X_mem _, rfl, le_rfl⟩
  · have hB' := slot_two hB hs
    simp only [List.mem_singleton] at hB'; subst hB'
    simp [P, prop, declaredHeadVotes, declaredSupportVotes] at hx
    rw [shouldCount_st (by rcases hx with rfl | rfl <;> rfl)]
    left; simpa using hx

/-- So the voter casts at `t_2 = 8`, before `t_2 + Δ`. -/
theorem early_vote_all_counted : (tryVote sp3 v2 (st [] [a, b]) (frm [P]) 8).2 ≠ [] :=
  tryVote_cast v2 (Or.inl ⟨rfl, ready_all_counted⟩)

/-! ## The timeout path and missing votes -/

/-- Nothing of `v1` held: `b` cannot be counted, so not ready. -/
theorem not_ready_missing : ¬ voteReady sp3 (st [] [a]) (frm [P]) 2 := by
  rintro ⟨-, h⟩
  have := h P (mem_frm (by simp)) rfl b (Or.inl (by simp [P, prop, declaredHeadVotes]))
  rw [shouldCount_st rfl] at this
  rcases this with h | ⟨x, hx, y, hy, hne, -, -⟩
  · simp [a, b] at h
  · simp only [Set.mem_ofPred_eq, List.nil_append, List.mem_singleton] at hx hy
    exact hne (hx.trans hy.symm)

/-- No early vote. -/
theorem no_early_vote_missing : tryVote sp3 v2 (st [] [a]) (frm [P]) 8 = (st [] [a], []) :=
  tryVote_wait v2 not_ready_missing

/-- At `t_2 + Δ = 9` the voter casts without the test. -/
theorem timeout_vote_missing : (tryVote sp3 v2 (st [] [a]) (frm [P]) 9).2 ≠ [] :=
  tryVote_cast v2 (Or.inr rfl)

/-- And it counts `a` but omits `b`, of which it holds nothing. -/
theorem missing_omitted :
    a ∈ (mergedVoteView sp3 (st [] [a]) (frm [P]) 2).votes ∧
      b ∉ (mergedVoteView sp3 (st [] [a]) (frm [P]) 2).votes := by
  have hps : ∀ B ∈ [P], B.slot = 2 := by simp [P, prop]
  refine ⟨(merged_votes hps).2 (Or.inr ⟨P, by simp, by simp [P, prop, declaredHeadVotes],
    (shouldCount_st rfl).2 (Or.inl (by simp))⟩), ?_⟩
  rw [merged_votes hps]
  rintro (h | ⟨B, -, -, hc⟩)
  · simp at h
  · rw [shouldCount_st rfl] at hc
    rcases hc with h | ⟨x, hx, y, hy, hne, -, -⟩
    · simp [a, b] at h
    · simp only [Set.mem_ofPred_eq, List.nil_append, List.mem_singleton] at hx hy
      exact hne (hx.trans hy.symm)

/-- One conflicting vote is no evidence: holding only `b'` (after the freeze), the voter omits
the declared `b`. -/
theorem single_conflict_omitted :
    b ∉ (mergedVoteView sp3 (st [] [a, b']) (frm [P]) 2).votes := by
  rw [merged_votes (by simp [P, prop])]
  rintro (h | ⟨B, -, -, hc⟩)
  · simp at h
  · rw [shouldCount_st rfl] at hc
    rcases hc with h | ⟨x, hx, y, hy, hne, hx1, hy1⟩
    · simp [a, b, b'] at h
    · simp only [Set.mem_ofPred_eq, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [a, b, b']

/-! ## Genuine pair -/

/-- The proposal declaring the unsigned `z` for `v1`. -/
def Pz : Blk sp3.n Unit := prop 4 ([z], [])

/-- Holding the pair `b`, `b'`, the voter counts the declared `z`, which nobody signed, while its
pool stays as it was. -/
theorem pair_counts_unsigned :
    z ∈ (mergedVoteView sp3 (st [] [b, b']) (frm [Pz]) 2).votes ∧ z ∉ (st [] [b, b']).pool 1 := by
  refine ⟨(merged_votes (by simp [Pz, prop])).2 (Or.inr ⟨Pz, by simp,
    by simp [Pz, prop, declaredHeadVotes],
    (shouldCount_st rfl).2 (Or.inr ⟨b, by simp, b', by simp, by decide, rfl, rfl⟩)⟩), ?_⟩
  simp [st, z, b, b']

/-- And the pair makes the proposal ready. -/
theorem pair_ready : voteReady sp3 (st [] [b, b']) (frm [Pz]) 2 := by
  refine ⟨⟨Pz, mem_frm (by simp), rfl,
    fun x hx _ => by simp [Pz, prop, declaredSupportVotes] at hx⟩,
    fun B hB hs x hx => ?_⟩
  have hB' := slot_two hB hs
  simp only [List.mem_singleton] at hB'; subst hB'
  simp [Pz, prop, declaredHeadVotes, declaredSupportVotes] at hx; subst hx
  exact (shouldCount_st rfl).2 (Or.inr ⟨b, by simp, b', by simp, by decide, rfl, rfl⟩)

/-! ## Support bits -/

/-- The supports of the merged view of a slot-`2` voter of `st [] l` (empty frozen base). -/
theorem merged_support {l : List (Vote sp3.n)} {ps : List (Blk sp3.n Unit)} {v : Vote sp3.n} :
    v ∈ (mergedVoteView sp3 (st [] l) (frm ps) 2).support ↔
      ∃ B ∈ (frm ps).tree, B.slot = 2 ∧ v ∈ declaredSupportVotes B ∧
        ShouldCountDeclaredVote sp3 (st [] l) v ∧
        v.slot + 1 = 2 ∧ ∃ H ∈ (frm ps).tree, H.root = v.head ∧ H.slot + 1 ≤ 2 := by
  simp only [mergedVoteView, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨B, hB, hs, hv, h⟩)
    · exact absurd ((base_st [] l (frm ps) v).1 (List.mem_of_mem_filter h)) (by simp)
    · exact ⟨B, hB, hs, hv, h⟩
  · rintro ⟨B, hB, hs, hv, h⟩
    exact Or.inr ⟨B, hB, hs, hv, h⟩

/-- The marked `a` counts as support. -/
theorem support_marked :
    a ∈ (mergedVoteView sp3 (st [] [a, b]) (frm [prop 3 ([a, b], [a])]) 2).support :=
  merged_support.2 ⟨prop 3 ([a, b], [a]), mem_frm (by simp), rfl,
    by simp [prop, declaredSupportVotes],
    (shouldCount_st rfl).2 (Or.inl (by simp)), rfl, X, X_mem _, rfl, le_rfl⟩

/-- The same declarations without the mark: `a` is a vote, not support. -/
theorem support_unmarked :
    a ∈ (mergedVoteView sp3 (st [] [a, b]) (frm [prop 3 ([a, b], [])]) 2).votes ∧
      a ∉ (mergedVoteView sp3 (st [] [a, b]) (frm [prop 3 ([a, b], [])]) 2).support := by
  refine ⟨(merged_votes (by simp [prop])).2 (Or.inr ⟨prop 3 ([a, b], []), by simp,
    by simp [prop, declaredHeadVotes],
    (shouldCount_st rfl).2 (Or.inl (by simp))⟩), ?_⟩
  rw [merged_support]
  rintro ⟨B, hB, hs, hv, -⟩
  have := slot_two hB hs
  simp only [List.mem_singleton] at this; subst this
  simp [prop, declaredSupportVotes] at hv

/-- A held vote of `v2` for a head outside the tree (root `5`). -/
def c5 : Vote sp3.n := ⟨v2, 1, 5⟩

/-- Marked, but its head is not in the tree: `c5` counts as a vote, not as support. -/
theorem support_unresolved :
    c5 ∈ (mergedVoteView sp3 (st [] [a, b, c5]) (frm [P, prop 4 ([c5], [c5])]) 2).votes ∧
      c5 ∉ (mergedVoteView sp3 (st [] [a, b, c5]) (frm [P, prop 4 ([c5], [c5])]) 2).support := by
  refine ⟨(merged_votes (by simp [P, prop])).2 (Or.inr ⟨prop 4 ([c5], [c5]), by simp,
    by simp [prop, declaredHeadVotes], (shouldCount_st rfl).2 (Or.inl (by simp))⟩), ?_⟩
  rw [merged_support]
  rintro ⟨-, -, -, -, -, -, H, hH, hr, -⟩
  rcases hH with rfl | rfl | rfl | h
  · simp [g, c5] at hr
  · simp [X, c5] at hr
  · simp [Y, c5] at hr
  · simp [P, prop] at h; rcases h with rfl | rfl <;> simp [c5] at hr

/-- Head readiness of one proposal suffices: `P` is resolved, the other proposal's marked head is
not, and with every declaration held the voter is ready. -/
theorem ready_one_resolved : voteReady sp3 (st [] [a, b, c5]) (frm [P, prop 4 ([c5], [c5])]) 2 := by
  refine ⟨⟨P, mem_frm (by simp), rfl, fun x hx _ => ?_⟩, fun B hB hs x hx => ?_⟩
  · simp [P, prop, declaredSupportVotes] at hx
    rcases hx with rfl | rfl <;> exact ⟨X, X_mem _, rfl, le_rfl⟩
  · have hB' := slot_two hB hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB'
    rcases hB' with rfl | rfl <;>
    · simp [P, prop, declaredHeadVotes, declaredSupportVotes] at hx
      rw [shouldCount_st (by rcases hx with rfl | rfl <;> rfl)]
      left; simp only [List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]; tauto

/-! ## Frozen evidence -/

/-- Conflicting frozen evidence: `b'` is frozen; the proposal declares `b`, held after the
freeze. Both count, and `v1` is an equivocator of the view: the frozen vote is not replaced. -/
theorem frozen_conflict_kept :
    let V := mergedVoteView sp3 (st [b'] [b]) (frm [prop 3 ([b], [b])]) 2
    b' ∈ V.votes ∧ b ∈ V.votes ∧ v1 ∈ equivocators V.votes := by
  have hps : ∀ B ∈ [prop 3 ([b], [b])], B.slot = 2 := by simp [prop]
  have hb' : b' ∈ (mergedVoteView sp3 (st [b'] [b]) (frm [prop 3 ([b], [b])]) 2).votes :=
    (merged_votes hps).2 (Or.inl (by simp))
  have hb : b ∈ (mergedVoteView sp3 (st [b'] [b]) (frm [prop 3 ([b], [b])]) 2).votes :=
    (merged_votes hps).2 (Or.inr ⟨prop 3 ([b], [b]), by simp, by simp [prop, declaredHeadVotes],
      (shouldCount_st rfl).2 (Or.inl (by simp))⟩)
  exact ⟨hb', hb, b, hb, b', hb', by decide, rfl, rfl⟩

/-- An already-frozen pair: `b`, `b'` are frozen; the proposal declares the singleton `z`. The
pair stays in the view (with `z`), and `v1` stays an equivocator. -/
theorem frozen_pair_kept :
    let V := mergedVoteView sp3 (st [b, b'] []) (frm [prop 4 ([z], [])]) 2
    b ∈ V.votes ∧ b' ∈ V.votes ∧ z ∈ V.votes ∧ v1 ∈ equivocators V.votes := by
  have hps : ∀ B ∈ [prop 4 ([z], [])], B.slot = 2 := by simp [prop]
  have hb := (merged_votes (f := [b, b']) (l := []) (v := b) hps).2 (Or.inl (by simp))
  have hb' := (merged_votes (f := [b, b']) (l := []) (v := b') hps).2 (Or.inl (by simp))
  have hz := (merged_votes (f := [b, b']) (l := []) (v := z) hps).2 (Or.inr ⟨prop 4 ([z], []),
    by simp,
    by simp [prop, declaredHeadVotes],
    (shouldCount_st rfl).2 (Or.inr ⟨b, by simp, b', by simp, by decide,
      rfl, rfl⟩)⟩)
  exact ⟨hb, hb', hz, b, hb, b', hb', by decide, rfl, rfl⟩

/-! ## Several same-slot proposals -/

/-- `P` declares and marks `a`; another proposal declares `b`. -/
def Pa : Blk sp3.n Unit := prop 3 ([a], [a])
def Pb : Blk sp3.n Unit := prop 4 ([b], [b])

/-- `Pa` is resolved and its declaration held, but the other proposal's `b` is not: not ready. -/
theorem not_ready_other_proposal : ¬ voteReady sp3 (st [] [a]) (frm [Pa, Pb]) 2 := by
  rintro ⟨-, h⟩
  have := h Pb (mem_frm (by simp)) rfl b (Or.inl (by simp [Pb, prop, declaredHeadVotes]))
  rw [shouldCount_st rfl] at this
  rcases this with h | ⟨x, hx, y, hy, hne, -, -⟩
  · simp [a, b] at h
  · simp only [Set.mem_ofPred_eq, List.nil_append, List.mem_singleton] at hx hy
    exact hne (hx.trans hy.symm)

/-- So no early vote, though `Pa` alone would be ready. -/
theorem no_early_vote_other_proposal :
    tryVote sp3 v0 (st [] [a]) (frm [Pa, Pb]) 8 = (st [] [a], []) :=
  tryVote_wait v0 not_ready_other_proposal

/-- A vote declared by two proposals counts once: `v0` is not an equivocator of the view. -/
theorem declared_twice_counts_once :
    let V := mergedVoteView sp3 (st [] [a]) (frm [prop 3 ([a], []), prop 4 ([a], [a])]) 2
    a ∈ V.votes ∧ v0 ∉ equivocators V.votes := by
  have hps : ∀ B ∈ [prop 3 ([a], []), prop 4 ([a], [a])], B.slot = 2 := by simp [prop]
  refine ⟨(merged_votes hps).2 (Or.inr ⟨prop 3 ([a], []), by simp,
    by simp [prop, declaredHeadVotes],
    (shouldCount_st rfl).2 (Or.inl (by simp))⟩), ?_⟩
  rintro ⟨x, hx, y, hy, hne, hx0, hy0⟩
  have only_a : ∀ w, w ∈ (mergedVoteView sp3 (st [] [a])
      (frm [prop 3 ([a], []), prop 4 ([a], [a])]) 2).votes → w = a := by
    intro w hw
    rw [merged_votes hps] at hw
    rcases hw with h | ⟨B, hB, hv, -⟩
    · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl <;> simpa [prop, declaredHeadVotes] using hv
  exact hne ((only_a x hx).trans (only_a y hy).symm)

end Consensus.Goldilocks.AC.Test.DeclaredVotes

end
