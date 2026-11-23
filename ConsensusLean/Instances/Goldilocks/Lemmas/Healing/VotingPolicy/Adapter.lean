module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Instance

public section

/-! # Voting-policy spike: the AC adapter

A voting policy changes when a node calls `ac_to_fg` (its signing calendar) and when it sends the
row it signs. This file is the first target of the bounded spike (plan rev 30, item 3): the AC
part of the relation between a calendar run and the stock run.

`ac_to_fg` writes only the report marker `fg_reported` (`acToFG_rep`), and no other AC call reads
it: from a state with the marker replaced, every other call returns its own result with the marker
replaced, and its emissions with the marker replaced at their read points (`step_rep`); a restart
resets the marker (`acRestart_rep`). Hence (`runCalls_filter_toFG`) running a node's AC calls with
or without its `ac_to_fg` calls, for the same frames and other calls, gives AC states and
emissions that agree up to `fg_reported`.

Not covered here: the frames, which read the FG store and so differ between policies, and the
tick groups of the node run (`Growing.LocalRun.grouped`), which fix one `ac_to_fg` per tick. -/

namespace Consensus.Goldilocks.VotingPolicy

open AC

variable {sp : ACParams} {FGP : Type}

theorem admitVote_rep (A : ACState sp.n) (r : Nat) t v :
    admitVote sp { A with fgReported := r } t v = { admitVote sp A t v with fgReported := r } := by
  unfold admitVote
  split_ifs <;> rfl

theorem blockReceipt_rep (A : ACState sp.n) (r : Nat) t (B : Blk sp.n FGP) :
    blockReceipt sp { A with fgReported := r } t B =
      { blockReceipt sp A t B with fgReported := r } := rfl

theorem updateLatestConfirmed_rep (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) C :
    updateLatestConfirmed sp { A with fgReported := r } Φ C =
      { updateLatestConfirmed sp A Φ C with fgReported := r } := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

theorem optimisticConfirmation_rep (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t :
    optimisticConfirmation sp { A with fgReported := r } Φ t =
      { optimisticConfirmation sp A Φ t with fgReported := r } := by
  unfold optimisticConfirmation
  rw [show optimisticSelect sp { A with fgReported := r } Φ t = optimisticSelect sp A Φ t
    from rfl]
  cases optimisticSelect sp A Φ t with
  | none => rfl
  | some B =>
    dsimp only
    unfold updateLatestConfirmed
    split_ifs <;> rfl

theorem updateConfirmation_rep (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t s :
    updateConfirmation sp { A with fgReported := r } Φ t s =
      { updateConfirmation sp A Φ t s with fgReported := r } := by
  unfold updateConfirmation
  rw [show getConfirmation sp { A with fgReported := r } Φ s = getConfirmation sp A Φ s
    from rfl]
  cases getConfirmation sp A Φ s with
  | none => rfl
  | some C =>
    dsimp only
    unfold updateLatestConfirmed
    split_ifs <;> rfl

/-- An emission with the report marker of its read point replaced. -/
abbrev emRep (r : Nat) (e : Em sp FGP) : Em sp FGP :=
  { e with readPoint := { e.readPoint with fgReported := r } }

theorem tryVote_rep (self : Fin sp.n) (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t :
    tryVote sp self { A with fgReported := r } Φ t =
      ({ (tryVote sp self A Φ t).1 with fgReported := r },
        (tryVote sp self A Φ t).2.map (emRep r)) := by
  have hj : joined sp { A with fgReported := r } t = joined sp A t := rfl
  have hr : ∀ s, voteReady sp { A with fgReported := r } Φ s = voteReady sp A Φ s :=
    fun _ => rfl
  unfold tryVote
  dsimp only
  rw [hj, hr]
  split_ifs <;> try rfl
  all_goals
    refine Prod.ext ?_ rfl
    dsimp only
    rw [← optimisticConfirmation_rep, ← admitVote_rep]
    rfl

theorem acOnMessage_rep (self : Fin sp.n) (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t v :
    acOnMessage sp self { A with fgReported := r } Φ t v =
      ({ (acOnMessage sp self A Φ t v).1 with fgReported := r },
        (acOnMessage sp self A Φ t v).2.map (emRep r)) := by
  unfold acOnMessage
  rw [admitVote_rep, optimisticConfirmation_rep, tryVote_rep]

theorem acOnBlock_rep (self : Fin sp.n) (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t B :
    acOnBlock sp self { A with fgReported := r } Φ t B =
      ({ (acOnBlock sp self A Φ t B).1 with fgReported := r },
        (acOnBlock sp self A Φ t B).2.map (emRep r)) := by
  unfold acOnBlock
  rw [blockReceipt_rep, optimisticConfirmation_rep, tryVote_rep]

theorem acOnTick_rep (self : Fin sp.n) (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t :
    acOnTick sp self { A with fgReported := r } Φ t =
      ({ (acOnTick sp self A Φ t).1 with fgReported := r },
        (acOnTick sp self A Φ t).2.map (emRep r)) := by
  have hj : joined sp { A with fgReported := r } t = joined sp A t := rfl
  unfold acOnTick
  dsimp only
  rw [hj]
  split_ifs
  all_goals first
    | rfl
    | rw [tryVote_rep, updateConfirmation_rep]
    | rw [tryVote_rep]
    | exact Prod.ext (updateConfirmation_rep A r Φ t _) rfl

theorem acProposal_rep (A : ACState sp.n) (r : Nat) (Φ : Frm sp.n FGP) t :
    acProposal sp { A with fgReported := r } Φ t =
      ({ (acProposal sp A Φ t).1 with fgReported := r }, (acProposal sp A Φ t).2) := by
  have hj : joined sp { A with fgReported := r } t = joined sp A t := rfl
  unfold acProposal
  dsimp only
  rw [hj]
  split_ifs <;> rfl

theorem acRestart_rep (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n) (r : Nat)
    (Φ : Frm sp.n FGP) t :
    acRestart sp ro self { A with fgReported := r } Φ t = acRestart sp ro self A Φ t := rfl

/-- `ac_to_fg` changes only the report marker. -/
theorem acToFG_rep (A : ACState sp.n) (Φ : Frm sp.n FGP) t :
    (acToFG sp A Φ t).1 = { A with fgReported := (acToFG sp A Φ t).1.fgReported } := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-- **Every AC call other than `ac_to_fg` and a restart ignores the report marker.** From the
state with a replaced marker, the call returns its own result with the same marker replaced, and
the same emissions with the marker replaced at their read points. A restart resets the marker
(`acRestart_rep`). -/
theorem step_rep (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n) (r : Nat)
    (Φ : Frm sp.n FGP) t (c : (goldilocksAC sp FGP ro).Call) (hc : c ≠ .toFG)
    (hr : c ≠ .restart) :
    (goldilocksAC sp FGP ro).step self { A with fgReported := r } Φ t c =
      ({ ((goldilocksAC sp FGP ro).step self A Φ t c).1 with fgReported := r },
        ((goldilocksAC sp FGP ro).step self A Φ t c).2.map (emRep r)) := by
  cases c with
  | tick => exact acOnTick_rep self A r Φ t
  | proposal =>
    change ((acProposal sp { A with fgReported := r } Φ t).1, []) = _
    rw [acProposal_rep]
    rfl
  | toFG => exact absurd rfl hc
  | message m => exact acOnMessage_rep self A r Φ t m
  | block B => exact acOnBlock_rep self A r Φ t B
  | restart => exact absurd rfl hr

/-- One node's AC calls from `A`, each with its frame and time: the final state and the
emissions in order. -/
noncomputable def runCalls (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n) :
    List (Frm sp.n FGP × Time × (goldilocksAC sp FGP ro).Call) →
      ACState sp.n × List (Em sp FGP)
  | [] => (A, [])
  | (Φ, t, c) :: cs =>
    let r := (goldilocksAC sp FGP ro).step self A Φ t c
    let q := runCalls ro self r.1 cs
    (q.1, r.2 ++ q.2)

theorem runCalls_nil (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n) :
    runCalls ro self A [] = (A, []) := by rfl

theorem runCalls_cons (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n) Φ t c cs :
    runCalls ro self A ((Φ, t, c) :: cs) =
      ((runCalls ro self ((goldilocksAC sp FGP ro).step self A Φ t c).1 cs).1,
        ((goldilocksAC sp FGP ro).step self A Φ t c).2 ++
          (runCalls ro self ((goldilocksAC sp FGP ro).step self A Φ t c).1 cs).2) := by rfl

private theorem eq_rep_of {A B : ACState sp.n}
    (h : { A with fgReported := 0 } = { B with fgReported := 0 }) :
    B = { A with fgReported := B.fgReported } := by
  cases A; cases B
  cases h
  rfl

/-- The calls that are not `ac_to_fg`. -/
def NotToFG (ro : ReplayOrder sp FGP)
    (x : Frm sp.n FGP × Time × (goldilocksAC sp FGP ro).Call) : Bool :=
  match x.2.2 with
  | .toFG => false
  | _ => true

/-- **The AC adapter: the report calls do not change the AC.** Running a node's AC calls, and
running the same calls with every `ac_to_fg` removed, from states that agree up to the report
marker `fg_reported`, ends in states that agree up to that marker, with the same emissions up to
the marker at their read points. So the AC state of a family that calls `ac_to_fg` at other times
(a signing calendar) differs from the AC state of the family that calls it at every tick only in
`fg_reported`, for the same frames and other calls. -/
theorem runCalls_filter_toFG (ro : ReplayOrder sp FGP) (self : Fin sp.n) :
    ∀ (cs : List (Frm sp.n FGP × Time × (goldilocksAC sp FGP ro).Call)) (A B : ACState sp.n),
      { A with fgReported := 0 } = { B with fgReported := 0 } →
      { (runCalls ro self A cs).1 with fgReported := 0 } =
          { (runCalls ro self B (cs.filter (NotToFG ro))).1 with fgReported := 0 } ∧
        (runCalls ro self A cs).2.map (emRep 0) =
          (runCalls ro self B (cs.filter (NotToFG ro))).2.map (emRep 0) := by
  intro cs
  induction cs with
  | nil => intro A B h; exact ⟨h, by simp [runCalls_nil]⟩
  | cons x cs ih =>
    intro A B h
    obtain ⟨Φ, t, c⟩ := x
    have hB := eq_rep_of h
    by_cases hc : c = .toFG
    · subst hc
      have hA := acToFG_rep A Φ t
      have h' : { (acToFG sp A Φ t).1 with fgReported := 0 } = { B with fgReported := 0 } := by
        rw [hA]; exact h
      have := ih _ B h'
      simpa [runCalls_cons, NotToFG, ACInterface.step] using this
    have hn : NotToFG ro (Φ, t, c) = true := by
      cases c <;> first | rfl | exact absurd rfl hc
    by_cases hr : c = .restart
    · subst hr
      have hs : (goldilocksAC sp FGP ro).step self B Φ t .restart =
          (goldilocksAC sp FGP ro).step self A Φ t .restart := by
        rw [hB]; exact acRestart_rep ro self A _ Φ t
      obtain ⟨h1, h2⟩ := ih _ _ rfl
      refine ⟨?_, ?_⟩
      · simp only [runCalls_cons, List.filter_cons, hn, ite_true, hs]
        exact h1
      · simp only [runCalls_cons, List.filter_cons, hn, ite_true, hs, List.map_append]
        rw [h2]
    have hs : (goldilocksAC sp FGP ro).step self B Φ t c =
        ({ ((goldilocksAC sp FGP ro).step self A Φ t c).1 with fgReported := B.fgReported },
          ((goldilocksAC sp FGP ro).step self A Φ t c).2.map (emRep B.fgReported)) := by
      rw [hB]; exact step_rep ro self A _ Φ t c hc hr
    obtain ⟨h1, h2⟩ := ih ((goldilocksAC sp FGP ro).step self A Φ t c).1
      { ((goldilocksAC sp FGP ro).step self A Φ t c).1 with fgReported := B.fgReported } rfl
    refine ⟨?_, ?_⟩
    · simp only [runCalls_cons, List.filter_cons, hn, ite_true, hs]
      exact h1
    · simp only [runCalls_cons, List.filter_cons, hn, ite_true, hs, List.map_append, List.map_map]
      rw [h2]
      rfl

end Consensus.Goldilocks.VotingPolicy
