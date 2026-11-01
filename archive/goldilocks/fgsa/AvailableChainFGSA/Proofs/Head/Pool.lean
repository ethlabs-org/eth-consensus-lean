module
public import AvailableChainFGSA.Model.Frame -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.AC.RootSupport
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.1, blueprint 02 §2.1. Class (iii), store instance.
DC: Legacy/Definitions/ConfirmationScore.lean:18–28; same cutoff inclusion. -/
theorem fgsa_early_subset_late (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    GridCO.earlyVotes p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s := by
  intro o ho
  obtain ⟨hm, hr⟩ := List.mem_filter.mp ho
  apply List.mem_filter.mpr
  refine ⟨hm, ?_⟩
  cases ht : GridCO.resolvedHead? v o with
  | none => change (match GridCO.resolvedHead? v o with | none => false | some _ => _) = true at hr
            simp only [ht, Bool.false_eq_true] at hr
  | some B =>
    change (match GridCO.resolvedHead? v o with | none => false | some _ => _) = true at hr
    simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hr
    have he : GridCO.earlyTime p.toParams.engine s < GridCO.gateTime p.toParams.engine s := by
      dsimp [GridCO.earlyTime, GridCO.gateTime]
      linarith [p.toParams.engine.deltaPos]
    exact decide_eq_true (lt_trans hr.1.2 he)

private theorem pool_same_seat (a b : GridCO.Wire n .root) (s : Slot) (i : Fin n)
    (ha : GridCO.headLabel? a = some s) (hb : GridCO.headLabel? b = some s)
    (hia : GridCO.headSeat? a = some i) (hib : GridCO.headSeat? b = some i) :
    GridCO.sameSeat a b = true := by
  have auth (o : GridCO.Wire n .root) (hl : GridCO.headLabel? o = some s)
      (hk : GridCO.headSeat? o = some i) : o.auth = .seat s i := by
    rcases o with ⟨aa, ap⟩
    cases aa with
    | none => cases ap <;> cases hl
    | proposer r => cases ap <;> cases hl
    | seat r j =>
      cases ap with
      | proposal C raw sup => cases hl
      | head C =>
        have hr : r = s := Option.some.inj hl
        have hj : j = i := Option.some.inj hk
        subst r; subst j
        rfl
  change (match a.auth, b.auth with
    | .seat r j, .seat t k => r == t && j == k
    | _, _ => false) = true
  rw [auth a ha hia, auth b hb hib]
  simp only [beq_self_eq_true, Bool.and_self]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.1, blueprint 02 §2.1. Class (iii), store instance.
DC b241081: Goldfish/Confirmation.lean:95 Numerator (`filtered`). SAME:
the early pool excludes each seat with a second vote in the late pool. -/
theorem fgsa_cleanSupport_no_equivocation (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (i : Fin p.n) :
    GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) i = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨a, ha, b, hb, hne, hia, hib⟩ :=
    (Gen.AC.Root.cap_pair _ i).mp he
  obtain ⟨hae, hac⟩ := List.mem_filter.mp ha
  have hbe := (List.mem_filter.mp hb).1
  have hal : GridCO.headLabel? a = some s := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hae).1).2
  have hbl : GridCO.headLabel? b = some s := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hbe).1).2
  have hx : (GridCO.lateVotes p.toParams.engine v s).any
      (fun u => GridCO.sameSeat u a && u != a) = true :=
    List.any_eq_true.mpr ⟨b, fgsa_early_subset_late p v s hbe,
      by simp only [pool_same_seat b a s i hbl hal hib hia, Bool.true_and,
        bne_iff_ne]; exact Ne.symm hne⟩
  simp only [hx, Bool.not_true, Bool.false_eq_true] at hac

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.1, blueprint 02 §2.1. Class (iii), store instance.
DC: Goldfish/Adoption.lean:128; same participant inclusion. -/
theorem fgsa_cleanSupport_seats_subset_late (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    (GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset :=
  Gen.AC.Root.vote_pool_seats_subset _ _ (fun _ h =>
    fgsa_early_subset_late p v s (List.mem_filter.mp h).1)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.1, blueprint 02 §2.1. Class (iii), Gen support instance.
DC: Goldfish/Confirmation.lean:210; INTENTIONAL resolved pool (02:354). -/
theorem fgsa_prefixSupport_antitone (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (X B : Block) (h : Block.Preceq X B) :
    SA.Root.prefixSupport p.toParams v s B ≤ SA.Root.prefixSupport p.toParams v s X :=
  Gen.AC.Root.goldfishScoreOn_antitone _ _ _ _ X B h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] P3 F1b.1, blueprint 02 §2.1. Class (iii), Gen incidence
instance.
DC: Goldfish/Adoption.lean:257; INTENTIONAL clean support and late denominator
(blueprint 02:116). -/
theorem fgsa_conflicting_support_sum_le_late (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (B D : Block) (h : Block.compatible B D = false) :
    SA.Root.prefixSupport p.toParams v s B + SA.Root.prefixSupport p.toParams v s D ≤
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) :=
  (Gen.AC.Root.conflicting_scoreOn_sum_le _ _ _ B D
    (fgsa_cleanSupport_no_equivocation p v s) h).trans
    (Gen.AC.Root.voterCount_le_of_seats_subset _ _ (fgsa_cleanSupport_seats_subset_late p v s))

/-- [ROOT-DIGEST-2 W1; DC root HEAD] ROOT-DIGEST W1b: mark the unused constructor root argument.
 P3:4900–4945, F1b.1; blueprint 02 §5.4:541. Class (iii), store wrapper.
DC: NamedConfirmationWalk:28 and GSTZeroPreparedWalk:546–578.
INTENTIONAL: F anchor and explicit anchor eligibility, spec:2506–2513;
only the suffix above the anchor must be stored (P3 Astra r3 #1). -/
theorem fgsa_confirmationFrom_covers_majority (p : Params) (v : GridCO.State p.n .root)
    (a B : Block) (s : Slot) (_r_s : BlockId) (hc : Block.Compatible a B)
    (ha : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a)
    (hb : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B)
    (hm : ∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) :
    ∃ C, SA.Root.confirmationFrom p.toParams a v s = some C ∧ Block.Preceq B C := by
  let score := SA.Root.prefixSupport p.toParams v s
  let elig := fun X => decide
    (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) < 2 * score X)
  have hd : DominatedSuffix a B v.blocks score elig := by
    rw [DominatedSuffix_def]
    intro X hax hxb
    have hax' : a ≠ X ∧ Block.Preceq a X := by
      change ((!decide (a = X)) && Block.preceq a X) = true at hax
      have hh := Bool.and_eq_true_iff.mp hax
      refine ⟨?_, hh.2⟩
      intro heq
      subst X
      have hf := hh.1
      simp only [decide_true, Bool.not_true, Bool.false_eq_true] at hf
    have hx := fgsa_prefixSupport_antitone p v s X B hxb
    refine ⟨hm X hax'.2 hxb (Ne.symm hax'.1), decide_eq_true (by dsimp [score]; omega), ?_⟩
    intro D _ hp _ hne
    have hdepth : D.depth = X.depth := by
      cases D with
      | genesis =>
        cases X with
        | genesis => rfl
        | node P s r_s id => cases hp
      | node P s r_s id =>
        cases X with
        | genesis => cases hp
        | node Q t r_t jd =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D X := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D X h (Nat.le_of_eq hdepth.symm))
      · exact hne (prefix_eq_of_depth X D h (Nat.le_of_eq hdepth)).symm
    have hconf : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hxb)
    have hs := fgsa_conflicting_support_sum_le_late p v s B D hconf
    dsimp [score]
    omega
  obtain ⟨hcover, hel⟩ := walk_covers_of_dominated_suffix_of_anchor_eligible
    a B v.blocks score elig hc hd (decide_eq_true ha)
  refine ⟨GridCO.ghost a v.blocks score elig, ?_, hcover⟩
  change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * score (GridCO.ghost a v.blocks score elig) then
        some (GridCO.ghost a v.blocks score elig) else none) = _
  exact ite_eq_left (of_decide_eq_true hel)

end AvailableChain.FGSA
