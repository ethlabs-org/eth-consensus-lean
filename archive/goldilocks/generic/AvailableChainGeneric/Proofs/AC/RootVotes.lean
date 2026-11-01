module
public import AvailableChainGeneric.Statements.AC.Votes
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import Mathlib.Data.Finset.Card -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.AC.Root

open AvailableChain
open AvailableChain.GridCO
open AvailableChain.Gen.Pure

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact vote_pool_eraseDups_nodup (xs.filter (fun b => !b == a))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/Schedule:99; same: Convert the cap test to two distinct HEADs;
record S1a:931. -/
theorem cap_pair_statement : CapPairStatement := by
  rw [CapPairStatement_def]
  intro n pool i
  have hcard : (seatVotes pool i).eraseDups.length = (seatVotes pool i).toFinset.card := by
    rw [← List.toFinset_card_of_nodup (vote_pool_eraseDups_nodup _)]
    congr 1
    ext o
    simp
  simp only [equivocates, hcard, decide_eq_true_eq, Nat.succ_le_iff]
  rw [Finset.one_lt_card]
  have hmem (o : Wire n HeadMode.root) : o ∈ (seatVotes pool i).toFinset ↔
      o ∈ pool ∧ headSeat? o = some i := by
    change o ∈ (pool.filter (fun o => headSeat? o == some i)).toFinset ↔ _
    simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq]
  simp only [hmem]
  constructor
  · rintro ⟨u, ⟨hu, hi⟩, v, ⟨hv, hj⟩, hne⟩
    exact ⟨u, hu, v, hv, hne, hi, hj⟩
  · rintro ⟨u, hu, v, hv, hne, hi, hj⟩
    exact ⟨u, ⟨hu, hi⟩, v, ⟨hv, hj⟩, hne⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/Schedule:99; same: Two distinct HEADs are the finite-pool cap;
record S1a:931. -/
theorem cap_pair : CapPairStatement := cap_pair_statement

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/AdoptionTransport:157; INTENTIONAL: Prove the local admission step;
record S1a:892,931. -/
theorem cap_vote_statement : CapVoteStatement := by
  rw [CapVoteStatement_def]
  intro p n st s i B hlo hhi
  dsimp only
  have hstep : admitVote p st (⟨.seat s i, .head B⟩ : Wire n HeadMode.root) =
      if s < (st.now / (4 * p.Δ)).toNat - 1 ||
          (st.now / (4 * p.Δ)).toNat < s ||
          decide ((⟨.seat s i, .head B⟩ : Wire n HeadMode.root) ∈ st.votes) ||
          equivocates (votesAt st s) i then st else
        { st with
          votes := st.votes ++ [⟨.seat s i, .head B⟩]
          voteStamp := st.voteStamp ++ [(⟨.seat s i, .head B⟩, st.now)] } := rfl
  rw [hstep]
  by_cases he : equivocates (votesAt st s) i = true
  · right
    simp [he]
  · left
    by_cases hm : (⟨.seat s i, .head B⟩ : Wire n HeadMode.root) ∈ st.votes
    · simp [hm]
    · simp [not_lt.mpr hlo, not_lt.mpr hhi, hm, he]

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/AdoptionTransport:157; INTENTIONAL: Separate admission from receipt timing;
record S1a:892,931. -/
theorem cap_vote : CapVoteStatement := cap_vote_statement

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_mem_seats {n : Nat} (pool : List (Wire n HeadMode.root)) (i : Fin n) :
    i ∈ (seats n pool).toFinset ↔ ∃ o ∈ pool, headSeat? o = some i := by
  change i ∈ (pool.filterMap headSeat?).dedup.toFinset ↔ _
  simp only [List.mem_toFinset, List.mem_dedup, List.mem_filterMap]

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_voterCount_card {n : Nat} (pool : List (Wire n HeadMode.root)) :
    voterCount pool = (seats n pool).toFinset.card := by
  exact (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_support_witness {n : Nat} (tree : List Block)
    (support : List (Wire n HeadMode.root)) (i : Fin n) (B : Block) :
    poolSupports tree support i B = true ↔
      ∃ o ∈ support, headSeat? o = some i ∧ voteSupports tree B o = true := by
  change (support.filter (fun o => headSeat? o == some i)).any (voteSupports tree B) = true ↔ _
  simp only [List.any_eq_true, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨o, ⟨ho, hi⟩, hb⟩
    exact ⟨o, ho, hi, hb⟩
  · rintro ⟨o, ho, hi, hb⟩
    exact ⟨o, ⟨ho, hi⟩, hb⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_support_ancestor {n : Nat} (tree : List Block)
    (o : Wire n HeadMode.root) {Y X : Block} (hYX : Block.Preceq Y X)
    (hX : voteSupports tree X o = true) : voteSupports tree Y o = true := by
  unfold voteSupports at hX ⊢
  cases ht : resolvedTarget? tree o with
  | none => simp [ht] at hX
  | some target =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hX ⊢
      exact ⟨hX.1, block_preceq_trans hYX hX.2⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_support_compatible {n : Nat} (tree : List Block)
    (o : Wire n HeadMode.root) {B C : Block} (hB : voteSupports tree B o = true)
    (hC : voteSupports tree C o = true) : Block.Compatible B C := by
  unfold voteSupports at hB hC
  cases ht : resolvedTarget? tree o with
  | none => simp [ht] at hB
  | some target =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hB hC
      exact block_compatible_of_common hB.2 hC.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_clean_unique {n : Nat} (raw : List (Wire n HeadMode.root)) (i : Fin n)
    (he : equivocates raw i = false) (u v : Wire n HeadMode.root) (hu : u ∈ raw) (hv : v ∈ raw)
    (hi : headSeat? u = some i) (hj : headSeat? v = some i) : u = v := by
  by_contra hne
  have := (cap_pair raw i).mpr ⟨u, hu, v, hv, hne, hi, hj⟩
  simp [he] at this

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_equivocates_mono {n : Nat} (xs ys : List (Wire n HeadMode.root)) (i : Fin n)
    (hsub : xs ⊆ ys) (he : equivocates xs i = true) : equivocates ys i = true := by
  obtain ⟨u, hu, v, hv, hne, hi, hj⟩ := (cap_pair xs i).mp he
  exact (cap_pair ys i).mpr ⟨u, hsub hu, v, hsub hv, hne, hi, hj⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_clean_subset {n : Nat} (xs ys : List (Wire n HeadMode.root)) (i : Fin n)
    (hsub : xs ⊆ ys) (he : equivocates ys i = false) : equivocates xs i = false := by
  cases hx : equivocates xs i with
  | false => rfl
  | true => have := vote_pool_equivocates_mono xs ys i hsub hx; simp [he] at this

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_equivocates_participant {n : Nat} (pool : List (Wire n HeadMode.root)) (i : Fin n)
    (he : equivocates pool i = true) : i ∈ (seats n pool).toFinset := by
  obtain ⟨u, hu, _, _, _, hi, _⟩ := (cap_pair pool i).mp he
  exact (vote_pool_mem_seats pool i).mpr ⟨u, hu, hi⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/Schedule:99; same: Use finite-pool participant and cap
facts; record S1a:931. -/
theorem vote_pool_seats_subset {n : Nat} (xs ys : List (Wire n HeadMode.root)) (hsub : xs ⊆ ys) :
    (seats n xs).toFinset ⊆ (seats n ys).toFinset := by
  intro i hi
  obtain ⟨o, ho, hs⟩ := (vote_pool_mem_seats xs i).mp hi
  exact (vote_pool_mem_seats ys i).mpr ⟨o, hsub ho, hs⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: DGF/Adoption:158; INTENTIONAL: Use the atomic backward pool premise;
record blueprint/02-clean.md:330–352. -/
theorem vote_pool_seats_backward {n : Nat} (xs ys : List (Wire n HeadMode.root))
    (hback : ∀ o ∈ ys, ∀ i, headSeat? o = some i →
      o ∈ xs ∨ equivocates xs i = true) :
    (seats n ys).toFinset ⊆ (seats n xs).toFinset := by
  intro i hi
  obtain ⟨o, ho, hs⟩ := (vote_pool_mem_seats ys i).mp hi
  rcases hback o ho i hs with hm | he
  · exact (vote_pool_mem_seats xs i).mpr ⟨o, hm, hs⟩
  · exact vote_pool_equivocates_participant xs i he

local notation "scoreVoters" =>
  (fun {n : Nat} (tree : List Block) (raw support : List (Wire n HeadMode.root)) (B : Block) =>
    Finset.filter (fun i => (equivocates raw i || poolSupports tree support i B) = true)
      (List.toFinset (seats n raw)))

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_score_card {n : Nat} (tree : List Block)
    (raw support : List (Wire n HeadMode.root)) (B : Block) :
    goldfishScore tree raw support B = (scoreVoters tree raw support B).card := by
  unfold goldfishScore goldfishScoreOn
  rw [← List.toFinset_card_of_nodup
    (List.Nodup.filter _ (show (seats n raw).Nodup from List.nodup_dedup _))]
  dsimp only
  rw [← List.toFinset_filter]
  congr 2
  apply List.filter_congr
  intro i _
  change _ = (equivocates raw i || (seatVotes support i).any (voteSupports tree B))
  apply congrArg (fun b => equivocates raw i || b)
  apply List.any_congr rfl
  intro o
  unfold voteSupports resolvedTarget?
  cases ht : headTarget? o with
  | none => rfl
  | some r =>
      change (match Block.findByRoot? tree r with
        | none => false
        | some target => decide (target ∈ tree) &&
            decide (target.slot ≤ (headLabel? o).getD 0) && Block.preceq B target) = _
      rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_plain_subset_score {n : Nat} (tree : List Block)
    (raw support : List (Wire n HeadMode.root)) (B : Block) (hsub : support ⊆ raw) :
    plainSupporters tree raw support B ⊆ scoreVoters tree raw support B := by
  intro i hi
  obtain ⟨_, he, hb⟩ := Finset.mem_filter.mp hi
  obtain ⟨o, ho, hs, _⟩ := (vote_pool_support_witness tree support i B).mp hb
  exact Finset.mem_filter.mpr ⟨(vote_pool_mem_seats raw i).mpr ⟨o, hsub ho, hs⟩,
    by simp [he, hb]⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
[helper] DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read the score support
incidence; record blueprint/02-clean.md:380–393. -/
theorem vote_pool_support_conflict {n : Nat} (tree : List Block)
    (raw support : List (Wire n HeadMode.root)) (i : Fin n) {X C : Block}
    (hsub : support ⊆ raw) (he : equivocates raw i = false)
    (hX : poolSupports tree support i X = true)
    (hc : Block.compatible X C = false) : poolSupports tree support i C = false := by
  cases hh : poolSupports tree support i C with
  | false => rfl
  | true =>
      obtain ⟨u, hu, hi, hb⟩ := (vote_pool_support_witness tree support i X).mp hX
      obtain ⟨v, hv, hj, hd⟩ := (vote_pool_support_witness tree support i C).mp hh
      have huv := vote_pool_clean_unique raw i he u v (hsub hu) (hsub hv) hi hj
      subst v
      have hcomp := vote_pool_support_compatible tree u hb hd
      change Block.compatible X C = true at hcomp
      simp [hc] at hcomp

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Share honest and rest counts
across denominator and score pools; record S1a:327–336. -/
theorem batch_counts_statement : BatchCountsStatement := by
  rw [BatchCountsStatement_def]
  intro n tree D raw support Hon h m X hraw hsupport hcard hclean hbatch hother hb
  have hHon : Hon ⊆ plainSupporters tree raw support X := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hclean i hi, hbatch i hi⟩
  have hHonD : Hon ⊆ (seats n D).toFinset := by
    intro i hi
    obtain ⟨o, ho, hs, _⟩ := (vote_pool_support_witness tree support i X).mp (hbatch i hi)
    exact (vote_pool_mem_seats D i).mpr ⟨o, hraw (hsupport ho), hs⟩
  have hDcard : voterCount D = ((seats n D).toFinset \ Hon).card + h := by
    rw [vote_pool_voterCount_card, ← Finset.card_sdiff_add_card_eq_card hHonD, hcard]
  have hD : voterCount D ≤ h + m := by omega
  have score_rest (C : Block)
      (hc : ∀ i ∈ Hon, poolSupports tree support i C = false) :
      goldfishScore tree raw support C ≤ ((seats n D).toFinset \ Hon).card := by
    rw [vote_pool_score_card]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hm, hv⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_sdiff.mpr ⟨vote_pool_seats_subset raw D hraw hm, ?_⟩
    intro hHonI
    simp [hclean i hHonI, hc i hHonI] at hv
  refine ⟨hHon, hD, ?_, ?_, ?_⟩
  · intro Y hYX
    have hHonY : Hon ⊆ plainSupporters tree raw support Y := by
      intro i hi
      obtain ⟨o, ho, hs, hv⟩ := (vote_pool_support_witness tree support i X).mp (hbatch i hi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hclean i hi,
        (vote_pool_support_witness tree support i Y).mpr
          ⟨o, ho, hs, vote_pool_support_ancestor tree o hYX hv⟩⟩
    have hscore : h ≤ goldfishScore tree raw support Y := by
      rw [← hcard, vote_pool_score_card]
      exact Finset.card_le_card
        (hHonY.trans (vote_pool_plain_subset_score tree raw support Y hsupport))
    have hlt := hb.lt
    exact ⟨hscore, by omega⟩
  · intro C hc
    exact (score_rest C (fun i hi => vote_pool_support_conflict tree raw support i
      hsupport (hclean i hi) (hbatch i hi) hc)).trans hother
  · intro C hc
    have hscore := score_rest C hc
    have hlt := hb.lt
    omega

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Use one shared count core;
record S1a:327–336. -/
theorem batch_counts : BatchCountsStatement := batch_counts_statement

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Honest support
replaces backward relay; record P3:2554–2562. -/
theorem transfer_n2_statement : TransferN2Statement := by
  rw [TransferN2Statement_def]
  intro n tree raw support Hon h a Q hsupport hcard hclean hbatch hother ha
  obtain ⟨hHon, hD, hpath, hconflict, _⟩ := batch_counts tree raw raw support Hon h a Q
    (fun _ hm => hm) hsupport hcard hclean hbatch hother ⟨ha⟩
  have hplain : h ≤ (plainSupporters tree raw support Q).card := by
    rw [← hcard]
    exact Finset.card_le_card hHon
  obtain ⟨hscore, hmajority⟩ := hpath Q (block_preceq_refl Q)
  refine ⟨hplain, hscore, hD, by omega, hconflict, hmajority, ?_⟩
  intro C hc
  have := hconflict C hc
  omega

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Count the full
honest batch without a source gate; record P3:2554–2562. -/
theorem transfer_n2 : TransferN2Statement := transfer_n2_statement

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210;
INTENTIONAL: Use candidate support incidence; record blueprint/02-clean.md:390–393. -/
theorem score_eq_on_statement : ScoreEqOnStatement := by
  rw [ScoreEqOnStatement_def]
  intro n tree tree' U U' support support' Cand hraw hextra hinc
  have hback : ∀ o ∈ U', ∀ i, headSeat? o = some i →
      o ∈ U ∨ equivocates U i = true := by
    intro o ho i hi
    by_cases hm : o ∈ U
    · exact Or.inl hm
    · exact Or.inr (hextra o ho i hi hm)
  have hseats : (seats n U).toFinset = (seats n U').toFinset :=
    Finset.Subset.antisymm (vote_pool_seats_subset U U' hraw) (vote_pool_seats_backward U U' hback)
  have hequiv (i : Fin n) : equivocates U i = equivocates U' i := by
    cases he : equivocates U i with
    | true => exact (vote_pool_equivocates_mono U U' i hraw he).symm
    | false =>
        cases he' : equivocates U' i with
        | false => rfl
        | true =>
            obtain ⟨u, hu, v, hv, hne, hi, hj⟩ := (cap_pair U' i).mp he'
            have huU := (hback u hu i hi).resolve_right (by simp [he])
            have hvU := (hback v hv i hj).resolve_right (by simp [he])
            exact False.elim (hne (vote_pool_clean_unique U i he u v huU hvU hi hj))
  refine ⟨hseats, hequiv, ?_, ?_⟩
  · rw [vote_pool_voterCount_card, vote_pool_voterCount_card, hseats]
  · intro B hB
    rw [vote_pool_score_card, vote_pool_score_card]
    congr 1
    ext i
    simp only [Finset.mem_filter, hseats, ← hequiv i]
    cases he : equivocates U i with
    | true => simp
    | false => simp only [Bool.false_or, hinc B hB i he]

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210;
INTENTIONAL: Candidate incidence preserves scores; record blueprint/02-clean.md:390–393. -/
theorem score_eq_on : ScoreEqOnStatement := score_eq_on_statement

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:112,152,169; DGF/Adoption:104,128,158,311;
INTENTIONAL: Combine pool transport and its count bounds;
record blueprint/02-clean.md:330–352. -/
theorem transfer_statement : TransferStatement := by
  rw [TransferStatement_def]
  intro n sourceTree targetTree P L U V B hPL hclean hforward hbackward hsupport hmajority
  have hPclean (i : Fin n) (hi : i ∈ (seats n P).toFinset) :
      equivocates P i = false := by
    obtain ⟨o, ho, hs⟩ := (vote_pool_mem_seats P i).mp hi
    exact vote_pool_clean_subset P L i hPL (hclean o ho i hs)
  have hsourceSet : scoreVoters sourceTree P P B = plainSupporters sourceTree P P B := by
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨hm, hv⟩ := Finset.mem_filter.mp hi
      have he := hPclean i hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, he, by simpa [he] using hv⟩
    · exact vote_pool_plain_subset_score sourceTree P P B (fun _ hm => hm)
  have hsource : goldfishScore sourceTree P P B =
      (plainSupporters sourceTree P P B).card := by
    rw [vote_pool_score_card, hsourceSet]
  have hUclean (o : Wire n HeadMode.root) (ho : o ∈ P) (i : Fin n) (hi : headSeat? o = some i) :
      equivocates U i = false := by
    have heL := hclean o ho i hi
    cases heU : equivocates U i with
    | false => rfl
    | true =>
        obtain ⟨u, hu, v, hv, hne, hs, ht⟩ := (cap_pair U i).mp heU
        have huL := (hbackward u hu i hs).resolve_right (by simp [heL])
        have hvL := (hbackward v hv i ht).resolve_right (by simp [heL])
        exact False.elim (hne (vote_pool_clean_unique L i heL u v huL hvL hs ht))
  have hplain : plainSupporters sourceTree P P B ⊆ plainSupporters targetTree U V B := by
    intro i hi
    obtain ⟨_, _, hb⟩ := Finset.mem_filter.mp hi
    obtain ⟨o, ho, hs, hv⟩ := (vote_pool_support_witness sourceTree P i B).mp hb
    have he := hUclean o ho i hs
    obtain ⟨hoV, hvT⟩ := (hforward o ho i hs hv).resolve_right (by simp [he])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, he,
      (vote_pool_support_witness targetTree V i B).mpr ⟨o, hoV, hs, hvT⟩⟩
  have hsourceL : plainSupporters sourceTree P P B ⊆ (seats n L).toFinset := by
    intro i hi
    obtain ⟨_, _, hb⟩ := Finset.mem_filter.mp hi
    obtain ⟨o, ho, hs, _⟩ := (vote_pool_support_witness sourceTree P i B).mp hb
    exact (vote_pool_mem_seats L i).mpr ⟨o, hPL ho, hs⟩
  have hUL := vote_pool_seats_backward L U hbackward
  have hcount : voterCount U ≤ voterCount L := by
    rw [vote_pool_voterCount_card, vote_pool_voterCount_card]
    exact Finset.card_le_card hUL
  have hplainCard := Finset.card_le_card hplain
  have hscore : (plainSupporters sourceTree P P B).card ≤
      goldfishScore targetTree U V B := by
    rw [vote_pool_score_card]
    exact Finset.card_le_card
      (hplain.trans (vote_pool_plain_subset_score targetTree U V B hsupport))
  have hconflict (C : Block) (hc : Block.compatible B C = false) :
      (plainSupporters sourceTree P P B).card + goldfishScore targetTree U V C ≤
        voterCount L := by
    have hdisjoint : Disjoint (plainSupporters sourceTree P P B)
        (scoreVoters targetTree U V C) := by
      apply Finset.disjoint_left.mpr
      intro i hi hci
      obtain ⟨_, he, hb⟩ := Finset.mem_filter.mp (hplain hi)
      have hn := vote_pool_support_conflict targetTree U V i hsupport he hb hc
      have hv := (Finset.mem_filter.mp hci).2
      simp [he, hn] at hv
    rw [vote_pool_score_card, vote_pool_voterCount_card, ← Finset.card_union_of_disjoint hdisjoint]
    apply Finset.card_le_card
    exact Finset.union_subset hsourceL (fun _ hi => hUL (Finset.mem_filter.mp hi).1)
  rw [hsource] at hmajority
  refine ⟨hplain, by omega, hscore, hconflict, hcount, by omega, ?_⟩
  intro C hc
  have := hconflict C hc
  omega

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:112,152,169; DGF/Adoption:104,128,158,311;
INTENTIONAL: Transport plain support and retain the score bounds;
record blueprint/02-clean.md:330–352. -/
theorem transfer : TransferStatement := transfer_statement

/-- [ROOT-DIGEST-2 W1; DC Goldfish.find?] Support has an explicit resolved-body witness. -/
theorem vote_support_body {n : Nat} (tree : List Block) (B : Block)
    (o : Wire n .root) : voteSupports tree B o = true ↔
      ∃ H, resolvedTarget? tree o = some H ∧ H ∈ tree ∧
        H.slot ≤ (headLabel? o).getD 0 ∧ Block.Preceq B H := by
  unfold voteSupports
  cases hr : resolvedTarget? tree o with
  | none => simp
  | some H => simp [Block.Preceq, and_assoc]

/-- [ROOT-DIGEST-2 W1; DC Goldfish.find?] Transport needs uniqueness on the larger domain. -/
theorem resolvedTarget_transport {n : Nat} (small large : List Block) (o : Wire n .root)
    (H : Block) (hs : small ⊆ large)
    (hu : ∀ A ∈ large, ∀ B ∈ large, A.root = B.root → A = B)
    (hh : resolvedTarget? small o = some H) : resolvedTarget? large o = some H := by
  unfold resolvedTarget? at hh ⊢
  cases ht : headTarget? o with
  | none => simp [ht] at hh
  | some r =>
      have hf : Block.findByRoot? small r = some H := by simpa [ht] using hh
      have hm := Block.findByRoot?_mem hf
      have he := Block.findByRoot?_root hf
      simpa [ht, he] using Block.findByRoot?_of_unique (hs hm) hu

end AvailableChain.Gen.AC.Root
