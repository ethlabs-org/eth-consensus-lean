module
public import AvailableChainFGSARun.Proofs.HeadIdentity
public import AvailableChainFGSA.Proofs.HeadDomain -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.AC.RootVotes
public import AvailableChainFGSA.Proofs.Head.Pool

public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A locally unique domain resolves its subtrees exactly. -/
theorem findByRoot_subtree (domain tree : List Block) (hs : tree ⊆ domain)
    (hu : ∀ A ∈ domain, ∀ B ∈ domain, A.root = B.root → A = B) (r : BlockId) :
    Block.findByRoot? tree r =
      (Block.findByRoot? domain r).filter (fun B => decide (B ∈ tree)) := by
  cases hd : Block.findByRoot? domain r with
  | none =>
    cases ht : Block.findByRoot? tree r with
    | none => rfl
    | some B =>
      have hm := Block.findByRoot?_mem ht
      have he := Block.findByRoot?_root ht
      have h := Block.findByRoot?_of_unique (hs hm) hu
      rw [he, hd] at h
      cases h
  | some B =>
    by_cases hm : B ∈ tree
    · have h := Block.findByRoot?_of_unique hm (fun A hA C hC => hu A (hs hA) C (hs hC))
      rw [Block.findByRoot?_root hd] at h
      simp [h, hm, Option.filter]
    · have hn : Block.findByRoot? tree r = none := by
        cases ht : Block.findByRoot? tree r with
        | none => rfl
        | some C =>
          have hc := Block.findByRoot?_mem ht
          have he := Block.findByRoot?_unique hd (hs hc) (Block.findByRoot?_root ht)
          exact (hm (he ▸ hc)).elim
      simp [hn, hm, Option.filter]

/-- [ROOT-DIGEST-2 W2; DC Goldfish] A locally unique domain gives the same active score. -/
theorem goldfishScoreOn_subtree {n : Nat} (domain tree : List Block) (hs : tree ⊆ domain)
    (hu : ∀ A ∈ domain, ∀ B ∈ domain, A.root = B.root → A = B)
    (raw sup : List (GridCO.Wire n .root)) (B : Block) :
    GridCO.goldfishScoreOn domain tree raw sup B = GridCO.goldfishScore tree raw sup B := by
  unfold GridCO.goldfishScore GridCO.goldfishScoreOn
  congr 2
  funext i
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes sup i).any f)
  funext o
  cases ht : GridCO.headTarget? o with
  | none => rfl
  | some r =>
    change (match Block.findByRoot? domain r with
      | none => false
      | some C => decide (C ∈ tree) && decide (C.slot ≤ (GridCO.headLabel? o).getD 0) &&
        Block.preceq B C) =
      (match Block.findByRoot? tree r with
      | none => false
      | some C => decide (C ∈ tree) && decide (C.slot ≤ (GridCO.headLabel? o).getD 0) &&
        Block.preceq B C)
    rw [findByRoot_subtree domain tree hs hu r]
    cases hd : Block.findByRoot? domain r with
    | none => rfl
    | some C => by_cases hm : C ∈ tree <;> simp [Option.filter, hm]

/-- [ROOT-DIGEST-2 W2; DC read metadata] The pre-clock stage retains the cumulative domain. -/
theorem clockPre_headDomain (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.headDomain = st.base.headDomain := by
  unfold clockPre
  dsimp only
  split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W2; DC Goldfish] The pinned active score has the ordinary tree formula. -/
theorem actView_score (p : Params) (st : State p.n) (h : CStoreInv p st)
    (hd : st.base.headDomain = none) (raw sup : List (GridCO.Wire p.n .root)) (B : Block) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree (actView st)) (actView st).blocks raw sup B =
      GridCO.goldfishScore (actView st).blocks raw sup B := by
  rw [actView_resolutionTree]
  change GridCO.goldfishScoreOn (st.base.headDomain.getD st.base.blocks) _ _ _ _ = _
  rw [hd]
  exact goldfishScoreOn_subtree st.base.blocks (actView st).blocks
    (fun _ hA => (List.mem_filter.mp hA).1) (baseBlocks_rootInj p st h) raw sup B

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A known active body resolves in the pinned domain. -/
theorem actView_resolve_of_mem (p : Params) (st : State p.n) (h : CStoreInv p st)
    (hd : st.base.headDomain = none) {B : Block} (hB : B ∈ (actView st).blocks)
    (s : Slot) (i : Fin p.n) :
    GridCO.resolvedHead? (actView st) ⟨.seat s i, .head B.root⟩ = some B := by
  have hm := (List.mem_filter.mp hB).1
  have hf := Block.findByRoot?_of_unique hm (baseBlocks_rootInj p st h)
  change ((Block.findByRoot? (GridCO.resolutionTree (actView st)) B.root).bind fun C =>
    if C ∈ (actView st).blocks then some C else none) = some B
  rw [actView_resolutionTree]
  change ((Block.findByRoot? (st.base.headDomain.getD st.base.blocks) B.root).bind fun C =>
    if C ∈ (actView st).blocks then some C else none) = some B
  rw [hd]
  change ((Block.findByRoot? st.base.blocks B.root).bind fun C =>
    if C ∈ (actView st).blocks then some C else none) = some B
  rw [hf]
  exact ite_eq_left hB

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A generic support lookup retains its signed root. -/
theorem resolvedTarget_root {n : Nat} (tree : List Block) (o : GridCO.Wire n .root)
    {B : Block} (h : Gen.AC.Root.resolvedTarget? tree o = some B) :
    GridCO.headTarget? o = some B.root := by
  obtain ⟨r, ht, hb⟩ := Option.bind_eq_some_iff.mp h
  simpa only [Block.findByRoot?_root hb] using ht

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A stored body gives the unique support lookup. -/
theorem resolvedTarget_of_mem {n : Nat} (tree : List Block)
    (hu : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B)
    (o : GridCO.Wire n .root) {B : Block} (hB : B ∈ tree)
    (ht : GridCO.headTarget? o = some B.root) :
    Gen.AC.Root.resolvedTarget? tree o = some B := by
  unfold Gen.AC.Root.resolvedTarget?
  rw [ht]
  exact Block.findByRoot?_of_unique hB hu

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A cumulative store resolves a known root. -/
theorem base_resolve_target (p : Params) (st : State p.n) (h : CStoreInv p st)
    (hd : st.base.headDomain = none) (o : GridCO.Wire p.n .root)
    {B : Block} (hB : B ∈ st.base.blocks) (ht : GridCO.headTarget? o = some B.root) :
    GridCO.resolvedHead? st.base o = some B := by
  have hf := Block.findByRoot?_of_unique hB (baseBlocks_rootInj p st h)
  change ((GridCO.headTarget? o).bind fun r =>
    (Block.findByRoot? (st.base.headDomain.getD st.base.blocks) r).bind fun C =>
      if C ∈ st.base.blocks then some C else none) = some B
  rw [ht, hd]
  change ((Block.findByRoot? st.base.blocks B.root).bind fun C =>
    if C ∈ st.base.blocks then some C else none) = some B
  rw [hf]
  exact ite_eq_left hB

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] Active membership keeps the cumulative resolution. -/
theorem actView_resolve_target (p : Params) (st : State p.n) (h : CStoreInv p st)
    (hd : st.base.headDomain = none) (o : GridCO.Wire p.n .root)
    {B : Block} (hB : B ∈ (actView st).blocks) (ht : GridCO.headTarget? o = some B.root) :
    GridCO.resolvedHead? (actView st) o = some B := by
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hB
  rw [actView_resolvedHead, base_resolve_target p st h hd o hm ht]
  simp only [Option.filter, ha, ite_true]

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree; S2] Prepared stores retain named origins. -/
theorem clock_stored_block_eq {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (i j : Nat) (x y : V) (t u : Time)
    {A B : Block} (hA : A ∈ (clock p (rho.stateBefore E i x).st t).base.blocks)
    (hB : B ∈ (clock p (rho.stateBefore E j y).st u).base.blocks)
    (he : A.root = B.root) : A = B := by
  rw [clock_base_blocks] at hA hB
  exact stored_block_eq_of_root_eq E rho hr i j x y hA hB he

/-- [ROOT-DIGEST-2 W2; DC Goldfish.Confirmation] Positive clean support gives a resolved
body, its slot bound, and its original early block stamp. -/
theorem prefixSupport_body (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (B : Block) (hscore : 0 < SA.Root.prefixSupport p.toParams v s B) :
    ∃ o K, o ∈ GridCO.cleanSupport p.toParams.engine v s ∧
      GridCO.resolvedHead? v o = some K ∧ K ∈ v.blocks ∧ K.slot ≤ s ∧
      Block.Preceq B K ∧ GridCO.stampBlock v K < SA.earlyTime p.toParams s := by
  unfold SA.Root.prefixSupport GridCO.prefixSupport GridCO.goldfishScoreOn at hscore
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp hscore)
  have hplain := (List.mem_filter.mp hk).2
  rw [fgsa_cleanSupport_no_equivocation p v s k, Bool.false_or] at hplain
  obtain ⟨o, ho, htarget⟩ := List.any_eq_true.mp hplain
  have hclean := (List.mem_filter.mp ho).1
  have hearly := (List.mem_filter.mp hclean).1
  have hlabel : GridCO.headLabel? o = some s :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
  cases ht : GridCO.headTarget? o with
  | none => simp only [ht, Bool.false_eq_true] at htarget
  | some r =>
    rw [ht] at htarget
    change (match GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
      | none => false
      | some C => decide (C ∈ v.blocks) &&
        decide (C.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B C) = true at htarget
    cases hf : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
    | none => simp only [hf, Bool.false_eq_true] at htarget
    | some K =>
      rw [hf] at htarget
      have hp := (Bool.and_eq_true_iff.mp htarget).2
      obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp htarget).1
      have hres : GridCO.resolvedHead? v o = some K := by
        change ((GridCO.headTarget? o).bind fun r =>
          (GridCO.resolveTarget .root (GridCO.resolutionTree v) r).bind fun C =>
            if C ∈ v.blocks then some C else none) = some K
        rw [ht]
        change ((GridCO.resolveTarget .root (GridCO.resolutionTree v) r).bind fun C =>
          if C ∈ v.blocks then some C else none) = some K
        rw [hf]
        exact ite_eq_left (of_decide_eq_true hm)
      have hr := (List.mem_filter.mp hearly).2
      unfold GridCO.resolvedBefore at hr
      rw [hres] at hr
      refine ⟨o, K, hclean, hres, of_decide_eq_true hm, ?_, hp, ?_⟩
      · simpa only [hlabel, Option.getD_some, decide_eq_true_eq] using hs
      · exact of_decide_eq_true (Bool.and_eq_true_iff.mp hr).2

/-- [ROOT-DIGEST-2 W2; DC Goldfish.Confirmation] A nonempty confirmation has an actual
resolved supporting body and its original early block stamp. -/
theorem confirmation_support_body (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (a B : Block) (h : SA.Root.confirmationFrom p.toParams a v s = some B) :
    ∃ o K, o ∈ GridCO.cleanSupport p.toParams.engine v s ∧
      GridCO.resolvedHead? v o = some K ∧ K ∈ v.blocks ∧ K.slot ≤ s ∧
      Block.Preceq B K ∧ GridCO.stampBlock v K < SA.earlyTime p.toParams s := by
  have hscore : 0 < SA.Root.prefixSupport p.toParams v s B := by
    have hex : ∃ C, GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s C ∧ some C = some B := by
      change (if _ then some _ else none) = some B at h
      split at h
      · exact ⟨_, ‹_›, h⟩
      · contradiction
    obtain ⟨C, hc, he⟩ := hex
    have he' := Option.some.inj he
    subst C
    omega
  exact prefixSupport_body p v s B hscore

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A state resolution retains the domain lookup. -/
theorem resolvedHead_target {n : Nat} (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    {B : Block} (h : GridCO.resolvedHead? v o = some B) :
    Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree v) o = some B := by
  change ((GridCO.headTarget? o).bind fun r =>
    (Block.findByRoot? (GridCO.resolutionTree v) r).bind fun C =>
      if C ∈ v.blocks then some C else none) = some B at h
  obtain ⟨r, ht, hh⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨C, hc, he⟩ := Option.bind_eq_some_iff.mp hh
  split at he
  · cases he
    exact Option.bind_eq_some_iff.mpr ⟨r, ht, hc⟩
  · contradiction

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] Lookup and membership are the two resolution checks. -/
theorem resolvedHead_of_lookup {n : Nat} (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) {B : Block}
    (hlookup : Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree v) o = some B)
    (hm : B ∈ v.blocks) : GridCO.resolvedHead? v o = some B := by
  obtain ⟨r, ht, hf⟩ := Option.bind_eq_some_iff.mp hlookup
  change ((GridCO.headTarget? o).bind fun r =>
    (Block.findByRoot? (GridCO.resolutionTree v) r).bind fun C =>
      if C ∈ v.blocks then some C else none) = some B
  rw [ht]
  change ((Block.findByRoot? (GridCO.resolutionTree v) r).bind fun C =>
    if C ∈ v.blocks then some C else none) = some B
  rw [hf]
  exact ite_eq_left hm

/-- [ROOT-DIGEST-2 W2; DC Goldfish.Confirmation] Clean votes already resolve inside the
state's block tree. Their domain score therefore keeps the active score exactly. -/
theorem cleanSupport_domain_score (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (B : Block) :
    SA.Root.prefixSupport p.toParams v s B =
      GridCO.goldfishScore (GridCO.resolutionTree v)
        (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s)
        B := by
  unfold SA.Root.prefixSupport GridCO.prefixSupport GridCO.goldfishScore GridCO.goldfishScoreOn
  congr 2
  funext i
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor <;> rintro ⟨o, ho, hval⟩ <;> refine ⟨o, ho, ?_⟩
  all_goals
    have hc := (List.mem_filter.mp ho).1
    have hr := (List.mem_filter.mp (List.mem_filter.mp hc).1).2
    unfold GridCO.resolvedBefore at hr
    cases hres : GridCO.resolvedHead? v o with
    | none => simp only [hres, Bool.false_eq_true] at hr
    | some H =>
      have hm := resolvedHead_mem v o hres
      have hd := resolvedHead_target v o hres
      obtain ⟨r, ht, hf⟩ := Option.bind_eq_some_iff.mp hd
      have hdomain := Block.findByRoot?_mem hf
      simp only [ht, GridCO.resolveTarget, hf, hm, hdomain, decide_true, Bool.true_and] at hval ⊢
      exact hval

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] Local admitted uniqueness identifies an active
lookup in the active block tree as well as in its pinned domain. -/
theorem actView_target_of_resolvedHead (p : Params) (st : State p.n) (h : CStoreInv p st)
    (o : GridCO.Wire p.n .root) {B : Block}
    (hr : GridCO.resolvedHead? (actView st) o = some B) :
    Gen.AC.Root.resolvedTarget? (actView st).blocks o = some B :=
  resolvedTarget_of_mem _ (fun A hA C hC =>
    baseBlocks_rootInj p st h A (List.mem_filter.mp hA).1 C (List.mem_filter.mp hC).1)
    o (resolvedHead_mem _ o hr) (resolvedHead_root _ o hr)

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A support lookup returns a member of its own domain. -/
theorem resolvedTarget_mem {n : Nat} (tree : List Block) (o : GridCO.Wire n .root)
    {B : Block} (h : Gen.AC.Root.resolvedTarget? tree o = some B) : B ∈ tree := by
  obtain ⟨_, _, hb⟩ := Option.bind_eq_some_iff.mp h
  exact Block.findByRoot?_mem hb

/-- [ROOT-DIGEST-2 W2; DC Goldfish] A resolved active supporter also supports in the
pinned domain. Local admitted uniqueness identifies the two lookup results. -/
theorem actView_support_in_domain (p : Params) (st : State p.n) (hi : CStoreInv p st)
    (o : GridCO.Wire p.n .root) {B H : Block}
    (hr : GridCO.resolvedHead? (actView st) o = some H)
    (hs : Gen.AC.Root.voteSupports (actView st).blocks B o = true) :
    Gen.AC.Root.voteSupports (GridCO.resolutionTree (actView st)) B o = true := by
  rw [Gen.AC.Root.voteSupports_def, actView_target_of_resolvedHead p st hi o hr] at hs
  have hd := resolvedHead_target _ o hr
  exact (Gen.AC.Root.vote_support_body _ _ _).mpr
    ⟨H, hd, resolvedTarget_mem _ o hd,
      of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hs).1).2,
      (Bool.and_eq_true_iff.mp hs).2⟩

end AvailableChain.FGSA.Run
end
