module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Restart
public import AvailableChainFGSA.Proofs.LeaseOutput
public import AvailableChainFGSARun.Proofs.RootLease
public import AvailableChainGeneric.Proofs.AC.RootSupport

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[bp bp.leaseOrigins.v1, clause (3)] Each non-genesis ancestor has a
lease at the same level with at least the descendant's deadline. -/
def AncestorDeadlines {n : Nat} (st : State n) : Prop :=
  ∀ K g deadline, (K, g, deadline) ∈ st.base.obligations →
    ∀ B, B ≠ .genesis → Block.Preceq B K →
      Gen.AC.Root.ProtectsUntil st.base B g deadline

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] Read the ancestor protection from the store predicate. -/
theorem AncestorDeadlines.protectsUntil {n : Nat} {st : State n}
    (h : AncestorDeadlines st) (K : Block) (g : Nat) (deadline : Time)
    (hr : (K, g, deadline) ∈ st.base.obligations) (B : Block)
    (hB : B ≠ .genesis) (hBK : Block.Preceq B K) :
    Gen.AC.Root.ProtectsUntil st.base B g deadline := h K g deadline hr B hB hBK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] Only the obligations field determines ancestor deadlines. -/
theorem ancestorDeadlines_of_obligations_eq {n : Nat} {st st' : State n}
    (he : st'.base.obligations = st.base.obligations) (h : AncestorDeadlines st) :
    AncestorDeadlines st' := by
  intro K g d hr B hB hBK
  rw [he] at hr
  obtain ⟨limit, hd, hm⟩ := h K g d hr B hB hBK
  exact ⟨limit, hd, he.symm ▸ hm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Store.lean:31] The initial store has no obligations. -/
theorem ancestorDeadlines_init (n : Nat) : AncestorDeadlines (initial n) := by
  intro K g d hr
  exact (List.not_mem_nil hr).elim

/-- The legacy initialAt store has no ancestor-deadline obligations. -/
theorem ancestorDeadlines_initialAt (n : Nat) (t : Time) :
    AncestorDeadlines (initialAt n t) := by
  intro K g deadline hrow
  exact (List.not_mem_nil hrow).elim

/-- Kept obligations retain every ancestor deadline through restart. -/
theorem ancestorDeadlines_acRestart (p : Params) (st : State p.n) (w : Time)
    (h : AncestorDeadlines st) : AncestorDeadlines (acRestart p st w) :=
  ancestorDeadlines_of_obligations_eq (acRestart_obligations p st w) h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Proofs/Reconcile.lean:28] Compatibility with finality is closed under
ancestors. Reconcile therefore keeps each ancestor of a surviving target. -/
theorem ancestorDeadlines_reconcile {n : Nat} (st : State n)
    (h : AncestorDeadlines st) : AncestorDeadlines (reconcile st) := by
  intro K g d hr B hB hBK
  rw [reconcile_obligations, List.mem_filter] at hr
  obtain ⟨limit, hd, hm⟩ := h K g d hr.1 B hB hBK
  refine ⟨limit, hd, ?_⟩
  rw [reconcile_obligations]
  exact List.mem_filter.mpr ⟨hm, block_compatible_of_preceq_compatible hBK hr.2⟩

private theorem ancestorDeadlines_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : AncestorDeadlines st) : AncestorDeadlines (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he <;> rw [he] <;> exact h

private theorem ancestorDeadlines_rows (p : Params) (rows : List (RowWire p.n))
    (st : State p.n) (h : AncestorDeadlines st) :
    AncestorDeadlines (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (ancestorDeadlines_row p st a h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Handlers.lean:64–89] Delivery keeps obligations, except for the
ancestor-closed reconcile filter. No store invariant premise is needed. -/
theorem ancestorDeadlines_process (p : Params) (st : State p.n) (o : Wire p.n)
    (h : AncestorDeadlines st) : AncestorDeadlines (process p st o) := by
  unfold process
  cases o.decode with
  | none => exact h
  | some input =>
    cases input with
    | vote s i b => exact ancestorDeadlines_of_obligations_eq (admitHead_obligations ..) h
    | row i body => exact ancestorDeadlines_row p st _ h
    | block s N =>
      change AncestorDeadlines (admitBlock p st s N)
      unfold admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply ancestorDeadlines_rows
            have hbase : ∀ (st' : State p.n) (o' : GridCO.Wire p.n .root)
                (b : Block) (raw : List (GridCO.HeadWire p.n .root)),
                st'.base = GridCO.admitProposal p.toParams.engine st.base o' b raw →
                AncestorDeadlines st' := by
              intro st' o' b raw he
              apply ancestorDeadlines_of_obligations_eq (st := st) _ h
              rw [he, admitProposal_obligations_slow]
            split
            · exact hbase _ (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map
                baseHead) rfl
            · exact ancestorDeadlines_reconcile _
                (hbase _ (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) rfl)
          · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Gen E-7] Expiry keeps the ancestor of each surviving row, because its
protected deadline is at least as late. -/
theorem ancestorDeadlines_expire {n : Nat} (st : State n) (t : Time)
    (h : AncestorDeadlines st) :
    AncestorDeadlines { st with base := GridCO.expire st.base t } := by
  intro K g d hr B hB hBK
  have hm := List.mem_filter.mp hr
  exact RootLease.root_expire_protectsUntil st.base B g d t
    (h K g d hm.1 B hB hBK) (of_decide_eq_true hm.2)

private theorem releaseCount_ancestor (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (r : Slot) (B K : Block) (hBK : Block.Preceq B K) :
    GridCO.releaseCount p st r B ≤ GridCO.releaseCount p st r K := by
  unfold GridCO.releaseCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro i _ hi
  obtain ⟨hne, ho⟩ := Bool.and_eq_true_iff.mp hi
  refine Bool.and_eq_true_iff.mpr ⟨hne, ?_⟩
  obtain ⟨o, hm, hc⟩ := List.any_eq_true.mp ho
  refine List.any_eq_true.mpr ⟨o, hm, ?_⟩
  cases ht : GridCO.resolvedHead? st o with
  | none => simp [ht] at hc
  | some target =>
    have hconf : ¬ Block.Compatible target B := by
      simpa [ht, Block.Compatible] using hc
    have hconf' := block_incompatible_of_preceq hconf hBK
    simpa [ht, Block.Compatible] using hconf'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Gen E-7; Model/Clock.lean:52] Release counts no more conflicts against
an ancestor than against its descendant. The active view needs no premise. -/
theorem ancestorDeadlines_release (p : SA.Params) {n : Nat} (st : State n) (r : Slot)
    (h : AncestorDeadlines st) :
    AncestorDeadlines (onView (fun v => SA.Root.release p v r) st) := by
  intro K g d hr B hB hBK
  have hm := List.mem_filter.mp hr
  have hc : GridCO.releaseCount p.engine (actView st) r K < g :=
    of_decide_eq_true hm.2
  exact RootLease.root_release_protectsUntil p.engine (actView st) r B g d
    (h K g d hm.1 B hB hBK)
    (lt_of_le_of_lt (releaseCount_ancestor p.engine (actView st) r B K hBK) hc)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Clock.lean:40–53] Expiry and release keep ancestor deadlines.
The freeze and early-cache steps keep the obligations field. -/
theorem ancestorDeadlines_clockPre (p : Params) (st : State p.n) (t : Time)
    (h : AncestorDeadlines st) : AncestorDeadlines (clockPre p st t) := by
  have hexp : AncestorDeadlines
      { st with base := GridCO.expire { st.base with now := t } t } :=
    ancestorDeadlines_expire { st with base := { st.base with now := t } } t h
  unfold clockPre
  dsimp only
  split <;> split <;> split
  all_goals first
    | apply ancestorDeadlines_release
      exact hexp
    | exact hexp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Clock.lean:57–62] A tick with no gate keeps ancestor deadlines. -/
theorem ancestorDeadlines_clock_offGate (p : Params) (st : State p.n) (t : Time)
    (hg : ¬ (0 ≤ t - 6 * p.Δ ∧
      t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat))
    (h : AncestorDeadlines st) : AncestorDeadlines (clock p st t) := by
  unfold clock
  rw [ite_eq_right (by simpa using hg)]
  exact ancestorDeadlines_clockPre p st t h

private theorem write_row_origin {n : Nat} (st : GridCO.State n .root)
    (b : Block) (g : Nat) (limit : Time) (row : Block × Nat × Time)
    (hm : row ∈ (GridCO.writeObligation st b g limit).obligations) :
    row ∈ st.obligations ∨ (row.1, row.2.1) = (b, g) ∧ row.2.2 = limit := by
  rcases List.mem_append.mp hm with hold | hnew
  · exact Or.inl (List.mem_filter.mp hold).1
  · have he := List.mem_singleton.mp hnew
    subst row
    have hlookup : GridCO.deadlineOf st b g =
        (st.obligations.find? (fun (target, level, _) => target == b && level == g)).map
          (fun row => row.2.2) := rfl
    cases hf : st.obligations.find? (fun (target, level, _) => target == b && level == g) with
    | none => exact Or.inr ⟨rfl, by simp [hlookup, hf]⟩
    | some row =>
      have hr := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      rcases row with ⟨target, level, d⟩
      obtain ⟨rfl, rfl⟩ : target = b ∧ level = g := by simpa using hp
      by_cases hd : d ≤ limit
      · exact Or.inr ⟨rfl, by simp [hlookup, hf, max_eq_right hd]⟩
      · left
        simpa [hlookup, hf, max_eq_left (le_of_not_ge hd)] using hr

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] Each written row is an old row or has a selected key and the new deadline.
Source: GridCO model `writeObligation` and `writeKeys`; local `write_row_origin`. -/
theorem writeKeys_deadline_cases {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (limit : Time) (row : Block × Nat × Time)
    (hm : row ∈ (GridCO.writeKeys st keys limit).obligations) :
    row ∈ st.obligations ∨ (row.1, row.2.1) ∈ keys ∧ row.2.2 = limit := by
  induction keys generalizing st with
  | nil => exact Or.inl hm
  | cons key keys ih =>
    rcases ih _ hm with hold | ⟨hk, hd⟩
    · rcases write_row_origin st key.1 key.2 limit row hold with hold | ⟨hk, hd⟩
      · exact Or.inl hold
      · exact Or.inr ⟨List.mem_cons.mpr (Or.inl hk), hd⟩
    · exact Or.inr ⟨List.mem_cons_of_mem key hk, hd⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] Public row cases for FG-SA gate writes. Keep the old name for existing proofs.
Source: `writeKeys_deadline_cases` in this file. -/
theorem writeKeys_row_cases {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (limit : Time) (row : Block × Nat × Time)
    (hm : row ∈ (GridCO.writeKeys st keys limit).obligations) :
    row ∈ st.obligations ∨ (row.1, row.2.1) ∈ keys ∧ row.2.2 = limit :=
  writeKeys_deadline_cases st keys limit row hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] A passed FG-SA gate equals the selected writes with the gate deadline.
Source: AvailableChainSA/Model/Protocol.lean, `gateFrom`; GridCO model `gateFrom`. -/
theorem gateFrom_eq_writeKeys_fgsa (p : SA.Params) {n : Nat}
    (a : Block) (st : GridCO.State n .root) (r : Slot) (C : Block)
    (hc : SA.Root.confirmationFrom p a st r = some C)
    (hguard : st.obligations.any (fun row => !Block.compatible row.1 C) = false) :
    SA.Root.gateFrom p a st r =
      GridCO.writeKeys { st with
        goldfishRecord := GridCO.advance st.goldfishRecord C
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root st r (some C)
        stableRecord := GridCO.advance st.stableRecord C }
        (@GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.engine n st r C)
        (SA.gateTime p r + SA.lifetime p) := by
  unfold SA.Root.gateFrom GridCO.gateFrom
  rw [show GridCO.confirmationFrom p.engine a st r = some C from hc]
  dsimp only
  rw [hguard]
  simp [@GridCO.writeKeys_def GridCO.slowLeasePolicy,
    @GridCO.gateWriteKeys_def GridCO.slowLeasePolicy .root, List.foldl_flatMap, List.foldl_map]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] All deadlines in an FG-SA base store are at most the given limit.
Source: AvailableChainGridCO/Proofs/Map.lean, `DeadlinesAtMost` (predicate body). -/
def DeadlinesAtMost {n : Nat} (st : GridCO.State n .root) (limit : Time) : Prop :=
  ∀ b g d, (b, g, d) ∈ st.obligations → d ≤ limit

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] Read the deadline bound as a statement about each row.
Source: `DeadlinesAtMost` in this file. -/
theorem DeadlinesAtMost_def {n : Nat} (st : GridCO.State n .root) (limit : Time) :
    DeadlinesAtMost st limit ↔ ∀ b g d, (b, g, d) ∈ st.obligations → d ≤ limit :=
  Iff.rfl

private theorem deadlineOf_le_fgsa {n : Nat} (st : GridCO.State n .root) (b : Block)
    (g : Nat) (limit : Time) (hbound : DeadlinesAtMost st limit) :
    (GridCO.deadlineOf st b g).getD limit ≤ limit := by
  unfold GridCO.deadlineOf
  cases hfind : st.obligations.find? (fun row => row.1 == b && row.2.1 == g) with
  | none => simp
  | some row =>
    have hmem : row ∈ st.obligations := List.mem_of_find?_eq_some hfind
    simpa [hfind] using hbound row.1 row.2.1 row.2.2 hmem

private theorem writeObligation_shape_fgsa {n : Nat} (st : GridCO.State n .root)
    (b : Block) (g : Nat) (limit : Time) (hbound : DeadlinesAtMost st limit) :
    (GridCO.writeObligation st b g limit).obligations =
      st.obligations.filter (fun row => !(row.1 == b && row.2.1 == g)) ++
        [(b, g, limit)] := by
  unfold GridCO.writeObligation
  simp only [max_eq_right (deadlineOf_le_fgsa st b g limit hbound)]

private theorem writeObligation_bound_fgsa {n : Nat} (st : GridCO.State n .root)
    (b : Block) (g : Nat) (limit : Time) (hbound : DeadlinesAtMost st limit) :
    DeadlinesAtMost (GridCO.writeObligation st b g limit) limit := by
  intro K level d hrow
  rw [writeObligation_shape_fgsa st b g limit hbound] at hrow
  rcases List.mem_append.mp hrow with hold | hnew
  · exact hbound K level d (List.mem_filter.mp hold).1
  · have he : (K, level, d) = (b, g, limit) := List.mem_singleton.mp hnew
    cases he
    exact le_refl _

private theorem write_preserves_limit_row_fgsa {n : Nat} (st : GridCO.State n .root)
    (K : Block) (g : Nat) (limit : Time) (key : Block × Nat)
    (hbound : DeadlinesAtMost st limit) (hrow : (K, g, limit) ∈ st.obligations) :
    (K, g, limit) ∈ (GridCO.writeObligation st key.1 key.2 limit).obligations := by
  rw [writeObligation_shape_fgsa st key.1 key.2 limit hbound]
  apply List.mem_append.mpr
  by_cases hkey : (K, g) = key
  · exact Or.inr (by simp [← hkey])
  · apply Or.inl
    apply List.mem_filter.mpr
    refine ⟨hrow, ?_⟩
    have hne : K ≠ key.1 ∨ g ≠ key.2 := by
      rcases key with ⟨b, level⟩
      simpa only [Prod.mk.injEq, not_and_or] using hkey
    rcases hne with hne | hne <;> simp [hne]

private theorem writeKeys_preserves_limit_row_fgsa {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit) (hrow : (K, g, limit) ∈ st.obligations) :
    (K, g, limit) ∈ (GridCO.writeKeys st keys limit).obligations := by
  induction keys generalizing st with
  | nil => exact hrow
  | cons key keys ih =>
    exact ih (GridCO.writeObligation st key.1 key.2 limit)
      (writeObligation_bound_fgsa st key.1 key.2 limit hbound)
      (write_preserves_limit_row_fgsa st K g limit key hbound hrow)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[helper] A bounded write installs each selected key at the given deadline.
Source: AvailableChainGridCO/Proofs/Map.lean, `writeKeys_mem_of_key` (local model proof). -/
theorem writeKeys_mem_of_key_fgsa {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit) (hkey : (K, g) ∈ keys) :
    (K, g, limit) ∈ (GridCO.writeKeys st keys limit).obligations := by
  induction keys generalizing st with
  | nil => simp at hkey
  | cons key keys ih =>
    rcases List.mem_cons.mp hkey with hfirst | htail
    · subst key
      apply writeKeys_preserves_limit_row_fgsa (GridCO.writeObligation st K g limit)
        keys K g limit (writeObligation_bound_fgsa st K g limit hbound)
      rw [writeObligation_shape_fgsa st K g limit hbound]
      simp
    · exact ih (GridCO.writeObligation st key.1 key.2 limit)
        (writeObligation_bound_fgsa st key.1 key.2 limit hbound) htail

private theorem writeKeys_protects {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (limit : Time) (B : Block) (g : Nat) (d : Time)
    (hu : Gen.AC.Root.UniqueLeaseKeys st) (h : Gen.AC.Root.ProtectsUntil st B g d) :
    Gen.AC.Root.ProtectsUntil (GridCO.writeKeys st keys limit) B g d := by
  induction keys generalizing st with
  | nil => exact h
  | cons key keys ih =>
    exact ih _ (RootLease.root_write_unique_keys st key.1 key.2 limit hu)
      (RootLease.root_write_protectsUntil st B key.1 g key.2 d limit hu h)

private theorem writeKeys_key {n : Nat} (st : GridCO.State n .root)
    (keys : List (Block × Nat)) (limit : Time) (B : Block) (g : Nat)
    (hu : Gen.AC.Root.UniqueLeaseKeys st) (hk : (B, g) ∈ keys) :
    Gen.AC.Root.ProtectsUntil (GridCO.writeKeys st keys limit) B g limit := by
  induction keys generalizing st with
  | nil => simp at hk
  | cons key keys ih =>
    have hu' := RootLease.root_write_unique_keys st key.1 key.2 limit hu
    rcases List.mem_cons.mp hk with he | hk
    · subst key
      apply writeKeys_protects _ keys limit B g limit hu'
      exact ⟨_, le_max_right _ _, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))⟩
    · exact ih _ hu' hk

private theorem writeKeys_ancestorDeadlines {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time) (hu : Gen.AC.Root.UniqueLeaseKeys st.base)
    (h : AncestorDeadlines st)
    (hkeys : ∀ K g, (K, g) ∈ keys → ∀ B, B ≠ .genesis → Block.Preceq B K →
      (B, g) ∈ keys) :
    AncestorDeadlines { st with base := GridCO.writeKeys st.base keys limit } := by
  intro K g d hr B hB hBK
  rcases writeKeys_deadline_cases st.base keys limit (K, g, d) hr with hold | ⟨hk, hd⟩
  · exact writeKeys_protects st.base keys limit B g d hu (h K g d hold B hB hBK)
  · change d = limit at hd
    subst d
    exact writeKeys_key st.base keys limit B g hu (hkeys K g hk B hB hBK)

private theorem prefixSupport_ancestor (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (r : Slot) (B K : Block) (hBK : Block.Preceq B K) :
    GridCO.prefixSupport p st r K ≤ GridCO.prefixSupport p st r B := by
  exact Gen.AC.Root.goldfishScoreOn_antitone _ _ _ _ B K hBK

private theorem admissionLevels_ancestor (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (r : Slot) (B K : Block) (hBK : Block.Preceq B K) :
    ∀ g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p n .root st r K,
      g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p n .root st r B := by
  intro g hg
  have hs : GridCO.slowEligible p st r K = true → GridCO.slowEligible p st r B = true := by
    intro hslow
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hslow
    refine Bool.and_eq_true_iff.mpr ⟨hlen, List.all_eq_true.mpr ?_⟩
    intro j hj
    have hc := List.all_eq_true.mp hall j hj
    cases he : GridCO.savedGenuine st (r - (j + 1)) with
    | none => simp [he] at hc
    | some result =>
      cases result with
      | none => simp [he] at hc
      | some C =>
        have hKC : Block.preceq K C = true := by simpa only [he] using hc
        have hBC : Block.preceq B C = true := block_preceq_trans hBK hKC
        simpa only [he] using hBC
  change g ∈ (if _ then [_] else []) at hg ⊢
  split at hg
  · rename_i ht
    have hb : (decide (GridCO.releaseThreshold p ≤ GridCO.prefixSupport p st r B) ||
        GridCO.slowEligible p st r B) = true := by
      rcases Bool.or_eq_true_iff.mp ht with hf | hslow
      · exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true
          (le_trans (of_decide_eq_true hf) (prefixSupport_ancestor p st r B K hBK))))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (hs hslow))
    simpa [hb] using hg
  · simp at hg

private theorem gateWriteKeys_ancestor (p : Params) (st : State p.n) (r : Slot) (C : Block)
    (hC : CStoreInv p st) :
    ∀ K g, (K, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView st) r C → ∀ B, B ≠ .genesis → Block.Preceq B K →
      (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
        (actView st) r C := by
  intro K g hk B hB hBK
  obtain ⟨K', hK', hm⟩ := List.mem_flatMap.mp hk
  obtain ⟨g', hg', he⟩ := List.mem_map.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hK := List.mem_filter.mp hK'
  have hKC := (Bool.and_eq_true_iff.mp hK.2).2
  apply List.mem_flatMap.mpr
  refine ⟨B, List.mem_filter.mpr
    ⟨actView_ancestor_closed p st hC hK.1 hBK, ?_⟩, ?_⟩
  · simp [hB, show Block.preceq B C = true from block_preceq_trans hBK hKC]
  · exact List.mem_map.mpr
      ⟨g', admissionLevels_ancestor p.toParams.engine (actView st) r B K' hBK g' hg', rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Clock.lean:28; Gen E-7] The anchored gate keeps ancestor deadlines.
`CStoreInv.leaseKeys` supplies unique keys; `actView_ancestor_closed` supplies
prefix closure. No time bound is needed: renewal uses `max`, and Gen E-7
keeps every old protected deadline even at a backward tick. -/
theorem ancestorDeadlines_gateStep (p : Params) (st : State p.n) (s : Slot)
    (hC : CStoreInv p st) (h : AncestorDeadlines st) :
    AncestorDeadlines (gateStep p st s) := by
  have hnorm : ∀ st' : State p.n, AncestorDeadlines st' → AncestorDeadlines (normalizeS st') := by
    intro st' hh
    apply ancestorDeadlines_of_obligations_eq (st := st') _ hh
    rw [normalizeS_fields]
  unfold gateStep
  dsimp only
  apply hnorm
  split
  · exact h
  · split
    · exact h
    · have hu : Gen.AC.Root.UniqueLeaseKeys (actView st) := by
        intro x hx y hy he
        exact List.inj_on_of_nodup_map hC.leaseKeys.1 hx hy (Prod.mk.inj he).1
      cases hc : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s with
      | none =>
        apply ancestorDeadlines_of_obligations_eq (st := st) _ h
        change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).obligations = _
        unfold SA.Root.gateFrom GridCO.gateFrom
        rw [show GridCO.confirmationFrom p.toParams.engine
          (eraseFG st.fg.F) (actView st) s = none from hc]
        rfl
      | some C =>
        cases hg : (actView st).obligations.any
            (fun (target, _, _) => !Block.compatible target C) with
        | true =>
          apply ancestorDeadlines_of_obligations_eq (st := st) _ h
          change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).obligations = _
          unfold SA.Root.gateFrom GridCO.gateFrom
          rw [show GridCO.confirmationFrom p.toParams.engine
            (eraseFG st.fg.F) (actView st) s = some C from hc]
          dsimp only
          rw [hg, ite_eq_left rfl]
          rfl
        | false =>
          let v : GridCO.State p.n .root := { actView st with
            goldfishRecord := GridCO.advance (actView st).goldfishRecord C
            genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root
              (actView st) s (some C)
            stableRecord := GridCO.advance (actView st).stableRecord C }
          let keys := @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView st) s C
          let limit := GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine
          have hw : AncestorDeadlines { st with base := GridCO.writeKeys v keys limit } :=
            writeKeys_ancestorDeadlines { st with base := v } keys limit hu h
              (gateWriteKeys_ancestor p st s C hC)
          apply ancestorDeadlines_of_obligations_eq
            (st := { st with base := GridCO.writeKeys v keys limit }) _ hw
          change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).obligations = _
          -- Unfold the model gate as in the `true` branch (no GridCO proof constant).
          unfold SA.Root.gateFrom GridCO.gateFrom
          rw [show GridCO.confirmationFrom p.toParams.engine
            (eraseFG st.fg.F) (actView st) s = some C from hc]
          dsimp only
          rw [hg]
          simp [v, keys, limit, @GridCO.writeKeys_def GridCO.slowLeasePolicy,
            @GridCO.gateWriteKeys_def GridCO.slowLeasePolicy .root,
            List.foldl_flatMap, List.foldl_map]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[Model/Clock.lean:57–62] Every tick keeps ancestor deadlines.
`cstoreInv_clockPre` supplies the gate's structural premises. -/
theorem ancestorDeadlines_clock (p : Params) (st : State p.n) (t : Time)
    (hC : CStoreInv p st) (h : AncestorDeadlines st) :
    AncestorDeadlines (clock p st t) := by
  unfold clock
  dsimp only
  split
  · exact ancestorDeadlines_gateStep p _ _ (cstoreInv_clockPre p st hC t)
      (ancestorDeadlines_clockPre p st t h)
  · exact ancestorDeadlines_clockPre p st t h

end AvailableChain.FGSA
end
