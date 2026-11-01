module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Nesting

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [GLY E-11; ACI step-3 note] Every stored target is below the
output.
This includes expired rows, so the predicate permits backward ticks. -/
def StoredTargetsBelowOutput (p : Params) (st : State p.n) : Prop :=
  ∀ ℓ ∈ st.base.obligations, Block.Preceq ℓ.1 st.base.stableRecord

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [Model/Store.lean:31] The initial store has no lease. -/
theorem storedTargetsBelowOutput_init (p : Params) :
    StoredTargetsBelowOutput p (initial p.n) := by
  intro ℓ hℓ
  exact False.elim (List.not_mem_nil hℓ)

/-- Ruling Y: reset stores have no obligations at any retained clock. -/
theorem storedTargetsBelowOutput_initialAt (p : Params) (t : Time) :
    StoredTargetsBelowOutput p (initialAt p.n t) := by
  intro ℓ hℓ
  exact False.elim (List.not_mem_nil hℓ)

/-- [Sleep v6; P24] Wipe keeps all target bounds, including expired rows. -/
theorem storedTargetsBelowOutput_wipe (p : Params) (st : State p.n) (w : Time)
    (h : StoredTargetsBelowOutput p st) : StoredTargetsBelowOutput p (wipe p st w) := h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Each stored target is below the output. -/
theorem storedTargetsBelowOutput_target (p : Params) (st : State p.n)
    (h : StoredTargetsBelowOutput p st) (row : Block × Nat × Time)
    (hr : row ∈ st.base.obligations) : Block.Preceq row.1 st.base.stableRecord :=
  h row hr

section StoreWrappers
attribute [local instance] GridCO.slowLeasePolicy

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A slow-policy gate keeps an old target or adds a
prefix of its result.
Source: AvailableChainGridCO/Proofs/StoreFacts.lean, `gateFrom_target_origin`. -/
theorem gateFrom_target_origin_slow (p : GridCO.Params) {n : Nat}
    (a : Block) (st : GridCO.State n .root) (r : Slot) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (@GridCO.gateFrom GridCO.slowLeasePolicy p n .root a st r).obligations) :
    (∃ k deadline, (B, k, deadline) ∈ st.obligations) ∨
      ∃ C, GridCO.confirmationFrom p a st r = some C ∧ Block.Preceq B C :=
  @GridCO.gateFrom_target_origin GridCO.slowLeasePolicy .root p n a st r B g d hm

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] [P3 §2 store wrapper] GridCO
`admitProposal_obligations` for the
FG-SA lease policy: a proposal admission keeps the obligations. The run
library may not cite GridCO proof constants (T7 used-constant guard). -/
theorem admitProposal_obligations_slow (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal p st o b raw).obligations = st.obligations :=
  GridCO.admitProposal_obligations p st o b raw

end StoreWrappers

-- Normalization can reset S to F. A compatible target below S is still below
-- that output: the other direction would give F ⪯ S.
private theorem target_below_normal {B F S : Block}
    (hB : Block.Preceq B S) (hF : Block.Compatible B F) :
    Block.Preceq B (if Block.preceq F S then S else F) := by
  split
  · exact hB
  · next h =>
    unfold Block.Compatible Block.compatible at hF
    rcases Bool.or_eq_true_iff.mp hF with hBF | hFB
    · exact hBF
    · exact False.elim (h (block_preceq_trans hFB hB))

private theorem storedTargets_normalize (p : Params) (st : State p.n)
    (hC : SACompat st) (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (normalizeS st) := by
  rw [normalizeS_fields]
  intro ℓ hℓ
  exact target_below_normal (hL ℓ hℓ) (hC.1 ℓ hℓ)

private theorem storedTargets_reconcile (p : Params) (st : State p.n)
    (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (reconcile st) := by
  intro ℓ hℓ
  rw [reconcile_obligations, List.mem_filter] at hℓ
  rw [reconcile_stable]
  exact target_below_normal (hL ℓ hℓ.1) hℓ.2

private theorem storedTargets_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he <;> rw [he] <;> exact hL

private theorem storedTargets_rows (p : Params) (rows : List (RowWire p.n))
    (st : State p.n) (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact hL
  | cons a rows ih => exact ih _ (storedTargets_row p st a hL)

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [Model/Handlers.lean:64–89; Proofs/Reconcile.lean:28,55]
Deliveries keep the target bound. Reconcile checks each surviving target. -/
theorem storedTargetsBelowOutput_process (p : Params) (st : State p.n) (o : Wire p.n)
    (hC : CStoreInv p st) (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (process p st o) := by
  unfold process
  cases o.decode with
  | none => exact hL
  | some input =>
    cases input with
    | vote s i b =>
      intro ℓ hℓ
      rw [admitHead_obligations] at hℓ
      rw [admitHead_base_stable]
      exact hL ℓ hℓ
    | row i body => exact storedTargets_row p st _ hL
    | block s N =>
      change StoredTargetsBelowOutput p (admitBlock p st s N)
      unfold admitBlock
      split
      · exact hL
      · cases parentFG st N.erase with
        | none => exact hL
        | some P =>
          dsimp only
          split
          · apply storedTargets_rows
            have hbase : ∀ (st' : State p.n) (o' : GridCO.Wire p.n .root)
                (b : Block) (raw : List (GridCO.HeadWire p.n .root)),
                st'.base = GridCO.admitProposal p.toParams.engine st.base o' b raw →
                StoredTargetsBelowOutput p st' := by
              intro st' o' b raw he ℓ hℓ
              rw [he, @GridCO.admitProposal_obligations GridCO.slowLeasePolicy] at hℓ
              rw [he, admitProposal_stable]
              exact hL ℓ hℓ
            split
            · exact hbase _ (baseProposal s N.erase N.raw N.support) N.erase
                (N.raw.map baseHead) rfl
            · exact storedTargets_reconcile p _
                (hbase _ (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) rfl)
          · exact hL


-- Renewal can change a deadline, but each target is old or is the written key.
private theorem writeKeys_targets {n : Nat} (v : GridCO.State n .root)
    (keys : List (Block × Nat)) (d : Time)
    (hL : ∀ ℓ ∈ v.obligations, Block.Preceq ℓ.1 v.stableRecord)
    (hk : ∀ key ∈ keys, Block.Preceq key.1 v.stableRecord) :
    ∀ ℓ ∈ (GridCO.writeKeys v keys d).obligations,
      Block.Preceq ℓ.1 (GridCO.writeKeys v keys d).stableRecord := by
  induction keys generalizing v with
  | nil => exact hL
  | cons key keys ih =>
    change ∀ ℓ ∈ (GridCO.writeKeys (GridCO.writeObligation v key.1 key.2 d) keys d).obligations,
      Block.Preceq ℓ.1
        (GridCO.writeKeys (GridCO.writeObligation v key.1 key.2 d) keys d).stableRecord
    apply ih
    · intro ℓ hℓ
      unfold GridCO.writeObligation at hℓ ⊢
      dsimp only at hℓ ⊢
      rcases List.mem_append.mp hℓ with hold | hnew
      · exact hL ℓ (List.mem_filter.mp hold).1
      · have he := List.mem_singleton.mp hnew
        subst ℓ
        exact hk key List.mem_cons_self
    · intro k hm
      exact hk k (List.mem_cons_of_mem key hm)

private theorem target_below_advance {B S C : Block}
    (hB : Block.Preceq B S) (hC : Block.Compatible B C) :
    Block.Preceq B (GridCO.advance S C) := by
  unfold GridCO.advance
  split
  · exact hB
  · next h =>
    unfold Block.Compatible Block.compatible at hC
    rcases Bool.or_eq_true_iff.mp hC with hBC | hCB
    · exact hBC
    · exact False.elim (h (block_preceq_trans hCB hB))

private theorem candidate_below_advance (S C : Block) :
    Block.Preceq C (GridCO.advance S C) := by
  unfold GridCO.advance
  split
  · assumption
  · exact block_preceq_refl _

private theorem saGate_targets (p : SA.Params) {n : Nat} (a : Block)
    (v : GridCO.State n .root) (s : Slot)
    (hL : ∀ ℓ ∈ v.obligations, Block.Preceq ℓ.1 v.stableRecord) :
    ∀ ℓ ∈ (SA.Root.gateFrom p a v s).obligations,
      Block.Preceq ℓ.1 (SA.Root.gateFrom p a v s).stableRecord := by
  cases hc : SA.Root.confirmationFrom p a v s with
  | none =>
    unfold SA.Root.gateFrom GridCO.gateFrom
    rw [show GridCO.confirmationFrom p.engine a v s = none from hc]
    exact hL
  | some C =>
    cases hg : v.obligations.any (fun (target, _, _) => !Block.compatible target C) with
    | true =>
      unfold SA.Root.gateFrom GridCO.gateFrom
      rw [show GridCO.confirmationFrom p.engine a v s = some C from hc]
      dsimp only
      rw [hg, ite_eq_left rfl]
      exact hL
    | false =>
      have he := @GridCO.gateFrom_eq_writeKeys GridCO.slowLeasePolicy .root p.engine n a v s C hc hg
      change SA.Root.gateFrom p a v s = _ at he
      rw [he]
      apply writeKeys_targets
      · intro ℓ hℓ
        apply target_below_advance (hL ℓ hℓ)
        have hguard := List.any_eq_false.mp hg ℓ hℓ
        change Block.compatible ℓ.1 C = true
        simpa using hguard
      · intro key hkey
        unfold GridCO.gateWriteKeys at hkey
        obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hkey
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hm
        have hBC : Block.Preceq b C := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
        exact block_preceq_trans hBC (candidate_below_advance v.stableRecord C)

private theorem storedTargets_gate (p : Params) (st : State p.n) (s : Slot)
    (hC : CStoreInv p st) (hN : NestOK st) (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (gateStep p st s) := by
  unfold gateStep
  dsimp only
  split
  · rw [normalizeS_fields]
    change ∀ ℓ ∈ st.base.obligations,
      Block.Preceq ℓ.1 (if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F)
    rw [ite_eq_left (show Block.preceq (eraseFG st.fg.F) st.base.stableRecord = true from hN)]
    exact hL
  · next hnew =>
    have hnone : GridCO.savedGenuine st.base s = none := Option.not_isSome_iff_eq_none.mp hnew
    split
    · apply storedTargets_normalize p _ (cstoreInv_gateUnjoined p st hC s hnone).saCompat
      exact hL
    · apply storedTargets_normalize p _ (cstoreInv_gateFresh p st hC s hnone).saCompat
      exact saGate_targets p.toParams (eraseFG st.fg.F) (actView st) s hL

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [Proofs/StoreInv.lean:278,428; Model/Clock.lean:28,40,57]
Expiry and release remove rows. A gate keeps the bound before and after normalization. -/
theorem storedTargetsBelowOutput_clock (p : Params) (st : State p.n) (t : Time)
    (hC : CStoreInv p st) (hN : NestOK st) (hL : StoredTargetsBelowOutput p st) :
    StoredTargetsBelowOutput p (clock p st t) := by
  have hpre : StoredTargetsBelowOutput p (clockPre p st t) := by
    intro ℓ hℓ
    rw [clockPre_stable]
    exact hL ℓ ((clockPre_obligations_sublist p st t).subset hℓ)
  unfold clock
  dsimp only
  split
  · apply storedTargets_gate p _ _ (cstoreInv_clockPre p st hC t) _ hpre
    unfold NestOK
    rw [clockPre_fg, clockPre_stable]
    exact hN
  · exact hpre

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [Statements/Invariants.lean:40] The bound on all rows implies
the live-row bound. -/
theorem leaseBelowOutputStore_of_storedTargetsBelowOutput
    (p : Params) (st : State p.n) (hL : StoredTargetsBelowOutput p st) :
    LeaseBelowOutputStore p st := by
  intro ℓ hℓ _
  exact hL ℓ hℓ

end AvailableChain.FGSA
end
