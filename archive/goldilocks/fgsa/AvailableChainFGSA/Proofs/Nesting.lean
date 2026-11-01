module
public import AvailableChainFGSA.Statements.Store
public import AvailableChainFGSA.Proofs.Fields

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! Output nesting in store form (K2; `comp.outputNesting.v1`, `v2`). The proof
needs no other invariant: the gate and every F advance end with `normalizeS`,
and every other completed step writes neither F nor S. The claim is about
completed events only: inside `admitBlock`, the state before `reconcile` can
have a moved F and the old S (G8 m3). -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp comp.outputNesting.v1] The accessor form: `F ⪯ (if F ⪯ S
then S else F)`. -/
theorem outputNesting_v1 (F S : Block) : Block.Preceq F (if Block.preceq F S then S else F) := by
  split
  · assumption
  · exact block_preceq_refl F

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `normalizeS` gives `F ⪯ S`. -/
theorem normalizeS_nest {n : Nat} (st : State n) : NestOK (normalizeS st) := by
  unfold NestOK
  rw [normalizeS_fields]
  exact outputNesting_v1 _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `reconcile` gives `F ⪯ S`. -/
theorem reconcile_nest {n : Nat} (st : State n) : NestOK (reconcile st) :=
  normalizeS_nest _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate gives `F ⪯ S`, also after an empty or vetoed
gate. -/
theorem gateStep_nest (p : Params) (st : State p.n) (s : Slot) : NestOK (gateStep p st s) :=
  normalizeS_nest _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A row keeps F and S. -/
theorem admitRow_nest (p : Params) (st : State p.n) (a : RowWire p.n) (h : NestOK st) :
    NestOK (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he <;> rw [he] <;> exact h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A fold of rows keeps F and S. -/
theorem foldl_admitRow_nest (p : Params) (rows : List (RowWire p.n)) (st : State p.n)
    (h : NestOK st) : NestOK (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (admitRow_nest p st a h)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA block admission and its carried votes keep S.
-/
theorem admitProposal_stable (q : GridCO.Params) {n : Nat} (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q v o b raw).stableRecord = v.stableRecord := by
  have hfold : ∀ (xs : List (GridCO.HeadWire n .root)) (acc : GridCO.State n .root),
      (xs.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) acc).stableRecord =
        acc.stableRecord := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
        intro acc
        rw [List.foldl_cons, ih]
        exact @GridCO.admitVote_stable GridCO.slowLeasePolicy .root _ _ _ _
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · rfl
  · rw [hfold]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A completed delivery keeps `F ⪯ S`: a vote or a row
writes neither;
a refused block changes nothing; an accepted block keeps S, and a moved F ends
with `reconcile`. -/
theorem process_nest (p : Params) (st : State p.n) (o : Wire p.n) (h : NestOK st) :
    NestOK (process p st o) := by
  unfold process
  split
  · unfold NestOK
    rw [admitHead_fg, admitHead_base_stable]
    exact h
  · exact admitRow_nest p st _ h
  · unfold admitBlock
    split
    · exact h
    · split
      · exact h
      · split
        · apply foldl_admitRow_nest
          split
          · next hF =>
            unfold NestOK at h ⊢
            rw [hF, admitProposal_stable]
            exact h
          · exact reconcile_nest _
        · exact h
  · exact h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate writes neither F nor S. -/
theorem clockPre_stable (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.stableRecord = st.base.stableRecord := by
  unfold clockPre
  dsimp only
  split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A tick keeps `F ⪯ S`: the pre-gate steps write
neither; the gate ends
with `normalizeS`. -/
theorem clock_nest (p : Params) (st : State p.n) (t : Time) (h : NestOK st) :
    NestOK (clock p st t) := by
  unfold clock
  dsimp only
  split
  · exact gateStep_nest _ _ _
  · unfold NestOK
    rw [clockPre_fg, clockPre_stable]
    exact h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp comp.outputNesting.v2; K2] -/
theorem outputNesting_stored (p : Params) : OutputNestingStored p := by
  intro st hst
  refine ⟨?_, rfl, rfl⟩
  induction hst with
  | init => exact block_preceq_refl _
  | restart w _ ih => exact ih
  | tick t _ ih => exact clock_nest p _ t ih
  | deliver o _ ih => exact process_nest p _ o ih

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp comp.outputNesting.v2; K2; G8 m2] The accessor form (spec
558–561): at
every reachable state, `finalized ⪯ stable` after erasure. -/
theorem finalized_preceq_stable (p : Params) (st : State p.n) (hst : Reachable p st) :
    Block.Preceq (eraseFG (finalized st)) (stable st) :=
  (outputNesting_stored p st hst).1

end AvailableChain.FGSA
end
