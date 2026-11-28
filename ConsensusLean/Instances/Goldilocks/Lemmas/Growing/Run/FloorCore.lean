module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorFast

public section

/-! # The lock floor over a run core

`Compose/LockFloorGlobal` and `Compose/LockFloorFast` over the node frame `frameOf` and the static
run core `StaticRunCore`: `FloorAtWith`, `FastFloorAtWith`, the frame transport and the floor over
one cut. The stock lemmas are these at `Node.frame`; the shadow run reads them at `Node.frame'`.
The statements are the stock ones with `Node.frame` replaced by `frameOf` (the frame's tree being
the store's tree above `F`, `StaticRunCore.frameOf_tree`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The floor at node `y`, cut `i`, over the node frame `frameOf` (`FloorAt`): a lock of slot `j`
and expiry at least `m` on a block `⪰ B₀` of the frame's tree. -/
abbrev FloorAtWith (frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n)))
    (tr : GoldilocksTrace sp) (y : Fin sp.n) (i : Nat)
    (B₀ : AC.Blk sp.n (List (FG.Att sp.n))) (j m : Nat) : Prop :=
  ∃ l ∈ (tr.state y i).ac.locks, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B ∈ (frameOf (tr.state y i)).tree, B.root = l.block ∧ (frameOf (tr.state y i)).Anc B₀ B

/-- The fast floor at node `y`, cut `i`, over the node frame `frameOf` (`FastFloorAt`). -/
abbrev FastFloorAtWith
    (frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n)))
    (tr : GoldilocksTrace sp) (y : Fin sp.n) (i : Nat)
    (B₀ : AC.Blk sp.n (List (FG.Att sp.n))) (j m : Nat) : Prop :=
  ∃ l ∈ (tr.state y i).ac.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
    ∃ B ∈ (frameOf (tr.state y i)).tree, B.root = l.block ∧ (frameOf (tr.state y i)).Anc B₀ B

/-- **A block above `B₀` stays above `B₀` in a later frame** that still holds `B₀`
(`floor_frame_transport`). -/
theorem floor_frame_transport_core (hrun : StaticRunCore u frameOf proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i i' : Nat} (hii' : i ≤ i')
    {B₀ B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB0 : B₀ ∈ (frameOf (tr.state y i')).tree) (hB : B ∈ (frameOf (tr.state y i)).tree)
    (h : (frameOf (tr.state y i)).Anc B₀ B) :
    B ∈ (frameOf (tr.state y i')).tree ∧ (frameOf (tr.state y i')).Anc B₀ B := by
  have hsub := hrun.tree_mono y hy hii'
  have hAnc : ∀ st : NodeState (goldilocksNode sp), ∀ A C,
      (frameOf st).Anc A C ↔ Anc {X | X ∈ st.fg.tree ∧ st.fg.Anc st.fg.F X} A C := fun st A C => by
    have h : (frameOf st).tree = {X | X ∈ st.fg.tree ∧ st.fg.Anc st.fg.F X} :=
      Set.ext (hrun.frameOf_tree st)
    change Anc (frameOf st).tree A C ↔ _
    rw [h]
  rw [hAnc] at h ⊢
  rw [hrun.frameOf_tree] at hB0 hB ⊢
  have h1 : Anc (tr.state y i').fg.tree B₀ B := (h.mono fun X hX => hX.1).mono hsub
  exact ⟨⟨hsub hB.1, hB0.2.trans h1⟩, Anc.restrict hB0.2 h1⟩

/-- **The floor over one cut** (`floor_run_view`). -/
theorem floor_run_view_core (hrun : StaticRunCore u frameOf proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {B₀ : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : FloorAtWith frameOf tr y i B₀ j m)
    (hk : sp.slot (tr.time i) ≤ m) (hB0 : B₀ ∈ (frameOf (tr.state y i)).tree)
    (hB0' : B₀ ∈ (frameOf (tr.state y (i + 1))).tree)
    (hva0 : (frameOf (tr.state y i)).viableAncestor B₀ = B₀)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      AC.unlockTarget sp (frameOf (tr.state y i))
        (AC.unlockView (tr.state y i).ac (frameOf (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀) :
    FloorAtWith frameOf tr y (i + 1) B₀ j m := by
  have hold : ∃ l ∈ (tr.state y (i + 1)).ac.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ (frameOf (tr.state y i)).tree, B.root = l.block ∧
        (frameOf (tr.state y i)).Anc B₀ B := by
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := (cutStepWith_ac _).1 hlaw
        rw [hfr] at hstep
        have := AC.exists_step_locks_floor y ℓ.call
          (hrun.frameOK y hy i) (hrun.time_nonneg i) hB0 hva0 hk (hu ℓ hc) hfl
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [((cutStepWith_block_true _).1 hlaw).2.2.1]; exact hfl
          | false => rw [((cutStepWith_block_false _).1 hlaw).2]; exact hfl
        | attestation a => rw [((cutStepWith_attestation _).1 hlaw).2.1]; exact hfl
        | attest C s =>
          cases s with
          | none => rw [((cutStepWith_attest_none _).1 hlaw).2]; exact hfl
          | some a => rw [((cutStepWith_attest_some _ _).1 hlaw).2.2]; exact hfl
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hfl
  obtain ⟨l, hl, hj, he, B, hB, hBr, hB0B⟩ := hold
  obtain ⟨hB', hB0B'⟩ := floor_frame_transport_core hrun hy (Nat.le_succ i) hB0' hB hB0B
  exact ⟨l, hl, hj, he, B, hB', hBr, hB0B'⟩

/-- **The fast floor over one cut** (`fastFloor_run_view`): `floor_run_view_core` with the fast
bit kept. -/
theorem fastFloor_run_view_core (hrun : StaticRunCore u frameOf proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {B₀ : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : FastFloorAtWith frameOf tr y i B₀ j m)
    (hk : sp.slot (tr.time i) ≤ m) (hB0 : B₀ ∈ (frameOf (tr.state y i)).tree)
    (hB0' : B₀ ∈ (frameOf (tr.state y (i + 1))).tree)
    (hva0 : (frameOf (tr.state y i)).viableAncestor B₀ = B₀)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      AC.unlockTarget sp (frameOf (tr.state y i))
        (AC.unlockView (tr.state y i).ac (frameOf (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀) :
    FastFloorAtWith frameOf tr y (i + 1) B₀ j m := by
  have hold : ∃ l ∈ (tr.state y (i + 1)).ac.locks, l.slot = j ∧ l.fast = true ∧
      m ≤ l.expiry ∧ ∃ B ∈ (frameOf (tr.state y i)).tree, B.root = l.block ∧
        (frameOf (tr.state y i)).Anc B₀ B := by
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := (cutStepWith_ac _).1 hlaw
        rw [hfr] at hstep
        have := AC.exists_step_locks_fastFloor y ℓ.call
          (hrun.frameOK y hy i) (hrun.time_nonneg i) hB0 hva0 hk (hu ℓ hc) hfl
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [((cutStepWith_block_true _).1 hlaw).2.2.1]; exact hfl
          | false => rw [((cutStepWith_block_false _).1 hlaw).2]; exact hfl
        | attestation a => rw [((cutStepWith_attestation _).1 hlaw).2.1]; exact hfl
        | attest C s =>
          cases s with
          | none => rw [((cutStepWith_attest_none _).1 hlaw).2]; exact hfl
          | some a => rw [((cutStepWith_attest_some _ _).1 hlaw).2.2]; exact hfl
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hfl
  obtain ⟨l, hl, hj, hf, he, B, hB, hBr, hB0B⟩ := hold
  obtain ⟨hB', hB0B'⟩ := floor_frame_transport_core hrun hy (Nat.le_succ i) hB0' hB hB0B
  exact ⟨l, hl, hj, hf, he, B, hB', hBr, hB0B'⟩

end Consensus.Goldilocks.Compose

end
