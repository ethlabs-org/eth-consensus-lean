module
public import AvailableChainFGSA.Proofs.ActView

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The reconcile facts (K3; K1 helper and origin form; `bp.reconcile.v1`,
bp01 §6.2–6.3). -/

variable {n : Nat}

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The exact effect of `reconcile`, as one record update.
-/
theorem reconcile_eq (st : State n) :
    reconcile st = { st with
      base := { st.base with
        obligations := st.base.obligations.filter (fun row => activeCompatible st row.1)
        genuine := st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st)))
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
          st.base.stableRecord else eraseFG st.fg.F }
      fastWrite := st.fastWrite.map (fun row => (row.1, row.2.filter (activeCompatible st))) } := by
  unfold reconcile
  rw [normalizeS_fields]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_obligations (st : State n) :
    (reconcile st).base.obligations =
      st.base.obligations.filter (fun row => activeCompatible st row.1) := by
  rw [reconcile_eq]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_genuine (st : State n) :
    (reconcile st).base.genuine =
      st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st))) := by
  rw [reconcile_eq]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (§6.2, exact effects) A label stays
evaluated; a result
is kept or emptied, never replaced. -/
theorem reconcile_savedGenuine (st : State n) (r : Slot) :
    GridCO.savedGenuine (reconcile st).base r =
      (GridCO.savedGenuine st.base r).map (fun c => c.filter (activeCompatible st)) := by
  unfold GridCO.savedGenuine
  rw [reconcile_genuine, List.find?_map, Option.map_map, Option.map_map]
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_fastWrite (st : State n) :
    (reconcile st).fastWrite =
      st.fastWrite.map (fun row => (row.1, row.2.filter (activeCompatible st))) := by
  rw [reconcile_eq]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_stable (st : State n) :
    (reconcile st).base.stableRecord =
      if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st.base.stableRecord
      else eraseFG st.fg.F := by
  rw [reconcile_eq]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1, bp.frame.v1; K3] Reconcile writes no frame
input and no
other field: Σ.T, the FG caches, the stamps, both pools, the proposals, the
time, the frozen and early caches, the release snapshots and G. -/
theorem reconcile_frame (st : State n) :
    (reconcile st).fg = st.fg ∧ (reconcile st).proposals = st.proposals ∧
    (reconcile st).rowPool = st.rowPool ∧
    (reconcile st).base.blocks = st.base.blocks ∧
    (reconcile st).base.blockStamp = st.base.blockStamp ∧
    (reconcile st).base.votes = st.base.votes ∧
    (reconcile st).base.voteStamp = st.base.voteStamp ∧
    (reconcile st).base.proposals = st.base.proposals ∧
    (reconcile st).base.now = st.base.now ∧
    (reconcile st).base.frozen = st.base.frozen ∧
    (reconcile st).base.early = st.base.early ∧
    (reconcile st).base.releaseSnapshots = st.base.releaseSnapshots ∧
    (reconcile st).base.goldfishRecord = st.base.goldfishRecord := by
  rw [reconcile_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.frame.v1, bp.reconcile.v1; K3] Reconcile keeps the FG
frame. -/
theorem storeControls_reconcile (p : Params) (st : State p.n) :
    storeControls p.E p.cfg (reconcile st).fg = storeControls p.E p.cfg st.fg := by
  rw [reconcile_fg]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `F ⪯ (if F ⪯ S then S else F)` in `Bool` form. -/
theorem preceq_normal (F S : Block) :
    Block.preceq F (if Block.preceq F S then S else F) = true := by
  split
  · assumption
  · exact block_preceq_refl F

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] (idempotence for fixed F) -/
theorem reconcile_idem (st : State n) : reconcile (reconcile st) = reconcile st := by
  rw [reconcile_eq (reconcile st)]
  rw [reconcile_eq st]
  simp only [activeCompatible, List.filter_filter, Bool.and_self, List.map_map,
    Function.comp_def, Option.filter_filter, preceq_normal, ite_true]
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1] After reconcile every SA target is
compatible with F. -/
theorem reconcile_saCompat (st : State n) : SACompat (reconcile st) := by
  have hF : (reconcile st).fg.F = st.fg.F := by rw [reconcile_fg]
  refine ⟨?_, ?_, ?_⟩
  · intro row hrow
    rw [reconcile_obligations, List.mem_filter] at hrow
    rw [hF]
    exact hrow.2
  · intro r C hC
    rw [reconcile_genuine, List.mem_map] at hC
    obtain ⟨row, _, he⟩ := hC
    simp only [Prod.mk.injEq] at he
    rw [hF]
    have := he.2
    rw [Option.filter_eq_some_iff] at this
    exact this.2
  · intro row hrow b hb
    rw [reconcile_fastWrite, List.mem_map] at hrow
    obtain ⟨row', _, rfl⟩ := hrow
    rw [List.mem_filter] at hb
    rw [hF]
    exact hb.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `S ⪯ (if F ⪯ S then S else F)` when S and F are
compatible. -/
theorem stable_preceq_normal {S F : Block} (hS : Block.Compatible S F) :
    Block.Preceq S (if Block.preceq F S then S else F) := by
  split
  · exact block_preceq_refl S
  · next h =>
    unfold Block.Compatible Block.compatible at hS
    simp only [Bool.or_eq_true] at hS
    rcases hS with hS | hS
    · exact hS
    · exact absurd hS h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; bp bp.reconcile.v1] Harmless reconcile, filter form:
if F is
compatible with every live lease, saved nonempty result, fastWrite member and S,
then reconcile deletes nothing and only moves S forward. The fastWrite premise
is discharged by `reconcile_harmless_origin`; do not cite this lemma as K1. -/
theorem reconcile_harmless (st : State n) (hC : SACompat st)
    (hS : Block.Compatible st.base.stableRecord (eraseFG st.fg.F)) :
    reconcile st = { st with base := { st.base with
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord
          then st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (reconcile st).base.stableRecord := by
  refine ⟨?_, by rw [reconcile_stable]; exact stable_preceq_normal hS⟩
  rw [reconcile_eq]
  have hO : st.base.obligations.filter (fun row => activeCompatible st row.1) =
      st.base.obligations :=
    List.filter_eq_self.2 (fun row hrow => hC.1 row hrow)
  have hG : st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st))) =
      st.base.genuine := by
    conv => rhs; rw [← List.map_id st.base.genuine]
    apply List.map_congr_left
    intro ⟨r, c⟩ hrc
    cases c with
    | none => rfl
    | some C =>
        simp only [id, Option.filter_some]
        rw [ite_eq_left (show activeCompatible st C = true from hC.2.1 r C hrc)]
  have hW : st.fastWrite.map (fun row => (row.1, row.2.filter (activeCompatible st))) =
      st.fastWrite := by
    conv => rhs; rw [← List.map_id st.fastWrite]
    apply List.map_congr_left
    intro ⟨r, bs⟩ hrb
    simp only [id]
    rw [List.filter_eq_self.2 (fun b hb =>
      (show activeCompatible st b = true from hC.2.2 (r, bs) hrb b hb))]
  rw [hO, hG, hW]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1 §6.3; K1 historical case] If the origin
invariant holds
for the old F₀ and F₀ ⪯ F, it holds for F after reconcile. An emptied body C
keeps only members B with B ⪯ F (C # F, B ⪯ C, B ∥ F force B ⪯ F). -/
theorem reconcile_fastOrigin (st : State n) (F₀ : Block) (hO : FastOrigin F₀ st)
    (hF : Block.Preceq F₀ (eraseFG st.fg.F)) :
    FastOrigin (eraseFG st.fg.F) (reconcile st) := by
  have hFr : (reconcile st).fg.F = st.fg.F := by rw [reconcile_fg]
  intro row hrow B hB
  rw [reconcile_fastWrite, List.mem_map] at hrow
  obtain ⟨⟨r, bs⟩, hrbs, rfl⟩ := hrow
  simp only [List.mem_filter] at hB
  have hBF : Block.Compatible B (eraseFG st.fg.F) := hB.2
  rcases hO (r, bs) hrbs B hB.1 with ⟨C, hC, hBC⟩ | hB0
  · by_cases hCF : Block.Compatible C (eraseFG st.fg.F)
    · refine Or.inl ⟨C, ?_, hBC⟩
      rw [reconcile_savedGenuine, hC]
      simp only [Option.map_some, Option.filter_some]
      rw [ite_eq_left (show activeCompatible st C = true from hCF)]
    · refine Or.inr ?_
      unfold Block.Compatible Block.compatible at hBF
      simp only [Bool.or_eq_true] at hBF
      rcases hBF with h | h
      · exact h
      · exfalso
        apply hCF
        rw [Block.Compatible, block_compatible_comm]
        exact block_compatible_of_preceq (block_preceq_trans h hBC)
  · exact Or.inr (block_preceq_trans hB0 hF)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A saved nonempty result is a row of `genuine`. -/
theorem mem_genuine_of_saved {v : GridCO.State n .root} {r : Slot} {C : Block}
    (h : GridCO.savedGenuine v r = some (some C)) : (r, some C) ∈ v.genuine := by
  unfold GridCO.savedGenuine at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨row, hrow, hc⟩ := h
  have hm := List.mem_of_find?_eq_some hrow
  have hr := List.find?_some hrow
  simp only [beq_iff_eq] at hr
  rw [← hr, ← hc]
  exact hm

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1; K1] Harmless reconcile, blueprint form.
The state holds
the new F; `F₀` is the F before the move, with its origin invariant. If the new
F is compatible with every live lease, every saved nonempty result and S, then
reconcile deletes no target, no body and no fastWrite member, and only extends
S. There is NO fastWrite premise. -/
theorem reconcile_harmless_origin (st : State n) (F₀ : Block) (hO : FastOrigin F₀ st)
    (hF : Block.Preceq F₀ (eraseFG st.fg.F))
    (hL : ∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F))
    (hG : ∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F))
    (hS : Block.Compatible st.base.stableRecord (eraseFG st.fg.F)) :
    reconcile st = { st with base := { st.base with
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord
          then st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (reconcile st).base.stableRecord := by
  refine reconcile_harmless st ⟨hL, hG, ?_⟩ hS
  intro row hrow B hB
  rcases hO row hrow B hB with ⟨C, hC, hBC⟩ | hB0
  · exact block_compatible_of_preceq_compatible hBC (hG _ _ (mem_genuine_of_saved hC))
  · exact block_compatible_of_preceq (block_preceq_trans hB0 hF)

end AvailableChain.FGSA
end
