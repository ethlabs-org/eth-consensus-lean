module
public import AvailableChainGridCO.Proofs.RecoveryPersistence
import Mathlib.Data.Finset.Max

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Levels outside the remaining set already have support in the current
honest batch. The row is read after release, so pending acquisitions are
included. The property holds throughout the complete synchronous suffix. -/
def RowsSupportedOutside [LeasePolicy] {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (boundary : Slot) (remaining : Finset Nat) : Prop :=
  ∀ r, boundary ≤ r → gateTime p r ≤ rho.horizon →
    ∀ reader ∈ rho.honest, ∀ B g d,
      (B, g, d) ∈ (nextHeadState p rho r reader).obligations → g ∉ remaining →
      HeadCovers p rho (r - 1) B

/-- A genuine prefix at the largest remaining level obtains permanent
support. Strictly stronger rows are already covered by the current batch;
release removes every other conflict. -/
theorem permanent_support_at_level [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary : Slot) (hpos : 0 < boundary) (remaining : Finset Nat) (g : Nat)
    (hmax : ∀ k ∈ remaining, k ≤ g)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hstrong : RowsSupportedOutside p rho boundary remaining)
    (s : Slot) (hbs : boundary ≤ s) (hh : gateTime p s ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho s source) s = some C) (hp : Block.Preceq B C)
    (hg : g ≤ prefixSupport p (gateInput p rho s source) s B) :
    ∀ t, s ≤ t → gateTime p t ≤ rho.horizon →
      ReleasedRowsCompatible p rho t B ∧ HeadCovers p rho t B := by
  have hsync := hseq s hbs hh
  have hspos : 0 < s := hpos.trans_le hbs
  have he : s - 1 + 1 = s := Nat.sub_add_cancel hspos
  have hcompat : ∀ reader ∈ rho.honest, ∀ K k d,
      (K, k, d) ∈ (nextHeadState p rho s reader).obligations →
      prefixSupport p (gateInput p rho s source) s B < k → Block.Compatible K B := by
    have hstep := supported_stronger_rows_compatible p E rho hΔ (s - 1)
    rw [he] at hstep
    apply hstep hsync source hs B C hc hp
    intro reader hr K k d hm hk
    exact hstrong s hbs hh reader hr K k d hm (fun hmem =>
      (not_lt.mpr (hmax k hmem)) (hg.trans_lt hk))
  have hrows : ReleasedRowsCompatible p rho s B := by
    intro reader hr K k d hm
    cases hKB : Block.compatible K B with
    | true => exact hKB
    | false =>
        exact hcompat reader hr K k d hm
          (nextHeadState_conflict_stronger p E rho hΔ s hsync source reader hs hr B C K k d
          hc hp hKB hm)
  have hheads : HeadCovers p rho s B := transfer_of_stronger_rows_from_engine p E rho hΔ
    s hsync source hs B C hc hp hcompat
  intro t hst hhor
  have hperm := permanent_support_of_release p E rho hΔ s hsync
    (fun t hst hhor => hseq t (hbs.trans hst) hhor) source hs B C hc hp hrows hheads t hst hhor
  exact ⟨hperm.1, hperm.2.1⟩

/-- One stage removes the largest remaining level from the induction.
Every old row at that level has expired; every later write has permanent
support. The argument is uniform over all targets and all readers. -/
theorem recovery_stage {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho)
    (boundary : Slot) (hpos : 0 < boundary) (remaining : Finset Nat) (g : Nat)
    (hmax : ∀ k ∈ remaining, k ≤ g)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hstrong : RowsSupportedOutside p rho boundary remaining) :
    RowsSupportedOutside p rho (boundary + p.m) (remaining.erase g) := by
  intro r hbr hh reader hr B k d hm hk
  have hbr' : boundary ≤ r := (Nat.le_add_right boundary p.m).trans hbr
  by_cases hkg : k = g
  · subst k
    obtain ⟨s, C, hbs, hsr, hc, hp, _, hg, _⟩ := nextHeadState_row_source_after_stage
      p E rho hexec.toScheduleWellFormed boundary r (hbr.trans (Nat.le_succ r)) reader B g d hm
    have hsbound : gateTime p s ≤ rho.horizon :=
      ((gateTime_le_iff p s r).mpr (Nat.le_of_lt hsr)).trans hh
    have hsr' : s ≤ r - 1 := Nat.le_sub_one_of_lt hsr
    exact (permanent_support_at_level p E rho hΔ boundary hpos remaining g hmax hseq hstrong
      s hbs hsbound reader hr B C hc hp hg (r - 1) hsr'
      (((gateTime_le_iff p (r - 1) r).mpr (Nat.sub_le r 1)).trans hh)).2
  · exact hstrong r hbr' hh reader hr B k d hm
      (fun hmem => hk (Finset.mem_erase.mpr ⟨hkg, hmem⟩))

/-- A source whose deadline extends past the stage boundary has permanent
support if its grid level has already been removed from the remaining set.
This retains the source information needed before a later release. -/
def SourcesSupportedOutside {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (boundary : Slot) (remaining : Finset Nat) : Prop :=
  ∀ s, gateTime p s ≤ rho.horizon → ∀ source ∈ rho.honest, ∀ B C g,
    g ∈ p.grid → g ∉ remaining → voteTime p boundary < gateTime p s + lifetime p →
    confirmation p (gateInput p rho s source) s = some C → Block.Preceq B C →
    g ≤ prefixSupport p (gateInput p rho s source) s B →
    ∀ t, s ≤ t → gateTime p t ≤ rho.horizon →
      ReleasedRowsCompatible p rho t B ∧ HeadCovers p rho t B

/-- The source invariant advances with the row invariant. A live deadline
past the new boundary excludes every old source, including the pending
gate at the previous boundary. -/
theorem recovery_source_stage {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary : Slot) (hpos : 0 < boundary) (remaining : Finset Nat) (g : Nat)
    (hmax : ∀ k ∈ remaining, k ≤ g)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary remaining)
    (hsources : SourcesSupportedOutside p rho boundary remaining) :
    SourcesSupportedOutside p rho (boundary + p.m) (remaining.erase g) := by
  intro s hh source hs B C k hk hn hd hc hp hcount t hst hhor
  by_cases hkg : k = g
  · subst k
    have hbs : boundary ≤ s := by
      by_contra hnot
      have hold := old_head_deadline_by_next_stage p s boundary (Nat.lt_of_not_ge hnot)
      have he : voteTime p (boundary + p.m) = voteTime p boundary + (lifetime p + p.Δ) := by
        simpa using healing_stage_time p boundary 1
      rw [he] at hd
      exact (not_lt.mpr hold) hd
    exact permanent_support_at_level p E rho hΔ boundary hpos remaining g hmax hseq hrows
      s hbs hh source hs B C hc hp hcount t hst hhor
  · have hb : voteTime p boundary ≤ voteTime p (boundary + p.m) := by
      have he : voteTime p (boundary + p.m) = voteTime p boundary + (lifetime p + p.Δ) := by
        simpa using healing_stage_time p boundary 1
      rw [he]; linarith [lifetime_nonneg p, p.deltaPos]
    exact hsources s hh source hs B C k hk
      (fun hmem => hn (Finset.mem_erase.mpr ⟨hkg, hmem⟩)) (hb.trans_lt hd) hc hp hcount t hst hhor

/-- K stages also establish permanent support for every source that can
supply a live row after the last stage. This also gives the source
support needed before release when a proposal chooses its parent. -/
theorem recovery_sources_and_rows {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho)
    (remaining : Finset Nat) (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary remaining)
    (hsources : SourcesSupportedOutside p rho boundary remaining) :
    RowsSupportedOutside p rho (boundary + remaining.card * p.m) ∅ ∧
      SourcesSupportedOutside p rho (boundary + remaining.card * p.m) ∅ := by
  classical
  induction remaining using Finset.strongInductionOn generalizing boundary
  rename_i remaining ih
  by_cases hn : remaining.Nonempty
  · let g := remaining.max' hn
    have hg : g ∈ remaining := Finset.max'_mem remaining hn
    have hmax : ∀ k ∈ remaining, k ≤ g := fun k hk => Finset.le_max' remaining k hk
    have hstage := recovery_stage p E rho hΔ hexec boundary hpos remaining g hmax hseq hrows
    have hsource := recovery_source_stage p E rho hΔ boundary hpos remaining g
      hmax hseq hrows hsources
    have hnext := ih (remaining.erase g) (Finset.erase_ssubset hg) (boundary + p.m)
      (hpos.trans_le (Nat.le_add_right boundary p.m))
      (fun t hbt hhor => hseq t ((Nat.le_add_right boundary p.m).trans hbt) hhor) hstage hsource
    have hcard : (remaining.erase g).card + 1 = remaining.card := Finset.card_erase_add_one hg
    have he : boundary + p.m + (remaining.erase g).card * p.m =
        boundary + remaining.card * p.m := by rw [← hcard]; ring
    simpa only [he] using hnext
  · have he : remaining = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst remaining
    simpa using And.intro hrows hsources

/-- Both stage invariants follow from the engine and a synchronous label
suffix. -/
theorem grid_sources_and_rows_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho) (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t) :
    RowsSupportedOutside p rho (boundary + p.grid.card * p.m) ∅ ∧
      SourcesSupportedOutside p rho (boundary + p.grid.card * p.m) ∅ := by
  apply recovery_sources_and_rows p E rho hΔ hexec p.grid boundary hpos hseq
  · intro r _ _ reader _ B g d hm hn
    have hold := (List.mem_filter.mp
      (nextHeadState_row_survives_release p rho r reader B g d hm).1).1
    obtain ⟨s, C, _, _, _, hg, _⟩ := time_input_row_genuine_origin p E rho
      hexec.toScheduleWellFormed (releaseTime p r) reader B g d hold
    exact (hn hg).elim
  · intro s hh source hs B C g hg hn
    exact (hn hg).elim

end AvailableChain.GridCO
end
