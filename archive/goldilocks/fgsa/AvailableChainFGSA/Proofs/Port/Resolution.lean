module
public import AvailableChainFGSA.Model.Resolution -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Model.Legacy.Frame
public import AvailableChainFGSA.Proofs.HeadResolution
public import AvailableChainFGSA.Proofs.BlockAncestry

public section

namespace AvailableChain.FGSA.Next

variable {n : Nat}

/-- [pinned spec 975–1015, 1120–1150] New support is the old ordered support
with the additional prefix test, after cumulative resolution. -/
theorem proposerSupportNext_eq_filter (st : State n) (s : Slot) :
    proposerSupportNext st s = (proposerSupport st s).filter (fun o =>
      (GridCO.resolvedHead? (actView st) o).any (Block.preceq (eraseFG st.fg.F))) := by
  unfold proposerSupportNext proposerSupport proposerVotes
  rw [List.filter_filter]
  congr 1
  funext o
  cases GridCO.resolvedHead? (actView st) o <;> simp [Bool.and_comm]

/-- [pinned spec 1120–1150] The prefix test preserves support order. -/
theorem proposerSupportNext_sublist (st : State n) (s : Slot) :
    (proposerSupportNext st s).Sublist (proposerSupport st s) := by
  rw [proposerSupportNext_eq_filter]
  exact List.filter_sublist

/-- [pinned spec 975–1015, 1120–1150] A vote is kept exactly when it was old
support and its resolved head extends F. -/
theorem mem_proposerSupportNext_iff (st : State n) (s : Slot) (o : GridCO.Wire n .root) :
    o ∈ proposerSupportNext st s ↔ o ∈ proposerSupport st s ∧
      ∃ h, GridCO.resolvedHead? (actView st) o = some h ∧
        Block.Preceq (eraseFG st.fg.F) h := by
  rw [proposerSupportNext_eq_filter]
  simp only [List.mem_filter]
  cases GridCO.resolvedHead? (actView st) o <;> simp [Block.Preceq]

/-- [pinned spec 975–1015] Resolve in the cumulative domain before testing F. -/
theorem mem_proposerSupportNext_iff_base (st : State n) (s : Slot)
    (o : GridCO.Wire n .root) :
    o ∈ proposerSupportNext st s ↔ o ∈ GridCO.votesAt st.base (s - 1) ∧
      ∃ h, GridCO.resolvedHead? st.base o = some h ∧
        Block.Preceq (eraseFG st.fg.F) h ∧ h.slot ≤ s - 1 := by
  unfold proposerSupportNext
  rw [List.mem_filter, actView_resolvedHead]
  cases hr : GridCO.resolvedHead? st.base o with
  | none => simp
  | some h =>
      cases hc : activeCompatible st h with
      | false =>
          have hn : ¬ Block.Preceq (eraseFG st.fg.F) h := by
            intro hp
            have : activeCompatible st h = true := by
              unfold activeCompatible
              simp [Block.compatible, Block.Preceq] at hp ⊢
              exact Or.inr hp
            simp [hc] at this
          simp [Option.filter, hc, hn]
      | true => simp [Option.filter, hc, Block.Preceq]

/-- [pinned spec 975–1015] An unresolved cumulative root cannot become support,
even if a tree-only domain would select one of its blocks. -/
theorem proposerSupportNext_unresolved (st : State n) (s : Slot) (o : GridCO.Wire n .root)
    (hr : GridCO.resolvedHead? st.base o = none) :
    o ∉ proposerSupportNext st s := by
  simp [mem_proposerSupportNext_iff_base, hr]

/-- [pinned spec 975–1015] Heads below F or off its chain are omitted. -/
theorem proposerSupportNext_drop (st : State n) (s : Slot) (o : GridCO.Wire n .root)
    (h : Block) (hr : GridCO.resolvedHead? st.base o = some h)
    (hp : ¬ Block.Preceq (eraseFG st.fg.F) h) :
    o ∉ proposerSupportNext st s := by
  simp [mem_proposerSupportNext_iff_base, hr, hp]

/-- [pinned spec 975–1015, 1120–1150] Held, resolved heads above F with a valid
slot are kept when their votes are in the previous-slot pool. -/
theorem proposerSupportNext_keep (st : State n) (s : Slot) (o : GridCO.Wire n .root)
    (h : Block) (ho : o ∈ GridCO.votesAt st.base (s - 1))
    (hr : GridCO.resolvedHead? st.base o = some h)
    (hp : Block.Preceq (eraseFG st.fg.F) h) (hs : h.slot ≤ s - 1) :
    o ∈ proposerSupportNext st s :=
  (mem_proposerSupportNext_iff_base st s o).mpr ⟨ho, h, hr, hp, hs⟩

/-- [pinned spec 975–1015, 1120–1150] Support lists agree if all resolved heads
of the previous-slot pool extend F. This is a pure state condition. -/
theorem proposerSupportNext_eq_of_extends (st : State n) (s : Slot)
    (he : ∀ o ∈ GridCO.votesAt st.base (s - 1), ∀ h,
      GridCO.resolvedHead? (actView st) o = some h → Block.Preceq (eraseFG st.fg.F) h) :
    proposerSupportNext st s = proposerSupport st s := by
  rw [proposerSupportNext_eq_filter]
  apply List.filter_eq_self.mpr
  intro o ho
  obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
  cases hr : GridCO.resolvedHead? (actView st) o with
  | none => simp [hr] at hs
  | some h => simpa [hr, Block.Preceq] using he o hm h hr

/-- [pinned spec 975–1015; minimal (h) correspondence] A supporting head for B
above F survives the prefix test. This compares incidence, not whole lists. -/
theorem proposerSupportNext_incidence (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (o : GridCO.Wire n .root) :
    (o ∈ proposerSupportNext st s ∧ ∃ h, GridCO.resolvedHead? st.base o = some h ∧
      Block.Preceq B h) ↔
    (o ∈ proposerSupport st s ∧ ∃ h, GridCO.resolvedHead? st.base o = some h ∧
      Block.Preceq B h) := by
  constructor
  · rintro ⟨ho, hh⟩
    exact ⟨(proposerSupportNext_sublist st s).subset ho, hh⟩
  · rintro ⟨ho, h, hr, hBh⟩
    have hFh := block_preceq_trans hFB hBh
    have ha : GridCO.resolvedHead? (actView st) o = some h := by
      rw [actView_resolvedHead, hr]
      unfold activeCompatible
      simp [Option.filter, Block.compatible, Block.Preceq] at hFh ⊢
      exact fun _ => hFh
    exact ⟨(mem_proposerSupportNext_iff st s o).mpr ⟨ho, h, ha, hFh⟩, h, hr, hBh⟩

private def supports {mode : GridCO.HeadMode} (domain tree : List Block)
    (B : Block) (o : GridCO.Wire n mode) : Bool :=
  match GridCO.headTarget? o with
  | none => false
  | some r => match GridCO.resolveTarget mode domain r with
    | none => false
    | some h => decide (h ∈ tree) &&
        decide (h.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B h

private theorem supports_iff (st : State n) (B : Block) (o : GridCO.Wire n .root) :
    supports (GridCO.resolutionTree st.base) st.base.blocks B o = true ↔
      ∃ h, GridCO.resolvedHead? st.base o = some h ∧
      h.slot ≤ (GridCO.headLabel? o).getD 0 ∧ Block.Preceq B h := by
  unfold supports GridCO.resolvedHead?
  cases ht : GridCO.headTarget? o with
  | none => simp
  | some r =>
      cases hr : GridCO.resolveTarget .root (GridCO.resolutionTree st.base) r with
      | none => simp [hr]
      | some h =>
          by_cases hm : h ∈ st.base.blocks <;> simp [hr, hm, Block.Preceq]

/-- [pinned spec 975–1015; minimal (h) correspondence] The supporting votes of
B above F are the same, in the same order, under both proposer support lists.
Resolution and score use the same cumulative domain. -/
theorem proposerSupportNext_supporters (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) :
    (proposerSupportNext st s).filter (fun o => (GridCO.resolvedHead? st.base o).any
      (fun h => decide (h.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B h)) =
    (proposerSupport st s).filter (fun o => (GridCO.resolvedHead? st.base o).any
      (fun h => decide (h.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B h)) := by
  rw [proposerSupportNext_eq_filter, List.filter_filter]
  apply List.filter_congr
  intro o ho
  cases hr : GridCO.resolvedHead? st.base o with
  | none => simp
  | some h =>
      by_cases hb : Block.Preceq B h
      · have hf := block_preceq_trans hFB hb
        rw [actView_resolvedHead, hr]
        simp only [Block.Preceq] at hf
        unfold activeCompatible
        simp [Option.filter, Block.compatible, hf]
      · simp only [Block.Preceq] at hb
        simp [hb]

/-- [pinned spec 975–1015; minimal (h) correspondence] Every seat has the same
support incidence for B above F. The raw votes and their equivocation test stay fixed. -/
theorem proposerSupportNext_seat_support (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (i : Fin n) :
    (GridCO.seatVotes (proposerSupportNext st s) i).any (fun o =>
      (GridCO.resolvedHead? st.base o).any (fun h =>
        decide (h.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B h)) =
    (GridCO.seatVotes (proposerSupport st s) i).any (fun o =>
      (GridCO.resolvedHead? st.base o).any (fun h =>
        decide (h.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B h)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, GridCO.seatVotes, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨ho, hi⟩, hh⟩
    exact ⟨o, ⟨(proposerSupportNext_sublist st s).subset ho, hi⟩, hh⟩
  · rintro ⟨o, ⟨ho, hi⟩, hh⟩
    have hp : ∃ h, GridCO.resolvedHead? st.base o = some h ∧ Block.Preceq B h := by
      cases hr : GridCO.resolvedHead? st.base o with
      | none => simp [hr] at hh
      | some h =>
          simp only [hr, Option.any_some, Bool.and_eq_true_iff] at hh
          exact ⟨h, rfl, hh.2⟩
    exact ⟨o, ⟨((proposerSupportNext_incidence st s B hFB o).mpr ⟨ho, hp⟩).1, hi⟩, hh⟩

/-- [pinned spec 975–1015; minimal (h) correspondence] Scores agree above F
for fixed raw votes and the cumulative resolution domain, in any state. -/
theorem proposerSupportNext_scoreOn (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (raw : List (GridCO.Wire n .root)) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      raw (proposerSupportNext st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      raw (proposerSupport st s) B := by
  have _ := hFB
  rfl

/-- [minimal (h) correspondence] Canonical scores agree above F when the
cumulative store has no temporary resolution override. This states a local
metadata condition; it does not assert a run invariant. -/
theorem proposerSupportNext_score (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (hd : st.base.headDomain = none)
    (raw : List (GridCO.Wire n .root)) :
    GridCO.goldfishScore st.base.blocks raw (proposerSupportNext st s) B =
      GridCO.goldfishScore st.base.blocks raw (proposerSupport st s) B := by
  unfold GridCO.goldfishScore
  simpa [GridCO.resolutionTree, hd] using
    proposerSupportNext_scoreOn st s B hFB raw

/-- The switched canonical support is the prefix filter of Legacy support. -/
theorem port_proposerSupport_eq_legacy_filter (st : State n) (s : Slot) :
    proposerSupport st s = (Legacy.proposerSupport st s).filter (fun o =>
      (GridCO.resolvedHead? (actView st) o).any (Block.preceq (eraseFG st.fg.F))) := by
  unfold proposerSupport Legacy.proposerSupport proposerVotes Legacy.proposerVotes
  rw [List.filter_filter]
  congr 1
  funext o
  cases GridCO.resolvedHead? (actView st) o <;> simp [Bool.and_comm]

/-- Prefix filtering keeps the order of the Legacy support list. -/
theorem port_proposerSupport_sublist_legacy (st : State n) (s : Slot) :
    (proposerSupport st s).Sublist (Legacy.proposerSupport st s) := by
  rw [port_proposerSupport_eq_legacy_filter]
  exact List.filter_sublist

/-- Canonical and Legacy scores agree above F in the same cumulative domain. -/
theorem port_proposerSupport_scoreOn_legacy (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (raw : List (GridCO.Wire n .root)) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      raw (proposerSupport st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      raw (Legacy.proposerSupport st s) B := by
  rw [port_proposerSupport_eq_legacy_filter]
  unfold GridCO.goldfishScoreOn
  congr 2
  funext i
  change (GridCO.equivocates raw i || (GridCO.seatVotes
      ((Legacy.proposerSupport st s).filter (fun o =>
        (GridCO.resolvedHead? (actView st) o).any (Block.preceq (eraseFG st.fg.F)))) i).any
      (supports (GridCO.resolutionTree st.base) st.base.blocks B)) =
    (GridCO.equivocates raw i || (GridCO.seatVotes (Legacy.proposerSupport st s) i).any
      (supports (GridCO.resolutionTree st.base) st.base.blocks B))
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [GridCO.seatVotes, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨⟨ho, _⟩, hi⟩, hh⟩
    exact ⟨o, ⟨ho, hi⟩, hh⟩
  · rintro ⟨o, ⟨ho, hi⟩, hh⟩
    obtain ⟨H, hr, _, hBH⟩ := (supports_iff st B o).mp hh
    have hFH := block_preceq_trans hFB hBH
    have ha : activeCompatible st H = true := by
      change (Block.preceq H (eraseFG st.fg.F) || Block.preceq (eraseFG st.fg.F) H) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr hFH)
    refine ⟨o, ⟨⟨ho, ?_⟩, hi⟩, hh⟩
    rw [actView_resolvedHead, hr]
    simpa [Option.filter, ha, Block.Preceq] using hFH

/-- The ordinary score comparison needs the same local domain premise as before. -/
theorem port_proposerSupport_score_legacy (st : State n) (s : Slot) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) (hd : st.base.headDomain = none)
    (raw : List (GridCO.Wire n .root)) :
    GridCO.goldfishScore st.base.blocks raw (proposerSupport st s) B =
      GridCO.goldfishScore st.base.blocks raw (Legacy.proposerSupport st s) B := by
  unfold GridCO.goldfishScore
  simpa [GridCO.resolutionTree, hd] using
    port_proposerSupport_scoreOn_legacy st s B hFB raw

end AvailableChain.FGSA.Next
end
