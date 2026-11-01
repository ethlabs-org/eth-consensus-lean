module
public import AvailableChainGridCO.Proofs.CleanSafety
public import AvailableChainGridCO.Proofs.Protection

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

section Shared
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Receipt-preserving clock phases also preserve each genuine prefix count. -/
theorem prefixSupport_eq_of_receiptData (p : Params) {n : Nat} (a b : State n)
    (he : receiptData a = receiptData b) (hb : ReceiptStamped b) (r : Slot) (B : Block) :
    prefixSupport p a r B = prefixSupport p b r B := by
  have ⟨h1, h2, h3, h4⟩ : a.blocks = b.blocks ∧ a.blockStamp = b.blockStamp ∧
      a.votes = b.votes ∧ a.voteStamp = b.voteStamp := by simpa [receiptData] using he
  have hp : ReceiptPrefix b a := by constructor <;> simp_all
  have hvotes : votesAt a r = votesAt b r := by simp [votesAt, h3]
  have hearly : earlyVotes p a r = earlyVotes p b r := by
    simp only [earlyVotes, hvotes]
    apply List.filter_congr
    intro o ho
    exact resolvedBefore_eq_of_receiptData a b he hb o (List.mem_filter.mp ho).1 _
  have hlate : lateVotes p a r = lateVotes p b r := by
    simp only [lateVotes, hvotes]
    apply List.filter_congr
    intro o ho
    rw [hp.stampVote hb o (List.mem_filter.mp ho).1]
  simp only [prefixSupport_block_eq, cleanSupport, hearly, hlate, h1]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Equal-time deliveries do not change the map after its unique local tick. -/
theorem read_field_eq_clock {α : Type} {V : Type} [DecidableEq V]
    (p : Params) (f : State p.n → α)
    (hf : ∀ st o, f (process p st o) = f st)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (reader : V) (t : Time) (htick : Event.tick reader t ∈ rho.events) :
    f (Run.readAt (gridCO p) rho t reader) =
      f (clock p (Run.stateBeforeTime (gridCO p) rho t reader) t) :=
  Engine.read_field_eq_clock (gridCO p) f hf E rho hs reader t htick

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Equal-time deliveries preserve the lease map after the public tick. -/
theorem read_obligations_eq_clock {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (reader : V) (t : Time) (htick : Event.tick reader t ∈ rho.events) :
    (Run.readAt (gridCO p) rho t reader).obligations =
      (clock p (Run.stateBeforeTime (gridCO p) rho t reader) t).obligations :=
  read_field_eq_clock p State.obligations (process_obligations p) E rho hs reader t htick

private theorem fold_max_origin (xs : List Nat) (acc : Nat) :
    xs.foldl max acc = acc ∨ xs.foldl max acc ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      rcases ih (max acc x) with he | hm
      · rcases le_total acc x with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl (he.trans (max_eq_right h))))
        · exact Or.inl (he.trans (max_eq_left h))
      · exact Or.inr (List.mem_cons_of_mem x hm)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Positive support selects a member of the declared grid. -/
theorem roundedLevel_mem (p : Params) (h : Nat) (hh : 1 ≤ h) : roundedLevel p h ∈ p.grid := by
  have hpos := one_le_roundedLevel p h hh
  unfold roundedLevel gridLevel at hpos ⊢
  rcases fold_max_origin ((List.range (p.n + 1)).filter (fun g => g ∈ p.grid && g ≤ h)) 0 with
    he | hm
  · omega
  · exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp hm).2).1 |> of_decide_eq_true

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A clean genuine result passes every reader's current map guard. -/
theorem clean_gate_guard {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (reader : V) (hr : reader ∈ rho.honest) (C : Block)
    (hc : confirmation p (gateInput p rho r reader) r = some C) :
    (gateInput p rho r reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨⟨B, g, d⟩, hm, hbad⟩ := List.any_eq_true.mp hh
  obtain ⟨s, D, ht, hD, hBD⟩ := time_input_target_genuine_origin p E rho
    (hclean r (le_refl _)).1.toScheduleWellFormed (gateTime p r) reader B g d hm
  have hsr : s < r := by
    by_contra hn
    have hle := (gateTime_le_iff p r s).mpr (le_of_not_gt hn)
    exact (not_lt.mpr hle) ht
  have hp := clean_genuine_prefix p E rho hΔ s r hsr hclean reader reader hr hr D C hD hc
  have hgood : Block.compatible B C = true :=
    Bool.or_eq_true_iff.mpr (Or.inl (prefix_trans B D C hBD hp))
  simp [hgood] at hbad

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The ordinary next HEADs cover every prefix of a clean stable read. -/
theorem clean_stable_heads_cover {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest) (B : Block)
    (hp : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source))) :
    ∀ reader ∈ rho.honest, Block.Preceq B (nextHead p (nextHeadState p rho r reader) r) := by
  have hsync := hclean r (le_refl _)
  rcases gate_record_genuine_origin p E rho hsync.1.toScheduleWellFormed hΔ r
      hsync.2.2.1 source hs with hg | ⟨s, hsr, hc⟩
  · rw [hg] at hp
    have he : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hp
    subst B; intro reader _; exact genesis_prefix _
  · obtain ⟨hhist, htransfer⟩ := clean_genuine_history p E rho hΔ r hclean
    rcases eq_or_lt_of_le hsr with he | hlt
    · subst s
      intro reader hr
      exact prefix_trans _ _ _ hp (htransfer source hs _ hc reader hr)
    · obtain ⟨C, hC, hBC⟩ := hhist s hlt source hs _ hc source hs
      intro reader hr
      exact prefix_trans _ _ _ (prefix_trans _ _ _ hp hBC) (htransfer source hs C hC reader hr)

theorem gate_covers_result (p : Params) {n : Nat} (st : State n) (r : Slot)
    (C : Block) (hc : confirmation p st r = some C)
    (hg : st.obligations.any (fun (target, _, _) => !Block.compatible target C) = false) :
    Block.Preceq C (stable (gate p st r)) := by
  rw [gate_eq_writeKeys p st r C hc hg]
  change Block.Preceq C (writeKeys _ _ _).stableRecord
  rw [writeKeys_stable]
  change Block.Preceq C (advance st.stableRecord C)
  unfold advance
  split
  · assumption
  · exact block_preceq_self C

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A permitted raw genuine result enters the public record, independently
of whether the admission policy writes any lease. -/
theorem read_gate_covers_result {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (C : Block)
    (hc : confirmation p (gateInput p rho r reader) r = some C)
    (hg : (gateInput p rho r reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false) :
    Block.Preceq C (stable (Run.readAt (gridCO p) rho (gateTime p r) reader)) := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    simp only [gateTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ gateTime p r := by
    dsimp [gateTime, proposalTime]; nlinarith [p.deltaPos, Int.natCast_nonneg r]
  rw [read_stable_eq_clock hs (hs.tick_total reader hr _ hpub hz hh), clock_at_gate]
  apply gate_covers_result
  · exact (confirmation_eq_of_receiptData p _ (gateInput p rho r reader)
      (clockPreGate_receiptData p _ _) (run_time_receiptStamped p rho _ reader) r).trans hc
  · apply List.any_eq_false.mpr
    intro row hm
    exact List.any_eq_false.mp hg row (clockPreGate_obligations_subset p _ _ row hm)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A permitted genuine gate records its prefix and installs every
supported grid row at the actual public read. -/
theorem read_gate_writes_admitted_prefix {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (B C : Block) (g : Nat)
    (hc : confirmation p (gateInput p rho r reader) r = some C)
    (hp : Block.Preceq B C) (hn : B ≠ .genesis) (hb : B ∈ (gateInput p rho r reader).blocks)
    (hadmit : g ∈ admissionLevels p
      (clockPreGate p (gateInput p rho r reader) (gateTime p r)) r B)
    (hguard : (gateInput p rho r reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false) :
    Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) reader)) ∧
      (B, g, gateTime p r + lifetime p) ∈
        (Run.readAt (gridCO p) rho (gateTime p r) reader).obligations := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    simp only [gateTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hpos : 0 < gateTime p r := by
    dsimp [gateTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have htick := hs.tick_total reader hr _ hpub (le_of_lt hpos) hh
  let st := gateInput p rho r reader
  let pre := clockPreGate p st (gateTime p r)
  have hdata : receiptData pre = receiptData st := clockPreGate_receiptData p st _
  have hstamp : ReceiptStamped st := run_time_receiptStamped p rho _ reader
  have hc' : confirmation p pre r = some C :=
    (confirmation_eq_of_receiptData p pre st hdata hstamp r).trans hc
  have hg' : pre.obligations.any (fun (target, _, _) => !Block.compatible target C) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨row, hm, he⟩ := List.any_eq_true.mp h
    have h : st.obligations.any (fun (target, _, _) => !Block.compatible target C) = true :=
      List.any_eq_true.mpr ⟨row, clockPreGate_obligations_subset p st _ row hm, he⟩
    rw [hguard] at h
    contradiction
  constructor
  · rw [read_stable_eq_clock hs htick, clock_at_gate]
    exact prefix_trans B C _ hp (gate_covers_result p pre r C hc' hg')
  · rw [read_obligations_eq_clock p E rho hs reader _ htick, clock_at_gate]
    change (B, g, gateTime p r + lifetime p) ∈ (gate p pre r).obligations
    rw [gate_eq_writeKeys p pre r C hc' hg']
    have hmap := run_time_map_reachable p E rho hs (gateTime p r) reader
    have hnow : st.now ≤ gateTime p r := le_of_lt (time_input_now_lt p E rho hs _ hpos reader)
    have hbound := (clockPreGate_invariants p st _ hmap.prefixOrder hmap.comparable
      hmap.blocks hmap.horizon hnow).2.2.2.1
    apply writeKeys_mem_of_key
      { pre with
        stableRecord := advance pre.stableRecord C
        goldfishRecord := advance pre.goldfishRecord C
        genuine := recordGenuine pre r (some C) } _ B g _ hbound
    apply List.mem_flatMap.mpr
    refine ⟨B, List.mem_filter.mpr
      ⟨?_, Bool.and_eq_true_iff.mpr ⟨by simp [hn], hp⟩⟩, ?_⟩
    · have he : pre.blocks = st.blocks := congrArg Prod.fst hdata
      rw [he]; exact hb
    · exact List.mem_map.mpr ⟨g, hadmit, rfl⟩

end Shared

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A permitted genuine gate records its prefix and installs every
supported grid row at the actual public read. -/
theorem read_gate_writes_supported_prefix {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (B C : Block) (g : Nat)
    (hc : confirmation p (gateInput p rho r reader) r = some C)
    (hp : Block.Preceq B C) (hn : B ≠ .genesis) (hb : B ∈ (gateInput p rho r reader).blocks)
    (hg : g ∈ p.grid) (hcount : g ≤ prefixSupport p (gateInput p rho r reader) r B)
    (hguard : (gateInput p rho r reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false) :
    Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) reader)) ∧
      (B, g, gateTime p r + lifetime p) ∈
        (Run.readAt (gridCO p) rho (gateTime p r) reader).obligations := by
  apply read_gate_writes_admitted_prefix p E rho hΔ hs r hh reader hr B C g hc hp hn hb
  · have he := prefixSupport_eq_of_receiptData p _ _
      (clockPreGate_receiptData p (gateInput p rho r reader) (gateTime p r))
      (run_time_receiptStamped p rho _ reader) r B
    change g ∈ (List.range (p.n + 1)).filter
      (fun g => g ∈ p.grid && g ≤ prefixSupport p _ r B)
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le (p.levels_le g hg)),
      by simp [hg, he, hcount]⟩
  · exact hguard

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Clean coverage follows from the engine. This discharges the full
coverage claim, including rounded strength, honest support, and the row
deadline at the next public gate. -/
theorem coverage_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, CleanThroughLabel p E rho (r + 1) → ∀ source ∈ rho.honest,
      ∀ B, Block.preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source)) = true →
        B ≠ .genesis → AwakeMajority E rho (voteTime p (r + 1)) →
        ∀ reader ∈ rho.honest,
          Block.preceq B
            (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)) = true ∧
          ∃ g deadline, g ∈ p.grid ∧
            g = roundedLevel p (prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B) ∧
            (awakeAt E rho.honest (voteTime p (r + 1))).card ≤
              prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B ∧
            gateTime p (r + 1) + lifetime p ≤ deadline ∧
            (B, g, deadline) ∈
              (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader).obligations := by
  intro r hclean source hs B hp hn hm reader hr
  have hsync := hclean (r + 1) (le_refl _)
  have hheads := clean_stable_heads_cover p E rho hΔ r
    (fun s hs => hclean s (hs.trans (Nat.le_succ r))) source hs B hp
  obtain ⟨C, hc, hBC, hB⟩ :=
    preserve_from_engine p E rho hΔ r hsync hm B hheads reader hr
  have hsupp := prefixSupport_ge_early_honest_batch p E rho hsync.1 _ reader (r + 1) B
    (synchronous_next_head_batch p E rho hΔ r (.of_synchronous hsync) B hheads reader hr)
  let count := prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B
  have hpos : 1 ≤ count := by
    change (faulty rho).card < (awakeAt E rho.honest (voteTime p (r + 1))).card at hm
    exact (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hm)).trans hsupp
  have hg := roundedLevel_mem p count hpos
  obtain ⟨hrecord, hrow⟩ := read_gate_writes_supported_prefix p E rho hΔ
    hsync.1.toScheduleWellFormed (r + 1) hsync.2.2.1 reader hr B C (roundedLevel p count)
    hc hBC hn hB hg (roundedLevel_le p count)
    (clean_gate_guard p E rho hΔ (r + 1) hclean reader hr C hc)
  exact ⟨hrecord, roundedLevel p count, gateTime p (r + 1) + lifetime p,
    hg, rfl, hsupp, le_refl _, hrow⟩

end AvailableChain.GridCO
end
