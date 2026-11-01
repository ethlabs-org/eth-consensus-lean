module
public import AvailableChainGridCO.Proofs.CrossView

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem early_public {V : Type} (p : Params) (E : Env V)
    (hΔ : E.Δ = p.Δ) (r : Slot) : PublicTime E (earlyTime p r) := by
  refine ⟨4 * r + 2, ?_⟩
  simp only [earlyTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem early_nonneg (p : Params) (r : Slot) : 0 ≤ earlyTime p r := by
  dsimp [earlyTime, proposalTime]
  nlinarith [p.deltaPos, Int.natCast_nonneg r]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every HEAD in a release snapshot reaches every honest late pool.
The relay deadline is the same label's gate, including the strict endpoint. -/
theorem synchronous_release_vote_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ votesAt (releaseInput p rho r source) r) :
    ∀ i, headSeat? o = some i →
      o ∈ lateVotes p (gateInput p rho r reader) r ∨
      equivocates (lateVotes p (gateInput p rho r reader) r) i = true := by
  have hsched := hsync.1.toScheduleWellFormed
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  have hhead : ∃ B, o.payload = .head B := by
    cases ho : o.payload <;> simp_all [headLabel?]
  obtain ⟨B, hb⟩ := hhead
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) source).votes at hm
  rw [time_input_eq_event_prefix p E rho hsched] at hm
  obtain ⟨index, hindex, t, ha, _⟩ := stored_head_stamp_source p rho _ source o _
    (stampVote_mem_of_stored _ (run_receiptStamped p rho _ source) o hm)
  obtain ⟨parent, hi, _⟩ := ha.1
  have ht : t < releaseTime p r := Int.le_sub_one_iff.mp
    ((index_lt_read_length_iff hsched (releaseTime p r - 1) hi).mp hindex)
  exact synchronous_accepted_head_before p E rho hΔ r hsync source reader hs hr
    index o B t (gateTime p r) (gateTime p r) hb (by simpa using hl) ha
    (by rw [hΔ]; dsimp [releaseTime, gateTime] at *; linarith)
    (by rw [hΔ]; dsimp [gateTime]; linarith [p.deltaPos]) (le_refl _) (le_refl _)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A genuine surviving seat cannot equivocate in another reader's
release snapshot: relay would expose both copies before the source gate. -/
theorem synchronous_survivor_not_equivocating {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (i : Fin p.n) (ho : o ∈ cleanSupport p (gateInput p rho r source) r)
    (hi : headSeat? o = some i) :
    equivocates (votesAt (releaseInput p rho r reader) r) i = false := by
  let xs := seatVotes (votesAt (releaseInput p rho r reader) r) i
  have hsingle : ∀ q ∈ xs, q = o := by
    intro q hq
    obtain ⟨hq, hseat⟩ := List.mem_filter.mp hq
    have hlate := synchronous_release_vote_late p E rho hΔ r hsync
      reader source hr hs q hq i (by simpa using hseat)
    have hlate := hlate.resolve_right (by
      rw [cleanSupport_not_equivocating p _ r o i hi ho]
      decide)
    exact (cleanSupport_eq_of_late_same_seat p _ r i o q ho hlate hi
      (by simpa using hseat)).symm
  have hcard : xs.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (hsingle a (List.mem_toFinset.mp ha)).trans
      (hsingle b (List.mem_toFinset.mp hb)).symm
  have hlen : xs.eraseDups.length ≤ 1 := by
    have heq : xs.eraseDups.toFinset = xs.toFinset := by ext q; simp
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup xs), heq]
    exact hcard
  change decide (2 ≤ xs.eraseDups.length) = false
  exact decide_eq_false (by omega)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A surviving early HEAD is present before release with a stamp before the
ordinary freeze. This includes faulty support and sleeping readers. -/
theorem synchronous_early_head_at_release {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ cleanSupport p (gateInput p rho r source) r) :
    o ∈ votesAt (releaseInput p rho r reader) r ∧
      stampVote (releaseInput p rho r reader) o < freezeTime p r := by
  have hearly := (List.mem_filter.mp ho).1
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp hearly
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hraw
  have hhead : ∃ B, o.payload = .head B := by
    cases ho : o.payload <;> simp_all [headLabel?]
  obtain ⟨B, hb⟩ := hhead
  have ht : stampVote (gateInput p rho r source) o < earlyTime p r := by
    simp only [resolvedBefore_block, headTarget?, hb, Bool.and_eq_true, decide_eq_true_eq] at hres
    exact hres.1.2
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).votes at hm
  change stampVote (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) o < _ at ht
  rw [time_input_eq_event_prefix p E rho hsync.1.toScheduleWellFormed] at hm ht
  obtain ⟨index, _, t, ha, ht⟩ := stored_head_accepted_before p E rho
    hsync.1.toScheduleWellFormed _ source o (earlyTime p r)
      (early_public p E hΔ r) (early_nonneg p r) hm ht
  have hsettle := synchronous_accepted_head_before p E rho hΔ r hsync source reader hs hr
    index o B t (freezeTime p r) (releaseTime p r) hb (by simpa using hl) ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith)
    (by rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, gateTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos])
  obtain ⟨i, hi⟩ : ∃ i, headSeat? o = some i := by
    cases o with
    | mk auth payload => cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]
  have hne := synchronous_survivor_not_equivocating p E rho hΔ r hsync
    source reader hs hr o i ho hi
  have hm := (hsettle i hi).resolve_right (fun he => by
    have he' := equivocates_mono _ (votesAt (releaseInput p rho r reader) r) i
      (fun q hq => (List.mem_filter.mp hq).1) he
    rw [hne] at he'
    contradiction)
  obtain ⟨hm, hstamp⟩ := List.mem_filter.mp hm
  exact ⟨hm, of_decide_eq_true hstamp⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The target of an early resolved HEAD is stored before release with
an early block stamp. Its accepted proposal relays independently of the HEAD. -/
theorem synchronous_early_target_at_release {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (B : Block) (hb : headTarget? o = some B)
    (ho : o ∈ earlyVotes p (gateInput p rho r source) r) :
    B ∈ (releaseInput p rho r reader).blocks ∧
      stampBlock (releaseInput p rho r reader) B < freezeTime p r := by
  have hsched := hsync.1.toScheduleWellFormed
  by_cases hn : B = .genesis
  · subst B
    obtain ⟨hm, ht⟩ := genesis_stored_at_time p E rho hsched (releaseTime p r) reader
    refine ⟨hm, ?_⟩
    change stampBlock (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader) _ < _
    rw [ht]
    dsimp [freezeTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hres := (List.mem_filter.mp ho).2
  simp only [resolvedBefore_block, hb, Bool.and_eq_true, decide_eq_true_eq, blockKnown] at hres
  have hm := hres.1.1.1
  have ht := hres.2
  change B ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).blocks at hm
  change stampBlock (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) B < _ at ht
  rw [time_input_eq_event_prefix p E rho hsched] at hm ht
  obtain ⟨index, _, t, obj, raw, support, hp, ha, ht⟩ := stored_block_accepted_before p E rho
    hsched _ source B (earlyTime p r) hn (early_public p E hΔ r) (early_nonneg p r) hm ht
  obtain ⟨j, e, hj, he, hstored⟩ := synchronous_accepted_block_before p E rho hΔ r hsync
    source reader hs hr index obj t (freezeTime p r) hp ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith)
    (by rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, gateTime]; linarith [p.deltaPos])
  exact stored_block_stamp_before_cut p E rho hsched hj
    (by simpa [processed, hp, blockKnown] using hstored) he
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos])

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every surviving early HEAD remains resolved at each reader's release
snapshot. Both the HEAD and its target path have arrived before the freeze. -/
theorem synchronous_early_resolved_at_release {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ cleanSupport p (gateInput p rho r source) r) :
    o ∈ votesAt (releaseInput p rho r reader) r ∧
      resolvedBefore (releaseInput p rho r reader) o (releaseTime p r) = true := by
  obtain ⟨hm, ht⟩ := synchronous_early_head_at_release p E rho hΔ r hsync
    source reader hs hr o ho
  refine ⟨hm, ?_⟩
  have hearly := (List.mem_filter.mp ho).1
  have hres := (List.mem_filter.mp hearly).2
  cases hb : headTarget? o with
  | none => simp [resolvedBefore_block, hb] at hres
  | some B =>
      obtain ⟨hblock, hstamp⟩ := synchronous_early_target_at_release p E rho hΔ r hsync
        source reader hs hr o B hb hearly
      have hcut : freezeTime p r ≤ releaseTime p r := by
        dsimp [freezeTime, releaseTime]; linarith [p.deltaPos]
      simp only [resolvedBefore_block, hb, Bool.and_eq_true, decide_eq_true_eq] at hres ⊢
      exact ⟨⟨⟨by simpa [blockKnown] using hblock, hres.1.1.2⟩,
        ht.trans_le hcut⟩, hstamp.trans_le hcut⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The engine supplies the resolved paths and reverse equivocation relay
for every genuine prefix support set. -/
theorem snapshotSeatAlignment_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) : SnapshotSeatAlignment p rho r := by
  intro source hs reader hr B C _ _ K hconflict
  refine ⟨prefixSupportSeats p (gateInput p rho r source) r B,
    (prefixSupport_eq_card p _ r B).symm, ?_, ?_⟩
  · intro i hi
    obtain ⟨o, ho, hseat, target, ht, hp⟩ := prefixSupportSeats_witness p _ r B i hi
    obtain ⟨hm, hresolved⟩ := synchronous_early_resolved_at_release p E rho hΔ r hsync
      source reader hs hr o ho
    refine ⟨o, hm, hresolved, hseat, ?_⟩
    have hc := conflict_mono_descendant B target K hp hconflict
    have hc' : Block.compatible target K = false := by
      simpa [Block.compatible, Bool.or_comm] using hc
    simp [ht, hc']
  · intro i hi
    obtain ⟨o, ho, hseat, _⟩ := prefixSupportSeats_witness p _ r B i hi
    exact synchronous_survivor_not_equivocating p E rho hΔ r hsync source reader hs hr o i ho hseat

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The snapshot bound follows from receipt relay in either label
regime. The conclusion counts actual resolved, non-equivocating seats. -/
theorem snapshot_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, SynchronousLabel p E rho r → ∀ source ∈ rho.honest,
      ∀ reader ∈ rho.honest, ∀ B C,
        confirmation p (gateInput p rho r source) r = some C →
        Block.preceq B C = true → ∀ K,
          Block.compatible K B = false →
          prefixSupport p (gateInput p rho r source) r B ≤
            releaseCount p (releaseInput p rho r reader) r K := by
  intro r hsync
  exact snapshot_from_alignment p rho r (snapshotSeatAlignment_from_engine p E rho hΔ r hsync)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The engine release clears a conflicting row when its level is no
greater than the genuine prefix support. -/
theorem release_clears_conflict_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C K : Block) (g : Nat) (deadline : Time)
    (hc : confirmation p (gateInput p rho r source) r = some C)
    (hp : Block.Preceq B C) (hk : Block.compatible K B = false)
    (hg : g ≤ prefixSupport p (gateInput p rho r source) r B) :
    (K, g, deadline) ∉ (release p (releaseInput p rho r reader) r).obligations := by
  have hcount := snapshot_from_engine p E rho hΔ r hsync source hs reader hr
    B C hc hp K hk
  intro hm
  have hkeep : releaseCount p (releaseInput p rho r reader) r K < g := by
    simpa [release] using (List.mem_filter.mp hm).2
  omega

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Any conflicting row left by release is strictly stronger than the
genuine prefix support. This is the count step of the recovery descent. -/
theorem surviving_conflict_stronger_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C K : Block) (g : Nat) (deadline : Time)
    (hc : confirmation p (gateInput p rho r source) r = some C)
    (hp : Block.Preceq B C) (hk : Block.compatible K B = false)
    (hm : (K, g, deadline) ∈ (release p (releaseInput p rho r reader) r).obligations) :
    prefixSupport p (gateInput p rho r source) r B < g := by
  by_contra hn
  exact release_clears_conflict_from_engine p E rho hΔ r hsync source reader hs hr
    B C K g deadline hc hp hk (by omega) hm

end AvailableChain.GridCO
end
