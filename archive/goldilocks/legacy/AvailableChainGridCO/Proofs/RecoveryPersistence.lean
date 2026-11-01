module
public import AvailableChainGridCO.Proofs.RecoverySupport

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- After an event boundary, an exact row is either retained from that
boundary or written by a later genuine gate. -/
theorem run_row_origin_since {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (start finish : Nat) (hle : start ≤ finish) (reader : V)
    (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho finish reader).obligations) :
    (B, g, d) ∈ (Run.stateBefore (gridCO p) rho start reader).obligations ∨
      ∃ j, start ≤ j ∧ j < finish ∧ ∃ s C,
        rho.events[j]? = some (.tick reader (gateTime p s)) ∧
        confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
  set_option backward.isDefEq.respectTransparency false in
  induction finish with
  | zero => simpa only [Nat.le_zero.mp hle] using Or.inl hm
  | succ finish ih =>
      by_cases he : start = finish + 1
      · subst start; exact Or.inl hm
      have hsf : start ≤ finish := by omega
      have old (hold : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho finish reader).obligations) :
          (B, g, d) ∈ (Run.stateBefore (gridCO p) rho start reader).obligations ∨
            ∃ j, start ≤ j ∧ j < finish + 1 ∧ ∃ s C,
              rho.events[j]? = some (.tick reader (gateTime p s)) ∧
              confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
        rcases ih hsf hold with h | ⟨j, hj, hlt, rest⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, hj, by omega, rest⟩
      cases hi : rho.events[finish]? with
      | none => exact old (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
      | some e =>
          rw [stateBefore_succ_event hi] at hm
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                have hrow : (B, g, d) ∈
                    (clock p (Run.stateBefore (gridCO p) rho finish reader) t).obligations := by
                  simpa [World.step] using! hm
                rcases clock_row_admitted_origin p _ t (run_receiptStamped p rho finish reader)
                    B g d hrow with hold | ⟨s, C, ht, hc, hp, _⟩
                · exact old hold
                · subst t
                  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hc
                  exact Or.inr ⟨finish, hsf, by omega, s, C, hi, hc, hp⟩
              · exact old (by simpa [World.step, hv] using hm)
          | deliver v o t =>
              apply old
              by_cases hv : reader = v
              · subst v; simpa [World.step, gridCO, process_obligations] using! hm
              · simpa [World.step, hv] using hm

/-- A later HEAD row was already present after the initial release or
comes from a gate at or after that release's label. This includes the
initial label's pending gate, which runs after the release. -/
theorem nextHeadState_row_origin_since {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r t : Slot) (hrt : r < t) (hsync : SynchronousLabel p E rho r)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (nextHeadState p rho t reader).obligations) :
    (B, g, d) ∈ (nextHeadState p rho r reader).obligations ∨
      ∃ s C, r ≤ s ∧ s < t ∧
        confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
  have hs := hsync.1.toScheduleWellFormed
  have hpub : PublicTime E (releaseTime p r) := by
    refine ⟨4 * r + 5, ?_⟩
    simp only [releaseTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ releaseTime p r := by
    dsimp [releaseTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hh : releaseTime p r ≤ rho.horizon := by
    have := hsync.2.2.1
    dsimp [releaseTime, gateTime] at *; linarith [p.deltaPos]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hsync.1.tick_total reader hr _ hpub hz hh)
  have hiState : Run.stateBefore (gridCO p) rho (i + 1) reader = nextHeadState p rho r reader := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    change clock p _ _ = clock p _ _
    rw [stateBefore_tick_eq_stateBeforeTime hs hi]
    rfl
  have hrow := (List.mem_filter.mp
    (nextHeadState_row_survives_release p rho t reader B g d hm).1).1
  change (B, g, d) ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p t) reader).obligations
    at hrow
  rw [time_input_eq_event_prefix p E rho hs] at hrow
  have htime : releaseTime p r < releaseTime p t := by
    have hc : (r : Time) < t := by exact_mod_cast hrt
    dsimp [releaseTime, proposalTime]; nlinarith [p.deltaPos]
  have hil := (index_lt_read_length_iff hs (releaseTime p t - 1) hi).mpr
    (Int.le_sub_one_iff.mpr htime)
  rcases run_row_origin_since p E rho hs (i + 1) _ (by omega) reader B g d hrow
      with hold | ⟨j, hj, hjt, s, C, hjget, hc, hp⟩
  · exact Or.inl (hiState ▸ hold)
  · have hbefore : gateTime p s < releaseTime p t :=
      Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs _ hjget).mp hjt)
    have hafter : releaseTime p r ≤ gateTime p s := by
      obtain ⟨hiL, hiE⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjL, hjE⟩ := List.getElem?_eq_some_iff.mp hjget
      have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hiL hjL (by omega)
      rw [hiE, hjE] at hk
      have hx : releaseTime p r < gateTime p s ∨ releaseTime p r = gateTime p s := by
        simpa [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] using hk
      exact hx.elim le_of_lt le_of_eq
    refine Or.inr ⟨s, C, ?_, ?_, hc, hp⟩
    · by_contra hn
      have hle := (gateTime_le_iff p (s + 1) r).mpr (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
      dsimp [gateTime, releaseTime, proposalTime] at hafter hle
      nlinarith [p.deltaPos]
    · by_contra hn
      have hle := (gateTime_le_iff p t s).mpr (Nat.le_of_not_gt hn)
      dsimp [gateTime, releaseTime] at hbefore hle
      linarith [p.deltaPos]

/-- Prefixes of compatible blocks are compatible. -/
theorem compatible_prefixes (A B C D : Block)
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D) (hBD : Block.Compatible B D) :
    Block.Compatible A C := by
  rcases Bool.or_eq_true_iff.mp hBD with h | h
  · exact ancestors_compatible A C D (prefix_trans A B D hAB h) hCD
  · exact ancestors_compatible A C B hAB (prefix_trans C D B hCD h)

/-- All honest would-be HEADs after release r cover B. Sleeping readers
are included, so changing the awake set does not change this property. -/
def HeadCovers {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (B : Block) : Prop :=
  ∀ reader ∈ rho.honest, Block.Preceq B (nextHead p (nextHeadState p rho r reader) r)

/-- Every row left by release is compatible with B, including rows that
do not currently supply the deepest live root. -/
def ReleasedRowsCompatible {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (B : Block) : Prop :=
  ∀ reader ∈ rho.honest, ∀ K g d,
    (K, g, d) ∈ (nextHeadState p rho r reader).obligations → Block.Compatible K B

/-- Source-support induction shared by SA and SA-PC. The callbacks concern
actual results, rows, and HEADs. They do not assume a clean initial state. -/
theorem source_support_induction {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block)
    (rows : Slot → V → List (Block × Nat × Time)) (valid : Slot → Prop)
    (down : ∀ s t, s ≤ t → valid t → valid s)
    (r : Slot) (source : V) (hs : honest source) (B C : Block)
    (below : Block.Preceq B C)
    (initialRows : ∀ v, honest v → ∀ K g d, (K, g, d) ∈ rows r v → Block.Compatible K B)
    (initialHeads : ∀ v, honest v → Block.Preceq B (next r v))
    (origin : ∀ t, r < t → valid t → ∀ v, honest v → ∀ K g d,
      (K, g, d) ∈ rows t v → (K, g, d) ∈ rows r v ∨ ∃ s D,
        r ≤ s ∧ s < t ∧ result s v = some D ∧ Block.Preceq K D)
    (same : ∀ v, honest v → ∀ D, result r v = some D → Block.Compatible D C)
    (preserve : ∀ t, r ≤ t → valid (t + 1) →
      (∀ v, honest v → Block.Preceq B (next t v)) →
      ∀ v, honest v → ∃ D, result (t + 1) v = some D ∧ Block.Preceq B D)
    (transfer : ∀ t, r ≤ t → valid t → ∀ D, result t source = some D → Block.Preceq B D →
      (∀ v, honest v → ∀ K g d, (K, g, d) ∈ rows t v → Block.Compatible K B) →
      ∀ v, honest v → Block.Preceq B (next t v)) :
    ∀ t, r ≤ t → valid t →
      (∀ v, honest v → ∀ K g d, (K, g, d) ∈ rows t v → Block.Compatible K B) ∧
      (∀ v, honest v → Block.Preceq B (next t v)) ∧
      (r < t → ∀ v, honest v → ∃ D, result t v = some D ∧ Block.Preceq B D) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro start horizon
    by_cases eq : t = r
    · subst t
      exact ⟨initialRows, initialHeads, by
        intro impossible; exact (Nat.lt_irrefl _ impossible).elim⟩
    have lt : r < t := by simp only [Slot] at *; omega
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt lt : t ≠ 0)
    have previous := ih u (Nat.lt_succ_self u) (by simp only [Slot] at *; omega)
      (down u (u + 1) (Nat.le_succ u) horizon)
    have results := preserve u (by simp only [Slot] at *; omega) horizon previous.2.1
    have compatible : ∀ v, honest v → ∀ K g d,
        (K, g, d) ∈ rows (u + 1) v → Block.Compatible K B := by
      intro v hv K g d member
      rcases origin (u + 1) lt horizon v hv K g d member with old | ⟨s, D, lo, hi, hD, hKD⟩
      · exact initialRows v hv K g d old
      · by_cases eq : s = r
        · subst s
          exact compatible_prefixes K D B C hKD below (same v hv D hD)
        · have past := ih s hi lo (down s (u + 1) hi.le horizon)
          obtain ⟨D', hD', hBD⟩ := past.2.2 (by simp only [Slot] at *; omega) v hv
          have eq : D' = D := Option.some.inj (hD'.symm.trans hD)
          subst D'
          exact ancestors_compatible K B D hKD hBD
    obtain ⟨D, hD, hBD⟩ := results source hs
    exact ⟨compatible, transfer (u + 1) start horizon D hD hBD compatible, fun _ => results⟩

/-- Once a genuine prefix transfers with compatible rows, it stays
covered by every later complete synchronous HEAD. Same-label safety
controls the initial pending gate. Later gates use the honest batch.
Expiry, release, and renewal cannot add another source of conflict. -/
theorem permanent_support_of_release {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (hseq : ∀ t, r ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho r source) r = some C) (hp : Block.Preceq B C)
    (hrows : ReleasedRowsCompatible p rho r B) (hheads : HeadCovers p rho r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      ReleasedRowsCompatible p rho t B ∧ HeadCovers p rho t B ∧
      (r < t → ∀ reader ∈ rho.honest, ∃ D,
        confirmation p (gateInput p rho t reader) t = some D ∧ Block.Preceq B D) := by
  apply source_support_induction (fun v => v ∈ rho.honest)
    (fun t v => confirmation p (gateInput p rho t v) t)
    (fun t v => nextHead p (nextHeadState p rho t v) t)
    (fun t v => (nextHeadState p rho t v).obligations)
    (fun t => gateTime p t ≤ rho.horizon)
    (fun s t le hh => ((gateTime_le_iff p s t).mpr le).trans hh)
    r source hs B C hp hrows hheads
  · intro t hrt _ v hv K g d hm
    exact nextHeadState_row_origin_since p E rho hΔ r t hrt hsync v hv K g d hm
  · intro v hv D hD
    exact sameLabel_from_engine p E rho hΔ r hsync v hv source hs D C hD hc
  · intro t hrt hh heads v hv
    have sync := hseq (t + 1) (hrt.trans (Nat.le_succ t)) hh
    obtain ⟨D, hD, hBD, _⟩ := preserve_from_engine p E rho hΔ t sync sync.2.1 B heads v hv
    exact ⟨D, hD, hBD⟩
  · intro t hrt hh D hD hBD compatible
    apply transfer_from_engine p E rho hΔ t (hseq t hrt hh) source hs B D hD hBD
    intro v hv K member
    obtain ⟨⟨target, g, d⟩, row, eq⟩ := List.mem_filterMap.mp member
    dsimp only at eq
    split at eq
    · have eq' : target = K := Option.some.inj eq
      subst target
      exact compatible v hv K g d row
    · contradiction

end AvailableChain.GridCO
end
