module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.Ready
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.Sync
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.LocalRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
@[expose] public section

/-! # The healthy two-validator run through C1.2: a literal good window

On the run of `Runs.TwoValidator.Run` (`n = 2`, both honest, `Δ = 1`, `t_s = 4s`, `k = c = 2`,
`δ_t = 11`; `v0` proposes every slot, `v1`'s rows reach `v0` thirty-five time units late, so a
height is justified once every ten slots), with `g = 0`, `Δ_F = 36`, `κ = 2Δ`,
`c_F = 𝓕 = 11` and `k_F = 0`, the premises of C1.2 (`Compose.OutcomeService`) hold at the entry
of height `3`, and its good-window branch is met literally.

* **The parameters** (computed from the definitions): `ḡ = 0`, `c_z = t_3 = 12` (`cutZ_zero`),
  `H_z = 1` (`hz_zero`: both `h_max` are `1` after all events at `12`), the reset `a_z = 45`
  (`run_isReset`: the rows of height `2` are signed at `rt 2 = t_11 + Δ = 45`), so
  `R_z = t_{slot(45) + 2k + 5} = t_20 = 80` (`resetSlot_le`). `c_F = 11 = ⌈(6Δ + Δ_F)/(4Δ)⌉`,
  the least `c_F` with `6Δ + Δ_F ≤ 4Δ c_F`, and `c_F + k_F ≤ δ_t` (`cF_bounds`).
* **The entry** `T = E_3 = blk 21` (slot `u = 21`, `t_u = 84 ≥ 80`): `v0`'s ready proposal
  (`run_ready`), accepted at cut `1024 · 84 + 2` with state height `3 = H_z + 2`, its previous
  height `2` justified (`run_runEntry`, `entry_height`, `entry_previous`).
* **The window** `I(E, 0, 0) = {32}`: `W = Bs = blk 32` on `Pr = blk 31 = E_4`, a ready proposal
  extending `T` (`ready_inclusion`). The rows `R = {(v0, 3), (v1, 3)}` (`q = 2`) are the target
  rows for `E_3` with the finality pair `(2, E_2)`.
* (a) `twoRun_goodWindow`: the literal `GW(E_3, 0, 0)` at `v0`'s proposal of `blk 32` (cut
  `1024 · 128 + 2`, time `128 < T₁ = t_33 = 132`), and both validators accept `blk 32` at
  `128 < T₁ + Δ`.
* (a) `twoRun_outcome`: C1.2 itself (`Healing.Recovery.outcome_service`) applied to the run at
  this entry, with every premise discharged; its conclusion, read at the computed values.

**Limits.** This witness is narrow:
* it exercises only the branch of an entry whose previous height is justified (`bound = true`);
  the `bound = false` conjunct of C1.2 holds vacuously here;
* there are no faults (`n = 2`, both honest), so the fault bounds are met only as `0 < …`;
* `Δ = 1`, both validators are awake at every time `t ≥ 0`, and nobody restarts
  (`run_facts.noRestart`), so every validator is joined throughout and no wake or rejoin case of
  the delivery deadlines or of `ReadyProposal`'s joinedness is exercised;
* both rows of `R` are already on `Pr`'s chain (carried by `blk 22` and `blk 31`), so the
  good window's `emitted` and `pooled` clauses are met through their on-chain alternative, and
  the pooled-row inclusion of a fresh row is exercised only by `Bs` carrying `(v0, 4)`;
* `Catch(2Δ)` is vacuous at `g = 0` (no block is accepted before `ḡ = 0`); the entry, window and
  inclusion claims are not;
* `k_F = 0` (forced by `δ_t = 11 = 𝓕`), so the window has one slot.

**Unconditional.** The run's facts are its own theorems: the per-time node states
(`world_good`), its observable events (`run_facts`, from which `Healthy(0)` is derived by
`run_healthy`) and its run laws (`run_goldilocksRun`). -/

namespace Consensus.Goldilocks.Witness.TwoRun

open Node SA

/-! ## The parameters -/

theorem gbar_zero : gbar 0 = 0 := max_self 0

/-- `c_z = t_{slot(ḡ)+3} = t_3 = 12` at `g = 0`. -/
theorem cutZ_zero : Healing.cutZ sp.toParams 0 = 12 := by
  unfold Healing.cutZ
  rw [gbar_zero]
  have h := slotOf_nat 0
  rw [Nat.cast_zero] at h
  rw [h]
  rfl

/-- The first cut after time `t` is the cut `1024 (t + 1)`. -/
theorem firstCutAfter_iff {j t : Nat} :
    Healing.FirstCutAfter run j (t : Int) ↔ j = 1024 * (t + 1) := by
  change ((∀ k < j, ((k / 1024 : Nat) : Int) ≤ (t : Int)) ∧
    (t : Int) < ((j / 1024 : Nat) : Int)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := fun k hk => Int.ofNat_le.1 (h1 k hk)
    have h4 := Int.ofNat_lt.1 h2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · omega
    · have := h3 (1024 * (t + 1)) hgt; omega
  · rintro rfl
    exact ⟨fun k hk => Int.ofNat_le.2 (by omega), Int.ofNat_lt.2 (by omega)⟩

/-- `H_z = 1` at `g = 0`: after all events at `12` both nodes hold the chain up to slot `3`, of
height `1`. -/
theorem hz_zero : Healing.HZ run Set.univ 0 = 1 := by
  unfold Healing.HZ
  rw [cutZ_zero]
  have hset : {h | ∃ y ∈ Set.univ, ∃ j, Healing.FirstCutAfter run j 12 ∧
      (run.state y j).fg.hmax = h} = {1} := by
    have hm : ∀ y, ((world 13).1 y).fg.hmax = 1 := fun y => (world_good 13 y).fg.hmax
    ext h
    constructor
    · rintro ⟨y, -, j, hj, rfl⟩
      rw [show (12 : Time) = ((12 : Nat) : Int) from rfl, firstCutAfter_iff] at hj
      subst hj
      rw [state_first]
      exact hm y
    · rintro rfl
      exact ⟨w0, trivial, _, firstCutAfter_iff.2 rfl, by rw [state_first]; exact hm w0⟩
  rw [hset, csSup_singleton]

/-- `v0` signs its row of height `2` at `rt 2 = t_11 + Δ = 45`. -/
theorem sign45 :
    run.SignAt w0 (1024 * (4 * 11 + 1) + 2) (row w0 2) ∧
      run.time (1024 * (4 * 11 + 1) + 2) = 45 := by
  obtain ⟨st', hex, -⟩ := tick_report_new (s := 11) (by decide) (by decide)
    (world_good (4 * 11 + 1) w0)
  obtain ⟨hc, ht⟩ := tick0_callAt hex (k := 2) (by decide) rfl
  exact ⟨⟨_, hc⟩, ht⟩

/-- **The reset `a_z = 45`** at `g = 0`: the first honest signing of a height pair of height
`H_z + 1 = 2`. -/
theorem run_isReset :
    Healing.IsReset run Set.univ 0 45 := by
  unfold Healing.IsReset
  rw [hz_zero]
  refine ⟨⟨w0, trivial, _, _, (sign45).1, rfl, (sign45).2⟩, fun y _ k att hs hh => ?_⟩
  obtain ⟨q, -, rfl, ht⟩ := run_facts.sign y k att hs
  rw [row_h] at hh
  subst hh
  rw [ht]
  decide

/-- `R_z = t_{slot(a_z) + 2k + 5} = t_20 = 80 ≤ t_21`. -/
theorem resetSlot_le :
    sp.ts (sp.slot 45 + 2 * sp.k + 5 : Nat) ≤ sp.ts ((21 : Nat) : Int) := by
  rw [show (45 : Time) = ((45 : Nat) : Int) from rfl, slot_nat, ts_nat, ts_nat]
  decide

/-- `c_F = 11 = ⌈(6Δ + Δ_F)/(4Δ)⌉` at `Δ_F = 36` (C1.2 takes the upper bound; the strict lower
bound says the window is not widened), and `c_F + k_F ≤ δ_t` at `k_F = 0`. -/
theorem cF_bounds :
    4 * sp.Δ * (((11 : Nat) : Time) - 1) < 6 * sp.Δ + 36 ∧
      6 * sp.Δ + 36 ≤ 4 * sp.Δ * ((11 : Nat) : Time) ∧ 11 + 0 ≤ sp.toParams.δt := by
  decide

/-! ## The regime premises -/

/-- **The HS shared premises** at `g = 0`, `Δ_F = 36`. -/
theorem run_hsShared : Healing.HSShared run Set.univ dg 0 36 :=
  ⟨dg_noColl run, dg_genesis, run_healthy run_facts,
    fun y _ k hk => absurd hk (run_facts.noRestart y k),
    by decide⟩

/-- `Catch(2Δ)` at `g = 0`, vacuously: no block is accepted before `ḡ = 0`. -/
theorem run_catch : Healing.CatchRun run Set.univ 0 (2 * sp.Δ) := by
  intro x _ i B _ hi
  rw [gbar_zero] at hi
  exact absurd hi (by change ¬ (((i / 1024 : Nat) : Int) < 0); omega)

/-! ## The entry and the window -/

/-- The store after `v0`'s acceptance of the entry `blk 21` holds the chain up to slot `21`. -/
theorem entry_sigma :
    (run.post (1024 * (4 * 21) + 2)).fg.σ (blk 21).root = cs 21 :=
  ((propose_cut (s := 21) (by decide)).2.2.2.2).sigma 21 le_rfl

/-- **The entry `E_3`**: `v0` accepts `blk 21` at cut `1024 · 84 + 2`, the entry of its state. -/
theorem run_runEntry :
    Compose.RunEntry run Set.univ w0 (1024 * (4 * 21) + 2) (blk 21) :=
  ⟨trivial, (propose_cut (s := 21) (by decide)).1, by rw [entry_sigma, cs_Th]; rfl⟩

/-- The entry's height is `3 ≥ H_z + 1`. -/
theorem entry_height :
    Healing.HZ run Set.univ 0 + 1 ≤ ((run.post (1024 * (4 * 21) + 2)).fg.σ (blk 21).root).h := by
  rw [hz_zero, entry_sigma, cs_h]; decide

/-- The entry's previous height `2 ≥ H_z + 1` is justified. -/
theorem entry_previous :
    ((run.post (1024 * (4 * 21) + 2)).fg.σ (blk 21).root).previousHeightJustified ∧
      Healing.HZ run Set.univ 0 + 1 ≤ ((run.post (1024 * (4 * 21) + 2)).fg.σ (blk 21).root).hj := by
  rw [hz_zero, entry_sigma]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rw [cs_hj] <;> (try rw [cs_h]) <;> decide

/-- **Retained ready inclusion**: the window's slot `32` has the ready proposal `blk 32`, whose
parent `blk 31` extends the entry. -/
theorem ready_inclusion :
    ∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
      Healing.ReadyProposal run Set.univ prop w kw W.slot W ∧
      21 + 11 ≤ W.slot ∧ W.slot ≤ 21 + 11 + 0 ∧
      ∃ Pr, W.parent = some Pr.root ∧ Anc (run.HonestBlocks Set.univ) (blk 21) Pr :=
  ⟨w0, _, blk 32, by rw [blk_slot]; exact run_ready (by decide),
    by rw [blk_slot], by rw [blk_slot], blk 31, blk_parent_succ 31,
    anc_blk (by decide) fun _ _ hk => ⟨w0, trivial, _, tree_at_vote_deadline w0 31 hk⟩⟩

/-! ## (a) The good window -/

/-- **(a) The literal good window `GW(E_3, 0, 0)`** on the FG projection, at `v0`'s proposal of
`blk 32` on `blk 31` (cut `1024 · 128 + 2`, before `T₁ = t_33`), with the target rows of both
validators for `E_3`; and both validators accept `blk 32` before `T₁ + Δ`. -/
theorem twoRun_goodWindow :
    run.projFG.time (1024 * (4 * 32) + 2) < sp.ts ((21 + 11 + 0 + 1 : Nat) : Int) ∧
      Store.GoodWindow sp.toParams (Payload sp.n) Set.univ run.projFG 11 (blk 21) 0 0 w0
        (1024 * (4 * 32) + 2) (blk 32) (blk 31) {row w0 3, row w1 3} ∧
      ∀ z ∈ Set.univ, ∃ k', run.AcceptAt z k' (blk 32) ∧
        run.time k' < sp.ts ((21 + 11 + 0 + 1 : Nat) : Int) + sp.Δ := by
  obtain ⟨hown, -, htime, hst, -⟩ := propose_cut (s := 32) (by decide)
  have hstore : run.projFG.store w0 (1024 * (4 * 32) + 2) = ((world (4 * 32)).1 w0).fg := by
    rw [Compose.store_eq run_goldilocksRun trivial, hst]
  have hg := (world_good (4 * 32) w0).fg
  have hatts := (world_good (4 * 32) w0).atts
  rw [tip_four] at hg
  have hσ : ∀ m ≤ 31, (run.projFG.store w0 (1024 * (4 * 32) + 2)).σ (blk m).root = cs m :=
    fun m hm => by rw [hstore]; exact hg.sigma m hm
  have hon : ∀ y, (run.projFG.store w0 (1024 * (4 * 32) + 2)).OnChain (blk 31) (row y 3) := by
    intro y
    rw [hstore]
    rcases eq_w0_or_w1 y with rfl | rfl
    · exact (onChain_row0 hg 3).2 ⟨by decide, by decide⟩
    · exact (onChain_row1 hg 3).2 ⟨by decide, by decide⟩
  refine ⟨by rw [ts_nat]; exact htime.trans_lt (by decide), ⟨⟨trivial, ?_, blk_proposer 32, ?_,
    ?_, blk_parent_succ 31, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_,
    by decide, by decide⟩, fun z _ => ?_⟩
  · exact Compose.projFG_callAt.2 hown
  · rw [blk_slot]; exact htime.symm
  · rw [hstore]; exact (mem_tree_iff hg.blocks).2 ⟨31, le_rfl, rfl⟩
  · intro r hr hv _
    rw [hstore, hatts, mem_poolOf] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    rw [hσ 31 le_rfl] at hv
    have h4 := (row_valid_iff (m := 31) _ (by omega)).1 hv
    have h7 : cnt w0 (4 * 32) = 7 := by decide
    have hi6 : i = 6 := by change i / 2 + 1 = 4 at h4; omega
    subst hi6
    exact mem_blk_fgPayload.2 (Or.inl ⟨4, by decide, rfl, rfl⟩)
  · rw [hstore]; exact (mem_tree_iff hg.blocks).2 ⟨21, by decide, rfl⟩
  · rw [hσ 21 (by decide), cs_Th]; rfl
  · rw [hstore]; exact anc_tree hg.blocks (by decide) le_rfl
  · rw [blk_slot, blk_slot]; decide
  · rw [Finset.image_insert, Finset.image_singleton, row_val, row_val, card_w01, gp_q]
  · intro r hr
    rw [hσ 21 (by decide)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;>
      exact ⟨by rw [row_h, cs_h]; rfl, by rw [row_T]; rfl, row_timeout _ _,
        fun _ => by rw [row_fin, cs_hj, cs_J]; rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> exact Or.inl (hon _)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> exact Or.inl (hon _)
  · obtain ⟨k', hk', ht⟩ := run_facts.accept_exists z 32 (by decide)
    refine ⟨k', hk', ?_⟩
    rw [ht, ts_nat, delta1]
    decide

/-! ## (a) C1.2 on the run -/

/-- **(a) C1.2 on the run** (`Healing.Recovery.outcome_service`) at the entry `E_3`, with every
premise discharged; read at the computed values (`h = 3`, previous height justified, `J = E_2`,
`T₁ = t_33`): a good window before `T₁`, its carrier accepted by both validators before `T₁ + Δ`,
or an early justification of `E_3` finalizing `E_2`. -/
theorem twoRun_outcome :
    (∃ (q : Fin sp.n) (j : Nat) (Bs Pr : SA.Blk sp.n (List (FG.Att sp.n)))
        (R : Finset (FG.Att sp.n)),
        run.projFG.time j < sp.ts ((21 + 11 + 0 + 1 : Nat) : Int) ∧
        Store.GoodWindow sp.toParams (Payload sp.n) Set.univ run.projFG 11 (blk 21) 0 0 q j Bs Pr
          R ∧
        ∀ z ∈ Set.univ, ∃ k', run.AcceptAt z k' Bs ∧
          run.time k' < sp.ts ((21 + 11 + 0 + 1 : Nat) : Int) + sp.Δ) ∨
      Compose.EarlyOutcome run Set.univ (blk 21) 3 true (blk 11).root
        (sp.ts ((21 + 11 + 0 + 1 : Nat) : Int)) := by
  have h := (Healing.Recovery.outcome_service sp ro prop dg Set.univ run 0 36 45 11 0
    run_goldilocksRun (run_hsShared) run_catch cF_bounds.2.1 cF_bounds.2.2 (run_isReset) w0 _ _
    (blk 21) 21 (run_ready (by decide))
    (run_runEntry) resetSlot_le (entry_height) (fun _ _ => (entry_previous).2)
    (ready_inclusion)).1
  rw [decide_eq_true (entry_previous).1, entry_sigma, cs_h, cs_J] at h
  exact h

end Consensus.Goldilocks.Witness.TwoRun

end
