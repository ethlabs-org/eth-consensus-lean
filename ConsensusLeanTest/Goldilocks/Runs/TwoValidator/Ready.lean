module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.FactsProof
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
@[expose] public section

/-! # The healthy two-validator run: ready proposals

On the run of `Runs.TwoValidator.Run`, `v0`'s own block of every slot `s ≥ 1` is a ready proposal
(`Healing.ReadyProposal`), made at the third cut of its tick at `t_s` (`1024 · 4s + 2`). Its
slot-`(s − 1)` support references are the two votes for the block of slot `s − 1`, which every
node holds at `t_s + Δ`. So `Prop⁺(4Δ)` holds from `ḡ = 0` (`run_propPlus`).

The state facts are read from the per-time node states (`world_good`) and the cuts of `v0`'s tick
(`tick_propose`); joinedness from the absence of restarts (`run_facts`). -/

namespace Consensus.Goldilocks.Witness.TwoRun

open Node SA

/-! ## The cuts of a time -/

/-- The state of `y` at the first cut of time `t` is its state in the world of `t`. -/
theorem state_first (y : Fin sp.n) (t : Nat) : run.state y (1024 * t) = (world t).1 y := by
  have h := segOf_eq t 0 0 (by decide) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at h
  rw [run_state]
  unfold preState
  rw [h, segs_zero]
  dsimp only
  split_ifs with hy
  · subst hy; rw [show 1024 * t % 8 = 0 by omega]; rfl
  · rfl

/-- The first cut at a time `≥ t` is the cut `1024 t`. -/
theorem firstCutFrom_iff {j t : Nat} : run.FirstCutFrom j (t : Int) ↔ j = 1024 * t := by
  change ((t : Int) ≤ ((j / 1024 : Nat) : Int) ∧
    ∀ k < j, ((k / 1024 : Nat) : Int) < (t : Int)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := fun k hk => Int.ofNat_lt.1 (h2 k hk)
    have h4 := Int.ofNat_le.1 h1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · omega
    · have := h3 (1024 * t) hgt; omega
  · rintro rfl
    exact ⟨Int.ofNat_le.2 (by omega), fun k hk => Int.ofNat_lt.2 (by omega)⟩

/-- The cuts of `v0`'s tick at `t` are the cuts `1024 t + k` of the run, at time `t`. -/
theorem tick0_callAt {t : Nat} {st' : St} {cs : List (Cut N)}
    (hex : Node.onTick prop dg w0 ((world t).1 w0) (t : Int) 0 = (st', cs)) {k : Nat}
    (hk : k < 8) {c : Cut N} (hc : cs[k]? = some c) :
    run.CallAt w0 (1024 * t + k) c ∧ run.time (1024 * t + k) = t := by
  have hs0 := segs_zero t
  rw [show ex (world t).1 w0 t (.tick 0) = (st', cs) from hex] at hs0
  have hi : 1024 * t + k = 1024 * t + 8 * 0 + k := rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hi, run_node (by decide) hk hs0]
  · rw [hi, run_label _ _ _ (by decide) hk, hs0]; exact hc
  · rw [hi, run_time _ _ _ (by decide) hk]

/-- No node is ever unjoined: nobody restarts. -/
theorem run_joined (y : Fin sp.n) (t : Time) :
    run.JoinedAt y t :=
  fun k hk => absurd hk (run_facts.noRestart y k)

/-! ## `v0`'s proposal -/

/-- An AC cut leaves the FG store. -/
theorem cutPost_ac_fg (y : Fin sp.n) (t : Time) (st : St) (ℓ : ACLabel N) :
    (cutPost y t st (.ac ℓ)).fg = st.fg := by
  rw [cutPost_eq]

/-- **`v0`'s proposal of slot `s ≥ 1`**, at the cut `1024 · 4s + 2` of its tick at `t_s`: the
acceptance of the block of slot `s`, from the FG store of the world of `t_s`, after which the
store holds the chain up to slot `s`. -/
theorem propose_cut {s : Nat} (hs : 1 ≤ s) :
    run.AcceptAt w0 (1024 * (4 * s) + 2) (blk s) ∧ run.pos (1024 * (4 * s) + 2) = 2 ∧
      run.time (1024 * (4 * s) + 2) = 4 * (s : Int) ∧
      (run.state w0 (1024 * (4 * s) + 2)).fg = ((world (4 * s)).1 w0).fg ∧
      FGGood (run.post (1024 * (4 * s) + 2)).fg s := by
  obtain ⟨st', e, hex, -, hv⟩ := tick_propose hs (world_good (4 * s) w0)
  have hc : (ex (world (4 * s)).1 w0 (4 * s) (.tick 0)) = (st', _) := hex
  have hs0 := segs_zero (4 * s)
  rw [hc] at hs0
  have hi : 1024 * (4 * s) + 2 = 1024 * (4 * s) + 8 * 0 + 2 := rfl
  obtain ⟨hcall, htime⟩ := tick0_callAt hex (k := 2) (by decide) rfl
  refine ⟨hcall, show (1024 * (4 * s) + 2) % 8 = 2 by omega, by rw [htime]; push_cast; rfl, ?_, ?_⟩
  · rw [hi, run_state_seg (by decide) (by decide) hs0]
    simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil, cutPost_ac_fg]
  · have hfull := foldl_seg hs0 (k := 7) le_rfl
    dsimp only at hfull
    rw [hc] at hfull
    simp only [List.take_succ_cons, List.take_nil, List.foldl_cons, List.foldl_nil] at hfull
    rw [hi, run_post (by decide) (by decide) hs0]
    simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
    rw [← cutPost_ac_fg w0 _ _ ⟨.block (blk s), Node.frame st', [e]⟩,
      ← cutPost_ac_fg w0 _ _ ⟨.toFG, Node.frame st', []⟩, hfull]
    exact hv.fg

/-- `v0`'s proposal of slot `s ≥ 1` is its own block, processed at `t_s`. -/
theorem run_proposesAt {s : Nat} (hs : 1 ≤ s) :
    run.ProposesAt w0 (1024 * (4 * s) + 2) (blk s) := by
  obtain ⟨hacc, hpos, htime, -⟩ := propose_cut hs
  refine ⟨⟨⟨true, hacc⟩, by rw [hpos]; decide⟩, blk_proposer s, ?_⟩
  rw [htime, blk_slot]

/-- Every node holds the chain up to slot `s` at the first cut of `t_s + Δ`. -/
theorem tree_at_vote_deadline (y : Fin sp.n) (s : Nat)
    {m : Nat} (hm : m ≤ s) : blk m ∈ (run.state y (1024 * (4 * s + 1))).fg.tree := by
  rw [state_first]
  have h := (world_good (4 * s + 1) y).fg
  rw [tip_four1] at h
  exact (mem_tree_iff h.blocks).2 ⟨m, hm, rfl⟩

/-- **The own block of every slot `s ≥ 1` is a ready proposal**, made at the cut
`1024 · 4s + 2`. -/
theorem run_ready
    {s : Nat}
    (hs : 1 ≤ s) :
    Healing.ReadyProposal run Set.univ prop w0 (1024 * (4 * s) + 2) s (blk s) := by
  refine ⟨Set.mem_univ _, rfl, run_joined _ _, run_proposesAt hs, blk_slot s, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  intro x hx _ y _ j hj
  rw [show sp.ts ((k + 1 : Nat) : Int) + sp.Δ = ((4 * (k + 1) + 1 : Nat) : Int) by
    rw [ts_nat]; push_cast; rfl, firstCutFrom_iff] at hj
  subst hj
  rw [blockSupport_blk] at hx
  have hh : x.head = (blk k).root := by
    rcases List.mem_pair.1 hx with rfl | rfl <;> rfl
  exact ⟨blk k, tree_at_vote_deadline y (k + 1) (by omega), hh.symm, by rw [blk_slot]⟩

/-- **`Prop⁺(4Δ)` from `ḡ = 0`**: every window `[τ, τ + 4]` with `τ ≥ 0` holds the start of a
slot `s ≥ 1`, whose own block is a ready proposal. -/
theorem run_propPlus :
    Healing.PropPlus run Set.univ prop 0 (4 * sp.Δ) := by
  intro τ hτ
  rw [show gbar 0 = 0 from max_self 0] at hτ
  refine ⟨τ.toNat / 4 + 1, _, _, by omega, ?_, ?_, run_ready (by omega)⟩
  · rw [ts_nat]; push_cast
    dsimp only [Time] at *; omega
  · rw [ts_nat, delta1]; push_cast
    dsimp only [Time] at *; omega

end Consensus.Goldilocks.Witness.TwoRun

end
