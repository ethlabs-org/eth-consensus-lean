module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Adopt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks milestone Service: A1.7, inclusion

At a cut `i` of A1.7, `y` ran its update of slot `s` at a cut `k₀ < i` with no restart since. That
update adopts the honest proposal `P` (`update_adopts`, workbench#12), and the record step of the
Sleepy invariant (`record_step`, at every honest cut) carries the record's descendant of `P` to
`i`. If the record's block is in the frame, it has `HeadSupport` (`served_head_support`, after the
update of `slot(t) − 2` or `slot(t) − 1`: `s` itself in the two slots after the update, else the
node, awake and unrestarted since `t_s + 6Δ`, ran the update of `slot(t) − 2` at its tick), so it
is the confirmed tip. Otherwise the confirmed tip is `Σ.F`; the record's block and `Σ.F` are on the
origin chain, so compatible, and the record's block is not above `Σ.F` (it would be in the frame),
so it is below. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- The first cut of a tick is the AC's tick. -/
private theorem onTick_head (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) : (Node.onTick proposer dg y st t x).2[0]? = some (Node.acCall y st t .tick).2 := by
  simp [Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep]

/-- Along cuts with no restart from `t_s + 6Δ` on, a node awake and joined at `t_s + 6Δ` and at a
later call has run, before that call, the update of `slot(t) − 2` or `slot(t) − 1`. -/
private theorem update_recent (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {s i : Nat} (hyw : tr.awake y (tr.time i))
    (hyj₀ : tr.JoinedAt y (sp.ts s + 6 * sp.Δ))
    (hnr : ∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time k' ≤ tr.time i →
      False)
    (hu : UpdatedNoRestart tr y i s) :
    ∃ s', sp.slot (tr.time i) ≤ s' + 2 ∧ UpdatedNoRestart tr y i s' := by
  by_cases hσ : sp.slot (tr.time i) ≤ s + 2
  · exact ⟨s, hσ, hu⟩
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti : 0 ≤ tr.time i := hrun.time_nonneg i
  set σ := sp.slot (tr.time i)
  set s' := σ - 2
  have hs's : s < s' := by omega
  set τ := sp.ts s' + 6 * sp.Δ
  have hτσ : τ < sp.ts (σ : Int) := by
    simp only [τ, SAParams.ts]
    have : ((s' : Int) + 2) = (σ : Int) := by omega
    rw [← this]; nlinarith
  have hσt : sp.ts (σ : Int) ≤ tr.time i := (SA.ts_le_iff_le_slot sp hti σ).2 le_rfl
  have hsτ : sp.ts s + 6 * sp.Δ < τ := by
    simp only [τ]
    have := (SA.ts_lt_iff sp).2 (show (s : Int) < s' by exact_mod_cast hs's)
    linarith
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ sp.ts s := by simp only [SAParams.ts]; positivity
    linarith
  -- awake at `τ`: a sleep before `t` would end in a restart after `t_s + 6Δ`
  have hwτ : tr.awake y τ := by
    by_contra hna
    obtain ⟨k', hr, h₁, h₂⟩ := hrun.restart_at_wake y hy τ (tr.time i) hτ0 (by linarith) hna hyw
    exact hnr k' hr (by linarith) h₂
  have hpub : sp.toParams.IsPublic τ :=
    ⟨4 * s' + 6, by simp only [τ, SAParams.ts]; ring⟩
  obtain ⟨j, x, hg⟩ := hrun.tick_of_awake y hy τ hτ0 hpub hwτ
  have hne := hg.1
  obtain ⟨hn, htj, -, -, hl⟩ := hg.2.1 0 (List.length_pos_iff.2 hne)
  simp only [Nat.add_zero] at hn htj hl
  have h0 : (Node.exec proposer dg y (tr.state y j) τ (.tick x)).2[0]'(List.length_pos_iff.2 hne) =
      (Node.acCall y (tr.state y j) τ .tick).2 :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (onTick_head y _ τ x))
  rw [h0] at hl
  set ℓ : ACLabel (goldilocksNode sp ro) :=
    ⟨.tick, Node.frame (tr.state y j), ((goldilocksNode sp ro).step y (tr.state y j).ac
      (Node.frame (tr.state y j)) τ .tick).2⟩
  have hl' : tr.label j = some (.ac ℓ) := hl
  -- the cut `j` is no restart, and `y` is joined at `τ`
  have hnrj : ¬ tr.RestartAt y j := by
    rintro ⟨ℓ', ⟨-, hl''⟩, hc⟩
    rw [hl'] at hl''
    cases Cut.ac.inj (Option.some.inj hl'')
    cases hc
  have hslτ : sp.slot τ = s' + 1 := by
    have := ((SA.slot_arithmetic sp (s' + 1)).1 2 (by omega))
    rw [show τ = sp.ts ((s' + 1 : Nat) : Int) + (2 : Nat) * sp.Δ by
      have := (SA.slot_arithmetic sp s').2.2
      simp only [τ]; rw [this]; push_cast; ring]
    exact this
  have hjτ : tr.JoinedAt y τ := by
    intro k hk hkτ
    refine ⟨by rw [show sp.toParams.slotOf τ = sp.slot τ from rfl, hslτ]; omega, ?_⟩
    by_cases hks : tr.time k ≤ sp.ts s + 6 * sp.Δ
    · obtain ⟨-, h⟩ := hyj₀ k hk hks
      have hsl₀ : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 := by
        have := ((SA.slot_arithmetic sp (s + 1)).1 2 (by omega))
        rwa [show sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + (2 : Nat) * sp.Δ by
          rw [(SA.slot_arithmetic sp s).2.2]; push_cast; ring]
      rw [show sp.toParams.slotOf (sp.ts s + 6 * sp.Δ) = s + 1 from hsl₀] at h
      rw [show sp.toParams.slotOf τ = s' + 1 from hslτ]
      simp only [Nat.add_sub_cancel] at h ⊢
      rw [sp.slotTime_eq] at h ⊢
      have : (s : Int) ≤ s' := by exact_mod_cast hs's.le
      have : 4 * sp.Δ * (s : Int) ≤ 4 * sp.Δ * (s' : Int) := by nlinarith
      exact h.trans this
    · exact (hnr k hk (lt_of_not_ge hks) (hkτ.trans (by linarith))).elim
  have hjoin : SA.joined sp (tr.state y j).ac τ :=
    ((joined_projection sp ro dg H tr proposer hrun y hy τ).2.1 j ⟨_, hn, hl'⟩ hnrj htj).1 hjτ
  have hji : j < i := by
    by_contra h
    have := hrun.time_mono (Nat.le_of_not_lt h)
    linarith
  refine ⟨s', by omega, j, hji, ℓ, ⟨⟨hn, ?_⟩, rfl, htj, ?_⟩, fun k' hjk hki hr => ?_⟩
  · simp [RunTrace.projAC, hl', RunTrace.acLabel]
  · rw [projAC_state hrun.toLocalRun hy j]; exact htj ▸ hjoin
  · have h₁ := hrun.time_mono hjk.le
    have h₂ := hrun.time_mono hki.le
    exact hnr k' hr (by linarith) h₂

/-- The record's block after the update moves forward to cut `i` (the record step at every honest
cut). -/
private theorem record_extends (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hinv : SleepyInvariant tr H) {y : Fin sp.n} (hy : y ∈ H)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {k₀ : Nat}
    (h₀ : ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E) :
    ∀ i, k₀ + 1 ≤ i → ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact h₀
  | succ m _ ih =>
    obtain ⟨E, hE, hEr, hPE⟩ := ih
    obtain ⟨E', hE', hE'r, hEE'⟩ := record_step hinv hrun hnc hy m E hE hEr
    exact ⟨E', hE', hE'r, hPE.trans hEE'⟩

/-- **A1.7, inclusion.** -/
theorem inclusion_sleepy : Inclusion := by
  intro sp ro proposer dg H tr ΔF hrun hnc hsl hg p hp k P s hP hPs hpj y hy i hc ht hyw hyj
    hyw₀ hyj₀ hnr hu
  have hinv := sleepy_invariant hrun hnc hsl
  have hcoh :=
    (ac_projection _ _ dg H _ tr proposer
      (goldilocksNode_requirements sp ro) hrun.toLocalRun hnc).coherent
  obtain ⟨k₀, hk₀, ℓ₀, hupd, -⟩ := id hu
  obtain ⟨E, hE, hEr, hPE⟩ := record_extends hrun hnc hinv hy
    (update_adopts hrun hnc hsl hp hP hPs hpj hy hupd) i hk₀
  by_cases hin : ∃ R, RecordAt tr y i R
  · obtain ⟨R, hR⟩ := hin
    obtain rfl : R = E := hcoh.1 ⟨y, hy, i, hR.1.1⟩ hE (hR.2.trans hEr.symm)
    obtain ⟨s', hs', hu'⟩ := update_recent hrun hy hyw hyj₀ hnr hu
    rw [(head_confirmed_of_support hrun hy hR
      (served_head_support hinv hrun hnc hsl hy hc hyw hyj hs' hu' hR)).2]
    exact hPE
  · have hΦ := frameOK_state hrun.toLocalRun hy i
    rw [show tr.confirmedAt y i = (Node.frame (tr.state y i)).F from
      SA.acConfirmed_eq_F hΦ fun ⟨R, hR, hr⟩ => hin ⟨R, hR, hr⟩]
    -- the record's block is on the origin chain with `Σ.F`, and not above `Σ.F` in the tree
    obtain ⟨C, hC, hCr, hCo⟩ := hinv.record y hy i
    obtain rfl : C = E := hcoh.1 ⟨y, hy, i, hC⟩ hE (hCr.trans hEr.symm)
    have hF : (tr.state y i).fg.F ∈ (tr.state y i).fg.tree := hΦ.rooted.1.1
    have hEc : OnOriginChain tr H C := onOriginChain_iff.2 (hCo.elim Or.inl fun ⟨s, ho⟩ =>
      Or.inr ⟨C, s, ho, Relation.ReflTransGen.refl⟩)
    rcases OnOriginChain.compatible hrun hnc hinv.origins_compatible hE ⟨y, hy, i, hF⟩ hEc
      (hinv.caches y hy i).1 with h | h
    · exact hPE.trans h
    -- `Σ.F ⪯ C` inside the honest blocks would put `C` in the frame
    obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree sp.toParams (Payload sp.n) _ _
      (fg_reachable hrun.toLocalRun hy i)
    have hΦg : FrameOK (⟨(tr.state y i).fg.tree, _, _, ∅⟩ :
        Frame sp.n (List (FG.Att sp.n)) (Payload sp.n)) :=
      { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
        F_anc_fcRoot := Relation.ReflTransGen.refl, viableHeads_subset := Set.empty_subset _
        fcRoot_anc_viableHeads := fun _ h => h.elim }
    exact (hin ⟨C, ⟨hC, SA.anc_tree_of_anc_U hcoh hΦg (fun X hX => ⟨y, hy, i, hX⟩) hF h hC⟩,
      hCr⟩).elim

end Consensus.Goldilocks.Compose

end
