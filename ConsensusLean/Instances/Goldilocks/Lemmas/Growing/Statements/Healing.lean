module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Statements.HealingAC

public section

/-! # The growing-fault run-level healing statements imply the static ones

At `H := fun _ => H₀` every honesty read, at any time or cohort horizon, is `H₀`, the blocks held
while honest are the honest blocks, `HealthyRunAt` is `HealthyRun` and the namers at any horizon
are the static namers (`Lemmas/Growing/Run/Const`); the healing vocabulary of
`Statements/Healing/Growing` is then the static one, so each statement there implies its static
counterpart (with any cohort horizon). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Vocabulary

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}

theorem hz_const (g : Time) : Growing.HZ tr (fun _ => H) g = HZ tr H g := rfl

theorem isReset_const {g a : Time} : Growing.IsReset tr (fun _ => H) g a ↔ IsReset tr H g a := by
  simp only [Growing.IsReset, IsReset, hz_const]; aesop

theorem highEntries_const (Hz : Nat) :
    Growing.HighEntries tr (fun _ => H) Hz = HighEntries tr H Hz := by
  ext E; simp only [Growing.HighEntries, HighEntries, Set.mem_ofPred_eq]; aesop

theorem catchRun_const {g κ : Time} :
    Growing.CatchRun tr (fun _ => H) g κ ↔ CatchRun tr H g κ := by
  simp only [Growing.CatchRun, CatchRun, RunTrace.honestBlocksAt_const]; aesop

theorem noRestartAfter_const {t : Time} :
    Growing.NoRestartAfter tr (fun _ => H) t ↔ NoRestartAfter tr H t := by
  simp only [Growing.NoRestartAfter, NoRestartAfter]; aesop

theorem settledAt_const {d g κ w : Time} :
    Growing.SettledAt tr (fun _ => H) d g κ w ↔ SettledAt tr H g κ w := by
  constructor
  · intro h
    exact ⟨h.late, h.joined, fun j hj m c hp y hy => h.evidence j hj m c hp y hy,
      fun x hx i B ha ht y hy j hj hanc => h.catchUp x i B hx ha ht y j hy hj
        (by rwa [RunTrace.honestBlocksAt_const])⟩
  · intro h
    exact ⟨h.late, h.joined, fun j hj m c hp y hy => h.evidence j hj m c hp y hy,
      fun x i B hx ha ht y j hy hj hanc => h.catchUp x hx i B ha ht y hy j hj
        (by rwa [RunTrace.honestBlocksAt_const] at hanc)⟩

theorem readyProposal_const {p : Fin sp.n} {k s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.ReadyProposal tr (fun _ => H) proposer p k s B ↔
      ReadyProposal tr H proposer p k s B := by
  simp only [Growing.ReadyProposal, ReadyProposal]; aesop

theorem propPlus_const {g Gp : Time} :
    Growing.PropPlus tr (fun _ => H) proposer g Gp ↔ PropPlus tr H proposer g Gp := by
  simp only [Growing.PropPlus, PropPlus, readyProposal_const]

theorem hsShared_of_static {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF : Time}
    (h : HSShared tr H dg g ΔF) : Growing.HSShared tr (fun _ => H) dg g ΔF :=
  ⟨h.noColl, h.genesisRoot, (RunTrace.healthyRunAt_const tr).mpr h.healthy,
    noRestartAfter_const.mpr h.noRestart, h.timeoutDelay⟩

theorem highOrigin_const {g : Time} {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.HighOrigin tr (fun _ => H) g x i j B ↔ HighOrigin tr H g x i j B := Iff.rfl

theorem retentionAt_to_static {g a : Time} (h : Growing.RetentionAt tr (fun _ => H) g a) :
    RetentionAt tr H g a where
  comparable := fun x i j B x' i' j' B' ho ho' => by
    rw [← RunTrace.honestBlocksAt_const]; exact h.comparable x i j B x' i' j' B' ho ho'
  fgAtts := fun y hy k att hs ha hh => h.fgAtts y k att hy hs ha hh
  caches := fun y hy k hc ha x i j B ho hi => by
    rw [← RunTrace.honestBlocksAt_const]; exact h.caches y k hy hc ha x i j B ho hi
  votes := fun x i j B ho y hy k ℓ e hc hs => by
    rw [← RunTrace.honestBlocksAt_const]; exact h.votes x i j B ho y k ℓ e hy hc hs
  records := fun hh hle r hr r' hr' => by
    refine h.records hh hle ?_ ?_
    · obtain ⟨y, hy, i, h'⟩ := hr; exact ⟨y, i, hy, h'⟩
    · obtain ⟨y, hy, i, h'⟩ := hr'; exact ⟨y, i, hy, h'⟩

theorem unanimous_const {p : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.Unanimous tr (fun _ => H) p P ↔ Unanimous tr H p P := by
  simp only [Growing.Unanimous, Unanimous]; aesop

theorem honestProposalRun_const {p : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.HonestProposalRun tr (fun _ => H) proposer p P ↔ HonestProposalRun tr H proposer p P :=
  Iff.rfl

theorem includedFrom_const {t₁ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.IncludedFrom tr (fun _ => H) t₁ P ↔ IncludedFrom tr H t₁ P := by
  simp only [Growing.IncludedFrom, IncludedFrom, RunTrace.honestBlocksAt_const]; aesop

theorem inSettledPhase_const {d g : Time} {p : Nat} :
    Growing.InSettledPhase tr (fun _ => H) d g p ↔ InSettledPhase tr H g p := by
  constructor
  · rintro ⟨w, m, c, hs, hw, h⟩
    refine ⟨w, m, c, settledAt_const.mp hs, hw, fun i hi hv => h i hi ?_⟩
    rcases hv with hv | ⟨y, hy, i', e, h1, h2⟩
    · exact Or.inl hv
    · exact Or.inr ⟨y, i', e, h1, hy, h2⟩
  · rintro ⟨w, m, c, hs, hw, h⟩
    refine ⟨w, m, c, settledAt_const.mpr hs, hw, fun i hi hv => h i hi ?_⟩
    rcases hv with hv | ⟨y, i', e, h1, hy, h2⟩
    · exact Or.inl hv
    · exact Or.inr ⟨y, hy, i', e, h1, h2⟩

theorem bridgeAt_const {g a Tb : Time} :
    Growing.BridgeAt tr (fun _ => H) proposer g a Tb ↔ BridgeAt tr H proposer g a Tb := by
  simp only [Growing.BridgeAt, BridgeAt, RunTrace.honestBlocksAt_const, SA.inv_const,
    honestProposalRun_const, inSettledPhase_const, SA.geo_const]
  exact and_congr_right fun _ => ⟨fun h => h 0, fun h _ => h⟩

theorem phaseOn_const {P : Params} {ACP : Type} {tr : FGTrace P ACP} {H : Set (Fin P.n)}
    {d : Time} {i k m : Nat} {c : PhaseCase (NodeBlock P ACP)} :
    Growing.PhaseOn tr (fun _ => H) d i k m c ↔ PhaseOn tr H i k m c := Iff.rfl

theorem settledIn_const {d g w : Time} {i₀ m : Nat}
    {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} :
    Growing.SettledIn tr (fun _ => H) d g w i₀ m c ↔ SettledIn tr H g w i₀ m c := by
  simp only [Growing.SettledIn, SettledIn, settledAt_const]

theorem voteKeeps_const {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.VoteKeeps tr (fun _ => H) ℓ e B ↔ VoteKeeps tr H ℓ e B := by
  simp only [Growing.VoteKeeps, VoteKeeps, RunTrace.honestBlocksAt_const]

end Vocabulary

section Statements

theorem cutAndReset_of_growing (h : Growing.CutAndReset) : CutAndReset := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc
  obtain ⟨h0, h1, h2, h3, h4⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
    ((RunTrace.healthyRunAt_const tr).mpr hh) hnc
  refine ⟨h0, fun y hy k att hs hk => h1 y k att hy hs hk, fun x hx i ℓ C hc ht => ?_,
    fun y hy i X hX hhX => h3 y i hy X hX hhX, fun a ha => ?_⟩
  · simpa only [RunTrace.honestBlocksAt_const] using h2 x i ℓ C hx hc ht
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h4 a (isReset_const.mpr ha)
    exact ⟨e1, fun y hy k att hs hh' => e2 y k att hy hs hh',
      fun y hy k src signed hc ht => e3 y k src signed hy hc ht,
      fun y hy k att hs ht => e4 y k att hy hs ht,
      fun 𝓔 h𝓔 E hE => e5 (a - sp.Δ) le_rfl 𝓔 (by rwa [highEntries_const]) E hE,
      fun T hT y hy k att hs ht => e6 T hT y k att hy hs ht⟩

theorem phaseCount_of_growing {P : Params} {ACP : Type} (h : Growing.PhaseCount P ACP) :
    PhaseCount P ACP := by
  intro acp₀ H U tr hrun hf
  obtain ⟨ha, hd⟩ := h acp₀ (fun _ => H) U tr (Growing.FGLocalRun.const_iff.mpr hrun)
  refine ⟨fun y hy z hz i j B hB B' hB' he => ha y z i j hy hz hf B hB B' hB' he,
    fun m i j c c' hij hp hp' => (hd (tr.time j) hf).1 m i j c c' hij le_rfl hp hp', fun m => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨t, hts, htc⟩ :=
    Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt : (2 : ℕ∞) + 1 ≤ _)
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  obtain ⟨d, hd'⟩ := (htf.image fun i => tr.time (i + 1)).bddAbove
  have hsub : t ⊆ {i | tr.time (i + 1) ≤ d ∧ ∃ c c', PhaseAt tr H i m c ∧
      PhaseAt tr H (i + 1) m c' ∧ c ≠ c'} := fun i hi => ⟨hd' ⟨i, hi, rfl⟩, hts hi⟩
  have := (Set.encard_le_encard hsub).trans ((hd d hf).2 m)
  rw [htc] at this
  exact absurd this (by decide)

theorem phaseCountAll_of_growing (h : Growing.PhaseCountAll) : PhaseCountAll :=
  fun P ACP => phaseCount_of_growing (h P ACP)

theorem resetExistence_of_growing (h : Growing.ResetExistence) : ResetExistence := by
  intro sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨⟨h0, ha⟩, hb, hc', h5, h6, h7⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF Gp
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (propPlus_const.mpr hp)
  obtain ⟨a, hra, hale⟩ := hc' 0 (Growing.resetWindow sp g ΔF Gp 0) le_rfl (Nat.le_add_right _ _)
  have hw : Growing.resetWindow sp g ΔF Gp 0 = cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp) := by
    simp only [Growing.resetWindow, Nat.cast_zero, zero_mul, add_zero]
  rw [hw] at hale
  refine ⟨⟨h0, fun u hu j j' hj hj' =>
      (ha (u + sp.Δ) u hu le_rfl j j' hj hj').imp id settledAt_const.mp⟩,
    fun w hw j j' hj hj' => hb (w + A_HS sp ΔF Gp) w le_rfl (settledAt_const.mpr hw) j j' hj hj',
    ⟨a, isReset_const.mp hra⟩, fun a' ha' => ?_, h5, h6, h7⟩
  obtain ⟨y, k, att, hy, hs', hh, hk⟩ := hra.1
  have := ha'.2 y hy k att hs' hh
  rw [hk] at this
  exact this.trans hale

theorem heightScopedRetention_of_growing (h : Growing.HeightScopedRetention) :
    HeightScopedRetention := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc a ha
  exact retentionAt_to_static (h sp ro proposer dg (fun _ => H) tr g ΔF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
    ((RunTrace.healthyRunAt_const tr).mpr hh) hnc a (isReset_const.mpr ha))

theorem runInclusion_of_growing (h : Growing.RunInclusion) : RunInclusion := by
  intro sp ro proposer dg H tr g ΔF hrun hnc hroot hh hc
  obtain ⟨⟨hd, hha, hca⟩, hrest⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) hnc hroot
    ((RunTrace.healthyRunAt_const tr).mpr hh) (catchRun_const.mpr hc)
  simp only [RunTrace.honestBlocksAt_const] at hha hca hrest
  refine ⟨⟨SA.driven_const.mp hd, SA.healthyAC_const.mp hha, SA.catchAC_const.mp hca⟩,
    fun t₀ ht hinv p P hP ht' => ?_⟩
  obtain ⟨h1, h2⟩ := hrest t₀ ht (SA.inv_const.mpr hinv) p P hP ht'
  exact ⟨fun hg => unanimous_const.mp (h1 (SA.geo_const.mpr hg)),
    fun hu => includedFrom_const.mp (h2 (unanimous_const.mpr hu))⟩

theorem nonInterference_of_growing (h : Growing.NonInterference) : NonInterference := by
  obtain ⟨Tb, hTb, h⟩ := h
  refine ⟨Tb, hTb, fun sp ro proposer dg H tr g ΔF Gp hrun hs hc hp => ?_⟩
  obtain ⟨a, ha, hle, hr, hb⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF Gp
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (propPlus_const.mpr hp) 0 (Growing.resetWindow sp g ΔF Gp 0) le_rfl
    (Nat.le_add_right _ _)
  exact ⟨a, isReset_const.mp ha, by simpa only [Nat.cast_zero, zero_mul, add_zero]
    using hle, retentionAt_to_static hr, bridgeAt_const.mp hb⟩

theorem availableHealing_of_growing (h : Growing.AvailableHealing) : AvailableHealing := by
  intro sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a Tb ha hTb hb p P hP ht hu
  exact includedFrom_const.mp (h sp ro proposer dg (fun _ => H) tr g ΔF Gp
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (propPlus_const.mpr hp) 0 (Growing.resetWindow sp g ΔF Gp 0) le_rfl
    (Nat.le_add_right _ _) a Tb (isReset_const.mpr ha) hTb (bridgeAt_const.mpr hb) p P hP
    (by simpa only [Nat.cast_zero, zero_mul, add_zero] using ht)
    (unanimous_const.mpr hu))

theorem viableWitnessRetention_of_growing (h : Growing.ViableWitnessRetention) :
    ViableWitnessRetention := by
  intro sp ro proposer dg H tr g ΔF hrun hs hc i k m c hph y hy W hW z hz k' h1 h2
  have := h sp ro proposer dg (fun _ => H) tr g ΔF 0
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) i k m c hph y W hy hW z k' hz h1 h2
  simpa only [RunTrace.honestBlocksAt_const] using this

theorem cleanLockDrain_of_growing (h : Growing.CleanLockDrain) : CleanLockDrain := by
  intro sp ro proposer dg H tr g ΔF w i₀ m c hrun hs hc hset
  obtain ⟨h1, h2, h3, h4⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF w 0 i₀ m c
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (settledIn_const.mpr hset)
  refine ⟨fun x hx i j B CV hl hw y hy k ℓ e hcast hs' hph => ?_,
    fun x hx i j B hl hw y hy k ℓ e hcast hs' hph => ?_,
    fun y hy k ℓ hcall hr => h3 y k ℓ hy hcall hr,
    fun s P hP hr y hy k ℓ e hcast hs' hph => ?_⟩
  · have := h1 x i j B CV hx hl hw y k ℓ e hy hcast hs' hph
    simpa only [voteKeeps_const, RunTrace.honestBlocksAt_const] using this
  · have := h2 x i j B hx hl hw y k ℓ e hy hcast hs' hph
    simpa only [voteKeeps_const, RunTrace.honestBlocksAt_const] using this
  · have := h4 s P hP hr y k ℓ e hy hcast hs' hph
    simpa only [RunTrace.honestBlocksAt_const] using this

theorem frozenTreeAgreement_of_growing (h : Growing.FrozenTreeAgreement) :
    FrozenTreeAgreement := by
  intro sp ro proposer dg H tr g ΔF w i₀ i m c hrun hs hc hset hi p kP s P hR hk h1 h2 hph hr
  obtain ⟨hA, hB, hC⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF w 0 i₀ i m c
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (settledIn_const.mpr hset) hi p kP s P (readyProposal_const.mpr hR)
    hk h1 h2 (fun y k ℓ e hy hcast hs' => hph y hy k ℓ e hcast hs') hr
  refine ⟨fun y hy k ℓ e hcast hs' => ?_, fun y hy k ℓ e hcast hs' hph' => ?_,
    fun s' P' k' hs' hP' hprop hpr hph' => ?_⟩
  · have := hA y k ℓ e hy hcast hs'
    simpa only [RunTrace.honestBlocksAt_const] using this
  · have := hB y k ℓ e hy hcast hs' hph'
    simpa only [RunTrace.honestBlocksAt_const] using this
  · have := hC s' P' k' hs' hP' hprop hpr hph'
    simpa only [RunTrace.honestBlocksAt_const] using this

theorem commonPathAcquisition_of_growing (h : Growing.CommonPathAcquisition) :
    CommonPathAcquisition := by
  intro sp ro proposer dg H tr g ΔF Gp w i₀ m c hrun hs hc hp hset
  obtain ⟨hA, hB⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF Gp w (w + D_HS sp Gp) i₀ m c
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (hsShared_of_static hs)
    (catchRun_const.mpr hc) (propPlus_const.mpr hp) le_rfl (settledIn_const.mpr hset)
  refine ⟨?_, fun y hy k C signed hcall hk hph => hB y k C signed hy hcall hk hph⟩
  rcases hA with hA | ⟨s, hh, E, W, kW, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13,
    e14, e15⟩
  · exact Or.inl hA
  · refine Or.inr ⟨s, hh, E, W, kW, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
      fun y hy k ℓ e hcast hs' => ?_, e13, fun y hy k ℓ e hcast hs' hph => ?_,
      fun s' P' k' a1 a2 a3 a4 a5 => ?_⟩
    · have := e12 y k ℓ e hy hcast hs'
      simpa only [RunTrace.honestBlocksAt_const] using this
    · have := e14 y k ℓ e hy hcast hs' hph
      simpa only [RunTrace.honestBlocksAt_const] using this
    · have := e15 s' P' k' a1 a2 a3 a4 a5
      simpa only [RunTrace.honestBlocksAt_const] using this

end Statements

section Recovery

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}

theorem clean_to_static {s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Compose.Growing.Clean tr (fun _ => H) s m B) : Compose.Clean tr H s m B where
  caches := fun y hy j hj => by
    rw [← RunTrace.honestBlocksAt_const]; exact h.caches y j hy hj
  fgAttCut := fun E' hE => by
    obtain ⟨hcE, y, hy, j, hj, hanc, hne⟩ := hE
    refine h.fgAttCut E' ⟨?_, y, j, hy, hj, ?_, hne⟩ <;> rwa [RunTrace.honestBlocksAt_const]
  heightLead := fun y hy i ℓ e hc h1 h2 => by
    have := h.heightLead y i ℓ e hy hc h1 h2
    simpa only [RunTrace.honestBlocksAt_const] using this

theorem rec_to_static {t₀ : Time} (h : Growing.Rec tr (fun _ => H) t₀) : Rec tr H t₀ where
  clean := fun x hx i s B CV hl ht hj m hm => clean_to_static (h.clean x i s B CV hx hl ht hj m hm)
  sources := fun y hy z hz k ℓ C k' ℓ' C' h1 h2 h3 h4 => by
    rw [← RunTrace.honestBlocksAt_const]; exact h.sources y z k ℓ C k' ℓ' C' hy hz h1 h2 h3 h4
  records := fun y hy k ℓ C E hh h1 h2 h3 h4 h5 => h.records y k ℓ C E hh hy h1 h2 h3 h4 h5

theorem upat_of_static {g : Time} {W M cF kF : Nat} (h : UPat tr H proposer g W M cF kF) :
    Growing.UPat tr (fun _ => H) proposer g W M cF kF := by
  intro τ hτ
  obtain ⟨v, h1, h2, h3⟩ := h τ hτ
  refine ⟨v, h1, h2, fun s hs hs' => ?_⟩
  obtain ⟨k, B, hR, hE⟩ := h3 s hs hs'
  refine ⟨k, B, readyProposal_const.mpr hR, fun y i hy => ?_⟩
  obtain ⟨w, kw, W', hR', a, b, Pr, hPr, hanc⟩ := hE y i hy
  exact ⟨w, kw, W', readyProposal_const.mpr hR', a, b, Pr, hPr,
    by rwa [RunTrace.honestBlocksAt_const]⟩

theorem patternPremises_of_static {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {g ΔF Gp : Time} {W M cF kF : Nat}
    (h : PatternPremises tr H proposer dg g ΔF Gp W M cF kF) :
    Growing.PatternPremises tr (fun _ => H) proposer dg g ΔF Gp W M cF kF :=
  ⟨hsShared_of_static h.shared, catchRun_const.mpr h.catchPremise, propPlus_const.mpr h.prop,
    h.cF_lower, h.cF_upper, h.timeout, h.one_le_W, upat_of_static h.pattern, h.long⟩

end Recovery

theorem patternRecovery_of_growing (h : Growing.PatternRecovery) : PatternRecovery := by
  intro sp ro proposer dg H tr g ΔF Gp W M cF kF hrun hpp
  obtain ⟨hr, h2⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF Gp W M cF kF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (patternPremises_of_static hpp)
    0 (Growing.resetWindow sp g ΔF Gp 0) le_rfl (Nat.le_add_right _ _)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hr h2
  exact ⟨rec_to_static hr, fun y hy k hc ht => h2 y k hy hc ht⟩

theorem finalizingCoverage_of_growing (h : Growing.FinalizingCoverage) : FinalizingCoverage := by
  intro sp ro proposer dg H tr g ΔF Gp W M cF kF hrun hpp t ht
  obtain ⟨q, kP, P, hq, hprop, h1, h2, ⟨x, kX, X, hx, hacc, Fx, hFx, hroot, hanc⟩, h3⟩ :=
    h sp ro proposer dg (fun _ => H) tr g ΔF Gp W M cF kF
      (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
      (patternPremises_of_static hpp) 0 (Growing.resetWindow sp g ΔF Gp 0) le_rfl
      (Nat.le_add_right _ _) t
      (by simpa only [Nat.cast_zero, zero_mul, add_zero] using ht)
  refine ⟨q, kP, P, hq, hprop, h1, h2,
    ⟨x, hx, kX, X, hacc, Fx, hFx, hroot, by rwa [RunTrace.honestBlocksAt_const] at hanc⟩,
    fun y hy k hc hk => ?_⟩
  have := h3 y k hy hc hk
  rwa [RunTrace.honestBlocksAt_const] at this

theorem cacheAcceptanceAfterReset_of_growing (h : Growing.CacheAcceptanceAfterReset) :
    CacheAcceptanceAfterReset := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc y hy k B hacc
  exact h sp ro proposer dg (fun _ => H) tr g ΔF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
    ((RunTrace.healthyRunAt_const tr).mpr hh) hnc y k B hy hacc

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-- A growing-fault good window of the constant honest set is a static good window. -/
theorem goodWindow_to_static {P : Params} {ACP : Type} {H : Set (Fin P.n)} {tr : FGTrace P ACP}
    {cF : Nat} {T : NodeBlock P ACP} {a kF : Nat} {p : Fin P.n} {i : Nat}
    {Bs Pr : NodeBlock P ACP} {R : Finset (FG.Att P.n)}
    (h : Store.Growing.GoodWindow P ACP (fun _ => H) tr cF T a kF p i Bs Pr R) :
    Store.GoodWindow P ACP H tr cF T a kF p i Bs Pr R :=
  { proposal := h.proposal
    entry := h.entry
    extends_entry := h.extends_entry
    window := h.window
    quorum := h.quorum
    fgAtts := h.fgAtts
    emitted := h.emitted
    pooled := h.pooled
    params := h.params }

theorem outcomeService_of_growing (h : Growing.OutcomeService) : OutcomeService := by
  intro sp ro proposer dg H tr g ΔF a cF kF hrun hs hc h1 h2 ha p k i T u hR hE hu hz hj hW
  obtain ⟨hA, hB⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF a cF kF
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
    (Healing.hsShared_of_static hs) (Healing.catchRun_const.mpr hc) h1 h2
    (Healing.isReset_const.mpr ha) p k i T u (Healing.readyProposal_const.mpr hR) hE hu hz hj
    (by
      obtain ⟨w, kw, W, hR', a1, a2, Pr, hPr, hanc⟩ := hW
      exact ⟨w, kw, W, Healing.readyProposal_const.mpr hR', a1, a2, Pr, hPr,
        by rwa [RunTrace.honestBlocksAt_const]⟩)
  refine ⟨?_, fun hb => ?_⟩
  · rcases hA with ⟨q, j, Bs, Pr, R, hj', hgw, hacc⟩ | ⟨y, k', X, hy, hacc, ht, hjust, hbd, hall⟩
    · exact Or.inl ⟨q, j, Bs, Pr, R, hj', goodWindow_to_static hgw, hacc⟩
    · exact Or.inr ⟨y, hy, k', X, hacc, ht, hjust, hbd, hall⟩
  · obtain ⟨y, k', X, hy, hacc, ht, hjust⟩ := hB hb
    exact ⟨y, hy, k', X, hacc, ht, hjust⟩

end Consensus.Goldilocks.Compose

end
