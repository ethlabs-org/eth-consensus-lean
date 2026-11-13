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
  simp only [Growing.IsReset, IsReset, hz_const]
  constructor
  · rintro ⟨⟨y, k, att, hy, h⟩, h2⟩
    exact ⟨⟨y, hy, k, att, h⟩, fun y hy k att hs hh => h2 y k att hy hs hh⟩
  · rintro ⟨⟨y, hy, k, att, h⟩, h2⟩
    exact ⟨⟨y, k, att, hy, h⟩, fun y k att hy hs hh => h2 y hy k att hs hh⟩

theorem highEntries_const (Hz : Nat) :
    Growing.HighEntries tr (fun _ => H) Hz = HighEntries tr H Hz := by
  ext E
  constructor
  · rintro ⟨y, i, hy, h⟩; exact ⟨y, hy, i, h⟩
  · rintro ⟨y, hy, i, h⟩; exact ⟨y, i, hy, h⟩

theorem catchRun_const {g κ : Time} :
    Growing.CatchRun tr (fun _ => H) g κ ↔ CatchRun tr H g κ := by
  simp only [Growing.CatchRun, CatchRun, RunTrace.honestBlocksAt_const]
  exact ⟨fun h x hx i B ha ht y hy j hj hF => h x i B hx ha ht y j hy hj hF,
    fun h x i B hx ha ht y j hy hj hF => h x hx i B ha ht y hy j hj hF⟩

theorem noRestartAfter_const {t : Time} :
    Growing.NoRestartAfter tr (fun _ => H) t ↔ NoRestartAfter tr H t :=
  ⟨fun h y hy k hr => h y k hy hr, fun h y k hy hr => h y hy k hr⟩

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
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun x hx hs y hy j hj => h6 x hx hs y j hy hj⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun x hx hs y j hy hj => h6 x hx hs y hy j hj⟩

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
    Growing.Unanimous tr (fun _ => H) p P ↔ Unanimous tr H p P :=
  ⟨fun h x hx j e hv hs => h x j e hx hv hs, fun h x j e hx hv hs => h x hx j e hv hs⟩

theorem honestProposalRun_const {p : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.HonestProposalRun tr (fun _ => H) proposer p P ↔ HonestProposalRun tr H proposer p P :=
  Iff.rfl

theorem includedFrom_const {t₁ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.IncludedFrom tr (fun _ => H) t₁ P ↔ IncludedFrom tr H t₁ P := by
  simp only [Growing.IncludedFrom, IncludedFrom, RunTrace.honestBlocksAt_const]
  exact ⟨fun h y hy j ℓ hc ht hk => h y j ℓ hy hc ht hk,
    fun h y j ℓ hy hc ht hk => h y hy j ℓ hc ht hk⟩

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

theorem heightScopedRetention_of_growing (h : Growing.HeightScopedRetention) :
    HeightScopedRetention := by
  intro sp ro proposer dg H tr g ΔF hstock hrun hh hnc a ha
  exact retentionAt_to_static (h sp ro proposer dg (fun _ => H) tr g ΔF hstock
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
    ((RunTrace.healthyRunAt_const tr).mpr hh) hnc a (isReset_const.mpr ha))

theorem runInclusion_of_growing (h : Growing.RunInclusion) : RunInclusion := by
  intro sp ro proposer dg H tr g ΔF hstock hrun hnc hroot hh hc
  obtain ⟨⟨hd, hha, hca⟩, hrest⟩ := h sp ro proposer dg (fun _ => H) tr g ΔF hstock
    (Consensus.Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) hnc hroot
    ((RunTrace.healthyRunAt_const tr).mpr hh) (catchRun_const.mpr hc)
  simp only [RunTrace.honestBlocksAt_const] at hha hca hrest
  refine ⟨⟨SA.driven_const.mp hd, SA.healthyAC_const.mp hha, SA.catchAC_const.mp hca⟩,
    fun t₀ ht hinv p P hP ht' => ?_⟩
  obtain ⟨h1, h2⟩ := hrest t₀ ht (SA.inv_const.mpr hinv) p P hP ht'
  exact ⟨fun hg => unanimous_const.mp (h1 (SA.geo_const.mpr hg)),
    fun hu => includedFrom_const.mp (h2 (unanimous_const.mpr hu))⟩

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

end Consensus.Goldilocks.Compose

end
