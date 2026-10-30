module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient

public section

/-! # Goldilocks Healing: HS.4 (a), the acquired common path

`hs234-exact-interface.md` §5 "actual acquisition" (HS.4 (a), with #88's current-source arm),
over `Γ` (§1: `GoldilocksRun`, `HSShared`, `Catch(2Δ)`, `Prop⁺(G_p)`, `SettledIn … w i₀ m c`):
either the phase has changed after all events at `w + D`, `D = (8k + 48)Δ + 2G_p`, or there is
an honest proposal `W` of a slot `s` with `t_s ≥ r`, unanimous and protected (HS.3 (b)), whose
entry `E` at `h = ht(W) ∈ {ℓ, m}` every honest node receives as a current source in
`[t_s, t_s + 6Δ]` (`acquired_or_changed`).

The assembly (proved): if the phase has not changed at the first cut `j_D` after `w + D`, it is
`(m, c)` at every cut of `[i₀, j_D]` (`phaseOn_of_not_changed`, HR.2's monotone phase). `Prop⁺`
at `r` gives the first ready proposal `P` of slot `s`, `t_s ≤ r + G_p`; HS.3 (b) protects it
(`ready_protected`, from `FrozenTreeAgreement` as an opaque hypothesis); every honest node
receives a source `C ⪰ P` in `[t_s, t_s + 6Δ]` (`ready_sources`). If every such source has
`P`'s height, `W = P`. Otherwise a source of height `m > ht(P) = m − 1` has a fresh optimistic
origin of label `s + 1` that later proposal parents extend (`descendant_source_parents`); the
ready proposal `Q` after `t_s + 14Δ` then has height `m`, and `W = Q`. Time: `t_a < w + 8Δ`,
`r < w + (8k + 16)Δ`, `t_Q + 6Δ < w + (8k + 36)Δ + 2G_p`.

Open (named contracts with the note's premises): `ready_allowed` (a ready proposal of the phase is
allowed: the aligned reader of `Geo.viableHeads_iff`, which this file cannot import),
`ready_sources` (the regular update at `t_s + 6Δ` and report tracing), and
`descendant_source_parents` (stored-fast-origin provenance and HS.2's proposal-boundary
transfer). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ## Time -/

/-- `w + 4Δ ≤ t_a` (`DrainCommon.slotA_spec`; restated, `DrainCommon` is being edited). -/
private theorem slotA_le (w : Time) : w + 4 * sp.Δ ≤ sp.ts (slotA sp w) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hne : {s : Nat | w + 4 * sp.Δ ≤ sp.ts s}.Nonempty := by
    refine ⟨(w + 4 * sp.Δ).toNat, ?_⟩
    change w + 4 * sp.Δ ≤ 4 * sp.Δ * (((w + 4 * sp.Δ).toNat : Nat) : Int)
    have h1 := Int.self_le_toNat (w + 4 * sp.Δ)
    have h2 : (0 : Int) ≤ ((w + 4 * sp.Δ).toNat : Int) := Int.natCast_nonneg _
    have h3 : (1 : Int) ≤ 4 * sp.Δ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h3 h2]
  exact Nat.sInf_mem hne

/-- `t_a < w + 8Δ` for `w ≥ 0`: `a` is the least slot with `t_a ≥ w + 4Δ`. -/
private theorem slotA_lt {w : Time} (hw : 0 ≤ w) : sp.ts (slotA sp w) < w + 8 * sp.Δ := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  rcases Nat.eq_zero_or_pos (slotA sp w) with h0 | hpos
  · rw [h0]
    simp only [SAParams.ts, Nat.cast_zero, mul_zero]
    linarith
  · have hn : slotA sp w - 1 ∉ {s : Nat | w + 4 * sp.Δ ≤ sp.ts s} :=
      Nat.notMem_of_lt_sInf (Nat.sub_lt hpos Nat.one_pos)
    simp only [Set.mem_ofPred_eq, not_le, SAParams.ts] at hn
    simp only [SAParams.ts]
    push_cast [Nat.cast_sub hpos] at hn
    linarith

/-- `r = t_a + (8k + 8)Δ`. -/
private theorem rTime_eq (w : Time) :
    rTime sp w = sp.ts (slotA sp w) + (8 * (sp.k : Time) + 8) * sp.Δ := by
  simp only [rTime, SAParams.ts]
  push_cast
  ring

/-! ## Phase persistence -/

/-- Every cut with a frontier has a phase case. -/
private theorem phaseAt_some {i m : Nat} (hF : FrontierAt tr.projFG H i m) :
    ∃ c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n))), PhaseAt tr.projFG H i m c := by
  classical
  by_cases hJ : ∃ J, JustifiedAt tr.projFG H i (m - 1) J
  · obtain ⟨J, hJ⟩ := hJ
    by_cases hC : ContestAt tr.projFG H i m J
    · exact ⟨.contest J, hF, hJ, hC⟩
    · exact ⟨.top J, hF, hJ, hC⟩
  · exact ⟨.gap, hF, fun J h => hJ ⟨J, h⟩⟩

/-- Two cases with the same rank and the first's top `J` kept are equal. -/
private theorem case_eq {β : Type} {c c' : PhaseCase β} (h₁ : c.rank ≤ c'.rank)
    (h₂ : c'.rank ≤ c.rank) (ht : ∀ J, c.topJ = some J → c'.topJ = some J) : c = c' := by
  cases c <;> cases c' <;> simp only [PhaseCase.rank, PhaseCase.topJ] at h₁ h₂ ht
  all_goals first
    | rfl
    | omega
    | rw [Option.some.inj (ht _ rfl)]

private theorem store_eq' (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

private theorem fg_run' (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
  obtain ⟨-, -, hf⟩ := hs.healthy
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hn := sp.toParams.hn
  exact ⟨Compose.fg_projection _ _ dg H _ tr hreq hs.genesisRoot hrun.toLocalRun hs.noColl,
    by change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n; omega⟩

/-- **The phase persists through an unchanged endpoint** (`hs234-exact-interface.md` §5, §4's
sandwich; HR.2): if the phase at `j` is the phase at `i₀`, it is `(m, c)` at every cut of
`[i₀, j]` (vacuous when `j < i₀`): the frontier is squeezed to `m` (`Σ.h_max` only grows), and
then the case rank is squeezed and the top `J` kept (`phaseAt_mono`). -/
theorem phaseOn_of_not_changed (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hset : SettledIn tr H g w i₀ m c) {j : Nat} (hnc : ¬ PhaseChanged tr.projFG H i₀ j) :
    PhaseOn tr.projFG H i₀ j m c := by
  obtain ⟨hfg, hq⟩ := fg_run' hrun hs
  have h₀ := hset.2.2
  have hj' : PhaseAt tr.projFG H j m c := by
    by_contra hn
    refine hnc fun m' c' h₁ h₂ => ?_
    obtain ⟨rfl, rfl⟩ := phaseAt_eq hfg hq h₀ h₁
    exact hn h₂
  intro k h₁ h₂
  obtain ⟨⟨y₀, hy₀, hm₀⟩, -⟩ := h₀.frontierAt
  have hFj := hj'.frontierAt.2
  have hF : FrontierAt tr.projFG H k m := by
    refine ⟨⟨y₀, hy₀, le_antisymm ?_ ?_⟩, fun y hy => ?_⟩
    · have := hFj y₀ hy₀
      have := hmax_mono hrun.toLocalRun hy₀ h₂
      simp only [store_eq' hrun hy₀] at *
      omega
    · have := hmax_mono hrun.toLocalRun hy₀ h₁
      simp only [store_eq' hrun hy₀] at *
      omega
    · have := hFj y hy
      have := hmax_mono hrun.toLocalRun hy h₂
      simp only [store_eq' hrun hy] at *
      omega
  obtain ⟨c', hc'⟩ := phaseAt_some hF
  obtain ⟨r₁, t₁⟩ := phaseAt_mono hfg hq h₁ h₀ hc'
  obtain ⟨r₂, t₂⟩ := phaseAt_mono hfg hq h₂ hc' hj'
  rwa [case_eq r₂ r₁ t₂] at hc'

/-! ## Store facts -/

/-- The block that `ac_to_fg` returns is in the frame of the call. -/
private theorem toFG_mem_frame {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2.1 = some C) : C ∈ Φ.tree := by
  unfold SA.acToFG at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1.1.1

/-- A source of an honest node is in its FG tree. -/
private theorem toFG_mem (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y k ℓ C) : C ∈ (tr.state y k).fg.tree :=
  mem_tree_of_frame hrun hy hto.1 (toFG_mem_frame hto.2.2)

/-- Allowedness moves between honest stores that hold the block (`Geo.effAllowed_transfer`). -/
private theorem effAllowed_move (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : EffAllowed (tr.state y i).fg m c X) (hX : X ∈ (tr.state z j).fg.tree) :
    EffAllowed (tr.state z j).fg m c X :=
  ⟨hX, by rw [σ_eq_honest hrun hnc hz hy hX h.1]; exact h.2.1, fun J hJ =>
    store_anc_of_honest_anc hrun hnc hz ((h.2.2 J hJ).mono fun Z hZ => ⟨y, hy, i, hZ⟩) hX⟩

/-- A held descendant of an allowed block is allowed (`Geo.effAllowed_of_anc`). -/
private theorem effAllowed_desc {st : Store sp.toParams (Payload sp.n)}
    {acp₀ : Payload sp.n} (hr : st.Reachable acp₀) {A W : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : EffAllowed st m c A) (hW : W ∈ st.tree) (hAW : st.Anc A W) : EffAllowed st m c W :=
  ⟨hW, h.2.1.trans (h_le_of_store_anc hr hAW), fun J hJ => (h.2.2 J hJ).trans hAW⟩

/-- The own block of an honest proposal is accepted at its cut, so it is held after it. -/
private theorem proposal_mem (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt p k W) :
    tr.CallAt p k (.fg (.block W true)) ∧ W ∈ (tr.state p (k + 1)).fg.tree := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
  rcases Compose.blockCall_cases hrun.toLocalRun hp hc with hg |
    ⟨j, x, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  obtain ⟨hacc, -⟩ :=
    own_block_accepted hrun.toLocalRun hreq hrun.genesis_root_ok hnc hp hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  refine ⟨hc, ?_⟩
  have hlaw := hrun.cutLaw p hp _ _ hc
  rw [tr.state_succ_of_call hc, (Goldilocks.Store.tree_grows _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hp _)).1 _ _ hlaw.2.1]
  exact Set.mem_insert _ _

/-- Heights at a cut of the phase are at most its frontier. -/
private theorem h_le_frontier (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H)
    {k j : Nat} (hkj : k ≤ j) (hph : PhaseAt tr.projFG H j m c)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree) :
    ((tr.state y k).fg.σ X.root).h ≤ m := by
  have hX' := Compose.tree_mono hrun.toLocalRun hy hkj hX
  have hR := Compose.fg_reachable hrun.toLocalRun hy j
  have h1 := (Goldilocks.Store.cache_invariants _ _ _ _ hR).2.2.2.2.1 X hX'
  have h2 := hph.frontierAt.2 y hy
  rw [store_eq' hrun hy] at h2
  rw [σ_eq_honest hrun hnc hy hy hX' hX] at h1
  omega

/-- Ancestry inside the honest blocks does not lower the state height, across honest stores. -/
private theorem h_le_of_anc_run (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {k j : Nat}
    {X C : SA.Blk sp.n (List (FG.Att sp.n))} (hXC : Anc (tr.HonestBlocks H) X C)
    (hC : C ∈ (tr.state y k).fg.tree) (hX : X ∈ (tr.state z j).fg.tree) :
    ((tr.state z j).fg.σ X.root).h ≤ ((tr.state y k).fg.σ C.root).h := by
  rw [σ_eq_honest hrun hnc hz hy hX (mem_of_honest_anc hrun hnc hy hXC hC)]
  exact h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
    (store_anc_of_honest_anc hrun hnc hy hXC hC)

/-- The floor is `m` or `m − 1`. -/
private theorem floor_cases {β : Type} (m : Nat) (c : PhaseCase β) :
    m - 1 ≤ phaseFloor m c ∧ phaseFloor m c ≤ m := by
  cases c <;> simp only [phaseFloor] <;> omega

/-! ## HS.3 (b) at a ready proposal -/

/-- **HS.3 (b) at a ready proposal after `r`** (`hs234-exact-interface.md` §5 "HS.3(b) gives exact
`P` votes and the later-parent property"): under `Γ`, a ready proposal `P` of slot `s` with
`t_s ≥ r`, in the phase through slot `s` (every honest slot-`s` vote is before `t_{s+1}`), is on
a protected branch. HS.3 is taken as the opaque hypothesis `hagree`: its premises at `i = i₀` are
discharged here (`i₀ ≤ k_P`; the proposer ticks at `t_{s−1} ∈ [w, t_{s−1} + 3Δ]`, so
`time i₀ ≤ t_{s−1} + 3Δ`; `ḡ ≤ t_{s−1} + 3Δ`), and only this proof reads HS.3's shape. -/
theorem ready_protected (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hagree : FrozenTreeAgreement) {s kP : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H (sp.toParams.proposer s) kP s P) (hr : rTime sp w ≤ sp.ts s)
    (hon : ∀ k, tr.time k < sp.ts ((s : Int) + 1) → PhaseOn tr.projFG H i₀ k m c) :
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      (P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot)) ∧
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  have hgb0 := gbar_nonneg g
  have ha := slotA_le (sp := sp) w
  have hrr := rTime_eq (sp := sp) w
  have hk0 : (0 : Time) ≤ (sp.k : Time) := Nat.cast_nonneg _
  have hkΔ : 0 ≤ (sp.k : Time) * sp.Δ := mul_nonneg hk0 hΔ.le
  have hts : w + 12 * sp.Δ ≤ sp.ts s := by nlinarith
  obtain ⟨hpH, -, -, hprop, hPs, -⟩ := id hP
  have hkP : tr.time kP = sp.ts s := by
    rw [hprop.2.2, hPs, sp.slotTime_eq]; rfl
  have hi₀ : i₀ ≤ kP := by
    by_contra h
    have := hset.2.1.2 kP (not_le.1 h)
    linarith
  -- the proposer ticks at `t_{s−1}`, a time `≥ w`
  have hts1 : sp.ts ((s : Int) - 1) = sp.ts s - 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have htime : tr.time i₀ ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ := by
    have hgt : gbar g ≤ sp.ts ((s : Int) - 1) := by linarith
    obtain ⟨j, _x, hne, hcs, -⟩ := hrun.tick_of_awake _ hpH _ (hgb0.trans hgt)
      ⟨4 * ((s : Int) - 1), by simp only [SAParams.ts]; ring⟩ (hs.healthy.2.1 _ hpH _ hgt)
    obtain ⟨-, ht, -, -, -⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at ht
    have hij : i₀ ≤ j := by
      by_contra h
      have := hset.2.1.2 j (not_le.1 h)
      linarith
    have := hrun.time_mono hij
    linarith
  have hacr := Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl
  have hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      PhaseOn tr.projFG H i₀ k m c := fun y hy k ℓ e hv he => by
    refine hon k (not_le.1 fun hle => ?_)
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).1 hle
    have h2 : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hacr.localRun hy hv).2.1
    rw [← h2, he] at this
    omega
  obtain ⟨h₁, h₂, h₃⟩ := (hagree sp ro dg H tr g ΔF w i₀ i₀ m c hrun hs hc hset le_rfl _ kP s P
    hP hi₀ htime (by linarith) hvotes).2 Gp hp hr
  exact ⟨fun y hy k ℓ e hv he => let ⟨a, b, _⟩ := h₁ y hy k ℓ e hv he;
    ⟨a, b.imp_left And.right⟩, h₂, h₃⟩

/-! ## The open contracts -/

/-- **A ready proposal of the settled phase is allowed** (`hs234-exact-interface.md` §4 "The
parent's full walk ends at an allowed head (`proposal_head_viable`); `P` is allowed by
`effAllowed_of_anc`", §5 "`P` is retained and allowed by HS.1"): the proposer reads the
effective geometry at `t_s ≥ w` (`Geo.viableHeads_iff`, it holds the phase's evidence from `w`
on), its walk ends at a viable head of state height `≥ ℓ` that extends the top `J`, and `P`
extends it. Open here only because `Geo` imports `Service` and so cannot be imported by it. -/
theorem ready_allowed (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hset : SettledIn tr H g w i₀ m c) {p : Fin sp.n}
    {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p kP s P)
    (hws : w ≤ sp.ts s) (hon : PhaseOn tr.projFG H i₀ kP m c) :
    EffAllowed (tr.post kP).fg m c P := by
  sorry

/-- **Every honest node receives a current source above a protected ready proposal**
(`hs234-exact-interface.md` §5 "acquisition", first two paragraphs): under `Γ`, let `P` be a
ready proposal of slot `s` with `t_s ≥ r` on a protected branch, in the phase through
`v₁ = t_s + 6Δ`. Every honest node's regular update at `v₁` has raw result and deepest fast
selection `P` (all honest slot-`s` votes are `P`, faulty weight cannot support a deeper result,
honest support is more than half), compatible with every live lock (HS.2's drain and transfer, so
the write is not vetoed); the FG update at `v₁` returns a candidate extending `P`, or reporting
is suppressed by a report record extending it, which traces back to an actual `ac_to_fg` return.
A source extending the fresh `P` is returned at `t_s` or later. -/
theorem ready_sources (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain) {s kP : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H (sp.toParams.proposer s) kP s P) (hr : rTime sp w ≤ sp.ts s)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      (P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
      sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr) :
    ∀ y ∈ H, ∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
      tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C := by
  sorry

/-- **A higher source above a protected proposal is followed by later proposal parents**
(`hs234-exact-interface.md` §5, "The only obstruction" and "The provenance bridge"): under `Γ`,
with `P` as in `ready_sources`, let an honest `ac_to_fg` return `C ⪰ P` in `[t_s, t_s + 6Δ]`
with `ht(C) > ht(P)`. `C` lies below the stored block `B` of an honest fast-lock write
(`stored_fast_lock_provenance`, through the source's lock instance); its counted heads extend
`B ⪰ C ⪰ P`, so their slot is `≥ s`; label `s` cannot support a strict descendant of `P` (all
honest slot-`s` votes are `P`, thresholds exceed faulty weight), a regular label-`(s+1)` write is
after `t_s + 10Δ`, so the origin is optimistic of label `s + 1`. HS.2's first transfer and the
proposal-boundary helper of §2 then put `B`, so `C`, below the parent of every honest proposal of
a slot `≥ s + 2` in the phase. -/
theorem descendant_source_parents (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain) {s kP : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H (sp.toParams.proposer s) kP s P) (hr : rTime sp w ≤ sp.ts s)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root ∧
      (P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
      sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC y k ℓ C)
    (hk : sp.ts s ≤ tr.time k) (hk' : tr.time k ≤ sp.ts s + 6 * sp.Δ)
    (hPC : Anc (tr.HonestBlocks H) P C)
    (hht : ((tr.state y k).fg.σ P.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s + 2 ≤ s' →
      P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
      sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr := by
  sorry

/-! ## The assembly -/

/-- **The acquired path at a witness** (`hs234-exact-interface.md` §5, last paragraphs): a
protected ready proposal `W` of slot `s`, allowed, with `ht(W) ∈ {ℓ, m}`, whose height every
honest node receives as a current source `C ⪰ W` in `[t_s, t_s + 6Δ]`: `C`'s entry at `ht(W)` is
`W`'s (entry constancy), and `C` is allowed (it extends the allowed `W`). -/
private theorem acquired_of_sources (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {s kW : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : ReadyProposal tr H (sp.toParams.proposer s) kW s W)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = W.root ∧
      (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
      sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr)
    (hall : EffAllowed (tr.post kW).fg m c W)
    (hsrc : ∀ y ∈ H, ∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
      tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) W C ∧
      ((tr.state y k).fg.σ C.root).h = ((tr.post kW).fg.σ W.root).h)
    (hhm : ((tr.post kW).fg.σ W.root).h = phaseFloor m c ∨ ((tr.post kW).fg.σ W.root).h = m)
    (hws : w ≤ sp.ts s) (hr : rTime sp w ≤ sp.ts s) (hD : sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) :
    ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
      (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
      tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧ sp.toParams.proposer s ∈ H ∧
      EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
      w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
      (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        e.msg.head = W.root ∧
        (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
          Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
      (∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
          tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
          EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
          EffAllowed (tr.state y k).fg m c C) ∨
        ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
          att.T = E.root) ∧
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
      ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
        tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
        PhaseOn tr.projFG H i₀ k' m c →
        ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr := by
  have hnc := hs.noColl
  obtain ⟨hpH, -, -, hprop, hWs, -⟩ := hW
  obtain ⟨hcall, hWt⟩ := proposal_mem hrun hnc hpH hprop
  have hpost : tr.post kW = tr.state (sp.toParams.proposer s) (kW + 1) :=
    (tr.state_succ_of_call hcall).symm
  rw [hpost] at hall hsrc hhm
  have hR := Compose.fg_reachable hrun.toLocalRun hpH (kW + 1)
  obtain ⟨⟨E, hE, hEr, hEW, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hR W hWt
  have hETh' : ((tr.state _ (kW + 1)).fg.σ E.root).Th = E.root := hETh.trans hEr.symm
  have hsub : ∀ {y : Fin sp.n} (_ : y ∈ H) (i : Nat),
      (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun hy i X hX => ⟨_, hy, i, hX⟩
  refine ⟨s, ((tr.state (sp.toParams.proposer s) (kW + 1)).fg.σ W.root).h, E, W, kW, ?_, ?_,
    hprop, hWs, hpH, ?_, ?_, hws, hr, hD, hon, hvotes, fun y hy => Or.inl ?_, hlater,
    hparents⟩ <;> try rw [hpost]
  · exact hhm
  · exact Store.one_le_h hR hWt
  · exact ⟨⟨hE, hETh'⟩, hEh, hEW⟩
  obtain ⟨k, ℓ, C, hto, hk₁, hk₂, hWC, hCh⟩ := hsrc y hy
  have hCt := toFG_mem hrun hy hto
  have hRy := Compose.fg_reachable hrun.toLocalRun hy k
  have hEC : Anc (tr.HonestBlocks H) E C := (hEW.mono (hsub hpH _)).trans hWC
  have hEt := mem_of_honest_anc hrun hnc hy hEC hCt
  have hσE := σ_eq_honest hrun hnc hy hpH hEt hE
  have hWCs := store_anc_of_honest_anc hrun hnc hy hWC hCt
  refine ⟨k, ℓ, C, hto, hk₁, hk₂, hWCs, ⟨⟨hEt, by rw [hσE, hETh']⟩, by rw [hσE, hEh],
    store_anc_of_honest_anc hrun hnc hy hEC hCt⟩, hCh, ?_⟩
  exact effAllowed_desc hRy (effAllowed_move hrun hnc hpH hy hall
    (mem_of_honest_anc hrun hnc hy hWC hCt)) hCt hWCs

/-- **HS.4 (a)** (`hs234-exact-interface.md` §5 "actual acquisition", timing): under `Γ`, with
HS.2 and HS.3 as opaque hypotheses, the phase has changed after all events at `w + D`, or the
common path is acquired (HS.4 (a)'s second branch, with #88's current-source arm). -/
theorem acquired_or_changed (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain)
    (hagree : FrozenTreeAgreement) :
    (∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG H i₀ j') ∨
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
        tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧ sp.toParams.proposer s ∈ H ∧
        EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
        w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
        (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          e.msg.head = W.root ∧
          (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
            Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
        (∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
            tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
            EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
            EffAllowed (tr.state y k).fg m c C) ∨
          ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
            att.T = E.root) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
          PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
          P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
          sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr := by
  classical
  by_cases hch : ∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG H i₀ j'
  · exact Or.inl hch
  right
  push Not at hch
  obtain ⟨jD, hjD, hnch⟩ := hch
  have hnc := hs.noColl
  have hper := phaseOn_of_not_changed hrun hs hset hnch
  -- time
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  have hgb0 := gbar_nonneg g
  have hw0 : 0 ≤ w := by linarith
  have ha := slotA_le (sp := sp) w
  have ha' := slotA_lt (sp := sp) hw0
  have hrr := rTime_eq (sp := sp) w
  have hk0 : (0 : Time) ≤ (sp.k : Time) := Nat.cast_nonneg _
  have hkΔ : 0 ≤ (sp.k : Time) * sp.Δ := mul_nonneg hk0 hΔ.le
  have hD : D_HS sp Gp = (8 * (sp.k : Time) + 48) * sp.Δ + 2 * Gp := rfl
  have hGp : 0 ≤ Gp := by
    obtain ⟨s₀, k₀, B₀, -, h₁, h₂, -⟩ := hp (gbar g) le_rfl
    linarith
  -- the cuts before the endpoint are in the phase
  have hi₀D : i₀ ≤ jD := by
    by_contra h
    have := hset.2.1.2 jD (not_le.1 h)
    linarith [hjD.2]
  have hphD : PhaseAt tr.projFG H jD m c := hper jD hi₀D le_rfl
  have hltD : ∀ k, tr.time k ≤ w + D_HS sp Gp → k < jD := fun k hk => by
    by_contra h
    have := hrun.time_mono (not_lt.1 h)
    linarith [hjD.2]
  have hbefore : ∀ k, tr.time k ≤ w + D_HS sp Gp → PhaseOn tr.projFG H i₀ k m c :=
    fun k hk k' h₁ h₂ => hper k' h₁ (h₂.trans (hltD k hk).le)
  have hafter : ∀ t, t ≤ w + D_HS sp Gp → ∀ jv, FirstCutAfter tr jv t →
      PhaseOn tr.projFG H i₀ jv m c := fun t ht jv hjv k' h₁ h₂ => by
    refine hper k' h₁ (h₂.trans ?_)
    by_contra h
    have := hjv.1 jD (not_le.1 h)
    linarith [hjD.2]
  have hfl := floor_cases m c
  -- the facts of a ready proposal after `r` that ends before the endpoint
  have ready : ∀ {s kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))},
      ReadyProposal tr H (sp.toParams.proposer s) kP s P → rTime sp w ≤ sp.ts s →
      sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp →
      tr.time kP = sp.ts s ∧ kP + 1 ≤ jD ∧
      P ∈ (tr.state (sp.toParams.proposer s) (kP + 1)).fg.tree ∧
      tr.post kP = tr.state (sp.toParams.proposer s) (kP + 1) ∧
      ((tr.post kP).fg.σ P.root).h ≤ m ∧ EffAllowed (tr.post kP).fg m c P ∧
      ((∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        e.msg.head = P.root ∧
        (P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
          Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot)) ∧
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
      ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
        P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
        sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
        ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr) := by
    intro s kP P hP hr hsD
    obtain ⟨hpH, -, -, hprop, hPs, -⟩ := id hP
    have hkP : tr.time kP = sp.ts s := by
      rw [hprop.2.2, hPs, sp.slotTime_eq]; rfl
    obtain ⟨hcall, hPt⟩ := proposal_mem hrun hnc hpH hprop
    have hkD := hltD kP (by linarith)
    have hpost : tr.post kP = tr.state (sp.toParams.proposer s) (kP + 1) :=
      (tr.state_succ_of_call hcall).symm
    refine ⟨hkP, hkD, hPt, hpost, by rw [hpost]; exact h_le_frontier hrun hnc hpH hkD hphD hPt,
      ready_allowed hrun hs hc hset hP (by linarith) (hbefore kP (by linarith)),
      ready_protected hrun hs hc hp hset hagree hP hr fun k hk => hbefore k ?_⟩
    have : sp.ts ((s : Int) + 1) = sp.ts s + 4 * sp.Δ := by simp only [SAParams.ts]; ring
    linarith
  -- the first ready proposal after `r`
  obtain ⟨s, kP, P, -, hs₁, hs₂, hP⟩ := hp (rTime sp w) (by linarith)
  have hsD : sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp := by rw [hD]; nlinarith
  obtain ⟨hkP, hkPD, hPt, hpostP, hPm, hallP, hvP, hlP, hpP⟩ := ready hP hs₁ hsD
  have honP := hafter _ hsD
  have hsrc := ready_sources hrun hs hc hp hset hclean hP hs₁ honP hvP hlP hpP
  have hpH : sp.toParams.proposer s ∈ H := hP.1
  have hPfl : phaseFloor m c ≤ ((tr.post kP).fg.σ P.root).h := hallP.2.1
  rw [hpostP] at hPm hPfl
  by_cases hob : ∃ y ∈ H, ∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
      tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state y k).fg.σ C.root).h ≠ ((tr.post kP).fg.σ P.root).h
  · -- a higher source: the second proposal `Q` after `t_s + 14Δ` has height `m`
    obtain ⟨y₀, hy₀, k₀, ℓ₀, C₀, hto₀, hk₀, hk₀', hPC₀, hne₀⟩ := hob
    rw [hpostP] at hne₀
    have hC₀t := toFG_mem hrun hy₀ hto₀
    have hPC₀h := h_le_of_anc_run hrun hnc hy₀ hpH hPC₀ hC₀t hPt
    have hC₀m := h_le_frontier hrun hnc hy₀ (hltD k₀ (by linarith)).le hphD hC₀t
    have hPt₀ := mem_of_honest_anc hrun hnc hy₀ hPC₀ hC₀t
    have hσP := σ_eq_honest hrun hnc hy₀ hpH hPt₀ hPt
    have hdesc := descendant_source_parents hrun hs hc hp hset hclean hP hs₁ honP hvP hlP hpP
      hy₀ hto₀ hk₀ hk₀' hPC₀ (by rw [hσP]; omega)
    obtain ⟨sQ, kQ, Q, -, hq₁, hq₂, hQ⟩ := hp (sp.ts s + 14 * sp.Δ) (by linarith)
    have hsQ : s + 2 ≤ sQ := by
      by_contra h
      have h' : (sQ : Int) ≤ s + 1 := by omega
      have := mul_le_mul_of_nonneg_left h' (by linarith : (0 : Int) ≤ 4 * sp.Δ)
      simp only [SAParams.ts] at hq₁
      nlinarith
    have hQD : sp.ts sQ + 6 * sp.Δ ≤ w + D_HS sp Gp := by rw [hD]; nlinarith
    obtain ⟨hkQ, hkQD, hQt, hpostQ, hQm, hallQ, hvQ, hlQ, hpQ⟩ := ready hQ (by linarith) hQD
    have hpQH : sp.toParams.proposer sQ ∈ H := hQ.1
    obtain ⟨Pr, hpar, hC₀Pr⟩ := hdesc sQ Q kQ hsQ hQ.2.2.2.2.1 hQ.2.2.2.1 hpQH
      (hbefore kQ (by linarith))
    have hPrU : Pr ∈ tr.HonestBlocks H := by
      by_cases he : C₀ = Pr
      · exact he ▸ ⟨y₀, hy₀, k₀, hC₀t⟩
      · exact (Anc.mem hC₀Pr he).2
    have hC₀Q : Anc (tr.HonestBlocks H) C₀ Q :=
      hC₀Pr.tail ⟨hPrU, ⟨_, hpQH, kQ + 1, hQt⟩, hpar⟩
    have hQm' : ((tr.post kQ).fg.σ Q.root).h = m := by
      have := h_le_of_anc_run hrun hnc hpQH hy₀ hC₀Q hQt hC₀t
      rw [hpostQ] at hQm ⊢
      omega
    have hsrcQ := ready_sources hrun hs hc hp hset hclean hQ (by linarith)
      (hafter _ hQD) hvQ hlQ hpQ
    refine acquired_of_sources hrun hs hQ hvQ hlQ hpQ hallQ (fun y hy => ?_) (Or.inr hQm')
      (by linarith) (by linarith) hQD (hafter _ hQD)
    obtain ⟨k, ℓ, C, hto, hk₁, hk₂, hQC⟩ := hsrcQ y hy
    have hCt := toFG_mem hrun hy hto
    have h₁ := h_le_of_anc_run hrun hnc hy hpQH hQC hCt hQt
    have h₂ := h_le_frontier hrun hnc hy (hltD k (by linarith)).le hphD hCt
    rw [← hpostQ, hQm'] at h₁
    exact ⟨k, ℓ, C, hto, hk₁, hk₂, hQC, by omega⟩
  · -- every source has `P`'s height: `W = P`
    refine acquired_of_sources hrun hs hP hvP hlP hpP hallP (fun y hy => ?_) ?_
      (by linarith) hs₁ hsD honP
    · obtain ⟨k, ℓ, C, hto, hk₁, hk₂, hPC⟩ := hsrc y hy
      exact ⟨k, ℓ, C, hto, hk₁, hk₂, hPC, by_contra fun hne =>
        hob ⟨y, hy, k, ℓ, C, hto, hk₁, hk₂, hPC, hne⟩⟩
    · rw [hpostP]
      omega

end Consensus.Goldilocks.Healing

end
