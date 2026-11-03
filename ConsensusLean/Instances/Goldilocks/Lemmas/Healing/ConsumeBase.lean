module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Goldilocks Healing, HS.5: the shared facts of the consumption step

`hs5-exact-helpers.md` §1 (the context `Γ` and the cut discipline) for the three steps of HS.5's
consumption (`ConsumeUpper`, `ConsumeMature`, `ConsumeContinue`):

* cuts: a cut at a time `≤ T` is before the first cut after `T` (`FirstCutAfter.lt_of_time_le`),
  first cuts after later times are later (`FirstCutAfter.le_of_le`, index inclusion, not endpoint
  timestamps), and a first cut after every time exists under `Healthy(g)`
  (`exists_firstCutAfter_of_healthy`);
* blocks: an honest proposal is accepted by its proposer at its cut (`accept_of_proposesAt`), a
  parent edge is an ancestry inside the honest blocks (`anc_of_parentRoot`), ancestry does not
  raise the slot (`slot_le_of_anc`), state heights at a cut of the phase are at most the frontier
  (`h_le_of_phaseAt`), and a block of state height `m`, or above the floor, at a cut of the phase
  `(m, c)` is allowed in its geometry (`effAllowed_of_height`: in the top-`J` case, no contest;
  `effAllowed_of_floor_lt`);
* deadlines: with no honest restart after `ḡ`, a deadline is at most `max(τ, ḡ) + Δ'`
  (`deadline_le_of_healthy`);
* sources: an `ac_to_fg` return is held (`toFG_mem_tree`), and an honest vote of slot `z` is cast
  by `t_z + Δ` (`cast_time_le_slot`, from `Compose.cast_head_fcRoot`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## Cuts -/

/-- A cut at a time `≤ T` is before the first cut after `T`. -/
theorem FirstCutAfter.lt_of_time_le {N S L : Type} {tr : Trace N S L} {j k : Nat} {T : Time}
    (hj : FirstCutAfter tr j T) (hmono : Monotone tr.time) (hk : tr.time k ≤ T) : k < j := by
  by_contra h
  have := hmono (not_lt.1 h)
  linarith [hj.2]

/-- **Index inclusion**: the first cut after `T₁ ≤ T₂` is at or before the first cut after `T₂`
(every cut before the latter is at a time `≤ T₂`, not only its endpoint). -/
theorem FirstCutAfter.le_of_le {N S L : Type} {tr : Trace N S L} {j₁ j₂ : Nat} {T₁ T₂ : Time}
    (h₁ : FirstCutAfter tr j₁ T₁) (h₂ : FirstCutAfter tr j₂ T₂) (hT : T₁ ≤ T₂) : j₁ ≤ j₂ := by
  by_contra h
  have := h₁.1 j₂ (not_le.1 h)
  linarith [h₂.2]

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time} {proposer : Nat → Fin sp.n}

/-- Under `Healthy(g)` (an honest node awake from `ḡ` on, so a cut after every time), the first
cut after any time `T` exists. -/
theorem exists_firstCutAfter_of_healthy (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) {y : Fin sp.n} (hy : y ∈ H) (T : Time) :
    ∃ j, FirstCutAfter tr j T := by
  classical
  obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon y hy (max T (gbar g) + 1)
    (hs.healthy.2.1 y hy _ (by change gbar g ≤ _; linarith [le_max_right T (gbar g)]))
  have hex : ∃ i, T < tr.time i := ⟨i, by linarith [le_max_left T (gbar g)]⟩
  exact ⟨Nat.find hex, fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩

/-! ## Blocks -/

/-- **An honest proposal is accepted by its proposer at its cut**, so it is held after it. -/
theorem accept_of_proposesAt (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
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
  refine ⟨hc, ?_, (tr.state_succ_of_call hc).symm⟩
  have hlaw := hrun.cutLaw p hp _ _ hc
  rw [tr.state_succ_of_call hc, (Goldilocks.Store.tree_grows _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hp _)).1 _ _ hlaw.2.1]
  exact Set.mem_insert _ _

/-- The right end of an ancestry inside `S` is in `S` when the left end is. -/
theorem mem_of_anc_right {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc S A B) (hA : A ∈ S) : B ∈ S := by
  induction h with
  | refl => exact hA
  | tail _ hst _ => exact hst.2.1

/-- **A parent edge extends an ancestry** inside the honest blocks: `A ⪯ Pr`, `X` held with
parent root `Pr.root`, so `A ⪯ X`. -/
theorem anc_of_parentRoot {A Pr X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : A ∈ tr.HonestBlocks H) (hAPr : Anc (tr.HonestBlocks H) A Pr)
    (hX : X ∈ tr.HonestBlocks H) (hpar : X.parent = some Pr.root) :
    Anc (tr.HonestBlocks H) A X :=
  hAPr.tail ⟨mem_of_anc_right hAPr hA, hX, hpar⟩

/-- Ancestry inside a coherent set does not raise the slot. -/
theorem slot_le_of_anc {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hS : Coherent S)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc S A B) : A.slot ≤ B.slot := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact ih.trans (hS.2 _ hst.1 _ hst.2.1 hst.2.2).le

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- **Heights at a cut of the phase are at most its frontier** (a held block at a cut `k ≤ j`,
with the phase at `j`). -/
theorem h_le_of_phaseAt (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    {k j : Nat} (hkj : k ≤ j) (hph : PhaseAt tr.projFG H j m c)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree) :
    ((tr.state y k).fg.σ X.root).h ≤ m := by
  have hX' := Compose.tree_mono hrun.toLocalRun hy hkj hX
  have hR := Compose.fg_reachable hrun.toLocalRun hy j
  have h1 := (Goldilocks.Store.cache_invariants _ _ _ _ hR).2.2.2.2.1 X hX'
  have h2 := hph.frontierAt.2 y hy
  rw [store_eq hrun hy] at h2
  rw [σ_eq_honest hrun hnc hy hy hX' hX] at h1
  omega

/-- **A block of state height `m` is allowed** in the geometry of the phase `(m, c)` at a cut of
the phase: its height is at least the floor, and in the top-`J` case it extends `J` (otherwise it
would be a contest against `J`). -/
theorem effAllowed_of_height (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {m k : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hph : PhaseAt tr.projFG H k m c) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hXh : ((tr.state y k).fg.σ X.root).h = m) :
    EffAllowed (tr.state y k).fg m c X := by
  refine ⟨hX, ?_, fun J hJ => ?_⟩
  · rw [hXh]
    cases c <;> simp only [phaseFloor] <;> omega
  · subst hJ
    by_contra hn
    exact hph.2.2 ⟨y, hy, X, by rw [store_eq hrun hy]; exact hX,
      by rw [store_eq hrun hy]; exact hXh, by rw [store_eq hrun hy]; exact hn⟩

/-- **A block above the floor is allowed** at a cut of the phase `(m, c)`: its height is at most
the frontier `m`, so in the top-`J` case (floor `m − 1`) it is `m` (`effAllowed_of_height`). -/
theorem effAllowed_of_floor_lt (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {m k : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hph : PhaseAt tr.projFG H k m c) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hlt : phaseFloor m c < ((tr.state y k).fg.σ X.root).h) :
    EffAllowed (tr.state y k).fg m c X := by
  have hle := h_le_of_phaseAt hrun hnc hy le_rfl hph hX
  cases c with
  | top J =>
    simp only [phaseFloor] at hlt
    exact effAllowed_of_height hrun hy hph hX (by omega)
  | gap => exact ⟨hX, hlt.le, fun J hJ => by cases hJ⟩
  | contest J => exact ⟨hX, hlt.le, fun J' hJ => by cases hJ⟩

/-- **Deadlines after `ḡ`** (no honest restart after `ḡ`): the deadline of an object of time `τ`
at an honest node is at most `max(τ, ḡ) + Δ'`, for every delivery parameter `Δ'`. -/
theorem deadline_le_of_healthy (hs : HSShared tr H dg g ΔF) {y : Fin sp.n} (hy : y ∈ H)
    (k : Nat) (τ Δ' : Time) : tr.deadline y k τ Δ' ≤ max τ (gbar g) + Δ' := by
  have h := deadline_le_restarts (T := tr.projAC) (c := k)
    (fun k' _ hk' => hs.noRestart y hy k' (Compose.projAC_restartAt.1 hk')) τ
  simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
  linarith

/-! ## Sources and votes -/

/-- The block that `ac_to_fg` returns is in the frame of the call. -/
private theorem toFG_mem_frame {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2 = some C) : C ∈ Φ.tree := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1.1.1

/-- A source of an honest node is in its FG tree. -/
theorem toFG_mem_tree (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y k ℓ C) : C ∈ (tr.state y k).fg.tree :=
  mem_tree_of_frame hrun hy hto.1 (toFG_mem_frame hto.2.2)

/-- **An honest vote of slot `z` is cast by `t_z + Δ`** (the vote guard;
`Compose.cast_head_fcRoot`). -/
theorem cast_time_le_slot (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e) :
    tr.time k ≤ sp.ts e.msg.slot + sp.Δ :=
  (Compose.cast_head_fcRoot
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hy hv).2

end Consensus.Goldilocks.Healing

end
