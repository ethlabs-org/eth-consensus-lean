module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records

public section

/-! # Goldilocks Refinement: exposure of honest proposals from a live fast lock (L5.1 with C3)

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §5, L5.4 step 3 (L5.1 with C3). The
exposure premise `hexp` of `window_justifies` follows from `Healed.c3` and one extra premise:
**some honest node `y` holds, at a cut `k` with `t_H ≤ time k`, a live fast lock on a block `B`
of its frame**. Then for every honest proposal `X` of a slot `s ≥ s₁` with
`time k + Δ ≤ t_{s₁}`, its held parent `Pr` extends `B` (C3), so `σ[Pr].h ≥ σ[B].h`, and at
equal height `σ[Pr].T_h = σ[B].T_h` (entry constancy). The exposed pair is `(h, T) =
(σ[B].h, σ[B].T_h)`; under `HealedRecords` with `h₀ ≤ h` and `T = (E h).root` it is the entry
of `h`. C4 is not needed for this step.

* `proposesAt_designated`: an honest own proposal `X` of `p` has `p = proposer X.slot`.
* `exposure_of_lock`: the exposure statement from C3 and the lock.
* `window_justifies_of_lock`: `window_justifies_healed` with `hexp` replaced by the lock. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **An honest own proposal is designated**: its proposer is the slot's proposer. -/
theorem proposesAt_designated (hrun : GoldilocksRun proposer dg H tr) {p : Fin sp.n}
    (hp : p ∈ H) {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p k X) : p = proposer X.slot := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, htk⟩ := hX
  rcases Compose.blockCall_cases hrun.toLocalRun hp hc with hg | ⟨j, x, rfl, -, hpr, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨-, -, hpr⟩ := hpr
  rw [htk, slotOf_slotTime] at hpr
  exact hpr.symm

/-- **L5.1 exposure from C3.** If an honest `y` holds at cut `k` (`t_H ≤ time k`) a live fast
lock on the frame block `B`, then the held parent `Pr` of every honest proposal of a slot
`≥ s₁` with `time k + Δ ≤ t_{s₁}` is past `σ[B].h`, or at `σ[B].h` with entry `σ[B].T_h`. -/
theorem exposure_of_lock (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) {s₁ : Nat} (hks : tr.time k + sp.Δ ≤ sp.ts s₁) :
    ∀ p ∈ H, ∀ k' X Pr, tr.ProposesAt p k' X → s₁ ≤ X.slot →
      X.parent = some Pr.root → Pr ∈ (tr.state p k').fg.tree →
      ((tr.state y k).fg.σ B.root).h < ((tr.state p k').fg.σ Pr.root).h ∨
        (((tr.state p k').fg.σ Pr.root).h = ((tr.state y k).fg.σ B.root).h ∧
          ((tr.state p k').fg.σ Pr.root).Th = ((tr.state y k).fg.σ B.root).Th) := by
  intro p hp k' X Pr hX hs hpar hPr
  have hXr := Healing.honestProposalRun_of_proposesAt hrun hnc hp
    (proposesAt_designated hrun hp hX) hX rfl
  have hts : tr.time k + sp.Δ ≤ sp.ts X.slot :=
    hks.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs))
  obtain ⟨Pr', hPr'H, hpar', hanc⟩ := hH.c3 y hy k ℓ hc htH l hl hf B hB hBl X.slot X hXr hts
  obtain rfl : Pr' = Pr := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 hPr'H
    ⟨p, hp, k', hPr⟩ (Option.some.inj (hpar'.symm.trans hpar))
  have hA := Healing.store_anc_of_honest_anc hrun hnc hp hanc hPr
  have hBp : B ∈ (tr.state p k').fg.tree := Healing.mem_of_honest_anc hrun hnc hp hanc hPr
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  rw [Healing.σ_eq_honest hrun hnc hy hp hBy hBp]
  have hr := Compose.fg_reachable hrun.toLocalRun hp k'
  rcases (Healing.σ_h_le_of_anc hr hA).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq.symm, Healing.Th_eq_of_anc hr hA heq.symm⟩

/-- **L5.4 with the exposure from a live fast lock** (`window_justifies_healed` and
`exposure_of_lock`): under `Healed` (so `HealedRecords` from `h₀`), M4 from `s₀ ≤ s₁`, an honest
live fast lock on `B` at a cut `k` with `t_H ≤ time k` and `time k + Δ ≤ t_{s₁}`, with
`(h, T) = (σ[B].h, σ[B].T_h)` and `h₀ ≤ h`, and the honest-row supply for `(h, T)`: some honest
proposal of a slot `s' ∈ [s₁, s₁ + g)` has a held parent past `h`, or justifies `(h, T)`. -/
theorem window_justifies_of_lock (hrun : GoldilocksRun proposer dg H tr)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ ≤ h)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      ∀ p ∈ H, ∀ k' Pr, Pr ∈ (tr.state p k').fg.tree →
        ((tr.state p k').fg.σ Pr.root).h = h → ((tr.state p k').fg.σ Pr.root).Th = T →
        ((tr.state p k').fg.σ Pr.root).bound →
        (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) ∈
          ((tr.state p k').fg.σ Pr.root).pending →
        att.fin = some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J)) :
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  subst hh hT
  exact window_justifies_healed hrun hH.toHealedRecords hs hv hM4 hs₁ hvs hh₀
    (exposure_of_lock hrun hs.noColl hH hy hc htH hl hf hB hBl hks) S hSH hS hsig

end Consensus.Goldilocks.Refinement

end
