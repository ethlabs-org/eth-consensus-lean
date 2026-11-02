module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ExposureHealed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindowUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPairUpTo

public section

/-! # Goldilocks Refinement: exposure from a live fast lock, through a horizon (L5.1, #137)

consensus-lean#137 (finite-horizon port). `exposure_of_lock`, `window_justifies_of_lock` and
`window_justifies_of_lock_healed` from `HealedUpTo … b` and `HSSharedUpTo … b`. The exposure
holds for honest proposals at cuts by `b` (`HealedUpTo.c3` needs `t_s ≤ b`); the window needs
every window slot by `b` (`hwb`) and `v ≤ b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **L5.1 exposure from C3, through the horizon** (`exposure_of_lock` from `HealedUpTo … b`,
for honest proposals at cuts by `b`). -/
theorem exposure_of_lock_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) {s₁ : Nat} (hks : tr.time k + sp.Δ ≤ sp.ts s₁) :
    ∀ p ∈ H, ∀ k' X Pr, tr.ProposesAt p k' X → s₁ ≤ X.slot → tr.time k' ≤ b →
      X.parent = some Pr.root → Pr ∈ (tr.state p k').fg.tree →
      ((tr.state y k).fg.σ B.root).h < ((tr.state p k').fg.σ Pr.root).h ∨
        (((tr.state p k').fg.σ Pr.root).h = ((tr.state y k).fg.σ B.root).h ∧
          ((tr.state p k').fg.σ Pr.root).Th = ((tr.state y k).fg.σ B.root).Th) := by
  intro p hp k' X Pr hX hs hk'b hpar hPr
  have hXr := Healing.honestProposalRun_of_proposesAt hrun hnc hp
    (proposesAt_designated hrun hp hX) hX rfl
  have hts : tr.time k + sp.Δ ≤ sp.ts X.slot :=
    hks.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs))
  have hsb : sp.ts X.slot ≤ b := proposesAt_time hX ▸ hk'b
  obtain ⟨Pr', hPr'H, hpar', hanc⟩ :=
    hH.c3 y hy k ℓ hc htH l hl hf B hB hBl X.slot X hXr hts hsb
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

/-- **L5.4 with the exposure from a live fast lock, through the horizon**
(`window_justifies_of_lock` from `HealedUpTo … b` and `HSSharedUpTo … b`). -/
theorem window_justifies_of_lock_upTo (hrun : GoldilocksRun proposer dg H tr)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) (hvb : v ≤ b)
    {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ ≤ h)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      ∀ p ∈ H, ∀ k' Pr, tr.time k' ≤ b → Pr ∈ (tr.state p k').fg.tree →
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
  exact window_justifies_healed_upTo hrun hH.toHealedRecordsUpTo hs hv hvb hM4 hs₁ hvs hwb hh₀
    (exposure_of_lock_upTo hrun hs.noColl hH hy hc htH hl hf hB hBl hks) S hSH hS hsig

/-- **`window_justifies_of_lock_upTo` with the fin clause discharged** (the horizon form of
`window_justifies_of_lock_healed`): each `y ∈ S` signs by `v` its first own row at `(h, T)`. -/
theorem window_justifies_of_lock_healed_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) (hvb : v ≤ b)
    {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ h) :
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  refine window_justifies_of_lock_upTo hrun hH hs hv hvb hM4 hs₁ hvs hwb hy hc htH hl hf hB hBl
    hks hh hT (by omega) S hSH hS ?_
  intro z hz
  obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
  refine ⟨kz, att, hsg, hkv, hah, haT, ?_⟩
  intro p hp k' Pr hk'b hPr hPh hPT hb _
  have hzH := hSH z hz
  have hkzb : tr.time kz ≤ b := hkv.trans hvb
  have h₀a : h₀ ≤ att.h := by omega
  obtain ⟨src, hcs, rfl⟩ := hH.toHealedRecordsUpTo.first_sign_target hrun hzH hsg hkzb h₀a
    (by rw [hah]; exact hfirst)
  have hj := bound_hj hb
  exact finalityPair_entry_healed'_upTo hrun hs.noColl hq hH.toHealedRecordsUpTo hzH
    (attest_src_mem hrun hzH hcs) hp hPr hk'b (hPT.trans haT.symm) hb (by omega) hb.1 hkzb

end Consensus.Goldilocks.Refinement

end
