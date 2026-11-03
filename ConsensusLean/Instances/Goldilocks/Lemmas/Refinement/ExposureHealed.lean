module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Exposure
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPair

public section

/-! # Goldilocks Refinement: the lock window with the fin clause discharged (L5.4, WI-18)

`window_justifies_of_lock` asks (`hsig`) that each of `q` honest target rows for `(h, T)` carries
`(σ.h_j, σ.J)` of every held honest state `σ` whose previous height is justified, at `(h, T)` with
that pair pending.

* `previousHeightJustified_hj`: a state whose previous height is justified has `σ.h_j + 1 = σ.h`
  (the definition of `previousHeightJustified`), so at a height `h` whose previous height is
  justified with `h₀ + 1 ≤ h` the premise `h₀ ≤ σ.h_j` of `finalityPair_entry_healed'` holds.
* `attest_src_mem`: the source of an honest signed `fg_attest` cut is held at that cut.
* `window_justifies_of_lock_healed`: `window_justifies_of_lock` where the rows are first own rows
  at `h` (so `HealedRecords.first_sign_target` gives their shape) and the fin clause is proved
  under `HealedRecords`, `h₀ + 1 ≤ h` and `|Hᶜ| < q`. The supply of rows stays a premise. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

/-- **A height whose previous height is justified is one above `h_j`.** -/
theorem previousHeightJustified_hj {n : Nat} {σ : FG.ChainState n}
    (hb : σ.previousHeightJustified) :
    σ.hj + 1 = σ.h := hb.2

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The source of an honest signed `fg_attest` cut is held at that cut.** -/
theorem attest_src_mem (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {src : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y k (.fg (.attest src (some a)))) : src ∈ (tr.state y k).fg.tree := by
  obtain ⟨j, rfl, ℓ, hj, -, -, hret, hfg⟩ := Compose.attest_source hrun.toLocalRun hy hc
  have hC : src ∈ ℓ.frame.tree := by
    change (SA.acToFG sp _ _ _).2 = some src at hret
    unfold SA.acToFG at hret
    split_ifs at hret
    split at hret
    · cases hret
    · rename_i C' hC'
      split_ifs at hret
      cases hret
      exact (SA.deepest_mem hC').1.1.1
  rw [(hrun.cutLaw y hy j _ hj).1] at hC
  rw [hfg]
  exact hC.1

/-- **`window_justifies_of_lock` with the fin clause discharged.** As `window_justifies_of_lock`,
with `h₀ + 1 ≤ h`, `|Hᶜ| < q`, and `hsig` replaced by: each `y ∈ S` signs by `v` a row `att`
at `(h, T)` that is its first own row at height `h`. -/
theorem window_justifies_of_lock_healed (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
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
    (hh₀ : h₀ + 1 ≤ h)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ h) :
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).previousHeightJustified →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  refine window_justifies_of_lock hrun hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl hks hh hT
    (by omega) S hSH hS ?_
  intro z hz
  obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
  refine ⟨kz, att, hsg, hkv, hah, haT, ?_⟩
  intro p hp k' Pr hPr hPh hPT hb _
  have hzH := hSH z hz
  have h₀a : h₀ ≤ att.h := by omega
  obtain ⟨src, hcs, rfl⟩ := hH.toHealedRecords.first_sign_target hrun hzH hsg h₀a
    (by rw [hah]; exact hfirst)
  have hj := previousHeightJustified_hj hb
  exact finalityPair_entry_healed' hrun hs.noColl hq hH.toHealedRecords hzH
    (attest_src_mem hrun hzH hcs) hp hPr (hPT.trans haT.symm) hb (by omega) hb.1 kz

end Consensus.Goldilocks.Refinement

end
