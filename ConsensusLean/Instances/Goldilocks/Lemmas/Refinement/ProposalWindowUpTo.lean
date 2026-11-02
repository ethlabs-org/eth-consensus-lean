module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedClientUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalSignedUpTo

public section

/-! # Goldilocks Refinement: an honest proposal in each window justifies, through a horizon

consensus-lean#137 (finite-horizon port). `window_justifies` and `window_justifies_healed` from
`HSSharedUpTo … b` and `HealedRecordsUpTo … b`. The guard `hwb`: every slot `s' < s₁ + g` of the
window has `t_{s'} ≤ b`, so the window proposal cut is by `b` (`rows_delivered_upTo`). The
exposure premise and the fin clause of the row supply are asked only at cuts by `b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The cut of an honest proposal is at its slot time. -/
theorem proposesAt_time {p : Fin sp.n} {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p k X) : tr.time k = sp.ts X.slot := by
  rw [hX.2.2, sp.slotTime_eq]; rfl

/-- **L5.4 at trace level through the horizon `b`** (`window_justifies` from
`HSSharedUpTo … b`, every window slot by `b`). -/
theorem window_justifies_upTo (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {h T : Nat}
    (hexp : ∀ p ∈ H, ∀ k X Pr, tr.ProposesAt p k X → s₁ ≤ X.slot → tr.time k ≤ b →
      X.parent = some Pr.root → Pr ∈ (tr.state p k).fg.tree →
      h < ((tr.state p k).fg.σ Pr.root).h ∨
        (((tr.state p k).fg.σ Pr.root).h = h ∧ ((tr.state p k).fg.σ Pr.root).Th = T))
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      att.timeout = false ∧ ∀ p ∈ H, ∀ k' Pr, tr.time k' ≤ b → Pr ∈ (tr.state p k').fg.tree →
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
  obtain ⟨s', h1, h2, P, hP⟩ := hM4 s₁ hs₁
  have hpH : proposer s' ∈ H := hP.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hrun hP
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held hrun hs.noColl hpH hk
  have htk : tr.time k = sp.ts s' := by rw [proposesAt_time hk, hPs]
  have hkb : tr.time k ≤ b := htk ▸ hwb s' h2
  refine ⟨s', h1, h2, hpH, k, P, Pr, hk, hPs, hpar, hPr, ?_⟩
  rcases hexp _ hpH k P Pr hk (hPs ▸ h1) hkb hpar hPr with hlt | ⟨hh, hT⟩
  · exact Or.inl hlt
  right
  have hvx : v + ΔF ≤ tr.time k :=
    hvs.trans (htk ▸ (SA.ts_le_iff sp).2 (by exact_mod_cast h1))
  obtain ⟨hj, hJ, hF⟩ := Healing.justify_of_signed_rows'_upTo hrun hs hv hpH hk hvx hkb hpar S
    hSH hS fun y hy => by
      obtain ⟨k₁, att, hsg, hkv, hah, haT, hto, hfin⟩ := hsig y hy
      exact ⟨k₁, att, hsg, hkv, hah.trans hh.symm, haT.trans hT.symm, hto,
        hfin _ hpH k Pr hkb hPr hh hT⟩
  exact ⟨hj.trans hh, hJ.trans hT, hF⟩

/-- `window_justifies_upTo` with N0⁺ through the horizon: under `HealedRecordsUpTo … b` from
`h₀ ≤ h`, every honest row signed by `v ≤ b` at `h` is a target. -/
theorem window_justifies_healed_upTo (hrun : GoldilocksRun proposer dg H tr)
    {g ΔF v gR b : Time} {h₀ : Nat} {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) (hvb : v ≤ b)
    {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {h T : Nat} (hh₀ : h₀ ≤ h)
    (hexp : ∀ p ∈ H, ∀ k X Pr, tr.ProposesAt p k X → s₁ ≤ X.slot → tr.time k ≤ b →
      X.parent = some Pr.root → Pr ∈ (tr.state p k).fg.tree →
      h < ((tr.state p k).fg.σ Pr.root).h ∨
        (((tr.state p k).fg.σ Pr.root).h = h ∧ ((tr.state p k).fg.σ Pr.root).Th = T))
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
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) :=
  window_justifies_upTo hrun hs hv hM4 hs₁ hvs hwb hexp S hSH hS fun y hy => by
    obtain ⟨k, att, hsg, hkv, hah, haT, hfin⟩ := hsig y hy
    exact ⟨k, att, hsg, hkv, hah, haT,
      hR.sign_target hrun (hSH y hy) hsg (hkv.trans hvb) (hah ▸ hh₀), hfin⟩

end Consensus.Goldilocks.Refinement

end
