module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.HealedClient
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks Refinement: an honest proposal in each window justifies (L5.4, trace level)

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §5, L5.4 (Theorem J), steps 1, 3, 5 and 6,
and §6, L5.3 step 6 (the handoff bound), at trace level. The paper-conditional inputs stay
explicit premises:

* **M4** (`hM4`): from slot `s₀` on, every `g` consecutive slots hold an honest proposal
  (`Healing.HonestProposalRun`);
* **L5.1 exposure with C3** (`hexp`, step 3): the parent of every honest proposal of a slot `≥ s₁`
  has the entry `(h, T)` or is past `h`;
* **the honest-row supply** (`hsig`): a set `S ⊆ H` of weight `≥ q` of honest validators, each of
  which signed by `v` a target row for `(h, T)`, with the finality pair of a parent whose previous
  height is justified where it is pending ("they attest" stays a premise; N0⁺
  `HealedRecords.sign_target` gives `timeout = false` in `window_justifies_healed`).

* `window_justifies`: some honest proposal `X` of a slot `s' ∈ [s₁, s₁ + g)` has a held parent
  `Pr` past `h`, or `X` justifies `(h, T)` (`justify_of_signed_rows'`), with `h_F = σ[Pr].h_j` at
  a parent whose previous height is justified.
* `window_justifies_healed`: the same, with `timeout = false` from `HealedRecords` (`h₀ ≤ h`).
* `theorem_J_slot_le`: L5.4 step 1, `s' ≤ u + c + 2(g − 1)` for
  `s₁ = u + x + c`, `x ≤ g − 1`.
* L5.3 step 6 (slot arithmetic only), `s' ≤ s_h + δ_t + g` for
  `s₁ = max (s₁′ + c) (u₀ + δ_t)` (`Healing.handoff_slot_le`). -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **L5.4 at trace level** (steps 1, 3, 5): under M4 from `s₀ ≤ s₁` (`hM4`), the exposure premise
`hexp` (every honest proposal of a slot `≥ s₁` has a held parent with the entry `(h, T)` or past
`h`), and `q` honest target rows for `(h, T)` signed by `v`, `ḡ ≤ v`, `v + Δ_F ≤ t_{s₁}`: some
honest proposal `X` of a slot `s' ∈ [s₁, s₁ + g)`, on a held parent `Pr`, has `Pr` past `h`, or
justifies `(h, T)`, with `h_F = σ[Pr].h_j` when `Pr`'s previous height is justified. -/
theorem window_justifies (hrun : GoldilocksRun proposer dg H tr) {g ΔF v : Time}
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) {h T : Nat}
    (hexp : ∀ p ∈ H, ∀ k X Pr, tr.ProposesAt p k X → s₁ ≤ X.slot →
      X.parent = some Pr.root → Pr ∈ (tr.state p k).fg.tree →
      h < ((tr.state p k).fg.σ Pr.root).h ∨
        (((tr.state p k).fg.σ Pr.root).h = h ∧ ((tr.state p k).fg.σ Pr.root).Th = T))
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
      att.timeout = false ∧ ∀ p ∈ H, ∀ k' Pr, Pr ∈ (tr.state p k').fg.tree →
        ((tr.state p k').fg.σ Pr.root).h = h → ((tr.state p k').fg.σ Pr.root).Th = T →
        ((tr.state p k').fg.σ Pr.root).previousHeightJustified →
        (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) ∈
          ((tr.state p k').fg.σ Pr.root).pending →
        att.fin = some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J)) :
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).previousHeightJustified →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  obtain ⟨s', h1, h2, P, hP⟩ := hM4 s₁ hs₁
  have hpH : proposer s' ∈ H := hP.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hrun hP
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held hrun hs.noColl hpH hk
  refine ⟨s', h1, h2, hpH, k, P, Pr, hk, hPs, hpar, hPr, ?_⟩
  rcases hexp _ hpH k P Pr hk (hPs ▸ h1) hpar hPr with hlt | ⟨hh, hT⟩
  · exact Or.inl hlt
  right
  have htk : tr.time k = sp.ts s' := by rw [hk.2.2, sp.slotTime_eq, hPs]; rfl
  have hvx : v + ΔF ≤ tr.time k :=
    hvs.trans (htk ▸ (SA.ts_le_iff sp).2 (by exact_mod_cast h1))
  obtain ⟨hj, hJ, hF⟩ := Healing.justify_of_signed_rows' hrun hs hv hpH hk hvx hpar S hSH hS
    fun y hy => by
      obtain ⟨k₁, att, hsg, hkv, hah, haT, hto, hfin⟩ := hsig y hy
      exact ⟨k₁, att, hsg, hkv, hah.trans hh.symm, haT.trans hT.symm, hto,
        hfin _ hpH k Pr hPr hh hT⟩
  exact ⟨hj.trans hh, hJ.trans hT, hF⟩

end Consensus.Goldilocks.Refinement

end
