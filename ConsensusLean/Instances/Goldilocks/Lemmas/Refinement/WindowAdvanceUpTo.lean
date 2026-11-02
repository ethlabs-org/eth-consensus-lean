module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowEntryUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAnchors
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Refinement: the window advance from three height steps (#137)

consensus-lean#137. `Store.WindowAdvance st A B₃` (`σ[A].h + 3 ≤ σ[B₃].h`) is a premise of
`cacheCoverage_of_anchors_upTo`. Here:

* `height_advance_upTo`: from the L5.4 premises at the height `h` of a lock whose entry is above
  the anchor `A` (`hAX`), and the slot condition of case (A) on the entry (`hδ`), an honest
  proposal `P'` of a slot in `[min s₁ s₂, max s₁ s₂ + gM)` has `A ⪯ P'` and, in every honest
  store that holds `P'`, `σ[A].h + 1 ≤ σ[P'].h`. Case (A) of `window_entry_justified_M4_anc_upTo`:
  the parent of `P'` is above an entry `D` at height `h + 1`. Case (B): the parent is above `h`,
  or `P'` justifies `h` (`h_j < h`, `Healing.Store.hj_lt_h`).
* `window_advance_of_steps`: three such steps `A ⪯ Q₁ ⪯ Q₂ ⪯ Q₃` and the C4 ancestry `Q₃ ⪯ B₃`
  give `WindowAdvance` in an honest store that holds `B₃`; `window_advance_post_of_steps` reads
  it on the post-store of an honest proposal cut of `B₃`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A height bound at one honest store holds at every honest store that holds the upper block. -/
private theorem advance_uniform (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y p : Fin sp.n} (hy : y ∈ H) (hp : p ∈ H) {k j₀ : Nat}
    {A P' : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hA : A ∈ (tr.state y k).fg.tree) (hAh : ((tr.state y k).fg.σ A.root).h ≤ h)
    (hP' : P' ∈ (tr.state p j₀).fg.tree) (hPh : h + 1 ≤ ((tr.state p j₀).fg.σ P'.root).h)
    (hAP : Anc (tr.HonestBlocks H) A P') :
    ∀ w ∈ H, ∀ j, P' ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ P'.root).h := by
  intro w hw j hP'w
  have hAw := Healing.mem_of_honest_anc hrun hnc hw hAP hP'w
  rw [← Healing.σ_eq_honest hrun hnc hy hw hA hAw, ← Healing.σ_eq_honest hrun hnc hp hw hP' hP'w]
  omega

/-- **One height of advance (L5.4 step).** From the premises of
`window_entry_justified_M4_anc_upTo` at the lock height `h`, with the anchor `A` below every
entry of the lock (`hAX`) and the case-(A) slot condition on the entry (`hδ`): an honest proposal
`P'` of a slot in `[min s₁ s₂, max s₁ s₂ + gM)` with `A ⪯ P'`, held after its cut, and
`σ[A].h + 1 ≤ σ[P'].h` in every honest store that holds `P'`. -/
theorem height_advance_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P)
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hAX : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) A X)
    (hδ : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1) :
    ∃ s, min s₁ s₂ ≤ s ∧ s < max s₁ s₂ + gM ∧ ∃ P',
      Healing.HonestProposalRun tr H proposer s P' ∧ ∃ kp, tr.ProposesAt (proposer s) kp P' ∧
        P' ∈ (tr.post kp).fg.tree ∧ Anc (tr.HonestBlocks H) A P' ∧
        ∀ w ∈ H, ∀ j, P' ∈ (tr.state w j).fg.tree →
          ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ P'.root).h := by
  have hnc := hp.noColl
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, -, hX₀h, -⟩ := lock_entry_block hrun hy hBy
  have hX₀T : X₀.root = T := hX₀r.trans hT
  have hAX₀ := hAX X₀ hX₀ hX₀T
  have hAy := Healing.mem_of_honest_anc hrun hnc hy hAX₀ hX₀
  have hAh : ((tr.state y k).fg.σ A.root).h ≤ h := by
    have := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
      (Healing.store_anc_of_honest_anc hrun hnc hy hAX₀ hX₀)
    omega
  rcases window_entry_justified_M4_anc_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf hB
      hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP hs₂ hvs₂ hwb₂ with
    hA | ⟨s', hs's, hs'g, hpH, kp, Xp, Pr, hprop, hsl, hpar, hPr, harm, hanc⟩
  · obtain ⟨s, hs2, hsl, P', hP', Pr, hPr, hpar, hXPr, hD⟩ := hA X₀ hX₀ hX₀T (hδ X₀ hX₀ hX₀T)
    obtain ⟨kp, hkp⟩ := proposesAt_of_honestProposalRun hrun hP'
    obtain ⟨-, hP'm, he⟩ := Healing.accept_of_proposesAt hrun hnc hP'.1 hkp
    have hP'H : P' ∈ tr.HonestBlocks H := ⟨_, hP'.1, kp + 1, hP'm⟩
    have hPrP' : Anc (tr.HonestBlocks H) Pr P' := .single ⟨hPr, hP'H, hpar⟩
    have hPrm := Healing.mem_of_honest_anc hrun hnc hP'.1 hPrP' hP'm
    obtain ⟨D, -, -, hDPr, hDh, -⟩ := hD _ hP'.1 _ hPrm
    have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hP'.1 (kp + 1))
      (hDPr.tail ⟨hPrm, hP'm, hpar⟩)
    have hAP := hAX₀.trans (hXPr.trans hPrP')
    refine ⟨s, by omega, by omega, P', hP', kp, hkp, he ▸ hP'm, hAP, ?_⟩
    exact advance_uniform hrun hnc hy hP'.1 hAy hAh hP'm (by omega) hAP
  · obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hrun hnc hpH hprop
    have hXH : Xp ∈ tr.HonestBlocks H := ⟨_, hpH, kp + 1, hXm⟩
    have hPrX : Anc (tr.HonestBlocks H) Pr Xp := .single ⟨⟨_, hpH, kp, hPr⟩, hXH, hpar⟩
    have hPrm := Healing.mem_of_honest_anc hrun hnc hpH hPrX hXm
    have hr := Compose.fg_reachable hrun.toLocalRun hpH (kp + 1)
    have hle := Healing.h_le_of_store_anc hr (.single ⟨hPrm, hXm, hpar⟩)
    have hXh : h + 1 ≤ ((tr.state (proposer s') (kp + 1)).fg.σ Xp.root).h := by
      rcases harm with hlt | ⟨hj, -, -⟩
      · rw [Healing.σ_eq_honest hrun hnc hpH hpH hPr hPrm] at hlt
        omega
      · rw [he] at hj
        have := Healing.Store.hj_lt_h hr hXm
        omega
    have hAP := hAX₀.trans ((hanc X₀ hX₀ hX₀T).trans hPrX)
    refine ⟨s', by omega, by omega, Xp,
      Healing.honestProposalRun_of_proposesAt hrun hnc hpH rfl hprop hsl, kp, hprop,
      he ▸ hXm, hAP, ?_⟩
    exact advance_uniform hrun hnc hy hpH hAy hAh hXm hXh hAP

/-- **The window advance from three height steps.** Three steps `A ⪯ Q₁ ⪯ Q₂ ⪯ Q₃` of one height
each (the conclusion shape of `height_advance_upTo`) and the C4 ancestry `Q₃ ⪯ B₃` give
`WindowAdvance` in every honest store that holds `B₃`. -/
theorem window_advance_of_steps (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {A Q₁ Q₂ Q₃ B₃ : SA.Blk sp.n (List (FG.Att sp.n))}
    (h₁ : Anc (tr.HonestBlocks H) A Q₁ ∧ ∀ w ∈ H, ∀ j, Q₁ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ Q₁.root).h)
    (h₂ : Anc (tr.HonestBlocks H) Q₁ Q₂ ∧ ∀ w ∈ H, ∀ j, Q₂ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ Q₁.root).h + 1 ≤ ((tr.state w j).fg.σ Q₂.root).h)
    (h₃ : Anc (tr.HonestBlocks H) Q₂ Q₃ ∧ ∀ w ∈ H, ∀ j, Q₃ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ Q₂.root).h + 1 ≤ ((tr.state w j).fg.σ Q₃.root).h)
    (h₄ : Anc (tr.HonestBlocks H) Q₃ B₃) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hB : B₃ ∈ (tr.state y k).fg.tree) :
    Store.WindowAdvance (tr.state y k).fg A B₃ := by
  have hQ₃ := Healing.mem_of_honest_anc hrun hnc hy h₄ hB
  have hQ₂ := Healing.mem_of_honest_anc hrun hnc hy h₃.1 hQ₃
  have hQ₁ := Healing.mem_of_honest_anc hrun hnc hy h₂.1 hQ₂
  have e₁ := h₁.2 y hy k hQ₁
  have e₂ := h₂.2 y hy k hQ₂
  have e₃ := h₃.2 y hy k hQ₃
  have e₄ := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
    (Healing.store_anc_of_honest_anc hrun hnc hy h₄ hB)
  exact Store.windowAdvance_of_le (by omega)

/-- **The window advance on the post-store of an honest proposal cut of `B₃`**
(the `hadv` input of `cacheCoverage_of_anchors_upTo` with `B₃ = P 3`). -/
theorem window_advance_post_of_steps (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {A Q₁ Q₂ Q₃ B₃ : SA.Blk sp.n (List (FG.Att sp.n))}
    (h₁ : Anc (tr.HonestBlocks H) A Q₁ ∧ ∀ w ∈ H, ∀ j, Q₁ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ Q₁.root).h)
    (h₂ : Anc (tr.HonestBlocks H) Q₁ Q₂ ∧ ∀ w ∈ H, ∀ j, Q₂ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ Q₁.root).h + 1 ≤ ((tr.state w j).fg.σ Q₂.root).h)
    (h₃ : Anc (tr.HonestBlocks H) Q₂ Q₃ ∧ ∀ w ∈ H, ∀ j, Q₃ ∈ (tr.state w j).fg.tree →
      ((tr.state w j).fg.σ Q₂.root).h + 1 ≤ ((tr.state w j).fg.σ Q₃.root).h)
    (h₄ : Anc (tr.HonestBlocks H) Q₃ B₃) {p : Fin sp.n} (hpH : p ∈ H) {k : Nat}
    (hk : tr.ProposesAt p k B₃) :
    Store.WindowAdvance (tr.post k).fg A B₃ := by
  obtain ⟨-, hB, he⟩ := Healing.accept_of_proposesAt hrun hnc hpH hk
  rw [he]
  exact window_advance_of_steps hrun hnc h₁ h₂ h₃ h₄ hpH hB

/-! ## Slot bookkeeping of the three steps (#137)

Step `i + 1` starts at the output slot `σ` of step `i` and takes `s₁ = s₂ = σ + x + cF` with the
proposal offset `x ≤ gap − 1` (L5.4 step 1). The entry `X` of its lock is above `Q_i`, so
`σ ≤ X.slot`. The case-(A) condition `hδ` then holds for every such `x` exactly when
`cF + gap + gM ≤ δt + 2` (`window_advance_slot_hδ`, `window_advance_slot_hδ_necessary`). -/

/-- **`hδ` for one step.** With `s₂ = σ + x + cF`, `x + 1 ≤ gap`, `σ ≤ X.slot` and
`cF + gap + gM ≤ δt + 2`: `s₂ + gM ≤ X.slot + δt + 1`. -/
theorem window_advance_slot_hδ {σ x cF gap gM δt Xs : Nat} (hx : x + 1 ≤ gap)
    (hpar : cF + gap + gM ≤ δt + 2) (hX : σ ≤ Xs) : σ + x + cF + gM ≤ Xs + δt + 1 := by
  omega

/-- The condition is the weakest: if `hδ` holds at `X.slot = σ` for the worst offset
`x = gap − 1`, then `cF + gap + gM ≤ δt + 2`. -/
theorem window_advance_slot_hδ_necessary {σ cF gap gM δt : Nat} (hg : 1 ≤ gap)
    (h : σ + (gap - 1) + cF + gM ≤ σ + δt + 1) : cF + gap + gM ≤ δt + 2 := by
  omega

/-- **The output slot of one step.** A slot `s ∈ [min s₁ s₂, max s₁ s₂ + gM)` with
`s₁ = s₂ = σ + x + cF` and `x + 1 ≤ gap` has `σ ≤ s` and `s + 2 ≤ σ + cF + gap + gM`. -/
theorem window_advance_slot_next {σ x cF gap gM s : Nat} (hx : x + 1 ≤ gap)
    (hs : min (σ + x + cF) (σ + x + cF) ≤ s) (hs' : s < max (σ + x + cF) (σ + x + cF) + gM) :
    σ ≤ s ∧ s + 2 ≤ σ + cF + gap + gM := by
  simp only [Nat.min_self, Nat.max_self] at hs hs'
  omega

/-- **The three steps.** From the anchor slot `σ₀`: step `i` takes `s₁ = s₂ = σᵢ₋₁ + xᵢ + cF`,
its lock entry has slot `Xᵢ ≥ σᵢ₋₁`, and its output slot `σᵢ` is in the step range. Under
`cF + gap + gM ≤ δt + 2` all three `hδ` hold, and the third crossing has
`σ₃ + 6 ≤ σ₀ + 3 (cF + gap + gM)`. -/
theorem window_advance_slots {σ₀ σ₁ σ₂ σ₃ x₁ x₂ x₃ X₁ X₂ X₃ cF gap gM δt : Nat}
    (hpar : cF + gap + gM ≤ δt + 2)
    (hx₁ : x₁ + 1 ≤ gap) (hx₂ : x₂ + 1 ≤ gap) (hx₃ : x₃ + 1 ≤ gap)
    (hX₁ : σ₀ ≤ X₁) (hX₂ : σ₁ ≤ X₂) (hX₃ : σ₂ ≤ X₃)
    (h₁ : min (σ₀ + x₁ + cF) (σ₀ + x₁ + cF) ≤ σ₁ ∧
      σ₁ < max (σ₀ + x₁ + cF) (σ₀ + x₁ + cF) + gM)
    (h₂ : min (σ₁ + x₂ + cF) (σ₁ + x₂ + cF) ≤ σ₂ ∧
      σ₂ < max (σ₁ + x₂ + cF) (σ₁ + x₂ + cF) + gM)
    (h₃ : min (σ₂ + x₃ + cF) (σ₂ + x₃ + cF) ≤ σ₃ ∧
      σ₃ < max (σ₂ + x₃ + cF) (σ₂ + x₃ + cF) + gM) :
    (σ₀ + x₁ + cF + gM ≤ X₁ + δt + 1 ∧ σ₁ + x₂ + cF + gM ≤ X₂ + δt + 1 ∧
      σ₂ + x₃ + cF + gM ≤ X₃ + δt + 1) ∧
    σ₀ ≤ σ₁ ∧ σ₁ ≤ σ₂ ∧ σ₂ ≤ σ₃ ∧ σ₃ + 6 ≤ σ₀ + 3 * (cF + gap + gM) := by
  have e₁ := window_advance_slot_next hx₁ h₁.1 h₁.2
  have e₂ := window_advance_slot_next hx₂ h₂.1 h₂.2
  have e₃ := window_advance_slot_next hx₃ h₃.1 h₃.2
  refine ⟨⟨window_advance_slot_hδ hx₁ hpar hX₁, window_advance_slot_hδ hx₂ hpar hX₂,
    window_advance_slot_hδ hx₃ hpar hX₃⟩, by omega, by omega, by omega, by omega⟩

/-- With `gap = gM = g ≥ 1`, the condition is `Λ_J = cF + 2(g − 1) ≤ δt` (`FGLive.ΛJ`). -/
theorem window_advance_slot_cond_ΛJ {cF g δt : Nat} (hg : 1 ≤ g) :
    cF + g + g ≤ δt + 2 ↔ cF + 2 * (g - 1) ≤ δt := by
  omega

end Consensus.Goldilocks.Refinement

end
