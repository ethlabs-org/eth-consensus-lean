module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeUpper
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeVotes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.5: consumption and continuation

`hs5-exact-helpers.md` §4 (`consume_continue`, "two crossings with the original drain"): under
`Γ`, with HS.1 and HS.2 as hypotheses (HS.3 (b) from HS.2, `frozen_tree_agreement_clean`),
from the acquired path's witness (an honest proposal `W` of slot `s`, entry `E` at
`h ∈ {ℓ, m}`, its protected parents, and the attestations by `v = t_s + 6Δ` that
`historical_source_rows` gives), the phase cannot stay `(m, c)` through the first cut `j_A` after
`w + A`, `A = 2C + Δ` (`consume_continue_of`, proved from `mature_progress_of` and
`fixed_upper_rows_of`).

1. The first crossing: `mature_progress_of` at `b₁ = max(v + Δ_F, t_{E.slot + δ_t}) + G_p + Δ
   ≤ w + C` (`E.slot ≤ s`) gives a ready `X` of height `≥ h + 1`, accepted by its proposer at
   `t_x < w + A`, so `h + 1 ≤ m` (the frontier): `h = ℓ = m − 1` and `ht(X) = m`.
2. HS.3 (b) at `X` with the original settled cut `i₀` (`time i₀ ≤ t_s ≤ t_{x−1}`; every slot-`x`
   vote is cast by `t_x + Δ < w + A`, `cast_time_le_slot`) protects `X`.
3. `Prop⁺` at `t_x + 8Δ` gives a ready `Y`; the entry-independent envelope
   `B₂ = t_y + (7 + 4δ_t)Δ + Δ_F + G_p ≤ w + 2C < w + A` is bounded first. `X`'s protected parent
   clause gives `X ⪯ Y`, so `ht(Y) = m`; HS.3 (b) at `Y` protects it, `fixed_upper_rows_of` gives
   its entry `E₂` and attestations at `m` by `t_y + 6Δ` (every deadline below `B₂` has its first cut
   at or before `j_A`, index inclusion), and `mature_progress_of` at `b₂ ≤ B₂` gives a ready
   proposal of height `≥ m + 1` accepted at a time `< w + A`: a frontier rise, a contradiction. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- The slot of an entry is at most the slot of the block it is the entry of. -/
private theorem entry_slot_le (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hpost : tr.post k = tr.state p (k + 1)) (hE : EntryOf (tr.post k).fg W E h) :
    E.slot ≤ W.slot :=
  slot_le_of_anc (Compose.honest_blocks_coherent hrun.toLocalRun hnc)
    ((hpost ▸ hE.2.2).mono fun _ hX => ⟨p, hp, k + 1, hX⟩)

/-- `t_{e + δ_t} ≤ t_s + 4Δδ_t` for an entry slot `e ≤ s`. -/
private theorem ts_entry_le {e s : Nat} (h : e ≤ s) :
    sp.ts (e + sp.toParams.δt : Nat) ≤ sp.ts s + 4 * sp.Δ * (sp.toParams.δt : Time) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have he : (e : Int) ≤ s := by exact_mod_cast h
  simp only [SAParams.ts]
  push_cast
  linarith [sp.toParams.hΔ, mul_le_mul_of_nonneg_left he sp.toParams.hΔ.le]

/-- **HS.5's consumption and continuation in the phase** (`hs5-exact-helpers.md` §4;
`Service`'s `consume_continue` with the acquired path destructured, its attestations from
`historical_source_rows`, and the phase `(m, c)` through `j_A`): a contradiction. -/
theorem consume_continue_of (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H proposer g Gp)
    (hret : ViableWitnessRetention) (hclean : CleanLockDrain)
    (hset : SettledIn tr H g w i₀ m c)
    (hcl : ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
      tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
      ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
        phaseFloor m c ≤ h →
        EffAllowed (tr.state y k).fg m c C →
        (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
        ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root)
    {s h kW : Nat} {E W : SA.Blk sp.n (List (FG.Att sp.n))} (h1 : h = phaseFloor m c ∨ h = m)
    (hW : tr.ProposesAt (proposer s) kW W) (hWs : W.slot = s)
    (hpH : proposer s ∈ H) (hE : EntryOf (tr.post kW).fg W E h)
    (hws : w ≤ sp.ts s) (hr : rTime sp w ≤ sp.ts s)
    (hvD : sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
      proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr)
    (hrows : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
      att.T = E.root)
    {jA : Nat} (hjA : FirstCutAfter tr jA (w + A_HS sp ΔF Gp))
    (hOn : PhaseOn tr.projFG H i₀ jA m c) : False := by
  have hnc := hs.noColl
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΔF : 0 ≤ ΔF := hs.healthy.1.deltaF.le
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  have hrw := add_le_rTime sp w
  have hδ : (0 : Time) ≤ 4 * sp.Δ * (sp.toParams.δt : Time) := by positivity
  have hkΔ : 0 ≤ (sp.k : Time) * sp.Δ := mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hGp : 0 ≤ Gp := by
    obtain ⟨_, _, _, -, h₁, h₂, -⟩ := hp (gbar g) le_rfl
    linarith
  have hC : C_HS sp ΔF Gp = D_HS sp Gp + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF + Gp + sp.Δ :=
    rfl
  have hA : A_HS sp ΔF Gp = 2 * C_HS sp ΔF Gp + sp.Δ := rfl
  have hD : D_HS sp Gp = 8 * ((sp.k : Time) * sp.Δ) + 48 * sp.Δ + 2 * Gp := by
    simp only [D_HS]; ring
  -- the cuts before `w + A` are in the phase
  have hcutA : ∀ k, tr.time k ≤ w + A_HS sp ΔF Gp → k < jA :=
    fun k hk => hjA.lt_of_time_le hrun.time_mono hk
  have hi₀ : ∀ k, w ≤ tr.time k → i₀ ≤ k := fun k hk => by
    by_contra hlt
    have := hset.2.1.2 k (not_le.1 hlt)
    linarith
  have hphase : ∀ k, tr.time k ≤ w + A_HS sp ΔF Gp → PhaseOn tr.projFG H i₀ k m c :=
    fun k hk k' h₁ h₂ => hOn k' h₁ (by have := hcutA k hk; omega)
  have hupto : ∀ T, T ≤ w + A_HS sp ΔF Gp → ∀ j, FirstCutAfter tr j T →
      PhaseOn tr.projFG H i₀ j m c :=
    fun T hT j hj k' h₁ h₂ => hOn k' h₁ (h₂.trans (hj.le_of_le hjA hT))
  -- an honest proposal accepted before `w + A` has height at most the frontier `m`
  have hcap : ∀ {q : Fin sp.n} {kq : Nat} {Q : SA.Blk sp.n (List (FG.Att sp.n))}, q ∈ H →
      tr.ProposesAt q kq Q → w ≤ tr.time kq → tr.time kq ≤ w + A_HS sp ΔF Gp →
      ((tr.post kq).fg.σ Q.root).h ≤ m := by
    intro q kq Q hq hQ hw₁ hw₂
    obtain ⟨-, hQt, hpost⟩ := accept_of_proposesAt hrun hnc hq hQ
    have := hcutA kq hw₂
    have := hi₀ kq hw₁
    rw [hpost]
    exact h_le_of_phaseAt hrun hnc hq le_rfl (hOn (kq + 1) (by omega) (by omega)) hQt
  have htime : ∀ {q : Fin sp.n} {kq z : Nat} {Q : SA.Blk sp.n (List (FG.Att sp.n))},
      tr.ProposesAt q kq Q → Q.slot = z → tr.time kq = sp.ts z := fun hQ hQs => by
    rw [hQ.2.2, hQs, sp.slotTime_eq]; rfl
  have hslot : ∀ {a b : Nat}, sp.ts a < sp.ts b → a < b := fun h => by
    exact_mod_cast (SA.ts_lt_iff sp).1 h
  have hpred : ∀ z : Nat, sp.ts ((z : Int) - 1) = sp.ts z - 4 * sp.Δ := fun z => by
    simp only [SAParams.ts]; ring
  have hsucc : ∀ {a b : Nat}, a < b → sp.ts a + 4 * sp.Δ ≤ sp.ts b := fun {a b} h => by
    have : sp.ts ((a : Int) + 1) ≤ sp.ts b := (SA.ts_le_iff sp).2 (by omega)
    simp only [SAParams.ts] at this ⊢
    linarith
  have hfloor : phaseFloor m c ≤ m := by cases c <;> simp only [phaseFloor] <;> omega
  -- the settled cut is at or before `W`'s proposal, at `t_s`
  have hi₀W : tr.time i₀ ≤ sp.ts s := by
    have := hrun.time_mono (hi₀ kW (by rw [htime hW hWs]; exact hws))
    rwa [htime hW hWs] at this
  -- HS.3 (b) at a ready proposal of a slot `z > s` whose votes are before `w + A`
  have hprot : ∀ {z kZ : Nat} {Z : SA.Blk sp.n (List (FG.Att sp.n))},
      ReadyProposal tr H proposer (proposer z) kZ z Z → s < z →
      sp.ts z + sp.Δ ≤ w + A_HS sp ΔF Gp →
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = z →
        e.msg.head = Z.root ∧
        (Z ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame z) ∨
          Anc (tr.HonestBlocks H) Z ℓ.frame.fcRoot)) ∧
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → z < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg Z) ∧
      ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), z < s' →
        P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
        proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
        ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) Z Pr := by
    intro z kZ Z hZ hsz hzA
    obtain ⟨-, -, -, hpropZ, hZs, -⟩ := id hZ
    have hkZ := htime hpropZ hZs
    have h₁ := hsucc hsz
    have h₂ := hpred z
    obtain ⟨hv, hl, hpa⟩ := frozen_tree_agreement_clean hclean sp ro proposer dg H tr g ΔF w i₀
      i₀ m c hrun hs hc hset le_rfl _ kZ z Z
      hZ (hi₀ kZ (by linarith)) (by linarith) (by linarith [gbar_nonneg g])
      (fun y hy k ℓ e hv he => hphase k (by
        have := cast_time_le_slot hrun hnc hy hv
        rw [he] at this
        linarith)) (by linarith)
    exact ⟨fun y hy k ℓ e hv' he => let ⟨a, b, _⟩ := hv y hy k ℓ e hv' he;
      ⟨a, b.imp_left And.right⟩, hl, hpa⟩
  -- the first crossing, by `b₁ ≤ w + C`
  have hEs := entry_slot_le hrun hnc hpH (accept_of_proposesAt hrun hnc hpH hW).2.2 hE
  rw [hWs] at hEs
  have hb₁ : max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp +
      sp.Δ ≤ w + C_HS sp ΔF Gp := by
    have := ts_entry_le (sp := sp) hEs
    have := max_le_iff.2 (⟨by linarith, by linarith⟩ :
      sp.ts s + 6 * sp.Δ + ΔF ≤ w + D_HS sp Gp + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF ∧
        sp.ts (E.slot + sp.toParams.δt : Nat) ≤
          w + D_HS sp Gp + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF)
    linarith
  have hCA : C_HS sp ΔF Gp + sp.Δ ≤ A_HS sp ΔF Gp := by linarith
  obtain ⟨jb, hjb⟩ := exists_firstCutAfter_of_healthy hrun hs hpH
    (max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ)
  obtain ⟨x, kX, X, hXr, hx₁, hx₂, hXh, -, -⟩ := mature_progress_of hrun hs hc hp hset hret hW
    hWs hpH hE (h1.elim (·.ge) (fun h => h ▸ hfloor)) hws hparents hrows hjb
    (hupto _ (by linarith) jb hjb)
  obtain ⟨hpX, -, -, hpropX, hXs, -⟩ := id hXr
  have hkX := htime hpropX hXs
  have hX₁ : sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts x := (le_max_left _ _).trans hx₁
  have hX₂ : sp.ts x + sp.Δ ≤ w + C_HS sp ΔF Gp := hx₂.trans hb₁
  have hsx : s < x := hslot (by linarith)
  have hXm := hcap hpX hpropX (by linarith) (by linarith)
  -- so `h = ℓ = m − 1` and `ht(X) = m`
  have hhm : h + 1 = m := by
    rcases h1 with rfl | rfl
    · cases c <;> simp only [phaseFloor] at hXh hXm ⊢ <;> omega
    · omega
  obtain ⟨-, -, hXpar⟩ := hprot hXr hsx (by linarith)
  -- the second proposal `Y`, after `t_x + 8Δ`, and the envelope `B₂ ≤ w + 2C`
  obtain ⟨y, kY, Y, -, hy₁, hy₂, hYr⟩ := hp (sp.ts x + 8 * sp.Δ) (by linarith)
  obtain ⟨hpY, -, -, hpropY, hYs, -⟩ := id hYr
  have hkY := htime hpropY hYs
  have hxy : x < y := hslot (by linarith)
  have hB₂ : sp.ts y + 8 * sp.Δ + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF + Gp ≤
      w + A_HS sp ΔF Gp := by
    linarith
  have hYm : ((tr.post kY).fg.σ Y.root).h = m := by
    refine le_antisymm (hcap hpY hpropY (by linarith) (by linarith)) ?_
    obtain ⟨Pr, hpar, hXPr⟩ := hXpar y Y kY hxy hYs hpropY hpY (hphase kY (by linarith))
    obtain ⟨-, hXt, hpostX⟩ := accept_of_proposesAt hrun hnc hpX hpropX
    obtain ⟨-, hYt, hpostY⟩ := accept_of_proposesAt hrun hnc hpY hpropY
    have hXY := anc_of_parentRoot ⟨_, hpX, _, hXt⟩ hXPr ⟨_, hpY, _, hYt⟩ hpar
    have hXt' := mem_of_honest_anc hrun hnc hpY hXY hYt
    have := h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hpY (kY + 1))
      (store_anc_of_honest_anc hrun hnc hpY hXY hYt)
    rw [hpostX] at hXh
    rw [← σ_eq_honest hrun hnc hpX hpY hXt hXt'] at this
    rw [hpostY]
    omega
  obtain ⟨hYv, hYl, hYp⟩ := hprot hYr (hsx.trans hxy) (by linarith)
  obtain ⟨E₂, hE₂, hrows₂⟩ := fixed_upper_rows_of hrun hs hc hset hclean hcl hpropY hYs hpY
    hYm (by linarith) hYv hYl hYp (hupto _ (by linarith))
  have hE₂s := entry_slot_le hrun hnc hpY (accept_of_proposesAt hrun hnc hpY hpropY).2.2 hE₂
  rw [hYs] at hE₂s
  have hb₂ : max (sp.ts y + 6 * sp.Δ + ΔF) (sp.ts (E₂.slot + sp.toParams.δt : Nat)) + Gp +
      sp.Δ ≤ w + A_HS sp ΔF Gp := by
    have := ts_entry_le (sp := sp) hE₂s
    have := max_le_iff.2 (⟨by linarith, by linarith⟩ :
      sp.ts y + 6 * sp.Δ + ΔF ≤ sp.ts y + 6 * sp.Δ + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF ∧
        sp.ts (E₂.slot + sp.toParams.δt : Nat) ≤
          sp.ts y + 6 * sp.Δ + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF)
    linarith
  obtain ⟨jb₂, hjb₂⟩ := exists_firstCutAfter_of_healthy hrun hs hpY
    (max (sp.ts y + 6 * sp.Δ + ΔF) (sp.ts (E₂.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ)
  obtain ⟨x₂, kX₂, X₂, hX₂r, hx₂₁, hx₂₂, hX₂h, -, -⟩ := mature_progress_of hrun hs hc hp hset hret
    hpropY hYs hpY hE₂ hfloor (by linarith) hYp hrows₂ hjb₂ (hupto _ hb₂ jb₂ hjb₂)
  obtain ⟨hpX₂, -, -, hpropX₂, hX₂s, -⟩ := id hX₂r
  have hkX₂ := htime hpropX₂ hX₂s
  have := (le_max_left _ _).trans hx₂₁
  have := hcap hpX₂ hpropX₂ (by linarith) (by linarith)
  omega

end Consensus.Goldilocks.Healing

end
