module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Goldilocks Refinement: the entry is justified on the parent's chain (L5.4, WI-19)

Workbench `fg-liveness/r14-end-to-end`, s5 L5.4: the entry `(h, T)` is justified on the
canonical chain, and the predecessor is finalized if the height is bound.

* `Store.chain_states_of_anc`: the store bridge. For a held `X ⪯ W`, a chain `c` reaches
  `σ[X]` and `c ++ d` reaches `σ[W]`; every block of `d` is held, between `X` and `W`, has a
  slot at most `W.slot`, and the prefix of `c ++ d` that ends at it reaches its state.
* `Store.entry_justified_of_anc`: `FGParams.early_cross_chain_justifies` at the store: if
  `σ[X].h < σ[W].h` and `W.slot < σ[X].ThSlot + δt`, a held `D` with `X ⪯ D ⪯ W` justified
  the entry of `σ[X]`, and finalized the predecessor block if `σ[X]` is bound.
* `window_justifies_or_parents_above_after'`: `window_justifies_or_parents_above_after` with
  `X ⪯ C` for every held `X` of root `T` in case (A).
* `window_justifies_or_parents_above_unanimous_entry`:
  `window_justifies_or_parents_above_unanimous''` with the same addition.
* `window_entry_justified_or_window` (L5.4): in case (A), every honest proposal of a slot `s`
  with `v + Δ ≤ t_s` and `s ≤ σ[X].ThSlot + δt` has an honest parent `Pr ⪰ X` on whose chain
  a block justified `(h, T)` (and finalized the predecessor if bound), at every honest holder.
  The bound `s ≤ σ[X].ThSlot + δt` stays a premise: the window gives only `v + Δ ≤ t_s`. -/

namespace Consensus.Goldilocks

namespace FG.FGParams

variable (gp : FGParams)

/-- `chainState_append` through a map. -/
theorem chainState_map_append_singleton {α : Type} (f : α → FGBlock gp.n) (c : List α)
    (B : α) : gp.chainState ((c ++ [B]).map f) =
      (gp.chainState (c.map f)).bind (gp.stateTransition · (f B)) := by
  rw [List.map_append, List.map_singleton, gp.chainState_append]

/-- `early_cross_chain_justifies` through a map: the justifying block is the image of a block of
`d`. -/
theorem early_cross_map_justifies {α : Type} (f : α → FGBlock gp.n) {c d : List α}
    {σ τ : ChainState gp.n} (hc : gp.chainState (c.map f) = some σ)
    (hd : gp.chainState ((c ++ d).map f) = some τ) (hh : σ.h < τ.h)
    (hs : ∀ B ∈ d, (f B).slot < σ.ThSlot + gp.δt) :
    ∃ d₁ B d₂ σ₂, d = d₁ ++ B :: d₂ ∧ gp.chainState ((c ++ d₁ ++ [B]).map f) = some σ₂ ∧
      σ₂.h = σ.h + 1 ∧ σ₂.hj = σ.h ∧ σ₂.J = σ.Th ∧
      (σ.bound → σ₂.F = σ.J ∧ σ₂.hF = σ.hj) := by
  rw [List.map_append] at hd
  obtain ⟨e₁, B, e₂, σ₂, he, hσ₂, h⟩ := gp.early_cross_chain_justifies hc hd hh (by
    intro B hB
    obtain ⟨B', hB', rfl⟩ := List.mem_map.1 hB
    exact hs B' hB')
  obtain ⟨d₁, r, rfl, rfl, hr'⟩ := List.map_eq_append_iff.1 he
  obtain ⟨D, d₂, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr'
  refine ⟨d₁, D, d₂, σ₂, rfl, ?_, h⟩
  simpa [List.map_append] using hσ₂

end FG.FGParams

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- **The store bridge (G0.1 along an ancestry).** For a held `X ⪯ W` in a reachable store, a
chain `c` reaches `σ[X]` and `c ++ d` reaches `σ[W]`, and every block `B` of `d` (with
`d = d₁ ++ B :: d₂`) is held, has `X ⪯ B ⪯ W` and `B.slot ≤ W.slot`, and `c ++ d₁ ++ [B]`
reaches `σ[B]`. -/
theorem chain_states_of_anc (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) :
    ∃ c d : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some (st.σ X.root) ∧
      P.fg.chainState ((c ++ d).map Block.fgView) = some (st.σ W.root) ∧
      ∀ d₁ B d₂, d = d₁ ++ B :: d₂ → B ∈ st.tree ∧ st.Anc X B ∧ st.Anc B W ∧
        B.slot ≤ W.slot ∧
        P.fg.chainState ((c ++ d₁ ++ [B]).map Block.fgView) = some (st.σ B.root) := by
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st hr X hX
  refine ⟨c, ?_⟩
  induction hXW with
  | refl => exact ⟨[], hc, by rw [List.append_nil]; exact hc, fun d₁ B d₂ h => by simp at h⟩
  | @tail W W' hXW' hWW' ih =>
    obtain ⟨d, -, hd, hpre⟩ := ih
    obtain ⟨hW, hW', hp⟩ := hWW'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hW' hp
    have hsl : W.slot < W'.slot := (accepted_tree P ACP acp₀ st hr).2.1.2 W hW W' hW' hp
    have hd' : P.fg.chainState ((c ++ (d ++ [W'])).map Block.fgView) = some (st.σ W'.root) := by
      have e := P.fg.chainState_map_append_singleton Block.fgView (c ++ d) W'
      rw [hd] at e
      rw [← List.append_assoc]
      exact e.trans ht
    refine ⟨d ++ [W'], hc, hd', fun d₁ B d₂ he => ?_⟩
    rcases List.eq_nil_or_concat d₂ with rfl | ⟨d₂', z, rfl⟩
    · obtain ⟨rfl, hB⟩ := List.append_inj' he rfl
      obtain rfl : W' = B := List.singleton_inj.1 hB
      refine ⟨hW', ?_, Relation.ReflTransGen.refl, le_rfl, ?_⟩
      · exact hXW'.tail ⟨hW, hW', hp⟩
      · rw [← List.append_assoc] at hd'; exact hd'
    · have he' : d ++ [W'] = (d₁ ++ B :: d₂') ++ [z] := by simpa using he
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      obtain ⟨hB, hXB, hBW, hBs, hσ⟩ := hpre d₁ B d₂' rfl
      exact ⟨hB, hXB, hBW.tail ⟨hW, hW', hp⟩, by omega, hσ⟩

/-- **The entry is justified below an early higher block (L5.4 step 4, store form).** In a
reachable store, for a held `X ⪯ W` with `σ[X].h < σ[W].h` and `W.slot < σ[X].ThSlot + δt`,
some held `D` with `X ⪯ D ⪯ W` has entered `σ[X].h + 1` by justifying the entry of `σ[X]`
(`h_j = σ[X].h`, `J = σ[X].Th`), and if `σ[X]` is bound, `D` finalized its predecessor block
(`F = σ[X].J`, `h_F = σ[X].h_j`). -/
theorem entry_justified_of_anc (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) (hh : (st.σ X.root).h < (st.σ W.root).h)
    (hs : W.slot < (st.σ X.root).ThSlot + P.fg.δt) :
    ∃ D ∈ st.tree, st.Anc X D ∧ st.Anc D W ∧ (st.σ D.root).h = (st.σ X.root).h + 1 ∧
      (st.σ D.root).hj = (st.σ X.root).h ∧ (st.σ D.root).J = (st.σ X.root).Th ∧
      ((st.σ X.root).bound → (st.σ D.root).F = (st.σ X.root).J ∧
        (st.σ D.root).hF = (st.σ X.root).hj) := by
  obtain ⟨c, d, hc, hd, hpre⟩ := chain_states_of_anc hr hX hXW
  obtain ⟨d₁, D, d₂, σ₂, rfl, hσ₂, h1, h2, h3, h4⟩ :=
    P.fg.early_cross_map_justifies Block.fgView hc hd hh (by
      intro B hB
      obtain ⟨d₁, d₂, rfl⟩ := List.append_of_mem hB
      exact lt_of_le_of_lt (hpre d₁ B d₂ rfl).2.2.2.1 hs)
  obtain ⟨hD, hXD, hDW, -, hσ⟩ := hpre d₁ D d₂ rfl
  obtain rfl : σ₂ = st.σ D.root := Option.some.inj (hσ₂.symm.trans hσ)
  exact ⟨D, hD, hXD, hDW, h1, h2, h3, h4⟩

end Store

namespace Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Two held blocks of one honest store with the same root are equal. -/
private theorem eq_of_root_eq (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {X X' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hX' : X' ∈ (tr.state y k).fg.tree)
    (he : X.root = X'.root) : X = X' :=
  (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy k)).2.1.1 hX hX' he

/-- **The window with the entry below the report.** `window_justifies_or_parents_above_after`
with one more fact in case (A): every held `X` with root `T` has `X ⪯ C` (the report of
`hreports'` is above the held block of root `T`, which is unique). -/
theorem window_justifies_or_parents_above_after' (hrun : GoldilocksRun proposer dg H tr)
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
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hreports' : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tH ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_crossed_after hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl
      hks hh hT hh₀ hp hvb hreports' with
    ⟨X₀, hX₀, hX₀r, -, z, hz, r, ell, C, hto, htr, hrv, hXC, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, htr, hrv, hlt, fun X hX hXr => ?_,
      fun s P hP hsv => ?_⟩
    · have hrh := hH.toHealedRecords.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · rw [eq_of_root_eq hrun hy hX hX₀ (hXr.trans hX₀r.symm)]
      exact hXC
    · exact crossed_parents_above hrun hp.noColl hH hz hto htr hlt hP (by linarith)
  · exact Or.inr hW

/-- **The two-way window theorem with the entry below the report.**
`window_justifies_or_parents_above_unanimous''` with one more fact in case (A): every held `X`
with root `T` has `X ⪯ C`; in the escape case, `X ⪯ P ⪯ C` by `hXP`. -/
theorem window_justifies_or_parents_above_unanimous_entry (hrun : GoldilocksRun proposer dg H tr)
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
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
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
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hXk, hXr, -, hXh, -⟩ := lock_entry_block hrun hy hBy
  rcases window_reports_of_unanimous hp hcatch hP hslot hu hPg hun hgu hR
      (huv.trans hvb) htu huv hXP with hrep | ⟨x, hx, r, e, C, hto, htr, hrv, hPC, hlt⟩
  · exact window_justifies_or_parents_above_after' hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl
      hf hB hBl hks hh hT hh₀ hp hvb hrep
  have hnc := hp.noColl
  have hXPa := hXP X hXk (hXr.trans hT)
  have hCx : C ∈ (tr.state x r).fg.tree :=
    Healing.mem_tree_of_frame hrun hx hto.1 (toFG_live_fast_lock hto).1
  have hPx : P ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hPC hCx
  have hXx : X ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hXPa hPx
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hx r)
    (Healing.store_anc_of_honest_anc hrun hnc hx hXPa hPx)
  rw [Healing.σ_eq_honest hrun hnc hx hy hXx hXk, hXh, hh] at hle
  have hhC : h < ((tr.state x r).fg.σ C.root).h := by omega
  refine Or.inl ⟨x, hx, r, e, C, hto, ?_, htr, hrv, hhC,
    fun X' hX' hX'r => (hXP X' hX' hX'r).trans hPC, fun s P' hP' hsv => ?_⟩
  · have hrh := hH.toHealedRecords.rh
    exact hp.cutZ_lt_of_high hx hCx (by omega)
  · exact crossed_parents_above hrun hnc hH hx hto htr hhC hP' (by linarith)

/-- **L5.4: the entry is justified on the parent's chain (r14 s5).** The premises of
`window_justifies_or_parents_above_unanimous''`. Conclusion: (A) for every held `X` of `y` with
root `T` (the entry block of `(h, T)`), every honest proposal `P` of a slot `s` with
`v + Δ ≤ t_s` and `s ≤ σ[X].ThSlot + δt` has an honest parent `Pr ⪰ X`, and at every honest
holder of `Pr` some held `D` with `X ⪯ D ⪯ Pr` justified `(h, T)` (`σ[D].h = h + 1`,
`σ[D].h_j = h`, `σ[D].J = T`) and, if `σ[X]` is bound, finalized the predecessor block
(`σ[D].F = σ[X].J`, `σ[D].h_F = σ[X].h_j`, L6.1 (i)); or (B) the window conclusion. -/
theorem window_entry_justified_or_window (hrun : GoldilocksRun proposer dg H tr)
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
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
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
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        s ≤ ((tr.state y k).fg.σ X.root).ThSlot + sp.toParams.fg.δt →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, -, hX₀h, hX₀T⟩ := lock_entry_block hrun hy hBy
  rcases window_justifies_or_parents_above_unanimous_entry hrun hq hH hs hv hM4 hs₁ hvs hy hc htH
    hl hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with
    ⟨-, -, -, -, C, -, -, -, -, -, hXC, hA⟩ | hW
  · refine Or.inl fun X hX hXr s P' hP' hsv hsδ => ?_
    obtain rfl : X = X₀ := eq_of_root_eq hrun hy hX hX₀ (hXr.trans (hX₀r.trans hT).symm)
    obtain ⟨Pr, hPr, hpar, hCPr, habove⟩ := hA s P' hP' hsv
    have hXPr := (hXC X hX hXr).trans hCPr
    refine ⟨Pr, hPr, hpar, hXPr, fun w hw j hPrj => ?_⟩
    have hnc := hp.noColl
    have hXw := Healing.mem_of_honest_anc hrun hnc hw hXPr hPrj
    have hσ := Healing.σ_eq_honest hrun hnc hy hw hX hXw
    obtain ⟨-, ℓ', -, -, -, -, -, -, -, hPs, -, -, j', -, hacc, -⟩ := hP'.2
    have hP'm : P' ∈ tr.HonestBlocks H := ⟨_, hP'.1, j', hp.acceptAt_mem hP'.1 hacc⟩
    have hPrs : Pr.slot < P'.slot := hp.honest_coherent.2 Pr hPr P' hP'm hpar
    have hXh : ((tr.state w j).fg.σ X.root).h = h := by rw [← hσ, hX₀h, hh]
    have hXT : ((tr.state w j).fg.σ X.root).Th = T := by rw [← hσ, hX₀T, hX₀r, hT]
    obtain ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩ := Store.entry_justified_of_anc
      (Compose.fg_reachable hrun.toLocalRun hw j) hXw
      (Healing.store_anc_of_honest_anc hrun hnc hw hXPr hPrj)
      (by rw [hXh]; exact habove w hw j hPrj) (by rw [← hσ]; omega)
    rw [hXh] at h1 h2
    rw [hXT] at h3
    rw [← hσ] at h4
    exact ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩
  · exact Or.inr hW

end Refinement

end Consensus.Goldilocks

end
