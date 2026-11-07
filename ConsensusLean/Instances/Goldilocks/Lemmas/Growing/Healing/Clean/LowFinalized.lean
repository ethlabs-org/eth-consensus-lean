module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # A low finalized block is below every bounded high origin, under growing faults

* `Growing.FGLocalRun.finalized_anc_of_lt_at` (G1.2 at strict height over an FG trace under
  growing faults): a block finalized at height `h_F` by the store of a reader honest at `t` is an
  ancestor of every block of state height `> h_F` held by a reader honest at `u`, when fewer than
  `2q − n` validators are faulty at `max t u`. Each reader's store, chain and signatures are read
  on the prefix through its own observation; the crossing quorum's honest validator is honest at
  `max t u`, so both of its signatures are before its compromise (`non_framing`).
* `ResetPremisesUpTo.low_finalized_below_origin_at`: for a reader honest at `t ≤ b` with
  `Σ.h_j ≤ H_z`, its `Σ.F` is genesis or finalized at a height `≤ H_z`, below the high origin's
  block held by its writer at its write `≤ b`; the faults are counted at the later of the two
  observations. -/

namespace Consensus.Goldilocks.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- A linked chain from `A` lies below its last block. -/
private theorem anc_of_linked {S : Set (NodeBlock P ACP)} :
    ∀ (c : List (NodeBlock P ACP)) (A : NodeBlock P ACP), A ∈ S → (∀ X ∈ c, X ∈ S) →
      c.map Block.parent = ((A.root :: c.map Block.root).take c.length).map some →
      ∀ B, (A :: c).getLast? = some B → ∀ X ∈ A :: c, Goldilocks.Anc S X B
  | [], A, _, _, _, B, hB, X, hX => by
    simp only [List.getLast?_singleton, Option.some.injEq, List.mem_singleton] at hB hX
    exact hX ▸ hB ▸ .refl
  | C :: c, A, hA, hc, hl, B, hB, X, hX => by
    simp only [List.map_cons, List.length_cons, List.take_succ_cons, List.cons.injEq] at hl
    rw [List.getLast?_cons_cons] at hB
    have ih := anc_of_linked c C (hc C List.mem_cons_self)
      (fun X hX => hc X (List.mem_cons_of_mem _ hX)) hl.2 B hB
    rcases List.mem_cons.1 hX with rfl | hX
    · exact .head ⟨hA, hc C List.mem_cons_self, hl.1⟩ (ih C List.mem_cons_self)
    · exact ih X hX

/-- The attestations of signers honest at `t` on a chain of blocks held by a reader honest at
`t` were signed before the reader's cut. -/
private theorem chain_signed_at (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} {i : Nat}
    {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    {c : List (NodeBlock P ACP)} (hc : ∀ X ∈ c, X ∈ (tr.store y i).tree) :
    ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H t →
      ∃ k < i, tr.time k ≤ t ∧ tr.SignAt a.val k a := by
  have hR := hr.upTo ht
  have hs : FGTrace.store (tr.upTo t) y i = tr.store y i := by
    simp only [FGTrace.store, Trace.upTo_state tr y hle]
  intro a ha hav
  obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
  rcases Store.tree_accepted hR hy (hs ▸ hc X hXc) with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · obtain ⟨k', hk', src, hcall⟩ := hR.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
    obtain ⟨hk'd, hcall⟩ := (Trace.upTo_callAt tr).mp hcall
    exact ⟨k', by omega, hk'd, src, hcall⟩

/-- **G1.2 at strict height under growing faults.** A block `F` finalized by the state of a
held `X` in the store of a reader honest at `t` is an ancestor of every block `W` held by a
reader honest at `u` whose state height exceeds the finalized height, when fewer than `2q − n`
validators are faulty at `max t u`. -/
theorem FGLocalRun.finalized_anc_of_lt_at (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n}
    {k m : Nat} {t u : Time} (ht : 0 ≤ t) (hk : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hm : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u)
    (hH : (H (max t u))ᶜ.ncard < 2 * P.fg.q - P.n) {X F W : NodeBlock P ACP}
    (hX : X ∈ (tr.store y k).tree) (hF : F ∈ (tr.store y k).tree)
    (hFr : F.root = ((tr.store y k).σ X.root).F) (hW : W ∈ (tr.store z m).tree)
    (hlt : ((tr.store y k).σ X.root).hF < ((tr.store z m).σ W.root).h) :
    Goldilocks.Anc U F W := by
  have hR₁ : (tr.store y k).Reachable acp₀ := by
    simpa only [FGTrace.store, Trace.upTo_state tr y hk] using
      Store.store_reachable (hr.upTo ht) hy k
  have hR₂ : (tr.store z m).Reachable acp₀ := by
    simpa only [FGTrace.store, Trace.upTo_state tr z hm] using
      Store.store_reachable (hr.upTo hu) hz m
  have hsub₁ := hr.tree_subset y k t ht hk hy
  have hsub₂ := hr.tree_subset z m u hu hm hz
  obtain ⟨c₁, hc₁, -, -, hσ₁⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hR₁ X hX
  obtain ⟨c₂, hc₂, hl₂, hlast₂, hσ₂⟩ :=
    Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hR₂ W hW
  obtain ⟨-, -, hg₂, -⟩ := Goldilocks.Store.accepted_tree P ACP acp₀ _ hR₂
  have hanc := anc_of_linked c₂ _ hg₂ hc₂ hl₂ W (by
    rcases hlast₂ with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  by_contra hn
  have hnot : ((tr.store y k).σ X.root).F ∉ P.fg.roots (c₂.map Block.fgView) := by
    intro hmem
    rw [← hFr] at hmem
    obtain ⟨Y, hY, hYF⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c₂, Y.root = F.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hmem
    have hYt : Y ∈ (tr.store z m).tree := by
      rcases List.mem_cons.1 hY with rfl | h
      exacts [hg₂, hc₂ _ h]
    obtain rfl : Y = F := hr.coherent.1 (hsub₂ hYt) (hsub₁ hF) hYF
    exact hn ((hanc Y hY).mono hsub₂)
  have hF1 : 1 ≤ ((tr.store y k).σ X.root).hF := by
    by_contra h0
    apply hnot
    rw [(FG.chain_invariants P.fg _ _ hσ₁).2.2.2.2.1 (by omega)]
    exact List.mem_cons_self
  obtain ⟨S, hS, hSv⟩ := P.fg.finalization_meets_crossing hσ₁ hσ₂ hF1 hlt hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H (max t u) := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin P.fg.n))) (t := (H (max t u))ᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : ((H (max t u))ᶜ : Set (Fin P.fg.n)).ncard = ((H (max t u))ᶜ : Set (Fin P.n)).ncard :=
      rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  obtain ⟨k₁, -, hk₁, hka⟩ := chain_signed_at hr ht hk hy hc₁ a ha
    (hr.antitone (le_max_left _ _) hv)
  obtain ⟨k₂, -, hk₂, hkb⟩ := chain_signed_at hr hu hm hz hc₂ b hb
    (hab.1 ▸ hr.antitone (le_max_right _ _) hv)
  rw [← hab.1] at hkb
  exact hr.non_framing hka hkb
    (hr.antitone (max_le (hk₁.trans (le_max_left _ _)) (hk₂.trans (le_max_right _ _))) hv) hab

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The FG projection's store of a reader honest at `t`, after cuts by `t`, is the run's. -/
private theorem projFG_store_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) :
    tr.projFG.store y m = (tr.state y m).fg := by
  have h := Compose.projFG_state (hrun.upTo ht).toLocalRun hy m
  rw [RunTrace.upTo_projFG, Trace.upTo_state tr.projFG y hle, Trace.upTo_state tr y hle] at h
  simp only [FGTrace.store, h]

/-- A low finalized block of a reader honest at `t ≤ b` is below every bounded high origin. -/
theorem low_finalized_below_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hBt := Outcome.high_origin_mem_at hrun hnc ho
  have hreach := fg_reachable_at hrun ht hle hy
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, m, t, ht, hle, hy, hX⟩
  have hcoh : Coherent (tr.state y m).fg.tree := hU.mono hsub
  have hg := Store.genesis_mem hreach
  have hgB : Anc (tr.HonestBlocksAt H)
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B :=
    ((Goldilocks.Store.accepted_tree _ _ _ _
      (fg_reachable_at hrun hi0 hlei ho.1)).2.2.2 B hBt).mono
        (fun X hX => (⟨x, i, tr.time i, hi0, hlei, ho.1, hX⟩ : X ∈ tr.HonestBlocksAt H))
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hgF : (tr.state y m).fg.Anc (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      (tr.state y m).fg.F := (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 _ hFm
  -- a genesis `Σ.F` is below `B`
  have hgen : (tr.state y m).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := fun he => by
    rw [hcoh.1 hFm hg he]
    exact hgB
  rcases Store.fin_pair_entry hreach hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgen (hBfF.symm.trans he)
  obtain rfl : W = (tr.state y m).fg.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : E = (tr.state y m).fg.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · -- `Σ.J` is genesis, so is `Σ.F ⪯ Σ.J`
    rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc hreach hFJ
  -- G1.2 at strict height, the faults counted at the later observation
  have hfg : Consensus.Goldilocks.Growing.FGLocalRun (goldilocksNode sp ro).genesisPayload H
      (tr.HonestBlocksAt H) tr.projFG :=
    have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
    Compose.Growing.fg_projection _ _ dg H _ tr proposer
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩
      hrun.genesis_root_ok hrun.toLocalRun hnc
  have hH : (H (max t (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have h3 := hp.faults (max t (tr.time i)) (ht.trans (le_max_left _ _)) (max_le htb hib)
    change 3 * _ ≤ sp.toParams.n - 1 at h3
    have hn := sp.toParams.hn
    change _ < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    clear * - h3 hn; omega
  have h := hfg.finalized_anc_of_lt_at ht hle hy hi0 hlei ho.1 hH (k := m) (m := i) (X := Bf)
    (F := (tr.state y m).fg.F) (W := B)
  rw [projFG_store_at hrun ht hle hy, projFG_store_at hrun hi0 hlei ho.1] at h
  have hhigh := ho.2.2.2
  exact h hBf hFm hBfF.symm hBt (by omega)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
