module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality

public section

/-! # Goldilocks Healing: HS.1, effective-phase viable-witness retention

Claims HS.1, `phase-service.md` §2 ("Why lower finality is benign"). Let the effective phase be
`(m, c)` at every cut of `[i, k]`, and let `W`, held by an honest node at cut `i`, be allowed in
the effective geometry (state height `≥ ℓ`, `ℓ = m` in a contest and `m − 1` otherwise; it
extends `J` in the top-`J` case).

* **(a) Lower finality is benign** (`finalized_anc_of_allowed`): at every cut of `[i, k]`, every
  honest `Σ.F` is below `W`. The `Σ.F` of a node is finalized by a held state at a height `h_F`
  with `h_F ≤ h_j < h ≤ m`; when `h_F` is below `W`'s state height, G1.2 at strict height
  (`finalized_anc_of_lt_fg`) gives it. Otherwise `h_F = h_j = m − 1` is the height of `W`, so
  the phase is not a contest (its floor is `m`), a gap is excluded by the justification at
  `m − 1`, and in the top-`J` case `Σ.F ⪯ Σ.J` (both at height `m − 1`) and `Σ.J` is the phase's
  `J` (HR.2 (a)), which `W` extends.
* **(b) The witness stays a viable head** (`viableHead_of_allowed`): an honest node of the phase
  that holds `W` has it in its viable heads, whatever its own lag. Its floor is at most `W`'s
  height, and its `fc_root` is `Σ.F` or `Σ.J`, below `W`: at `W`'s height `Σ.h_max` the absence of
  a local contest puts `Σ.J` below `W`; above it `Σ.h_j = m − 1` and the phase is the top `J`
  with `Σ.J = J` (HR.2 (a)), with no contest at height `m`.
* (c), (d) follow: every ancestor of `W` is below `fc_root` or above it, in the viable tree with
  the witness `W` (the voter block tree is closed under ancestors).
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- The FG projection under the HS shared premises, with `f < 2q − n`. -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
  obtain ⟨-, -, hf⟩ := hs.healthy
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hn := sp.toParams.hn
  exact ⟨Compose.fg_projection _ _ dg H _ tr proposer hreq hs.genesisRoot hrun.toLocalRun hs.noColl,
    by change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n; omega⟩

/-- At a cut of the phase, a node whose `Σ.h_j` is `m − 1` has the phase's justification as
`Σ.J` (HR.2 (a)). -/
private theorem J_eq_phase (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    {z : Fin sp.n} (hz : z ∈ H) {k m : Nat} {J₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hJ₀ : JustifiedAt tr.projFG H k (m - 1) J₀) (hj : (tr.state z k).fg.hj = m - 1) :
    (tr.state z k).fg.J = J₀ := by
  obtain ⟨hfg, hq⟩ := fg_run hrun hs
  have hR := Compose.fg_reachable hrun.toLocalRun hz k
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR
  obtain ⟨y₀, hy₀, hJ₀t, B₀, hB₀, hB₀j, hB₀J⟩ := hJ₀
  have he := J_eq_of_hj_eq hfg hq hz hy₀ (i := k) (j := k) (B := Bj) (B' := B₀)
    (by rw [store_eq hrun hz]; exact hBj) hB₀ (by rw [store_eq hrun hz, hBjhj, hj, hB₀j])
  rw [store_eq hrun hz, hBjJ, hB₀J] at he
  exact (Compose.honest_blocks_coherent hrun.toLocalRun hs.noColl).1 ⟨z, hz, k, hJm⟩
    ⟨y₀, hy₀, k, by rw [← store_eq hrun hy₀]; exact hJ₀t⟩ he

/-- A node's own justification makes `JustifiedAt` at its `Σ.h_j`. -/
private theorem justifiedAt_own (hrun : GoldilocksRun proposer dg H tr) {z : Fin sp.n} (hz : z ∈ H)
    (k : Nat) : JustifiedAt tr.projFG H k (tr.state z k).fg.hj (tr.state z k).fg.J := by
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hz k)
  exact ⟨z, hz, by rw [store_eq hrun hz]; exact hJm, Bj, by rw [store_eq hrun hz]; exact hBj,
    by rw [store_eq hrun hz]; exact hBjhj, by rw [store_eq hrun hz]; exact hBjJ⟩

private theorem floor_ge {β : Type} (m : Nat) (c : PhaseCase β) : m - 1 ≤ phaseFloor m c := by
  cases c <;> simp only [phaseFloor] <;> omega

/-- **HS.1 (a), lower finality is benign.** -/
theorem finalized_anc_of_allowed (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    {i k m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hon : PhaseOn tr.projFG H i k m c) {y : Fin sp.n} (hy : y ∈ H)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : EffAllowed (tr.state y i).fg m c W)
    {z : Fin sp.n} (hz : z ∈ H) {k' : Nat} (h1 : i ≤ k') (h2 : k' ≤ k) :
    Anc (tr.HonestBlocks H) (tr.state z k').fg.F W := by
  obtain ⟨hfg, hq⟩ := fg_run hrun hs
  have hl := hrun.toLocalRun
  have hU := Compose.honest_blocks_coherent hl hs.noColl
  have hph := hon k' h1 h2
  have hR := Compose.fg_reachable hl hz k'
  have hRy := Compose.fg_reachable hl hy i
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, hge, -, ⟨X, hX, hXF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  have hmax : (tr.state z k').fg.hmax ≤ m := by
    have := hph.frontierAt.2 z hz
    rwa [store_eq hrun hz] at this
  obtain ⟨c₁, -, -, -, hσ₁⟩ := Goldilocks.Store.chain_state_of_chain _ _ _ _ hR X hX
  obtain ⟨-, hFj, hjh, -⟩ := FG.chain_invariants _ _ _ hσ₁
  have hXh := hge X hX
  have hWf := hW.2.1
  have hfl := floor_ge m c
  -- the genesis case
  have hgen : (tr.state z k').fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload →
      Anc (tr.HonestBlocks H) (tr.state z k').fg.F W := fun he => by
    rw [he]
    exact Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨y, hy, i, hZ⟩)
      ((Goldilocks.Store.accepted_tree _ _ _ _ hRy).2.2.2 W hW.1)
  by_cases hlt : ((tr.state z k').fg.σ X.root).hF < ((tr.state y i).fg.σ W.root).h
  · exact finalized_anc_of_lt_fg hfg hq hz hy (k := k') (m := i)
      (by rw [store_eq hrun hz]; exact hX) (by rw [store_eq hrun hz]; exact hFm)
      (by rw [store_eq hrun hz]; exact hXF.symm) (by rw [store_eq hrun hy]; exact hW.1)
      (by rw [store_eq hrun hz, store_eq hrun hy]; exact hlt)
  push Not at hlt
  cases c with
  | gap =>
    obtain ⟨E, hE, hEr, -⟩ := Store.J_entry_of_reachable hR hX
    exact absurd ⟨z, hz, by rw [store_eq hrun hz]; exact hE, X, by rw [store_eq hrun hz]; exact hX,
      by rw [store_eq hrun hz]; omega, by rw [store_eq hrun hz]; exact hEr.symm⟩ (hph.2 E)
  | contest J₀ =>
    change m ≤ _ at hWf
    omega
  | top J₀ =>
    have hcoh := (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1
    have hG := (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.2.1
    rcases Store.fin_pair_entry hR hX with hg | ⟨W', hW', hW'r, hW'h⟩
    · exact hgen (hcoh.1 hFm hG (hXF.symm.trans hg))
    obtain rfl : W' = (tr.state z k').fg.F := hcoh.1 hW' hFm (hW'r.trans hXF)
    obtain ⟨E, hE, hEr, -, hEg⟩ := Store.J_entry_of_reachable hR hBj
    obtain rfl : E = (tr.state z k').fg.J := hcoh.1 hE hJm (hEr.trans hBjJ)
    rcases hEg with hEg | ⟨hEh, -⟩
    · have hFg : (tr.state z k').fg.F = _ :=
        Anc.antisymm hcoh (hEg ▸ hFJ) ((Goldilocks.Store.accepted_tree _ _ _ _ hR).2.2.2 _ hFm)
      exact hgen hFg
    have hle := h_le_of_store_anc hR hFJ
    have hjlt := (Store.hj_lt_h hR hBj).trans_le (hge Bj hBj)
    have hj : (tr.state z k').fg.hj = m - 1 := by omega
    have hJ := J_eq_phase hrun hs hz hph.2.1 hj
    rw [hJ] at hFJ
    exact (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨z, hz, k', hZ⟩) hFJ).trans
      (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨y, hy, i, hZ⟩) (hW.2.2 J₀ rfl))

/-- **HS.1 (b), the witness stays a viable head** of every honest node of the phase that holds
it. -/
theorem viableHead_of_allowed (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    {i k m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hon : PhaseOn tr.projFG H i k m c) {y : Fin sp.n} (hy : y ∈ H)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : EffAllowed (tr.state y i).fg m c W)
    {z : Fin sp.n} (hz : z ∈ H) {k' : Nat} (h1 : i ≤ k') (h2 : k' ≤ k)
    (hWz : W ∈ (tr.state z k').fg.tree) : W ∈ (Node.frame (tr.state z k')).viableHeads := by
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hph := hon k' h1 h2
  have hR := Compose.fg_reachable hl hz k'
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR
  have hmax : (tr.state z k').fg.hmax ≤ m := by
    have := hph.frontierAt.2 z hz
    rwa [store_eq hrun hz] at this
  have hFW := store_anc_of_honest_anc hrun hnc hz
    (finalized_anc_of_allowed hrun hs hon hy hW hz h1 h2) hWz
  have hσ := σ_eq_honest hrun hnc hz hy hWz hW.1
  have hWf : phaseFloor m c ≤ ((tr.state z k').fg.σ W.root).h := hσ ▸ hW.2.1
  have hfl := floor_ge m c
  have hWle := hge W hWz
  have hjlt := (Store.hj_lt_h hR hBj).trans_le (hge Bj hBj)
  rw [hBjhj] at hjlt
  -- below the node's frontier, `W` is at `m − 1`, the node's at `m`, and its `Σ.h_j` is `m − 1`
  have hlow : ((tr.state z k').fg.σ W.root).h < (tr.state z k').fg.hmax →
      (tr.state z k').fg.hmax = (tr.state z k').fg.hj + 1 → ∃ J₀, c = .top J₀ ∧
        (tr.state z k').fg.J = J₀ ∧ (tr.state z k').fg.hmax = m := by
    intro hl1 hl2
    have hj : (tr.state z k').fg.hj = m - 1 := by omega
    cases c with
    | gap => exact absurd (by rw [← hj]; exact justifiedAt_own hrun hz k') (hph.2 _)
    | contest J₀ =>
      change m ≤ _ at hWf
      omega
    | top J₀ => exact ⟨J₀, rfl, J_eq_phase hrun hs hz hph.2.1 hj, by omega⟩
  refine ⟨hWz, hFW, ?_, ?_⟩
  · unfold Store.fcRoot
    split_ifs with hcond
    · by_cases heq : ((tr.state z k').fg.σ W.root).h = (tr.state z k').fg.hmax
      · by_contra hn
        exact hcond.2 ⟨hcond.1, W, hWz, hFW, heq, hn⟩
      · obtain ⟨J₀, rfl, hJ, -⟩ := hlow (lt_of_le_of_ne hWle heq) hcond.1
        rw [hJ]
        exact store_anc_of_honest_anc hrun hnc hz
          (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨y, hy, i, hZ⟩) (hW.2.2 J₀ rfl)) hWz
    · exact hFW
  · change (tr.state z k').fg.headHeightFloor ≤ _
    unfold Store.headHeightFloor
    split_ifs with hcon
    · by_contra hn
      obtain ⟨J₀, rfl, hJ, hm⟩ := hlow (not_le.1 hn) hcon.1
      obtain ⟨-, B, hB, -, hBh, hBn⟩ := hcon
      rw [hJ] at hBn
      exact hph.2.2 ⟨z, hz, B, by rw [store_eq hrun hz]; exact hB,
        by rw [store_eq hrun hz, hBh, hm], by rw [store_eq hrun hz]; exact hBn⟩
    · omega

/-- **HS.1, effective-phase viable-witness retention** (claims HS.1, `phase-service.md` §2). -/
theorem viable_witness_retention_of (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    {i k m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hon : PhaseOn tr.projFG H i k m c) {y : Fin sp.n} (hy : y ∈ H)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : EffAllowed (tr.state y i).fg m c W)
    {z : Fin sp.n} (hz : z ∈ H) {k' : Nat} (h1 : i ≤ k') (h2 : k' ≤ k) :
    Anc (tr.HonestBlocks H) (tr.state z k').fg.F W ∧
      (W ∈ (tr.state z k').fg.tree →
        W ∈ (Node.frame (tr.state z k')).tree ∧
        (W ∈ (Node.frame (tr.state z k')).viableHeads ∨
          Anc (tr.HonestBlocks H) W (Node.frame (tr.state z k')).fcRoot) ∧
        ∀ X, Anc (tr.HonestBlocks H) X W →
          Anc (tr.HonestBlocks H) X (Node.frame (tr.state z k')).fcRoot ∨
          X ∈ (Node.frame (tr.state z k')).viableTree (Node.frame (tr.state z k')).tree) ∧
      ∀ ℓ e, SA.CastAt tr.projAC z k' ℓ e →
        W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot →
        ∀ X, Anc (tr.HonestBlocks H) X W →
          X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
          Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot := by
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hR := Compose.fg_reachable hl hz k'
  have hcoh := (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1
  have hsub : (tr.state z k').fg.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨z, hz, k', hZ⟩
  obtain ⟨-, -, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR
  have hFfc : (tr.state z k').fg.Anc (tr.state z k').fg.F (tr.state z k').fg.fcRoot := by
    unfold Store.fcRoot
    split_ifs
    · exact hFJ
    · exact .refl
  -- every ancestor of a held viable head is below `fc_root` or above it, in the frame
  have hanc : W ∈ (tr.state z k').fg.tree → ∀ X, Anc (tr.HonestBlocks H) X W →
      Anc (tr.HonestBlocks H) X (Node.frame (tr.state z k')).fcRoot ∨
        ((Node.frame (tr.state z k')).Anc (Node.frame (tr.state z k')).fcRoot X ∧
          (Node.frame (tr.state z k')).Anc X W) := by
    intro hWz X hX
    have hv := viableHead_of_allowed hrun hs hon hy hW hz h1 h2 hWz
    have hXW := store_anc_of_honest_anc hrun hnc hz hX hWz
    rcases Anc.total hcoh hXW hv.2.2.1 with h | h
    · exact Or.inl (Anc.mono hsub h)
    · exact Or.inr ⟨Anc.restrict hFfc h, Anc.restrict (hFfc.trans h) hXW⟩
  refine ⟨finalized_anc_of_allowed hrun hs hon hy hW hz h1 h2, fun hWz => ?_,
    fun ℓ e hce hWv X hX => ?_⟩
  · have hv := viableHead_of_allowed hrun hs hon hy hW hz h1 h2 hWz
    refine ⟨⟨hWz, hv.2.1⟩, Or.inl hv, fun X hX => (hanc hWz X hX).imp_right fun h => ?_⟩
    exact ⟨⟨mem_of_honest_anc hrun hnc hz hX hWz, hFfc.trans (Anc.mono (fun _ h' => h'.1) h.1)⟩,
      h.1, W, ⟨hWz, hv.2.1⟩, hv, h.2⟩
  · have hfr := Compose.frame_of_projAC hrun hz hce.1
    have hWz : W ∈ (tr.state z k').fg.tree := by
      have := hWv.1
      rw [hfr] at this
      exact this.1
    have hv := viableHead_of_allowed hrun hs hon hy hW hz h1 h2 hWz
    rcases hanc hWz X hX with h | ⟨hfX, hXW⟩
    · exact Or.inr (hfr ▸ h)
    · have hXv := SA.voterBlockTree_anc
        (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
        hz hce W hWv X (hfr ▸ hXW)
      rw [hfr] at hXv hWv ⊢
      exact Or.inl ⟨hXv, hfX, W, hWv, hv, hXW⟩

end Consensus.Goldilocks.Healing

end
