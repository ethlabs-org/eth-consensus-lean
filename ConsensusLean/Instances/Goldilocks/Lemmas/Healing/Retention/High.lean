module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Goldilocks Healing, HR.4: high blocks are accepted after the cut

`hr4-boot-carry.md` §2: a block whose state height is `≥ H_z + 1` is not held by an honest node
at a cut at or before `c_z` (`cutZ_lt_of_high`: the state before the first cut after `c_z` has
`Σ.h_max ≤ H_z`); every honest block above a high origin is high (`high_of_anc`), so its
acceptances are after `c_z`. With the store facts these need: heights do not decrease along
ancestry (`σ_h_le_of_anc`), ancestry below a held block is ancestry in the tree
(`anc_tree_of_anc`), and one state per block across honest stores (`σ_eq_run`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Vote Payload gbar)

/-- **Along ancestry the state height does not decrease** (a reachable store). -/
theorem σ_h_le_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W) :
    (st.σ A.root).h ≤ (st.σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    rcases stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

/-- The honest blocks of the run are coherent. -/
theorem honest_coherent (hp : ResetPremises tr H proposer dg g ΔF a) :
    Coherent (tr.HonestBlocks H) :=
  Compose.honest_blocks_coherent hp.run.toLocalRun hp.noColl

/-- **Ancestry below a held block is ancestry in the tree** (honest trees are parent-closed). -/
theorem anc_tree_of_anc (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {A C : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocks H) A C)
    (hC : C ∈ (tr.state y k).fg.tree) : (tr.state y k).fg.Anc A C := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((Store.accepted_tree _ _ _ _ hr).2.2.2 _ hC).cases_tail with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := (honest_coherent hp).1 ⟨y, hy, k, hZ.1⟩ hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

/-- A block below a held block is held. -/
theorem mem_tree_of_anc (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {A C : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocks H) A C)
    (hC : C ∈ (tr.state y k).fg.tree) : A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (anc_tree_of_anc hp hy h hC) he).1

/-- **One state per block across the honest stores.** -/
theorem σ_eq_run (hp : ResetPremises tr H proposer dg g ΔF a)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H)
    {k j : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hX' : X ∈ (tr.state z j).fg.tree) :
    (tr.state y k).fg.σ X.root = (tr.state z j).fg.σ X.root :=
  Store.σ_eq_of_mem (Compose.fg_reachable hp.run.toLocalRun hy k)
    (Compose.fg_reachable hp.run.toLocalRun hz j) (honest_coherent hp).1
    (fun _ hB => ⟨y, hy, k, hB⟩) (fun _ hB => ⟨z, hz, j, hB⟩) hX hX'

/-- The blocks held before the first cut after `c_z` have state height `≤ H_z`. -/
theorem h_le_HZ_of_firstCut {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    (hj : FirstCutAfter tr j (cutZ sp.toParams g)) (hp : ResetPremises tr H proposer dg g ΔF a)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y j).fg.tree) :
    ((tr.state y j).fg.σ X.root).h ≤ HZ tr H g :=
  ((Store.cache_invariants _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hy j)).2.2.2.2.1 X
    hX).trans (hmax_le_HZ hy hj)

/-- **A high block is held only after `c_z`** (`hr4-boot-carry.md` §2): a block of state height
`≥ H_z + 1` held by an honest node before cut `k` puts `k` after `c_z`. -/
theorem cutZ_lt_of_high (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hXh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ X.root).h) : cutZ sp.toParams g < tr.time k := by
  by_contra hk
  obtain ⟨j, hj⟩ := exists_firstCutAfter hp.run hp.healthy hy
  have hkj : k ≤ j := by
    by_contra hjk
    have := hp.run.time_mono (le_of_not_ge hjk)
    linarith [hj.2]
  have hXj := Compose.tree_mono hp.run.toLocalRun hy hkj hX
  have := h_le_HZ_of_firstCut hy hj hp hXj
  rw [σ_eq_run hp hy hy hX hXj] at hXh
  omega

/-- **Genesis is not high.** -/
theorem genesis_not_high (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hg : X.root = sp.genesisRoot) : ((tr.state y k).fg.σ X.root).h ≤ HZ tr H g := by
  obtain ⟨j, hj⟩ := exists_firstCutAfter hp.run hp.healthy hy
  have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
  obtain rfl : X = _ := (honest_coherent hp).1 ⟨y, hy, k, hX⟩ ⟨y, hy, j, hG⟩ hg
  rw [σ_eq_run hp hy hy hX hG]
  exact h_le_HZ_of_firstCut hy hj hp hG

/-- The block a fast lock selects is in the frame of the writing call. -/
theorem fastLock_mem {x : Fin sp.n} {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt tr.projAC x i s D CV) :
    ∃ ℓ, tr.projAC.CallAt x i ℓ ∧ D ∈ ℓ.frame.tree := by
  rcases hfl with ⟨ℓ, C, ⟨hc, -⟩, -, -, hsel, -⟩ | ⟨ℓ, A, hpt, -, hsel, -⟩
  · exact ⟨ℓ, hc, (SA.deepest_mem hsel).1.1.1⟩
  · unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact ⟨ℓ, hpt.1, (SA.deepest_mem hsel).1.1⟩

/-- The frame of an honest AC call is inside the node's FG tree. -/
theorem frame_tree_subset (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame.tree ⊆ (tr.state y k).fg.tree := by
  rw [Compose.frame_of_projAC hp.run hy hc]
  exact fun B hB => hB.1

/-- An honest AC acceptance of `W` at cut `k` follows its FG acceptance: `W` is in the node's FG
tree before cut `k`. -/
theorem acceptAt_mem (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hk : tr.projAC.AcceptAt y k W) :
    W ∈ (tr.state y k).fg.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ℓ, hc, hcall⟩ := hk
  exact frame_tree_subset hp hy hc ((SA.accept_new sp hr hy ⟨ℓ, hc, hcall⟩).1 ℓ hc)

/-- The stored block of a high origin is held by its writer at the write. -/
theorem highOrigin_mem (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    ∃ ℓ D CV, tr.projAC.CallAt x i ℓ ∧ SA.FastLockAt tr.projAC x i j D CV ∧
      B = ℓ.frame.viableAncestor D ∧ D ∈ ℓ.frame.tree ∧ B ∈ ℓ.frame.tree ∧
      ℓ.frame.Anc B D ∧ B ∈ (tr.state x i).fg.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨CV, ℓ, D, hc, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨ℓ', hc', hD⟩ := fastLock_mem hfl
  obtain rfl : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hc'.2)
  obtain ⟨hB, hBD⟩ := SA.viableAncestor_anc (SA.frameIn_of_callAt hr ho.1 hc).1 hD
  exact ⟨ℓ, D, CV, hc, hfl, rfl, hD, hB, hBD, frame_tree_subset hp ho.1 hc hB⟩

/-- **Every honest block above a high origin is high.** -/
theorem high_of_anc (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {z : Fin sp.n}
    (hz : z ∈ H) {k : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocks H) B W) :
    HZ tr H g + 1 ≤ ((tr.state z k).fg.σ W.root).h := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := highOrigin_mem hp ho
  have hBz := mem_tree_of_anc hp hz hBW hW
  have h₁ := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hz k)
    (anc_tree_of_anc hp hz hBW hW)
  rw [← σ_eq_run hp ho.1 hz hBx hBz] at h₁
  exact ho.2.2.2.trans h₁

/-- **An honest block above a high origin is held only after `c_z`**, and it is not genesis. -/
theorem cutZ_lt_of_anc (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {z : Fin sp.n}
    (hz : z ∈ H) {k : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocks H) B W) :
    cutZ sp.toParams g < tr.time k ∧ W.root ≠ sp.genesisRoot :=
  ⟨cutZ_lt_of_high hp hz hW (high_of_anc hp ho hz hW hBW), fun hg => by
    have := genesis_not_high hp hz hW hg
    have := high_of_anc hp ho hz hW hBW
    omega⟩

end Consensus.Goldilocks.Healing

end
