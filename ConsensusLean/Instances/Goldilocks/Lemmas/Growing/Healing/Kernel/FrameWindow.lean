module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Step 2 of the growing drain kernel: a frame window from per-cut service

`exists_frameWindow_seq_of_service_proof_at`: per-cut height range and relay calls give a frame
window (`FrameWindow`) of the requested length. The sequential pigeonhole
(`exists_const_window_seq`) runs over the cuts of nodes honest at them; its lag is the merged
frame-key lag between two independently honest observations (`frameKey'_lag_obs`): the source
`x` is honest at its cut `i`, the receiver `z` at its cut `m`, and the source need not stay honest.
The frame data of a window agree across its honest cuts (`frameWindow_of_frameKey'_eq_obs`).

Every cross-node fact is charged at the later of the two observations: certificate
intersection for `Σ.F` below a crossing (`finalized_anc_obs`, `F_anc_of_hj_lt_obs`) and
justification agreement (`J_eq_obs`). Each chain's signatures are recovered at its own reader's
time; no global cache invariant of a terminal honest cohort is used. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-! ### Chains of held blocks (as in `Growing/Healing/B2`) -/

private theorem held_chain_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree) :
    ∃ c : List (SA.Blk sp.n (List (FG.Att sp.n))),
      sp.toParams.fg.chainState (c.map Block.fgView) = some ((tr.state y i).fg.σ B.root) ∧
      (∀ r ∈ sp.toParams.fg.roots (c.map Block.fgView),
        ∃ Y ∈ (tr.state y i).fg.tree, Y.root = r ∧ (tr.state y i).fg.Anc Y B) ∧
      ∀ a ∈ sp.toParams.fg.chainAtts (c.map Block.fgView), a.val ∈ H t →
        ∃ k < i, tr.SignAt a.val k a := by
  have hR := fg_reachable_at hrun ht hle hy
  obtain ⟨c, hc, hl, hlast, hσ⟩ := Store.chain_state_of_chain _ _ _ _ hR B hB
  obtain ⟨-, -, hg, -⟩ := Store.accepted_tree _ _ _ _ hR
  have hanc := Store.anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨c, hσ, fun r hr => ?_, fun a ha hav => ?_⟩
  · obtain ⟨Y, hY, hYr⟩ : ∃ Y ∈ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :: c,
        Y.root = r := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hr
    refine ⟨Y, ?_, hYr, hanc Y hY⟩
    rcases List.mem_cons.mp hY with rfl | h
    exacts [hg, hc _ h]
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.mp ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.mp hX
    have hs := Trace.upTo_state tr y hle
    have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [hs]; exact hc X hXc
    rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hXt with rfl | ⟨k, hk, hacc⟩
    · cases haX
    · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
      obtain ⟨k', hk', hs'⟩ := hrun.toLocalRun.att_unforgeable y k a
        (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
        (hrun.antitone (hle k hk) hav)
      exact ⟨k', hk'.trans hk, hs'⟩

/-! ### Cross-node facts at two independently honest observations -/

/-- **`Σ.F` below a crossing**: a finalized block `F` of `y`'s chain to `X` (observed while honest
at `u`) is below a block `W` held by `x` (observed while honest at `t`) whose state height exceeds
the finalized height of `X`. Certificate intersection is charged at `max u t`. -/
theorem finalized_anc_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y m).fg.tree)
    (hFt : F ∈ (tr.state y m).fg.tree) (hFr : F.root = ((tr.state y m).fg.σ X.root).F)
    (hW : W ∈ (tr.state x i).fg.tree)
    (hlt : ((tr.state y m).fg.σ X.root).hF < ((tr.state x i).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain_obs hrun hu hytime hy hX
  obtain ⟨c₂, h₂, hr₂, ha₂⟩ := held_chain_obs hrun ht hxtime hx hW
  obtain ⟨-, -, -, -, hF0, -⟩ := FG.chain_invariants sp.toParams.fg _ _ h₁
  have hsuby : (tr.state y m).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩
  have hsubx : (tr.state x i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩
  suffices hmem : F.root ∈ sp.toParams.fg.roots (c₂.map Block.fgView) by
    obtain ⟨Y, hY, hYr, hYW⟩ := hr₂ _ hmem
    rw [hU.1 (hsubx hY) (hsuby hFt) hYr] at hYW
    exact honest_anc_of_store_anc_at ht hxtime hx hYW
  rw [hFr]
  rcases Nat.eq_zero_or_pos ((tr.state y m).fg.σ X.root).hF with h0 | h0
  · rw [hF0 h0]
    exact List.mem_cons_self
  by_contra hnot
  obtain ⟨S, hS, hSv⟩ := sp.toParams.fg.finalization_meets_crossing h₁ h₂ h0 hlt hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H (max u t) := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard (s := (S : Set (Fin sp.toParams.fg.n)))
      (t := (H (max u t))ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : sp.toParams.fg.n = sp.n := rfl
    have : ((H (max u t))ᶜ : Set (Fin sp.toParams.fg.n)).ncard =
        ((H (max u t))ᶜ : Set (Fin sp.n)).ncard := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  obtain ⟨k, hk, hka⟩ := ha₁ a ha (hrun.antitone (le_max_left _ _) hv)
  obtain ⟨l, hl, hlb⟩ := ha₂ b hb (hab.1 ▸ hrun.antitone (le_max_right _ _) hv)
  rw [← hab.1] at hlb
  have hd : 0 ≤ max u t := hu.trans (le_max_left _ _)
  have hr := (hrun.upTo hd)
  have hka' : (tr.upTo (max u t)).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans (le_max_left _ _), hka⟩
  have hlb' : (tr.upTo (max u t)).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans (le_max_right _ _), hlb⟩
  have hfg := Compose.fg_projection sp.toParams (goldilocksNode sp ro) dg (H (max u t))
    (fun v => v.val) (tr.upTo (max u t)) proposer (Compose.requirements sp ro)
    hr.genesis_root_ok hr.toLocalRun (hnc.upTo _)
  obtain ⟨inputs, hin, hs⟩ := Store.signed_run hfg hv (max k l + 1)
  have ha' := hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩
  have hb' := hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩
  exact FG.client_safety sp.toParams.fg a.val inputs hin a ha' b hb' hab

/-- **Equal justified heights agree** at two independently honest observations: two
justification quorums of one height meet in a validator honest at `max u t`, whose two
attestations would be an E2 pair. -/
private theorem J_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y m).fg.tree)
    (hB' : B' ∈ (tr.state x i).fg.tree)
    (he : ((tr.state y m).fg.σ B.root).hj = ((tr.state x i).fg.σ B'.root).hj) :
    ((tr.state y m).fg.σ B.root).J = ((tr.state x i).fg.σ B'.root).J :=
  Store.J_eq_of_hj_eq_of_safe (fg_reachable_at hrun hu hytime hy)
    (fg_reachable_at hrun ht hxtime hx) hf
    (held_atts_safe_at hrun hnc hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hB hB' he

/-- `Σ.J` of two stores observed while honest with equal `h_j` agree. -/
private theorem J_eq_of_hj_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (he : (tr.state y m).fg.hj = (tr.state x i).fg.hj) :
    (tr.state y m).fg.J = (tr.state x i).fg.J := by
  have hRy := fg_reachable_at hrun hu hytime hy
  have hRx := fg_reachable_at hrun ht hxtime hx
  obtain ⟨-, hJy, -, ⟨By, hBy, hByJ, hByhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hRy
  obtain ⟨-, hJx, -, ⟨Bx, hBx, hBxJ, hBxhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hRx
  have h := J_eq_obs hrun hnc hu hytime hy ht hxtime hx hf hBy hBx (by omega)
  exact (Compose.Growing.honest_blocks_coherent hrun hnc).1 ⟨y, m, u, hu, hytime, hy, hJy⟩
    ⟨x, i, t, ht, hxtime, hx, hJx⟩ (hByJ.symm.trans (h.trans hBxJ))

/-- `h_j < h_max` at a store observed while honest. -/
private theorem hj_lt_hmax_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
  have hR := fg_reachable_at hrun ht hle hy
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := Store.cache_invariants _ _ _ _ hR
  exact hBjhj ▸ (Store.hj_lt_h hR hBj).trans_le (hge Bj hBj)

/-- **`Σ.F` below every block of state height `> h_j`** (store-level G1.2) at two independently
honest observations. -/
private theorem F_anc_of_hj_lt_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBt : B ∈ (tr.state x i).fg.tree)
    (hlt : (tr.state y m).fg.hj < ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := by
  have hreach := fg_reachable_at hrun hu hytime hy
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩
  have hcoh : Coherent (tr.state y m).fg.tree := hU.mono hsub
  have hg := Store.genesis_mem hreach
  have hgB : Anc (tr.HonestBlocksAt H)
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B :=
    ((Store.accepted_tree _ _ _ _ (fg_reachable_at hrun ht hxtime hx)).2.2.2 B hBt).mono
      (fun X hX => (⟨x, i, t, ht, hxtime, hx, hX⟩ : X ∈ tr.HonestBlocksAt H))
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Store.cache_invariants _ _ _ _ hreach
  have hgF : (tr.state y m).fg.Anc (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      (tr.state y m).fg.F := (Store.accepted_tree _ _ _ _ hreach).2.2.2 _ hFm
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
  · rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc hreach hFJ
  exact finalized_anc_obs hrun hnc hu hytime hy ht hxtime hx hf hBf hFm hBfF.symm hBt
    (by omega)

/-! ### The frame-key lag between independently honest observations -/

/-- **The frame-key lag** with the source `x` honest at its cut `i` and the receiver `z` honest at
its cut `m`, after a call of `z` at or after the relay deadline of `i` (`frameKey_lag_le` at
`τ = tr.time i`). -/
theorem frameKey_lag_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey (tr.state x i).fg ≤ frameKey (tr.state z m).fg := by
  have hi0 := hrun.time_nonneg i
  have hm0 := hrun.time_nonneg m
  have hxle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hzle : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hfmi : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    rw [max_eq_right him]; exact hf _ hm0 hmb
  have hfim : (H (max (tr.time m) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    rw [max_eq_left him]; exact hf _ hm0 hmb
  have hfmm : (H (max (tr.time m) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    rw [max_self]; exact hf _ hm0 hmb
  have hRx := fg_reachable_at hrun hi0 hxle hx
  have hRz := fg_reachable_at hrun hm0 hzle hz
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have memx : ∀ X ∈ (tr.state x i).fg.tree, X ∈ tr.HonestBlocksAt H :=
    fun X hX => ⟨x, i, tr.time i, hi0, hxle, hx, hX⟩
  have memz : ∀ X ∈ (tr.state z m).fg.tree, X ∈ tr.HonestBlocksAt H :=
    fun X hX => ⟨z, m, tr.time m, hm0, hzle, hz, hX⟩
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Store.cache_invariants _ _ _ _ hRz
  have hbx := frameKey_bounds (tr.state x i).fg
  have hbz := frameKey_bounds (tr.state z m).fg
  by_cases hlt : (tr.state x i).fg.hmax < (tr.state z m).fg.hmax
  · omega
  have hle : (tr.state z m).fg.hmax ≤ (tr.state x i).fg.hmax := not_lt.1 hlt
  have hheld : ∀ {B : SA.Blk sp.n (List (FG.Att sp.n))}, B ∈ (tr.state x i).fg.tree →
      (tr.state x i).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h → B ∈ (tr.state z m).fg.tree :=
    fun hB hh => held_of_relay_le_at hrun hnc hsvc hcatch hi0 hx hz hfmi hB (hle.trans hh) hxle
      hcall hcm
  have hσ : ∀ {B : SA.Blk sp.n (List (FG.Att sp.n))}, B ∈ (tr.state z m).fg.tree →
      B ∈ (tr.state x i).fg.tree →
      (tr.state z m).fg.σ B.root = (tr.state x i).fg.σ B.root :=
    fun hBz hBx => σ_eq_honest_at hrun hnc hm0 hzle hz hi0 hxle hx hBz hBx
  -- the `h_max` carrier
  have hBhz := hheld hBh hBhh.ge
  have heq : (tr.state z m).fg.hmax = (tr.state x i).fg.hmax := by
    have := hgez Bh hBhz
    rw [hσ hBhz hBh] at this
    omega
  -- the `J` carrier
  have hjz := hj_lt_hmax_obs hrun hm0 hzle hz
  have hjx := hj_lt_hmax_obs hrun hi0 hxle hx
  have hb : (tr.state x i).fg.hmax = (tr.state x i).fg.hj + 1 →
      (tr.state z m).fg.hmax = (tr.state z m).fg.hj + 1 := by
    intro hbx'
    have hBjh := Store.hj_lt_h hRx hBj
    have hBjz := hheld hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hRx hBj
    obtain rfl : E = (tr.state x i).fg.J := hU.1 (memx E hE) (memx _ hJx) (hEr.trans hBjJ)
    have hJz : (tr.state x i).fg.J ∈ (tr.state z m).fg.tree :=
      mem_of_honest_anc_at hrun hnc hm0 hzle hz (hEB.mono memx) hBjz
    have hJh := Store.J_height_le hRx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : (tr.state z m).fg.hj < (tr.state x i).fg.hj := by omega
    have hFJ := store_anc_of_honest_anc_at hrun hnc hm0 hzle hz
      (F_anc_of_hj_lt_obs hrun hnc hm0 hzle hz hi0 hxle hx hfim (m := m) (i := i) hJx
        (by rw [hBjhj] at hJh; omega)) hJz
    have hσj := hσ hBjz hBj
    have := (jMax_iff _).1 (jMax_of_reachable hRz) Bj hBjz _ hJz (by rw [hσj, hBjJ]) hFJ
    rw [hσj] at this
    omega
  -- the contest witness
  have hC : (tr.state x i).fg.Contest → (tr.state z m).fg.Contest := by
    rintro ⟨hbx', W, hW, -, hWh, hJW⟩
    have hbz' := hb hbx'
    have hWz := hheld hW hWh.ge
    have hσW := hσ hWz hW
    have hJ := J_eq_of_hj_eq_obs hrun hnc hm0 hzle hz hi0 hxle hx hfim (by omega)
    refine ⟨hbz', W, hWz, ?_, by rw [hσW]; omega, ?_⟩
    · exact store_anc_of_honest_anc_at hrun hnc hm0 hzle hz
        (F_anc_of_hmax_le_at hrun hnc hm0 hzle hz hm0 hzle hz hfmm hWz (by rw [hσW]; omega)) hWz
    · intro hJW'
      rw [hJ] at hJW'
      exact hJW (store_anc_of_honest_anc_at hrun hnc hi0 hxle hx (hJW'.mono memz) hW)
  rw [frameKey_def, frameKey_def]
  split_ifs <;> first | omega | tauto

/-- **The merged-key lag** between independently honest observations. -/
theorem frameKey'_lag_obs (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg :=
  (frameKey'_def _).symm ▸ (frameKey'_def _).symm ▸ keyMerge_mono
    (frameKey_lag_obs hrun hnc hf hsvc hcatch hx hz him hmb hcall hcm)

/-! ### The frame window -/

/-- A merged key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`. -/
theorem frameWindow_of_frameKey'_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      frameKey' (tr.state y i).fg = frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow tr H lo hi floor kindJ J := by
  classical
  have hpos : ∀ y i, y ∈ H (tr.time i) → 1 ≤ (tr.state y i).fg.hmax := fun y i hy => by
    have := hj_lt_hmax_obs hrun (hrun.time_nonneg i) (fun k hk => hrun.time_mono hk.le) hy
    omega
  by_cases hex : ∃ y i, y ∈ H (tr.time i) ∧ lo ≤ tr.time i ∧ tr.time i ≤ hi
  · obtain ⟨y₀, i₀, hy₀, h₁, h₂⟩ := hex
    let st := (tr.state y₀ i₀).fg
    refine ⟨st.headHeightFloor, st.hmax = st.hj + 1 ∧ ¬st.Contest, st.J, ⟨?_, ?_, ?_⟩⟩
    · intro y i hy hlo hhi'
      exact (frameKey'_eq_floor_kind (hpos y i hy) (hpos y₀ i₀ hy₀)
        (hK y y₀ i i₀ hy hy₀ hlo hhi' h₁ h₂)).1
    · intro y i hy hlo hhi'
      exact (frameKey'_eq_floor_kind (hpos y i hy) (hpos y₀ i₀ hy₀)
        (hK y y₀ i i₀ hy hy₀ hlo hhi' h₁ h₂)).2
    · intro y i hy hlo hhi' hk
      change (tr.state y₀ i₀).fg.hmax = (tr.state y₀ i₀).fg.hj + 1 ∧
        ¬(tr.state y₀ i₀).fg.Contest at hk
      change _ = (tr.state y₀ i₀).fg.J
      have he := hK y y₀ i i₀ hy hy₀ hlo hhi' h₁ h₂
      obtain ⟨hfl, hkd⟩ := frameKey'_eq_floor_kind (hpos y i hy) (hpos y₀ i₀ hy₀) he
      have hk' := hkd.2 hk
      have hj1 := hj_lt_hmax_obs hrun (hrun.time_nonneg i) (fun k hk => hrun.time_mono hk.le) hy
      have hj2 := hj_lt_hmax_obs hrun (hrun.time_nonneg i₀)
        (fun k hk => hrun.time_mono hk.le) hy₀
      have hmax : max (tr.time i) (tr.time i₀) ≤ b := max_le (hhi'.trans hhi) (h₂.trans hhi)
      apply J_eq_of_hj_eq_obs hrun hnc (hrun.time_nonneg i) (fun k hk => hrun.time_mono hk.le) hy
        (hrun.time_nonneg i₀) (fun k hk => hrun.time_mono hk.le) hy₀
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) hmax)
      unfold Store.headHeightFloor at hfl
      simp [hk.2, hk'.2] at hfl
      omega
  · push Not at hex
    refine ⟨0, True, sp.toParams.genesisBlock ([], []), ⟨?_, ?_, ?_⟩⟩ <;>
      intro y i hy hlo hhi' <;> exact absurd hhi' (not_le.2 (hex y i hy hlo))

/-- **Step 2 (proof of `exists_frameWindow_seq_of_service_at`)**: per-cut height range and relay
calls produce a frame window, by the sequential pigeonhole over the cuts of nodes honest at them
with the merged-key lag between independently honest observations. -/
theorem exists_frameWindow_seq_of_service_proof_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => frameKey' (tr.state y i).fg) (2 * hz) 4
    len hlen hlam
    (fun y i hy h1 h2 => by
      have := hrange y i hy h1 h2
      exact frameKey'_bounds this.1 this.2)
    (fun x z i m hx hz' hi _ him hmT => frameKey'_lag_obs hrun hnc hf hsvc hcatch hx hz'
      ((le_add_of_nonneg_right hlam).trans him) (hmT.le.trans hTb)
      (hcall z i m hz' hi him hmT) (hlo.trans (hi.trans ((le_add_of_nonneg_right hlam).trans him))))
    hT
  -- the window ends before `T`
  have hS : ∀ j, j ≤ 4 → ∑ i ∈ Finset.range (j + 1), (len (2 * hz + i) + lam) ≤
      ∑ i ∈ Finset.range 5, (len (2 * hz + i) + lam) := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun i _ _ => add_nonneg (hlen _) hlam
  have hend : a + len v < T := by
    have := hS (v - 2 * hz) (by omega)
    linarith
  refine ⟨v, hv1, hv2, a, h1, h2, hK, frameWindow_of_frameKey'_eq_obs hrun hnc hf
    (hend.le.trans hTb) ?_⟩
  intro y z i m hy hz' hi1 hi2 hm1 hm2
  rw [hK y i hy hi1 hi2, hK z m hz' hm1 hm2]

end Consensus.Goldilocks.Healing.Growing

end
