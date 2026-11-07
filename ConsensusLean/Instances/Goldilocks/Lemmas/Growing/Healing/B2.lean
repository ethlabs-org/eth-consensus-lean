module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # Finalized ancestry at independent honest observations

Certificate intersection is charged at the later observation. Each chain's signatures
are recovered at its own reader's horizon, rather than through a terminal honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem held_chain_at
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

/-- Strict-height finalized ancestry for two independently honest held-state observations. -/
theorem F_anc_of_hmax_le_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x i).fg.tree)
    (hle : (tr.state y m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := by
  have hR := fg_reachable_at hrun hu hytime hy
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨hF, -, -, -, hge, -, X, hX, hXF⟩ := Store.cache_invariants _ _ _ _ hR
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain_at hrun hu hytime hy hX
  obtain ⟨c₂, h₂, hr₂, ha₂⟩ := held_chain_at hrun ht hxtime hx hB
  obtain ⟨-, hFj, hjh, -, hF0, -⟩ := FG.chain_invariants sp.toParams.fg _ _ h₁
  have hXh := hge X hX
  have hsuby : (tr.state y m).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩
  have hsubx : (tr.state x i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩
  suffices hmem : (tr.state y m).fg.F.root ∈ sp.toParams.fg.roots (c₂.map Block.fgView) by
    obtain ⟨Y, hY, hYr, hYB⟩ := hr₂ _ hmem
    rw [hU.1 (hsubx hY) (hsuby hF) hYr] at hYB
    exact honest_anc_of_store_anc_at ht hxtime hx hYB
  rw [← hXF]
  rcases Nat.eq_zero_or_pos ((tr.state y m).fg.σ X.root).hF with h0 | h0
  · rw [hF0 h0]
    exact List.mem_cons_self
  by_contra hnot
  obtain ⟨S, hS, hSv⟩ := sp.toParams.fg.finalization_meets_crossing h₁ h₂ h0 (by omega) hnot
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

end Consensus.Goldilocks.Healing.Growing

end
