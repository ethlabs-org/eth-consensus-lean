module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow P-U windows

The maximum height and top status are fixed at every honest cut. Justification is fixed
only in top windows. The sequential pigeonhole is the existing frame-independent theorem;
the key-to-frame-data step uses the shadow key instead of the merged stock key.
-/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {A : NodeAC P}

/-- Transitional alias of the milestone `Generic.FrameWindow`, which now carries the P-U frame
data (`h_max`, top status, and `J` when top). Removed by the final rename sweep. -/
abbrev FrameWindow' (tr : RunTrace A) (H : Time → Set (Fin P.n)) (lo hi : Time) (M : Nat)
    (isTop : Prop) (J : A.Blk) : Prop :=
  Generic.FrameWindow tr H lo hi M isTop J

/-- The P-U floor, unlike the stock contest floor, is always `hmax - 1`. -/
theorem le_pred_add_riseRounds (st : Store P A.Payload) {hz : Nat}
    (hpos : 1 ≤ st.hmax) (hv : 2 * hz ≤ Generic.frameKey'' A st) :
    hz + 1 ≤ st.hmax - 1 + riseRounds hz (Generic.frameKey'' A st) := by
  classical
  rw [riseRounds_eq, Generic.frameKey''_eq] at *
  split_ifs at * <;> omega

/-- A P-U viable held block is above finality. In the predecessor-height top case use
`F ⪯ J ⪯ Q`; all other cases are strictly above `hj` and use the existing G1.2 proof. -/
theorem finalized_below_viable {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hR : st.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub : st.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ st.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ st.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    {Q : NodeBlock P ACP} (hQ : Q ∈ st.tree) (hv : st.IsViable Q) : st.Anc st.F Q := by
  have hj := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
    hR.reachableWith
  rcases (Store.isViable_iff st Q).mp hv with hh | ⟨hh, hgap | hJ⟩
  · exact Store.F_anc_of_hj_lt_of_safe_with Store.finalitySpec_updateFinality
      hR.reachableWith hR.reachableWith hU hsub hsub hV hsafe hQ (by omega)
  · exact Store.F_anc_of_hj_lt_of_safe_with Store.finalitySpec_updateFinality
      hR.reachableWith hR.reachableWith hU hsub hsub hV hsafe hQ (by omega)
  · exact (Store.cache_invariants _ _ _ _ hR).2.2.1.trans hJ

/-- Viability transport within fixed numerical frame data. The caller separately supplies
finalized ancestry at the receiving cut, using `finalized_below_viable'`. -/
theorem isViable_of_window_data {ACP : Type} {a b : Store P ACP} {Q : NodeBlock P ACP}
    (hm : a.hmax = b.hmax) (ht : (a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1))
    (hJ : a.hmax = a.hj + 1 → a.J = b.J) (hb : b.hj < b.hmax)
    (hσ : a.σ Q.root = b.σ Q.root)
    (hanc : a.Anc a.J Q → b.Anc a.J Q) (hv : a.IsViable Q) : b.IsViable Q := by
  rw [Store.isViable_iff] at hv ⊢
  rcases hv with hh | ⟨hh, hgap | hAQ⟩
  · exact Or.inl (by rw [← hm, ← hσ]; exact hh)
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, Or.inl ?_⟩
    have hnot : ¬ b.hmax = b.hj + 1 := fun h => by
      have := ht.mpr h
      omega
    omega
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, ?_⟩
    by_cases htop : a.hmax = a.hj + 1
    · exact Or.inr (hJ htop ▸ hanc hAQ)
    · exact Or.inl (by have := ht.not.mp htop; omega)

/-- The shadow key lag needs only the maximum-height and J carriers. The stock contest
witness is unnecessary: contest and clean top frames have the same shadow key. -/
theorem frameKey''_le_of_relay {acp₀ : A.Payload} {stx stz : Store P A.Payload}
    (hRx : stx.Reachable acp₀) (hRz : stz.Reachable acp₀)
    {U : Set (NodeBlock P A.Payload)} (hU : Coherent U)
    (hsubx : stx.tree ⊆ U) (hsubz : stz.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ stz.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ stx.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    (hancz : ∀ A C, Anc U A C → C ∈ stz.tree → stz.Anc A C)
    (hheld : ∀ B ∈ stx.tree, stz.hmax ≤ (stx.σ B.root).h → B ∈ stz.tree) :
    Generic.frameKey'' A stx ≤ Generic.frameKey'' A stz := by
  classical
  have hu := Store.finalitySpec_updateFinality (P := P) (ACP := A.Payload)
  have hrx := hRx.reachableWith
  have hrz := hRz.reachableWith
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Store.cache_invariants _ _ _ _ hRz
  by_cases hlt : stx.hmax < stz.hmax
  · rw [Generic.frameKey''_eq, Generic.frameKey''_eq]
    split_ifs <;> omega
  have hle : stz.hmax ≤ stx.hmax := not_lt.mp hlt
  have hheld' : ∀ {B : NodeBlock P A.Payload}, B ∈ stx.tree → stx.hmax ≤ (stx.σ B.root).h →
      B ∈ stz.tree := fun hB hh => hheld _ hB (hle.trans hh)
  have hσ : ∀ {B : NodeBlock P A.Payload}, B ∈ stz.tree → B ∈ stx.tree →
      stz.σ B.root = stx.σ B.root :=
    fun hBz hBx => Store.σ_eq_of_mem_with hrz hu hrx hU.1 hsubz hsubx hBz hBx
  have hBhz := hheld' hBh hBhh.ge
  have heq : stz.hmax = stx.hmax := by
    have := hgez Bh hBhz
    rw [hσ hBhz hBh] at this
    omega
  have hjz := Store.hj_lt_hmax_of_reachable_with hu hrz
  have htop : stx.hmax = stx.hj + 1 → stz.hmax = stz.hj + 1 := by
    intro htx
    have hBjh := Store.hj_lt_h_with hu hrx hBj
    have hBjz := hheld' hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_with hu hrx hBj
    obtain rfl : E = stx.J := hU.1 (hsubx hE) (hsubx hJx) (hEr.trans hBjJ)
    have hJz : stx.J ∈ stz.tree := mem_of_anc (hancz _ _ (hEB.mono hsubx) hBjz) hBjz
    have hJh := Store.J_height_le_with hu hrx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : stz.hj < stx.hj := by omega
    have hFJ := hancz _ _ ((Store.F_anc_of_hj_lt_of_safe_with hu hrz hrx hU hsubz hsubx
      hV hsafe hJx (by rw [hBjhj] at hJh; omega)).mono hsubx) hJz
    have hσj := hσ hBjz hBj
    have := (jMax_iff _).mp hRz.jMax Bj hBjz _ hJz (by rw [hσj, hBjJ]) hFJ
    rw [hσj] at this
    omega
  rw [Generic.frameKey''_eq, Generic.frameKey''_eq]
  split_ifs <;> omega

open AC (ACParams ReplayOrder Payload)

section Persistence

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The shadow fork-choice root is F at every cut, so its monotonicity needs no window
or top-status case split. -/
theorem fcRoot_mono (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i) :
    Anc (tr.HonestBlocks H) (Node.frame (tr.state y a)).fcRoot
      (Node.frame (tr.state y i)).fcRoot := by
  rw [Node.frame_eq, Node.frame_eq, Store.toFrame_fcRoot, Store.toFrame_fcRoot]
  exact run_F_mono hrun.toLocalRun hy hai

/-- V-B4: a write-frame viable head remains a viable head at later cuts in the P-U window.
The only new geometric step is `finalized_below_viable'`; the rest is the stock persistence
argument, with fixed maximum height and top status in place of the old merged floor. -/
theorem _root_.Consensus.Goldilocks.Generic.FrameWindow.viableHead_persists'
    {lo hi : Time} {M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) lo hi M isTop J)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y a ell)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    Q ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  have htime := hrun.time_mono hai
  rw [Node.frame_of_projAC_at hrun.toLocalRun hy hc, Node.frame_eq,
    Store.toFrame_viableHeads] at hv
  have hQa : Q ∈ (tr.state y a).fg.tree := hv.1
  have hQi := Compose.tree_mono hrun.toLocalRun hy hai hQa
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun B hB => ⟨y, hy, i, hB⟩
  have hvi : (tr.state y i).fg.IsViable Q := by
    apply isViable_of_window_data
      ((hframe.M_eq y a hy halo (htime.trans hihi)).trans
        (hframe.M_eq y i hy (halo.trans htime) hihi).symm)
      ((hframe.top_iff y a hy halo (htime.trans hihi)).trans
        (hframe.top_iff y i hy (halo.trans htime) hihi).symm)
      (fun ht => (hframe.root_eq y a hy halo (htime.trans hihi)
        ((hframe.top_iff y a hy halo (htime.trans hihi)).mp ht)).trans
        (hframe.root_eq y i hy (halo.trans htime) hihi
          ((hframe.top_iff y a hy halo (htime.trans hihi)).mp ht)).symm)
      (hj_lt_hmax' hrun hy i)
      (Store.σ_eq_of_mem_with
        (Node.fg_reachable_at hrun.toLocalRun hy a).reachableWith
        Store.finalitySpec_updateFinality
        (Node.fg_reachable_at hrun.toLocalRun hy i).reachableWith
        (Coherence.honest_blocks_coherent hrun.toLocalRun hnc).1
        (fun _ hB => ⟨y, hy, a, hB⟩) hsub hQa hQi)
      (fun h => h.mono (Compose.tree_mono hrun.toLocalRun hy hai)) hv.2.2
  have hFQ := finalized_below_viable (Node.fg_reachable_at hrun.toLocalRun hy i)
    (Coherence.honest_blocks_coherent hrun.toLocalRun hnc) hsub hf
    (fun a b ha hb hv => held_atts_safe (Compose.projFG_localRun hrun hnc) hy hy i i a b
      (by simpa only [Compose.store_eq hrun hy] using ha)
      (by simpa only [Compose.store_eq hrun hy] using hb) hv) hQi hvi
  have hQt : Q ∈ (tr.state y i).fg.toFrame.tree := by
    rw [Store.toFrame_tree]
    exact ⟨hQi, hFQ⟩
  refine ⟨?_, ?_, ?_⟩
  · rwa [Node.frame_eq]
  · rw [Node.frame_eq, Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict .refl hFQ
  · rw [Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hQi, hFQ, hvi⟩

/-- An earlier action supplies a frozen viable descendant of the current F-root, in both
top and gap windows. No non-top premise or common-J fallback is needed. -/
theorem _root_.Consensus.Goldilocks.Generic.FrameWindow.root_witness_of_earlier_call'
    {lo hi g : Time} {M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) lo hi M isTop J)
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode sp ro)}
    (ha : tr.projAC.CallAt y a ell₀) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < AC.freeze sp e.msg.slot)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot) :
    ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hR := Node.fg_reachable_at hrun.toLocalRun hy a
  obtain ⟨-, -, -, -, -, ⟨Q, hQ, hQh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hv : (tr.state y a).fg.IsViable Q :=
    (Store.isViable_iff _ _).mpr (Or.inl hQh.ge)
  have hFQ := finalized_below_viable hR
    (Coherence.honest_blocks_coherent hrun.toLocalRun hnc)
    (fun B hB => ⟨y, hy, a, hB⟩) hf
    (fun b c h₁ h₂ hv => held_atts_safe (Compose.projFG_localRun hrun hnc) hy hy a a b c
      (by simpa only [Compose.store_eq hrun hy] using h₁)
      (by simpa only [Compose.store_eq hrun hy] using h₂) hv) hQ hv
  have hQt : Q ∈ ell₀.frame.tree := by
    rw [Node.frame_of_projAC_at hrun.toLocalRun hy ha, Node.frame_eq,
      Store.toFrame_tree]
    exact ⟨hQ, hFQ⟩
  have hv₀ : Q ∈ ell₀.frame.viableHeads := by
    rw [Node.frame_of_projAC_at hrun.toLocalRun hy ha, Node.frame_eq,
      Store.toFrame_viableHeads]
    exact ⟨hQ, hFQ, hv⟩
  obtain ⟨hQi, hrooti, hvi⟩ :=
    hframe.viableHead_persists' hrun hnc hf hy hai halo hihi ha hv₀
  rw [← Node.frame_of_projAC_at hrun.toLocalRun hy hc.1] at hQi hrooti hvi
  refine ⟨Q, ⟨hQi, Or.inl ?_⟩, hvi, hrooti⟩
  apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQt hQi hat
  intro r _ hrs
  exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf

end Persistence

namespace Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {hold : Time}

/-- Relay and catch-up transport a held block whose height is not below the receiver's
maximum. This is the observation-level service obligation for the shadow lag core. -/
theorem held_of_relay_le_at_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) sp.Δ ≤ tr.time j)
    (hcm : AC.gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree := by
  have hm0 := hrun.time_nonneg m
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hs : ∀ j ≤ m, (tr.upTo (tr.time m)).state z j = tr.state z j :=
    fun j hj => Trace.upTo_state tr z (fun k hk => hrun.time_mono (by omega))
  have hr := (hrun.upTo hm0).toLocalRun
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocksAt H) (tr.state z j).fg.F B := by
    intro j hj
    have hheight := Coherence.hmax_mono hr hz hj
    dsimp only at hheight
    rw [hs j hj, hs m le_rfl] at hheight
    have hjtime : ∀ k < j, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono (by omega)
    exact (Store.F_anc_of_hmax_le_of_safe_with Store.finalitySpec_updateFinality
      (Compose.Growing.reachable_at hrun hm0 hz hjtime).reachableWith
      (Compose.Growing.reachable_at hrun hτ0 hx hτ).reachableWith
      (Coherence.honestBlocksAt_coherent hrun hnc)
      (Compose.Growing.tree_held_at hm0 hz hjtime)
      (Compose.Growing.tree_held_at hτ0 hx hτ) hf
      (fun a b ha hb hav => Shadow.held_atts_safe_at hrun hnc hm0 hjtime hz hτ0 hτ hx
        (le_max_right _ _) (le_max_left _ _) a b ha hb hav)
      hB (hheight.trans hh)).mono (Compose.Growing.tree_held_at hτ0 hx hτ)
  have hlift : ∀ k, k + 1 ≤ m → tr.AcceptAt z k B → B ∈ (tr.state z m).fg.tree := by
    intro k hkm ha
    have ha' : (tr.upTo (tr.time m)).AcceptAt z k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨hrun.time_mono (by omega), ha⟩
    have hmem := Coherence.accept_mem_from hr hz ha'
    have := Coherence.tree_mono hr hz hkm hmem
    rwa [hs m le_rfl] at this
  have hB' : B ∈ ((tr.upTo τ).state x i).fg.tree := by
    rwa [Trace.upTo_state tr x hτ]
  rcases Coherence.tree_accepted (hrun.upTo hτ0).toLocalRun hx hB' with he | ⟨k, hk, ha⟩
  · rw [he]
    exact Store.genesis_mem_with Store.finalitySpec_updateFinality
      (Compose.Growing.reachable_at hrun hm0 hz hm).reachableWith
  have ha := ((RunTrace.upTo_acceptAt tr).mp ha).2
  have hxk := hrun.antitone (hτ k hk) hx
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' := (tr.deadline_mono z j (max_le_max (hτ k hk) le_rfl) sp.Δ).trans hdl
    obtain ⟨k', hk'j, ha', -⟩ := hsvc.relay x k B hxk ha hg z j
      (hrun.antitone (hrun.time_mono hjm.le) hz) hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha'
  · obtain ⟨k', hk', ha', _⟩ := Healing.accept_before_snapshot hcm fun q hq hfirst =>
      hcatch x k B hxk ha (lt_of_lt_of_le (not_le.mp hg) (le_max_left _ _)) z q
        (hrun.antitone hcm hz) hfirst (hF q hq)
    exact hlift k' hk' ha'

/-- Shadow key lag between independently honest observations, from relay and catch-up. -/
theorem frameKey''_lag_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : AC.gbar g + κ ≤ tr.time m) :
    Generic.frameKey'' (goldilocksNode sp ro) (tr.state x i).fg ≤
      Generic.frameKey'' (goldilocksNode sp ro) (tr.state z m).fg := by
  have hi := hrun.time_nonneg i
  have hm := hrun.time_nonneg m
  have hbi : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hbm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hfm := hf _ hm hmb
  apply frameKey''_le_of_relay
    (Compose.Growing.reachable_at hrun hi hx hbi)
    (Compose.Growing.reachable_at hrun hm hz hbm)
    (Coherence.honestBlocksAt_coherent hrun hnc)
    (Compose.Growing.tree_held_at hi hx hbi) (Compose.Growing.tree_held_at hm hz hbm) hfm
  · exact fun a b ha hb hav => Shadow.held_atts_safe_at hrun hnc hm hbm hz hi hbi hx
      le_rfl him a b ha hb hav
  · exact fun _ _ h hC => store_anc_of_honest_anc_at hrun hnc hm hbm hz h hC
  · intro B hB hh
    exact held_of_relay_le_at_from hrun hnc hsvc hcatch hi hx hz
      (by simpa only [max_eq_right him] using hfm) hB hh hbi hcall hcm

/-- Equal cached justification heights agree at independently honest observations. -/
theorem J_eq_of_hj_eq_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i m : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (hf : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (he : (tr.state y i).fg.hj = (tr.state z m).fg.hj) :
    (tr.state y i).fg.J = (tr.state z m).fg.J := by
  have hi := hrun.time_nonneg i
  have hm := hrun.time_nonneg m
  have hbi : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hbm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  exact Store.J_eq_of_cache_hj_eq_of_safe_with Store.finalitySpec_updateFinality
    (Compose.Growing.reachable_at hrun hi hy hbi).reachableWith
    (Compose.Growing.reachable_at hrun hm hz hbm).reachableWith
    (Coherence.honestBlocksAt_coherent hrun hnc)
    (Compose.Growing.tree_held_at hi hy hbi) (Compose.Growing.tree_held_at hm hz hbm) hf
    (fun a b ha hb hav => Shadow.held_atts_safe_at hrun hnc hi hbi hy hm hbm hz
      (le_max_left _ _) (le_max_right _ _) a b ha hb hav) he

/-- V-B2: the four-attempt window supplier, using service relay and J agreement at two
independently honest shadow observations. -/
theorem exists_frameWindow'_seq_of_service_proof_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : AC.gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 4, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 3 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        Generic.frameKey'' (goldilocksNode sp ro) (tr.state y i).fg = v) ∧
      ∃ M isTop J, Generic.FrameWindow tr H a (a + len v) M isTop J := by
  apply Generic.exists_frameWindow_seq_of_mem len hlen hlam hrange
  · intro x z i k hx hz hi _ hik hk
    exact frameKey''_lag_obs hrun hnc hf hsvc hcatch hx hz (by linarith)
      (hk.le.trans hTb) (hcall z i k hz hi hik hk) (hlo.trans (by linarith))
  · intro y z i m hy hz _ hi _ hm he
    apply J_eq_of_hj_eq_obs hrun hnc hy hz _ he
    exact hf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
      (max_le (hi.le.trans hTb) (hm.le.trans hTb))
  · exact hT

/-- Finite shadow service projects to the unchanged AC synchrony contract. -/
theorem _root_.Consensus.Goldilocks.Healing.PU.service_syncACAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b lo hi : Time} (hsvc : ResetService tr H g ΔF b hold) (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp ro) H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  refine ⟨?_, ?_⟩
  · intro x i m hx hsa hai _ y j ell hy hcj hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ell₀, hc₀, hm⟩ := hsa
      refine ⟨ell₀, Compose.projAC_callAt.1 hc₀, ?_⟩
      have hs := Compose.projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hx i
      rw [RunTrace.upTo_projAC,
        Trace.upTo_state tr.projAC x (fun k hk => hrun.time_mono hk.le),
        RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at hs
      rwa [hs] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hsvc.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ell', hc', hm'⟩ | ⟨ell', hc', e, he', hem⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x i B hx hacc hai _ y j ell hy hcj hdl hanc
    apply Consensus.Goldilocks.Growing.LocalRun.acRelayAt hrun.toLocalRun
      (σ := tr.time i) hx hacc hy hcj hanc
    intro k hki hx' hk hj hF
    have hgi : g ≤ tr.time k := hki ▸ hg.trans hai
    have he : max (tr.time k) g = tr.time i := (max_eq_left hgi).trans hki
    simpa only [he] using hsvc.relay x k B hx' hk hgi y j hy hj
      (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- Pool membership and declared backing give committee membership for every counted vote
on the shadow AC projection. -/
theorem _root_.Consensus.Goldilocks.Compose.Growing.CommitteeFacts.committeeTAt'
    {K : AC.CommitteeDict sp.n} (hK : Compose.Growing.CommitteeFacts tr H K)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) : AC.CommitteeTAt K tr.projAC H := by
  intro y i ℓ e hy hcast m v hv
  have hri := Compose.goldilocks_ac_projection_from
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo (tr.time i))
  rw [RunTrace.upTo_projAC] at hri
  have hb : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hcastU := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hpool : ∀ k, ∀ w ∈ e.readPoint.pool k, w.slot = k := fun k w hw =>
    AC.state_pool_slotU _ hri.localRun.toU hri.vstart hy (i + 1) k w
      (AC.readPoint_poolU hri.localRun.toU hy hcastU hw).1
  have hmem : ∀ w ∈ e.readPoint.pool v.slot, w.val = v.val →
      v.val ∈ K.committee v.slot := by
    intro w hw hwv
    have hp := (AC.readPoint_poolU hri.localRun.toU hy hcastU hw).1
    rw [Trace.upTo_state tr.projAC y hb] at hp
    exact hwv ▸ hK.hP.1 (tr.time i) y hy (i + 1) hb _ w hp
  rcases AC.merged_declared_backing_at_vote_slot hpool hv with h | ⟨w, hw, -, -, -, hwv, -⟩
  · exact hmem v h rfl
  · exact hmem w hw hwv

/-- The stock-shaped healthy AC base supplier on shadow executions. The committee and
prefix bookkeeping is unchanged. Service synchrony and catch-up restrict to the prefix;
driven execution follows from the static shadow run on that prefix. -/
theorem CommitteeHalfUpTo.healthy_base_before_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b hold : Time} (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → AC.gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  have hpre := hrun.upTo hd0
  have hr := Compose.goldilocks_ac_projection_from hpre (hnc.upTo d)
  rw [RunTrace.upTo_projAC] at hr
  refine ⟨hr, ?_, ?_, ?_, ?_, hfaults d hd0 hdb, hK.facts.hsize,
    AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP d,
    AC.CommitteeTAt.upTo hrun.antitone (hK.facts.committeeTAt' hrun hnc) d,
    fun s hgs hsd => hK.cs2 s hgs (hsd.trans hdb) d hd0 hdb⟩
  · -- Shadow driven execution (proposal and acceptance run laws).
    have hdr := projection_driven_of_run hpre (hnc.upTo d) hpre.genesis_root_ok
    rwa [RunTrace.upTo_projAC] at hdr
  · -- Restrict actual service witnesses to the read prefix.
    have hm := hrun.time_mono
    have hsync := Healing.PU.service_syncACAt hrun hs (lo := g) (hi := d) le_rfl
    constructor
    · intro x hx i m hsend hi y hy j ell hj ht hd
      obtain ⟨hid, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
      obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
      rw [ACTrace.upTo_deadline hm hjd] at ht hd
      obtain ⟨k, hkj, hik, hproc, hkt⟩ := hsync.1 x i m (hrun.antitone hid hx) hsend
        ((AC.le_gbar g).trans hi) hid y j ell (hrun.antitone hjd hy) hj hd
      have hkd : tr.time k ≤ d := (hm hkj).trans hjd
      exact ⟨k, hkj, hik, ACTrace.upTo_processAt.mpr ⟨hkd, hproc⟩,
        by rwa [ACTrace.upTo_deadline hm hkd]⟩
    · intro x hx i B hacc hi y hy j ell hj ht hd hF
      obtain ⟨hid, hacc⟩ := ACTrace.upTo_acceptAt.mp hacc
      obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
      rw [ACTrace.upTo_deadline hm hjd] at ht hd
      obtain ⟨k, hkj, hak, hkt⟩ := hsync.2 x i B (hrun.antitone hid hx) hacc
        ((AC.le_gbar g).trans hi) hid y j ell (hrun.antitone hjd hy) hj hd
        (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
      have hkd : tr.time k ≤ d := (hm hkj).trans hjd
      exact ⟨k, hkj, ACTrace.upTo_acceptAt.mpr ⟨hkd, hak⟩,
        by rwa [ACTrace.upTo_deadline hm hkd]⟩
  · -- Shadow AC catch-up on the prefix.
    rw [← RunTrace.upTo_projAC]
    constructor
    intro x hx i B ha hi y hy j ell hj ht hjd hF
    change AC.gbar g + 2 * sp.Δ ≤ tr.time j at ht
    change tr.time j ≤ d at hjd
    rw [RunTrace.upTo_projAC] at ha hj ⊢
    obtain ⟨hid, ha'⟩ := ACTrace.upTo_acceptAt.mp ha
    obtain ⟨_, hj'⟩ := (Trace.upTo_callAt _).mp hj
    obtain ⟨k, hkj, hak, hkt⟩ := hrun.toLocalRun.acCatchAt hc
      (hrun.antitone hid hx) ha' hi (hrun.antitone hjd hy) hj' ht
      (hF.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd0))
    exact ⟨k, hkj,
      ACTrace.upTo_acceptAt.mpr ⟨(hrun.time_mono hkj).trans hjd, hak⟩, hkt⟩
  · intro y hy t hgt htd
    exact (Trace.upTo_awake _ y t).mpr
      ⟨hawake y t (hrun.antitone htd hy) hgt (htd.trans hdb), htd⟩

end Growing

end Consensus.Goldilocks.Healing

end
