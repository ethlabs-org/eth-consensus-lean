module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Crossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety

public section

/-! # Goldilocks Healing: finalized ancestry and viable frame heads

G1.2 at strict height (for a low finalized height `d ≤ H`): the cut
step's conclusion for `Σ.F` when `Σ.J` is low. The finalized pair of a state names the entry of
its height (`fin_pair_entry`: a pending pair is a past justification, whose block is the entry of
the justified height), so `Σ.F ⪯ Σ.J` is finalized at a height `≤ Σ.h_j`.
By `finalized_anc_of_height_lt_of_run`, it is below every honest block of greater state height. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Along one block, the finalized pair and the pending pairs of the new state are old ones
(pending, or the old finalized pair) or the old height's entry pair. -/
private theorem step_pairs {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (Q : Nat × Nat → Prop)
    (hp : ∀ p ∈ σ.pending, Q p) (hF : Q (σ.hF, σ.F)) (hE : Q (σ.h, σ.Th)) :
    (∀ p ∈ σ'.pending, Q p) ∧ Q (σ'.hF, σ'.F) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF', σ₁, rfl, hFc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hpend : ∀ r ∈ σ.pending.filter (fun p => hF' < p.1), Q r :=
    fun r hr => hp r (List.mem_of_mem_filter hr)
  have hF₁ : Q (hF', F) := by
    rcases hFc with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact hF
    · exact hp _ hm
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · refine ⟨fun r hr => ?_, hF₁⟩
    simp only [FG.ChainState.advance] at hr
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · exact hpend r hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hE
  · exact ⟨hpend, hF₁⟩
  · exact ⟨hpend, hF₁⟩

/-- **The finalized pair of a held block's state names the entry of its height** (or genesis):
the finalized pair is the old one or a pending pair, and every pending pair was appended at a
justification of the entry of the parent's height (G0.2 (d), (g) at the store). -/
theorem fin_pair_entry (hr : st.Reachable acp₀) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    (st.σ X.root).F = P.genesisRoot ∨
      ∃ W ∈ st.tree, W.root = (st.σ X.root).F ∧ (st.σ W.root).h = (st.σ X.root).hF := by
  let Q : Nat × Nat → Prop := fun p =>
    p.2 = P.genesisRoot ∨ ∃ W ∈ st.tree, W.root = p.2 ∧ (st.σ W.root).h = p.1
  suffices key : (∀ p ∈ (st.σ X.root).pending, Q p) ∧ Q ((st.σ X.root).hF, (st.σ X.root).F) from
    key.2
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 X hX
  clear hX
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact ⟨fun p hp => by simp [FG.ChainState.init] at hp, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, -, hEh, -⟩, -⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
    exact step_pairs ht Q ih.1 ih.2 (Or.inr ⟨E, hE, hEr, hEh⟩)

/-- A non-genesis finalized target retains its self-entry witness, not only its height. -/
theorem fin_pair_self_entry (hr : st.Reachable acp₀) {X : NodeBlock P ACP}
    (hX : X ∈ st.tree) :
    (st.σ X.root).F = P.genesisRoot ∨ ∃ W ∈ st.tree,
      W.root = (st.σ X.root).F ∧ (st.σ W.root).h = (st.σ X.root).hF ∧
      (st.σ W.root).Th = W.root := by
  let Q : Nat × Nat → Prop := fun p =>
    p.2 = P.genesisRoot ∨ ∃ W ∈ st.tree,
      W.root = p.2 ∧ (st.σ W.root).h = p.1 ∧ (st.σ W.root).Th = W.root
  suffices key : (∀ p ∈ (st.σ X.root).pending, Q p) ∧ Q ((st.σ X.root).hF, (st.σ X.root).F) from
    key.2
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 X hX
  clear hX
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact ⟨fun p hp => by simp [FG.ChainState.init] at hp, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨_, _, _, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, _, hEh, hET⟩, _⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
    exact step_pairs ht Q ih.1 ih.2 (Or.inr ⟨E, hE, hEr, hEh, hET.trans hEr.symm⟩)

end Store

/-- A retained justification at least as high as a replay-finalized target covers that
target. At equal height the retained carrier supplies the common descendant and self-entries. -/
theorem replay_finalized_below_justification {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {x y : Fin P.n} (hx : x ∈ H) (hy : y ∈ H) {i j : Nat} {B X Y J : NodeBlock P ACP}
    (hB : B ∈ (tr.store x i).tree) (hX : X ∈ (tr.store x i).tree)
    (hXr : X.root = ((tr.store x i).σ B.root).F)
    (hY : Y ∈ (tr.store y j).tree) (hJ : J ∈ (tr.store y j).tree)
    (hJr : J.root = ((tr.store y j).σ Y.root).J)
    (hh : ((tr.store x i).σ B.root).hF ≤ ((tr.store y j).σ Y.root).hj) :
    Anc U X J := by
  have hrx := Goldilocks.Store.store_reachable hr hx i
  have hry := Goldilocks.Store.store_reachable hr hy j
  have subx := hr.tree_subset x hx i
  have suby := hr.tree_subset y hy j
  rcases Store.fin_pair_self_entry hrx hB with hg | ⟨X', hX', hX'r, hXh, hXT⟩
  · have he : X = P.genesisBlock acp₀ := hr.coherent.1 (subx hX)
      (subx (Store.genesis_mem hrx)) (hXr.trans hg)
    rw [he]
    exact ((Goldilocks.Store.accepted_tree P ACP acp₀ _ hry).2.2.2 J hJ).mono suby
  have he : X' = X := hr.coherent.1 (subx hX') (subx hX) (hX'r.trans hXr.symm)
  subst X'
  obtain ⟨J', hJ', hJ'r, hJY, hcase⟩ := Store.J_entry_of_reachable hry hY
  have he : J' = J := hr.coherent.1 (suby hJ') (suby hJ) (hJ'r.trans hJr.symm)
  subst J'
  have hYh := Store.hj_lt_h hry hY
  have hXY := finalized_anc_of_lt_fg hr hH hx hy hB hX hXr hY (hh.trans_lt hYh)
  have hXY' := Goldilocks.Store.anc_of_U hr hy hXY hY
  have hXt : X ∈ (tr.store y j).tree := by
    by_cases he : X = Y
    · exact he ▸ hY
    · exact (Anc.mem hXY' he).1
  have hσ := Goldilocks.Store.σ_eq_of_held hr hx hy hX hXt
  have hJh := Store.J_height_le hry hY hJ hJr
  have hJT : ((tr.store y j).σ J.root).Th = J.root := by
    rcases hcase with rfl | hcase
    · rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hry]
      rfl
    · exact hcase.2
  by_cases hlt : ((tr.store x i).σ B.root).hF < ((tr.store y j).σ J.root).h
  · exact finalized_anc_of_lt_fg hr hH hx hy hB hX hXr hJ hlt
  · have he : X = J := self_entries_eq hry hXt hJ hXY' hJY
      (by rw [← hσ, hXh]; (clear * - hh hJh hlt; omega)) (by rw [← hσ]; exact hXT) hJT
    rw [he]
    exact .refl

/-- Successful acceptance transfers replay finality into the actual cache when the old
cache is below the target. The inserted store is used only through its actual post-state. -/
theorem accepted_replay_finalized_cached {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {B X : NodeBlock P ACP}
    (ha : tr.AcceptAt y k B) (hX : X ∈ (tr.store y (k + 1)).tree)
    (hXr : X.root = ((tr.store y (k + 1)).σ B.root).F)
    (hFX : Anc U (tr.store y k).F X) : Anc U X (tr.store y (k + 1)).F := by
  classical
  let pre := tr.store y k
  let post := tr.store y (k + 1)
  have hpre := Goldilocks.Store.store_reachable hr hy k
  have hpost := Goldilocks.Store.store_reachable hr hy (k + 1)
  have hab := Goldilocks.Store.accept_onBlock hr hy ha
  obtain ⟨pr, σ, _, _, _, _, _, hp⟩ := Goldilocks.Store.onBlock_eq_some hab
  let ins : Goldilocks.Store P ACP :=
    { pre with blocks := Function.update pre.blocks B.root (some B),
               σ := Function.update pre.σ B.root σ }
  have hp' : post = (ins.updateFinality σ).addAtts B.fgPayload := hp
  obtain ⟨atts, hatts⟩ := Goldilocks.Store.addAtts_eq (ins.updateFinality σ) B.fgPayload
  have heq : post = { ins.updateFinality σ with atts := atts } := hp'.trans hatts
  have hb : post.blocks = ins.blocks := by
    rw [heq]; exact (Goldilocks.Store.updateFinality_spec ins σ).1
  have hs : post.σ = ins.σ := by
    rw [heq]; exact (Goldilocks.Store.updateFinality_spec ins σ).2.1
  have ht : post.tree = ins.tree := by unfold Goldilocks.Store.tree; rw [hb]
  have hB : B ∈ post.tree := by
    change post.blocks B.root = some B
    rw [hb]; simp [ins]
  have hσ : post.σ B.root = σ := by rw [hs]; simp [ins]
  have sub := hr.tree_subset y hy (k + 1)
  have hFX' : post.Anc pre.F X := Goldilocks.Store.anc_of_U hr hy hFX hX
  by_cases he : pre.F = X
  · rw [← he]
    exact ((Goldilocks.Store.finalized_monotone P ACP _).1 B _ hab).mono sub
  have hXF : ins.blocks (ins.σ B.root).F = some X := by
    rw [← hs, ← hb, ← hXr]
    exact hX
  have hXB : post.Anc X B := by
    obtain ⟨_, ⟨X', hX', hX'r, hX'B⟩, _⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hpost B hB
    have h := hr.coherent.1 (sub hX') (sub hX) (hX'r.trans hXr.symm)
    exact h ▸ hX'B
  have hlimits := Goldilocks.Store.entry_input hpost B.root
  have hfin : (post.σ B.root).hF ≤ (post.σ B.root).hj := by
    obtain ⟨c, _, _, _, hc⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hpost B hB
    exact (FG.chain_invariants P.fg _ _ hc).2.1
  obtain ⟨J, hJ, hJr, _⟩ :=
    (Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hpost B hB).2.2
  have hXJ : post.Anc X J := Goldilocks.Store.anc_of_U hr hy
    (replay_finalized_below_justification hr hH hy hy hB hX hXr hB hJ hJr hfin) hJ
  have hafter : (Goldilocks.Store.afterJustification P ACP ins (ins.σ B.root)).Anc X
      (Goldilocks.Store.afterJustification P ACP ins (ins.σ B.root)).J := by
    have hlookup : ins.blocks (ins.σ B.root).J = some J := by
      rw [← hs, ← hb, ← hJr]; exact hJ
    have hFJ : ins.Anc ins.F J := by
      change Anc ins.tree pre.F J
      rw [← ht]; exact hFX'.trans hXJ
    unfold Goldilocks.Store.afterJustification
    simp only [hlookup]
    split_ifs with htake
    · change Anc ins.tree X J
      rw [← ht]; exact hXJ
    · have hn : ¬ Goldilocks.Store.LexLt (pre.hj, pre.J.root) ((post.σ B.root).hj,
          (post.σ B.root).J) := by
        intro hn
        apply htake
        exact ⟨hFJ, by simpa only [hs] using hn⟩
      have hh : (post.σ B.root).hj ≤ pre.hj := by
        by_contra h
        exact hn (Or.inl (by clear * - h; omega))
      obtain ⟨_, hJpre, _, ⟨Y, hY, hYJ, hYh⟩, _⟩ :=
        Goldilocks.Store.cache_invariants P ACP acp₀ _ hpre
      have hxj := replay_finalized_below_justification hr hH hy hy hB hX hXr
        hY hJpre hYJ.symm (hfin.trans (hh.trans hYh.symm.le))
      have hJpost := (Goldilocks.Store.held_mono hr hy (Nat.le_succ k) hJpre).1
      change Anc ins.tree X pre.J
      rw [← ht]
      exact Goldilocks.Store.anc_of_U hr hy hxj hJpost
  have hv : ({ ins with hmax := max ins.hmax (ins.σ B.root).h } :
      Goldilocks.Store P ACP).HasViableDescendant X := by
    obtain ⟨_, _, _, _, _, ⟨M, hM, hMh⟩, _⟩ :=
      Goldilocks.Store.cache_invariants P ACP acp₀ _ hpre
    have hMpost := (Goldilocks.Store.held_mono hr hy (Nat.le_succ k) hM).1
    have hMs := Goldilocks.Store.σ_eq_of_held hr hy hy hM hMpost
    have hmax : ∃ W ∈ post.tree, (post.σ W.root).h = max pre.hmax (post.σ B.root).h := by
      by_cases h : pre.hmax ≤ (post.σ B.root).h
      · exact ⟨B, hB, (max_eq_right h).symm⟩
      · exact ⟨M, hMpost, by rw [← hMs, hMh, max_eq_left (le_of_not_ge h)]⟩
    obtain ⟨W, hW, hWh⟩ := hmax
    have hXW := finalized_anc_of_lt_fg hr hH hy hy hB hX hXr hW
      ((hfin.trans_lt hlimits.2.1).trans_le (hWh ▸ le_max_right _ _))
    refine ⟨W, ?_, ?_, ?_⟩
    · change W ∈ ins.tree; rw [← ht]; exact hW
    · change Anc ins.tree X W; rw [← ht]
      exact Goldilocks.Store.anc_of_U hr hy hXW hW
    · refine Or.inl ?_
      change max ins.hmax (ins.σ B.root).h ≤ (ins.σ W.root).h
      rw [← hs]
      have hm : ins.hmax = pre.hmax := rfl
      rw [hm]
      exact hWh.ge
  have hc := Goldilocks.Store.cache_acceptance P ACP ins B X
    (ht ▸ hB) (by rw [← hs]; exact hlimits.2.1) hXF
    (by change Anc ins.tree X B; rw [← ht]; exact hXB)
    (by change Anc ins.tree pre.F X; rw [← ht]; exact hFX') he hafter hv
  rw [show ins.σ B.root = σ by simp [ins]] at hc
  have hF : post.F = (ins.updateFinality σ).F := by rw [heq]
  have htree : (ins.updateFinality σ).tree = post.tree := by
    unfold Goldilocks.Store.tree
    rw [(Goldilocks.Store.updateFinality_spec ins σ).1, ← hb]
  change Anc (ins.updateFinality σ).tree X (ins.updateFinality σ).F at hc
  rw [htree, ← hF] at hc
  exact hc.mono sub

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n} {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **G1.2 over the run** (claims G1.2, G1.3, G0.5). A block `F` finalized by
the state of a held `X` in an honest store is an ancestor of every honest block `W` whose state
height exceeds the finalized height: otherwise the finality quorum of `(h_F, F)` on `X`'s chain and
the crossing quorum of `h_F` on `W`'s chain (whose roots do not contain `F`) share `2q − n > f`
validators with an E1 pair (`FG.finalization_meets_crossing`), an honest one of which signed both
attestations (unforgeability) in one client run (`Store.signed_run`), against client safety (G0.5).
-/
theorem finalized_anc_of_height_lt_of_run (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hF : F ∈ (tr.state y k).fg.tree)
    (hFr : F.root = ((tr.state y k).fg.σ X.root).F) (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) F W := by
  have hfg := Compose.fg_projection_from
    (fun y _ => Compose.requirements_from sp (hrun.vstart y))
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hst : ∀ {w : Fin sp.n}, w ∈ H → ∀ i, tr.projFG.store w i = (tr.state w i).fg :=
    fun hw i => by simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hw i]
  have hH : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have h3 := hf
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at h3
    have hn := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    clear * - h3 hn; omega
  have h := finalized_anc_of_lt_fg hfg hH hy hz (k := k) (m := m) (X := X) (F := F) (W := W)
  rw [hst hy, hst hz] at h
  exact h hX hF hFr hW hlt

/-- A held block at or above `hmax - 1` is a viable frame head if it extends `J` when its
height is not above `hj`. In that case `F ⪯ J ⪯ X`; otherwise strict height gives `F ⪯ X`. -/
theorem viable_head_of_height (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    (hh : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ X.root).h)
    (hJ : ((tr.state y i).fg.σ X.root).h ≤ (tr.state y i).fg.hj →
      (tr.state y i).fg.Anc (tr.state y i).fg.J X) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F X ∧
      X ∈ (tr.state y i).fg.toFrame.tree ∧ X ∈ (tr.state y i).fg.toFrame.viableHeads := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  have hj := hBjhj ▸ (Store.hj_lt_h hr hBj).trans_le (hge Bj hBj)
  have hFX : (tr.state y i).fg.Anc (tr.state y i).fg.F X := by
    by_cases h : ((tr.state y i).fg.σ X.root).h ≤ (tr.state y i).fg.hj
    · exact (Goldilocks.Store.cache_invariants _ _ _ _ hr).2.2.1.trans (hJ h)
    have hfg := Compose.fg_projection_from
      (fun y _ => Compose.requirements_from sp (hrun.vstart y))
      hrun.genesis_root_ok hrun.toLocalRun hnc
    have hs : tr.projFG.store y i = (tr.state y i).fg := by
      simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]
    have hsafe := held_atts_safe hfg hy hy i i
    rw [hs] at hsafe
    have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun B hB => ⟨y, hy, i, hB⟩
    have hcoh := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).mono hsub
    have hg := Store.genesis_mem hr
    obtain ⟨hFm, -, hFJ, ⟨B, hB, hBJ, hBhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
      Goldilocks.Store.cache_invariants _ _ _ _ hr
    have hgF := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
        (tr.state y i).fg.Anc (tr.state y i).fg.F X := fun he => by
      rw [hcoh.1 hFm hg he]
      exact (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 X hX
    rcases Store.fin_pair_entry hr hBf with he | ⟨W, hW, hWr, hWh⟩
    · exact hgen (hBfF.symm.trans he)
    obtain rfl : W = (tr.state y i).fg.F := hcoh.1 hW hFm (hWr.trans hBfF)
    obtain ⟨E, hE, hEr, -, hcase⟩ := Store.J_entry_of_reachable hr hB
    obtain rfl : E = (tr.state y i).fg.J :=
      hcoh.1 hE (Goldilocks.Store.cache_invariants _ _ _ _ hr).2.1 (hEr.trans hBJ)
    rcases hcase with hEg | ⟨hEh, -⟩
    · rw [hEg] at hFJ
      exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
    have h₁ := Healing.h_le_of_store_anc hr hFJ
    exact Goldilocks.Store.finalized_anc_of_safe hr hr
      (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hsub hsub hf hsafe
      hBf hFm hBfF.symm hX (by omega)
  have hv : (tr.state y i).fg.IsViable X := by
    change _ ∨ (_ ∧ _)
    by_cases hm : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ X.root).h
    · exact Or.inl hm
    refine Or.inr ⟨by omega, ?_⟩
    by_cases hg : (tr.state y i).fg.hj + 1 < (tr.state y i).fg.hmax
    · exact Or.inl hg
    exact Or.inr (hJ (by omega))
  exact ⟨hFX, ⟨hX, hFX⟩, ⟨hX, hFX, hv⟩⟩

end Consensus.Goldilocks.Healing

end
