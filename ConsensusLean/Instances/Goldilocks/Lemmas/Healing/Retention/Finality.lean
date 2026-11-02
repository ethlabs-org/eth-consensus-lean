module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Crossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks Healing, HR.4: a low `Σ.F` is below every high origin

G1.2 at strict height (`hr4-cut-scope.md` §3, "For low finalized height `d ≤ H`"): the cut
step's conclusion for `Σ.F` when `Σ.J` is low. The finalized pair of a state names the entry of
its height (`fin_pair_entry`: a pending pair is a past justification, whose block is the entry of
the justified height), so a store's `Σ.F ⪯ Σ.J` is finalized at a height `≤ Σ.h_j`
(`low_finalized_below_origin`); G1.2 over the run (`finalized_anc_of_height_lt`) puts it below
every honest block of greater state height. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

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
      (by rw [← hσ, hXh]; omega) (by rw [← hσ]; exact hXT) hJT
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
    exact ((Goldilocks.Store.finalized_monotone P ACP acp₀ _ hpre).1 B _ hab).mono sub
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
        exact hn (Or.inl (by omega))
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
    · change _ ≤ (ins.σ W.root).h
      rw [← hs]
      have hm : ins.hmax = pre.hmax := rfl
      unfold Goldilocks.Store.headHeightFloor
      split_ifs <;> change _ ≤ (post.σ W.root).h <;> simp only [hm] <;> omega
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

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

/-- **G1.2 over the run** (claims G1.2, G1.3, G0.5; `hr4-cut-scope.md` §3; the same statement as
Boot's `finalized_anc_of_lt`). A block `F` finalized by the state of a held `X` in an honest
store is an ancestor of every honest block `W` whose state height exceeds the finalized height:
otherwise the finality quorum of `(h_F, F)` on `X`'s chain and the crossing quorum of `h_F` on
`W`'s chain (whose roots do not contain `F`) share `2q − n > f` validators with an E1 pair
(`FG.finalization_meets_crossing`), an honest one of which signed both attestations
(unforgeability) in one client run (`Store.signed_run`), against client safety (G0.5). -/
theorem finalized_anc_of_height_lt_of_run (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hF : F ∈ (tr.state y k).fg.tree)
    (hFr : F.root = ((tr.state y k).fg.σ X.root).F) (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) F W := by
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hst : ∀ {w : Fin sp.n}, w ∈ H → ∀ i, tr.projFG.store w i = (tr.state w i).fg :=
    fun hw i => by simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hw i]
  have hH : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have h3 := hf
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at h3
    have hn := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have h := finalized_anc_of_lt_fg hfg hH hy hz (k := k) (m := m) (X := X) (F := F) (W := W)
  rw [hst hy, hst hz] at h
  exact h hX hF hFr hW hlt

/-- Before any honest height advance, every held state's non-genesis finalized height
is strictly below the frontier. The no-advance premise concerns actual signatures. -/
theorem run_hF_le_of_noAdvance (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hq : Hᶜ.ncard < sp.toParams.fg.q) {T : Time}
    (hna : ∀ v ∈ H, ∀ j att, tr.SignAt v j att → tr.time j ≤ T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hi : tr.time i ≤ T)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree) :
    ((tr.state y i).fg.σ X.root).hF + 1 ≤ HZ tr H g ∨
      ((tr.state y i).fg.σ X.root).hF = 0 := by
  by_cases hzero : ((tr.state y i).fg.σ X.root).hF = 0
  · exact Or.inr hzero
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨c, hc, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr X hX
  obtain ⟨Q, hQ, hrows⟩ := FG.FGParams.finalized_quorum _ hcs (by omega)
  change Finset (Fin sp.n) at Q
  have hex : ∃ v ∈ Q, v ∈ H := by
    by_contra hn
    have hsub : (↑Q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => hn ⟨v, hv, hvH⟩
    have hf := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hf
    exact (not_lt_of_ge (hQ.trans hf)) hq
  obtain ⟨v, hvQ, hv⟩ := hex
  obtain ⟨att, hatt, hav, hfin⟩ := hrows v hvQ
  simp only [FG.FGParams.chainAtts, List.mem_flatMap] at hatt
  obtain ⟨Z', hZ', hatt⟩ := hatt
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
  have haH : att.val ∈ H := hav ▸ hv
  obtain ⟨m, hmi, _, j, hjm, hs⟩ :=
    Compose.honest_row_signed_before hrun hnc hy (hc Z hZ) hatt haH
  have hw := (signAt_wellFormed hrun haH hs).2
    (((tr.state y i).fg.σ X.root).hF, ((tr.state y i).fg.σ X.root).F) (by simp [hfin])
  have hh := hna att.val haH j att hs ((hrun.time_mono (by omega)).trans hi)
  exact Or.inl (by omega)

/-- Before height advance, an honest node's finalized block is below every honest-held
block of frontier height or greater. Only the finalized node's cut is bounded by T. -/
theorem finalized_below_high_held (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {T : Time}
    (hna : ∀ v ∈ H, ∀ j att, tr.SignAt v j att → tr.time j ≤ T → att.h ≤ HZ tr H g)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i m : Nat} (hi : tr.time i ≤ T)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z m).fg.tree)
    (hWh : HZ tr H g ≤ ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F W := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  obtain ⟨hF, -, -, -, -, -, X, hX, hXF⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hr
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change Hᶜ.ncard < (2 * sp.n + 2) / 3
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n at hf
    change 0 < sp.n at hn
    omega
  rcases run_hF_le_of_noAdvance hrun hnc hq hna hy hi hX with hlt | hzero
  · have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
    have hfg := Compose.fg_projection _ _ dg H _ tr proposer
      ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
      hrun.genesis_root_ok hrun.toLocalRun hnc
    have hst : ∀ {v : Fin sp.n}, v ∈ H → ∀ j, tr.projFG.store v j = (tr.state v j).fg :=
      fun hv j => by simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hv j]
    have h := finalized_anc_of_lt_fg hfg hf hy hz (k := i) (m := m)
      (X := X) (F := (tr.state y i).fg.F) (W := W)
    rw [hst hy, hst hz] at h
    exact h hX hF hXF.symm hW (by omega)
  · obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr X hX
    have hg := (FG.chain_invariants _ _ _ hcs).2.2.2.2.1 hzero
    have he := Compose.honest_eq_genesis hrun hU (hsub hF) (hXF.symm.trans hg)
    rw [he]
    exact ((Goldilocks.Store.accepted_tree _ _ _ _
      (Compose.fg_reachable hrun.toLocalRun hz m)).2.2.2 W hW).mono
      (fun B hB => ⟨z, hz, m, hB⟩)

/-- Whole-run specialization; strict-height ancestry needs no future health. -/
theorem finalized_anc_of_height_lt (hp : ResetPremises tr H proposer dg g ΔF a) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hF : F ∈ (tr.state y k).fg.tree)
    (hFr : F.root = ((tr.state y k).fg.σ X.root).F) (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) F W :=
  finalized_anc_of_height_lt_of_run hp.run hp.noColl hp.healthy.2.2 hy hz hX hF hFr hW hlt

/-- **G1.2 at strict height: a low `Σ.F` is below an honest-held high block**
(`hr4-cut-scope.md` §3, "For low finalized height `d ≤ H`, `B`'s accepted chain has height `> d`";
claims G1.2;
`producer-reset-continuation.md` §11 "Historical finality and acceptance"). When an honest
node's `Σ.h_j ≤ H_z`, its `Σ.F ⪯ Σ.J` is genesis or finalized at a height
`d = σ[Σ.F].h ≤ σ[Σ.J].h = Σ.h_j ≤ H_z < σ[B].h` (`fin_pair_entry`; a genesis `Σ.J` makes `Σ.F`
genesis), so `Σ.F ⪯ B` by G1.2 (`finalized_anc_of_height_lt`). -/
theorem low_finalized_below_high_block_of_run (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {m i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBt : B ∈ (tr.state x i).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := by
  have hreach := Compose.fg_reachable hrun.toLocalRun hy m
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have hcoh : Coherent (tr.state y m).fg.tree := hU.mono hsub
  have hg := Store.genesis_mem hreach
  have hgB : Anc (tr.HonestBlocks H)
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B :=
    ((Goldilocks.Store.accepted_tree _ _ _ _
      (Compose.fg_reachable hrun.toLocalRun hx i)).2.2.2 B hBt).mono
        (fun X hX => (⟨x, hx, i, hX⟩ : X ∈ tr.HonestBlocks H))
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hgF : (tr.state y m).fg.Anc (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      (tr.state y m).fg.F := (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 _ hFm
  -- a genesis `Σ.F` is below `B`
  have hgen : (tr.state y m).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := fun he => by
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
  refine finalized_anc_of_height_lt_of_run hrun hnc hf hy hx hBf hFm hBfF.symm hBt ?_
  omega

/-- A block held anywhere honestly extends the target's finalized block if it meets the
target's floor and, in the J-root case, extends the target's J. No target acceptance is needed. -/
theorem finalized_below_floor_held (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i m : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state z m).fg.tree)
    (hheight : (tr.state y i).fg.headHeightFloor ≤ ((tr.state z m).fg.σ W.root).h)
    (hJ : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬(tr.state y i).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y i).fg.J W) :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F W := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  have hcoh := hU.mono hsub
  obtain ⟨hF, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, hmax, -, X, hX, hXF⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · exact (hFJ.mono hsub).trans (hJ hk.1 hk.2)
  have hg := Store.genesis_mem hr
  have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocks H) (tr.state y i).fg.F W := fun he => by
    rw [hcoh.1 hF hg he]
    exact ((Goldilocks.Store.accepted_tree _ _ _ _
      (Compose.fg_reachable hrun.toLocalRun hz m)).2.2.2 W hW).mono
      (fun B hB => ⟨z, hz, m, hB⟩)
  rcases Store.fin_pair_entry hr hX with he | ⟨E, hE, hEr, hEh⟩
  · exact hgen (hXF.symm.trans he)
  obtain rfl : E = (tr.state y i).fg.F := hcoh.1 hE hF (hEr.trans hXF)
  obtain ⟨J, hJt, hJr, -, hcase⟩ := Store.J_entry_of_reachable hr hBj
  obtain rfl : J = (tr.state y i).fg.J := hcoh.1 hJt hJm (hJr.trans hBjJ)
  rcases hcase with he | ⟨hJh, -⟩
  · have hgF := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 _ hF
    rw [he] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have hFh := h_le_of_store_anc hr hFJ
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr Bj hBj
  have hjlt := (FG.chain_invariants _ _ _ hc).2.2.1
  have hmaxBj := hmax Bj hBj
  have hstrict : ((tr.state y i).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h := by
    by_cases hcon : (tr.state y i).fg.Contest
    · simp only [Goldilocks.Store.headHeightFloor, ite_eq_left hcon] at hheight
      omega
    · have hne : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 :=
        fun he => hk ⟨he, hcon⟩
      simp only [Goldilocks.Store.headHeightFloor, ite_eq_right hcon] at hheight
      omega
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hst : ∀ {v : Fin sp.n}, v ∈ H → ∀ j, tr.projFG.store v j = (tr.state v j).fg :=
    fun hv j => by simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hv j]
  have h := finalized_anc_of_lt_fg hfg hf hy hz (k := i) (m := m)
    (X := X) (F := (tr.state y i).fg.F) (W := W)
  rw [hst hy, hst hz] at h
  exact h hX hF hXF.symm hW hstrict

/-- Equal frame floors, contest status and root kind suffice for cross-node finality
ancestry of an actual viable head. J roots agree only in the J-root case. -/
theorem finalized_below_viable_head (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i m : Nat}
    (hfloor : (tr.state y i).fg.headHeightFloor = (tr.state z m).fg.headHeightFloor)
    (_hcontest : (tr.state y i).fg.Contest ↔ (tr.state z m).fg.Contest)
    (hkind : ((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
        ¬(tr.state y i).fg.Contest) ↔
      ((tr.state z m).fg.hmax = (tr.state z m).fg.hj + 1 ∧ ¬(tr.state z m).fg.Contest))
    (hJ : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬(tr.state y i).fg.Contest → (tr.state y i).fg.J = (tr.state z m).fg.J)
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hv : W ∈ (tr.state z m).fg.toFrame.viableHeads) :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F W := by
  rcases hv with ⟨hW, -, hroot, hheight⟩
  refine finalized_below_floor_held hrun hnc hf hy hz hW (hfloor ▸ hheight) ?_
  intro hm hc
  have hkz := hkind.mp ⟨hm, hc⟩
  have he : (tr.state z m).fg.fcRoot = (tr.state z m).fg.J := by
    simp [Goldilocks.Store.fcRoot, hkz.1, hkz.2]
  rw [he, ← hJ hm hc] at hroot
  exact hroot.mono (fun B hB => ⟨z, hz, m, hB⟩)

/-- A locally held floor-viable block satisfying the J-root condition is a viable frame head.
This is local: no agreement between different frames is assumed. -/
theorem viable_head_of_floor (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    (hh : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ X.root).h)
    (hJ : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬(tr.state y i).fg.Contest → (tr.state y i).fg.Anc (tr.state y i).fg.J X) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F X ∧
      X ∈ (tr.state y i).fg.toFrame.tree ∧
      (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot X ∧
      (tr.state y i).fg.IsViable X ∧ X ∈ (tr.state y i).fg.toFrame.viableHeads := by
  have hFX := Compose.honest_held_anc hrun hnc hy
    (finalized_below_floor_held hrun hnc hf hy hy hX hh
      (fun hm hc => (hJ hm hc).mono (fun B hB => ⟨y, hy, i, hB⟩))) hX
  have hroot : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot X := by
    by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
        ¬(tr.state y i).fg.Contest
    · simpa [Goldilocks.Store.fcRoot, hk] using hJ hk.1 hk.2
    · simpa [Goldilocks.Store.fcRoot, hk] using hFX
  exact ⟨hFX, ⟨hX, hFX⟩, hroot, hh, ⟨hX, hFX, hroot, hh⟩⟩

/-- Whole-run specialization of the actual held-block finality comparison. -/
theorem low_finalized_below_high_block (hp : ResetPremises tr H proposer dg g ΔF a)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {m i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBt : B ∈ (tr.state x i).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B :=
  low_finalized_below_high_block_of_run hp.run hp.noColl hp.healthy.2.2 hy hx hBt hhigh hlow

/-- The origin-specialized form of strict-height finalized ancestry. -/
theorem ResetPremisesUpTo.low_finalized_below_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n}
    (hy : y ∈ H) (m : Nat) (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := by
  obtain ⟨CV, hst⟩ := ho.2.2.1
  exact low_finalized_below_high_block_of_run hp.run hp.noColl hp.faults hy ho.1
    (storedFastLock_mem hp.run hp.noColl ho.1 hst).1 ho.2.2.2 hlow

/-- Whole-run specialization of low finalization below a high origin. -/
theorem low_finalized_below_origin (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n}
    (hy : y ∈ H) (m : Nat) (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B :=
  (hp.toUpTo tr H (le_refl a)).low_finalized_below_origin hy m hlow ho

end Consensus.Goldilocks.Healing

end
