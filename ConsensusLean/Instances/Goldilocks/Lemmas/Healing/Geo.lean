module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: settled-phase geometry (H.3 (c3))

`geo_of_settled` proves `Geo(P)` for an honest proposal whose proposal and slot-`p` votes lie in one
settled effective phase `(m, c)`, from HS.1 (`viable_witness_retention_of`, `Retain`). Its pieces:

* **Aligned readers** (service readers are aligned after settling;
  `viableHeads_iff`): at a cut of the phase, an honest node's head height floor is the phase floor
  and its `fc_root` is `Σ.F` (gap, contest) or the phase's `J` (top `J`), so a block it holds is
  a viable head of its frame exactly when it extends its `Σ.F` and is allowed in the effective
  geometry. The cache side needs `JMax` (`Σ.h_j` is at least the justified height of every held
  state whose `J` is a held block extending `Σ.F`, an FG store invariant), HR.2 (a) for `Σ.J`,
  and HS.1 for `Σ.F ⪯ J` and for the contest witness.
* **The voter block tree**: a block stamped before the freeze was held
  by the voter at an earlier call (`stamp_origin`, `readPoint_blockStamp_eq`), so accepted before
  `t_p − Δ` and relayed to the proposer by `t_p` (`relay_held`); the other blocks are ancestors
  of the slot's block, which is `P` (one block per honest proposer and slot).
* **The proposal**: its parent is a viable head (requirement 1; the walk starts at an anchor in
  the viable tree, `getAnchor_viable`, `proposal_head_viable`), so `P` is allowed wherever it is
  held; a voter holds it (ready at an early vote, `cast_ready`; relayed by `t_p + Δ` otherwise).
  `Geo` quantifies over every proposal call at `t_p`; there is one (`proposal_call_unique`).
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## Stores -/

section Stores

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- The justification of a held block's state names a held block whose state height is at least
the justified height. -/
theorem J_entry_h {st : Store P ACP} (hr : st.Reachable acp₀) {W : NodeBlock P ACP}
    (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).J ∧ (st.σ W.root).hj ≤ (st.σ E.root).h := by
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    exact ⟨_, Store.genesis_mem hr, rfl, by simp [FG.ChainState.init]⟩
  | tail _ hYW ih =>
    obtain ⟨X, -, hXr, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    rcases Compose.step_J ht with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, h2⟩ := ih
      exact ⟨E, hE, h1.trans hJ.symm, hj ▸ h2⟩
    · obtain ⟨⟨E, hE, h1, -, h2, -⟩, -⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      exact ⟨E, hE, h1.trans hJ.symm, by rw [hj, h2]⟩

/-- **The justification cache is maximal**: `Σ.h_j` is at least the justified height of every
held state whose justification is a held block extending `Σ.F` (`update_finality` takes the
lex-greatest such justification, and `Σ.F` only moves up). -/
def JMax (st : Store P ACP) : Prop :=
  ∀ B ∈ st.tree, ∀ X ∈ st.tree, X.root = (st.σ B.root).J → st.Anc st.F X →
    (st.σ B.root).hj ≤ st.hj

theorem jMax_iff (st : Store P ACP) : JMax st ↔ ∀ B ∈ st.tree, ∀ X ∈ st.tree,
    X.root = (st.σ B.root).J → st.Anc st.F X → (st.σ B.root).hj ≤ st.hj := Iff.rfl

open Classical in
/-- `update_finality` does not lower `Σ.h_j`, and raises it to the justified height of a state
whose justification is a held block extending `Σ.F`. -/
private theorem hj_updateFinality (st : Store P ACP) (σ : FG.ChainState P.n) :
    st.hj ≤ (st.updateFinality σ).hj ∧ ∀ X ∈ st.tree, X.root = σ.J → st.Anc st.F X →
      σ.hj ≤ (st.updateFinality σ).hj := by
  have key : ∀ hj' : Nat, st.hj ≤ hj' → (∀ X ∈ st.tree, X.root = σ.J → st.Anc st.F X →
      σ.hj ≤ hj') → st.hj ≤ hj' ∧ ∀ X ∈ st.tree, X.root = σ.J → st.Anc st.F X →
        σ.hj ≤ hj' := fun _ h1 h2 => ⟨h1, h2⟩
  unfold Store.updateFinality
  dsimp only
  rcases hJ : st.blocks σ.J with _ | X
  · have hno : ∀ X ∈ st.tree, X.root = σ.J → False := fun X hX hXr => by
      change st.blocks X.root = some X at hX
      rw [hXr, hJ] at hX
      cases hX
    dsimp only
    rcases st.blocks σ.F with _ | Y
    · exact key _ le_rfl fun X hX hXr _ => (hno X hX hXr).elim
    · dsimp only
      split_ifs
      · exact key _ le_rfl fun X hX hXr _ => (hno X hX hXr).elim
      · exact key _ le_rfl fun X hX hXr _ => (hno X hX hXr).elim
  · have hXe : ∀ X' ∈ st.tree, X'.root = σ.J → X' = X := fun X' hX' hXr => by
      change st.blocks X'.root = some X' at hX'
      rw [hXr, hJ] at hX'
      exact (Option.some.inj hX').symm
    dsimp only
    by_cases hJc : ({ st with hmax := max st.hmax σ.h } : Store P ACP).Anc st.F X ∧
        Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)
    · have hle : st.hj ≤ σ.hj := by
        rcases hJc.2 with h | h
        · exact h.le
        · exact h.1.le
      simp only [eq_true hJc, ite_true]
      rcases st.blocks σ.F with _ | Y
      · exact key _ hle fun _ _ _ _ => le_rfl
      · dsimp only
        split_ifs
        · exact key _ hle fun _ _ _ _ => le_rfl
        · exact key _ hle fun _ _ _ _ => le_rfl
    · have hle : ∀ X' ∈ st.tree, X'.root = σ.J → st.Anc st.F X' → σ.hj ≤ st.hj := by
        intro X' hX' hXr ha
        obtain rfl := hXe X' hX' hXr
        by_contra hlt
        exact hJc ⟨ha, Or.inl (not_le.1 hlt)⟩
      simp only [eq_false hJc, ite_false]
      rcases st.blocks σ.F with _ | Y
      · exact key _ le_rfl hle
      · dsimp only
        split_ifs
        · exact key _ le_rfl hle
        · exact key _ le_rfl hle

/-- Ancestry in a tree with a new block, ending in an old block, is ancestry in the old tree
(the old tree is closed under parents). -/
private theorem anc_of_anc_insert {st : Store P ACP} (hr : st.Reachable acp₀)
    {B : NodeBlock P ACP} (hn : st.blocks B.root = none) {A X : NodeBlock P ACP}
    (h : Goldilocks.Anc (insert B st.tree) A X) (hX : X ∈ st.tree) : st.Anc A X := by
  induction h with
  | refl => exact .refl
  | tail _ hYX ih =>
    obtain ⟨Z, hZ, hZr, -⟩ := Store.step_σ hr hX hYX.2.2
    rcases hYX.1 with rfl | hY
    · change st.blocks Z.root = some Z at hZ
      rw [hZr, hn] at hZ
      cases hZ
    · exact (ih hY).tail ⟨hY, hX, hYX.2.2⟩

private theorem jMax_init : JMax (Store.init (P := P) acp₀) := by
  intro B _ _ _ _ _
  change (FG.ChainState.init P.fg).hj ≤ 0
  rfl

private theorem jMax_congr {st st' : Store P ACP} (hb : st'.blocks = st.blocks)
    (hσ : st'.σ = st.σ) (hF : st'.F = st.F) (hj : st'.hj = st.hj) (h : JMax st) : JMax st' := by
  have ht : st'.tree = st.tree := by
    ext Y
    change st'.blocks Y.root = some Y ↔ st.blocks Y.root = some Y
    rw [hb]
  intro B hB X hX hXr hFX
  simp only [Store.Anc, ht] at hB hX hFX
  rw [hσ] at hXr ⊢
  rw [hj]
  exact h B hB X hX hXr (hF ▸ hFX)

private theorem jMax_updateFinality {st : Store P ACP} (hr : st.Reachable acp₀) (hJ : JMax st)
    {B : NodeBlock P ACP} {σ' : FG.ChainState P.n} (hn : st.blocks B.root = none)
    (st₁ : Store P ACP) (hb₁ : st₁.blocks = Function.update st.blocks B.root (some B))
    (hσ₁ : st₁.σ = Function.update st.σ B.root σ') (hFe : st₁.F = st.F) (hj₁ : st₁.hj = st.hj) :
    JMax (st₁.updateFinality σ') := by
  obtain ⟨hb, hσ, -, -, -, hF⟩ := Store.updateFinality_spec st₁ σ'
  obtain ⟨hhj, hhjσ⟩ := hj_updateFinality st₁ σ'
  have hmem : ∀ Y, Y ∈ st₁.tree ↔ Y = B ∨ Y ∈ st.tree := by
    intro Y
    change st₁.blocks Y.root = some Y ↔ Y = B ∨ st.blocks Y.root = some Y
    rw [hb₁, Function.update_apply]
    split_ifs with hY
    · refine ⟨fun e => Or.inl (Option.some.inj e).symm, ?_⟩
      rintro (rfl | e)
      · rfl
      · rw [hY, hn] at e
        cases e
    · refine ⟨Or.inr, ?_⟩
      rintro (rfl | e)
      · exact absurd rfl hY
      · exact e
  have htree : st₁.tree = insert B st.tree := Set.ext fun Y => hmem Y
  have ht : (st₁.updateFinality σ').tree = st₁.tree := by
    ext Y
    change (st₁.updateFinality σ').blocks Y.root = some Y ↔ st₁.blocks Y.root = some Y
    rw [hb]
  intro B₀ hB₀ X hX hXr hFX
  simp only [Store.Anc, ht] at hB₀ hX hFX
  rw [hσ] at hXr ⊢
  have hF₁ : st₁.Anc st.F X := by
    rcases hF with h | ⟨-, h, -, -⟩
    · rwa [h, hFe] at hFX
    · exact (hFe ▸ h).trans hFX
  rcases (hmem B₀).1 hB₀ with rfl | hB₀s
  · have : st₁.σ B₀.root = σ' := by rw [hσ₁]; exact Function.update_self _ _ _
    rw [this] at hXr ⊢
    exact hhjσ X hX hXr (hFe ▸ hF₁)
  · have hne : B₀.root ≠ B.root := fun e => by
      change st.blocks B₀.root = some B₀ at hB₀s
      rw [e, hn] at hB₀s
      cases hB₀s
    have hσ₀ : st₁.σ B₀.root = st.σ B₀.root := by rw [hσ₁]; exact Function.update_of_ne hne _ _
    rw [hσ₀] at hXr ⊢
    obtain ⟨-, -, ⟨X', hX', hX'r, -⟩⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr B₀ hB₀s
    have hXs : X ∈ st.tree := by
      rcases (hmem X).1 hX with rfl | h
      · change st.blocks X'.root = some X' at hX'
        rw [hX'r, ← hXr, hn] at hX'
        cases hX'
      · exact h
    have hF₀ : st.Anc st.F X := anc_of_anc_insert hr hn (htree ▸ hF₁) hXs
    exact (hJ B₀ hB₀s X hXs hXr hF₀).trans (hj₁ ▸ hhj)

private theorem jMax_step {st st' : Store P ACP} (hr : st.Reachable acp₀) (hJ : JMax st)
    (hs : Store.Step st st') : JMax st' := by
  rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
  · obtain ⟨pr, σ', -, hn, -, -, -, rfl⟩ := Store.onBlock_eq_some hB
    obtain ⟨atts, he⟩ := Store.addAtts_eq (Store.updateFinality
      { st with blocks := Function.update st.blocks B.root (some B),
                σ := Function.update st.σ B.root σ' } σ') B.fgPayload
    rw [he]
    exact jMax_congr rfl rfl rfl rfl (jMax_updateFinality hr hJ hn _ rfl rfl rfl rfl)
  · obtain ⟨atts, he⟩ := Store.onAttestation_eq st a
    rw [he]
    exact jMax_congr rfl rfl rfl rfl hJ

/-- **`JMax` holds at every reachable FG state.** -/
theorem jMax_of_reachable {st : Store P ACP} (hr : st.Reachable acp₀) : JMax st := by
  induction hr with
  | refl => exact jMax_init
  | tail hr hs ih => exact jMax_step hr ih hs

/-- A frame's viable heads read with the effective geometry: when the head height floor is the
phase floor and the fork-choice root is `Σ.F`, or `J` in the top-`J` case, a held block is a viable
head exactly when it extends `Σ.F` and is allowed in the effective geometry. -/
private theorem viableHeads_iff_of {st : Store P ACP} {m : Nat} {c : PhaseCase (NodeBlock P ACP)}
    (hfl : st.headHeightFloor = phaseFloor m c)
    (hfc : ∀ J, c = .top J → st.fcRoot = J) (hfF : (∀ J, c ≠ .top J) → st.fcRoot = st.F)
    {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    X ∈ st.toFrame.viableHeads ↔ st.Anc st.F X ∧ EffAllowed st m c X := by
  change (X ∈ st.tree ∧ st.Anc st.F X ∧ st.Anc st.fcRoot X ∧ st.headHeightFloor ≤
    (st.σ X.root).h) ↔ st.Anc st.F X ∧ X ∈ st.tree ∧ phaseFloor m c ≤ (st.σ X.root).h ∧
      ∀ J, c = .top J → st.Anc J X
  rw [hfl]
  by_cases htop : ∃ J, c = .top J
  · obtain ⟨J, rfl⟩ := htop
    rw [hfc J rfl]
    exact ⟨fun ⟨_, hF, hJ, hh⟩ => ⟨hF, hX, hh, fun J' e => by cases e; exact hJ⟩,
      fun ⟨hF, _, hh, hJ⟩ => ⟨hX, hF, hJ J rfl, hh⟩⟩
  · push Not at htop
    rw [hfF htop]
    exact ⟨fun ⟨_, hF, _, hh⟩ => ⟨hF, hX, hh, fun J e => absurd e (htop J)⟩,
      fun ⟨hF, _, hh, _⟩ => ⟨hX, hF, hF, hh⟩⟩

end Stores

/-! ## Runs: aligned readers in a settled phase -/

section Runs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time} {proposer : Nat → Fin sp.n}

theorem projFG_store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- The FG projection of a run under the HS shared premises is an FG trace, with `f < 2q − n`. -/
theorem fg_run_of_hs (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF) :
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

/-- The evidence of a phase, once held, stays held (stores keep their blocks and states, and
ancestry of a held block does not change). -/
theorem holdsEvidence_mono (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {z : Fin sp.n} (hz : z ∈ H) {a b m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hab : a ≤ b) (h : HoldsEvidence (tr.state z a).fg m c) :
    HoldsEvidence (tr.state z b).fg m c := by
  have hsub := Compose.tree_mono hrun.toLocalRun hz hab
  have hσ : ∀ B ∈ (tr.state z a).fg.tree,
      (tr.state z b).fg.σ B.root = (tr.state z a).fg.σ B.root :=
    fun B hB => σ_eq_honest hrun hnc hz hz (hsub hB) hB
  have hh : ∀ k, (∃ B ∈ (tr.state z a).fg.tree, ((tr.state z a).fg.σ B.root).h = k) →
      ∃ B ∈ (tr.state z b).fg.tree, ((tr.state z b).fg.σ B.root).h = k :=
    fun k ⟨B, hB, e⟩ => ⟨B, hsub hB, by rw [hσ B hB, e]⟩
  have hj : ∀ J : SA.Blk sp.n (List (FG.Att sp.n)), (∃ B ∈ (tr.state z a).fg.tree,
      ((tr.state z a).fg.σ B.root).hj = m - 1 ∧ ((tr.state z a).fg.σ B.root).J = J.root) →
      ∃ B ∈ (tr.state z b).fg.tree,
        ((tr.state z b).fg.σ B.root).hj = m - 1 ∧ ((tr.state z b).fg.σ B.root).J = J.root :=
    fun J ⟨B, hB, e1, e2⟩ => ⟨B, hsub hB, by rw [hσ B hB, e1], by rw [hσ B hB, e2]⟩
  have hc : ∀ J : SA.Blk sp.n (List (FG.Att sp.n)), (∃ B ∈ (tr.state z a).fg.tree,
      ((tr.state z a).fg.σ B.root).h = m ∧ ¬ (tr.state z a).fg.Anc J B) →
      ∃ B ∈ (tr.state z b).fg.tree,
        ((tr.state z b).fg.σ B.root).h = m ∧ ¬ (tr.state z b).fg.Anc J B :=
    fun J ⟨B, hB, e, hn⟩ => ⟨B, hsub hB, by rw [hσ B hB, e], fun ha => hn
      (store_anc_of_honest_anc hrun hnc hz (ha.mono fun X hX => ⟨z, hz, b, hX⟩) hB)⟩
  cases c with
  | gap => exact hh m h
  | top J => exact ⟨hh m h.1, hsub h.2.1, hj J h.2.2⟩
  | contest J => exact ⟨hh m h.1, hsub h.2.1, hj J h.2.2.1, hc J h.2.2.2⟩

/-- **Aligned readers**: at a cut where the effective phase is `(m, c)`
and an honest node holds the phase's evidence, a block it holds is a viable head of its frame
exactly when it extends its `Σ.F` and is allowed in the effective phase geometry. The head height
floor is the phase floor and `fc_root` is `Σ.F`, or the phase's `J` in the top-`J` case: the
node's `Σ.h_max` is `m`; its `Σ.h_j` is `m − 1` exactly when the phase has a justification there
(`JMax`, with `Σ.F ⪯ J` from HS.1), its `Σ.J` is then the phase's `J` (HR.2 (a)), and its local
contest test agrees with the phase case (the contest witness extends `Σ.F` by HS.1). -/
theorem viableHeads_iff (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (_hc : CatchRun tr H g (2 * sp.Δ)) {z : Fin sp.n} (hz : z ∈ H) {k m : Nat}
    {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} (hph : PhaseAt tr.projFG H k m c)
    (hev : HoldsEvidence (tr.state z k).fg m c) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state z k).fg.tree) :
    X ∈ (Node.frame (tr.state z k)).viableHeads ↔
      (tr.state z k).fg.Anc (tr.state z k).fg.F X ∧ EffAllowed (tr.state z k).fg m c X := by
  obtain ⟨hfg, hq⟩ := fg_run_of_hs hrun hs
  have hR := Compose.fg_reachable hrun.toLocalRun hz k
  have hcoh : Coherent (tr.state z k).fg.tree :=
    (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1
  have hF : ∀ W, EffAllowed (tr.state z k).fg m c W →
      (tr.state z k).fg.Anc (tr.state z k).fg.F W := fun W hW =>
    store_anc_of_honest_anc hrun hs.noColl hz
      ((viable_witness_retention_of hrun hs
        (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hph) hz hW hz le_rfl le_rfl).1) hW.1
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, hge, -, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  have hjlt : (tr.state z k).fg.hj < (tr.state z k).fg.hmax :=
    hBjhj ▸ (Store.hj_lt_h hR hBj).trans_le (hge Bj hBj)
  have hmax : (tr.state z k).fg.hmax = m := by
    have h1 := hph.frontierAt.2 z hz
    rw [projFG_store_eq hrun hz] at h1
    obtain ⟨B, hB, hBh⟩ : ∃ B ∈ (tr.state z k).fg.tree, ((tr.state z k).fg.σ B.root).h = m := by
      cases c with
      | gap => exact hev
      | top J => exact hev.1
      | contest J => exact hev.1
    have := hge B hB
    omega
  have hjust : JustifiedAt tr.projFG H k (tr.state z k).fg.hj (tr.state z k).fg.J :=
    ⟨z, hz, by rw [projFG_store_eq hrun hz]; exact hJm, Bj,
      by rw [projFG_store_eq hrun hz]; exact hBj, by rw [projFG_store_eq hrun hz]; exact hBjhj,
      by rw [projFG_store_eq hrun hz]; exact hBjJ⟩
  -- with a justification at `m − 1` held whose `J` extends `Σ.F`, the cache is it
  have hcache : ∀ J₀ B₀, J₀ ∈ (tr.state z k).fg.tree → B₀ ∈ (tr.state z k).fg.tree →
      ((tr.state z k).fg.σ B₀.root).hj = m - 1 → ((tr.state z k).fg.σ B₀.root).J = J₀.root →
      (tr.state z k).fg.Anc (tr.state z k).fg.F J₀ →
      (tr.state z k).fg.hj = m - 1 ∧ (tr.state z k).fg.J = J₀ := by
    intro J₀ B₀ hJ₀ hB₀ hB₀j hB₀J hFJ
    have h1 := jMax_of_reachable hR B₀ hB₀ J₀ hJ₀ hB₀J.symm hFJ
    have hhj : (tr.state z k).fg.hj = m - 1 := by omega
    refine ⟨hhj, hcoh.1 hJm hJ₀ ?_⟩
    have := J_eq_of_hj_eq hfg hq hz hz (i := k) (j := k) (B := Bj) (B' := B₀)
      (by rw [projFG_store_eq hrun hz]; exact hBj) (by rw [projFG_store_eq hrun hz]; exact hB₀)
      (by rw [projFG_store_eq hrun hz]; omega)
    rw [projFG_store_eq hrun hz] at this
    rw [← hBjJ, ← hB₀J, this]
  -- the justification of a held state is a held ancestor
  have hJanc : ∀ J₀ B₀, J₀ ∈ (tr.state z k).fg.tree → B₀ ∈ (tr.state z k).fg.tree →
      ((tr.state z k).fg.σ B₀.root).J = J₀.root → (tr.state z k).fg.Anc J₀ B₀ ∧
        ((tr.state z k).fg.σ B₀.root).hj ≤ ((tr.state z k).fg.σ J₀.root).h := by
    intro J₀ B₀ hJ₀ hB₀ hB₀J
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hR hB₀
    obtain ⟨E', hE', hE'r, hle⟩ := J_entry_h hR hB₀
    obtain rfl : E = J₀ := hcoh.1 hE hJ₀ (hEr.trans hB₀J)
    obtain rfl : E' = E := hcoh.1 hE' hE (hE'r.trans hEr.symm)
    exact ⟨hEB, hle⟩
  have hheld : ∀ B ∈ (tr.state z k).fg.tree, (tr.state z k).fg.σ B.root =
      (tr.projFG.store z k).σ B.root := fun B _ => by rw [projFG_store_eq hrun hz]
  refine viableHeads_iff_of ?_ ?_ ?_ hX
  all_goals cases c with
  | gap =>
    have hne : ¬ (tr.state z k).fg.hmax = (tr.state z k).fg.hj + 1 := fun he =>
      hph.2 _ (by rw [show m - 1 = (tr.state z k).fg.hj by omega]; exact hjust)
    have hcon : ¬ (tr.state z k).fg.Contest := fun h => hne h.1
    first
      | (simp only [Store.headHeightFloor, hcon, ↓reduceIte, hmax]; rfl)
      | (intro J e; cases e)
      | (intro _; simp only [Store.fcRoot, hne, false_and, ↓reduceIte])
  | top J₀ =>
    obtain ⟨-, hJ₀, B₀, hB₀, hB₀j, hB₀J⟩ := hev
    obtain ⟨hJB, hle⟩ := hJanc J₀ B₀ hJ₀ hB₀ hB₀J
    obtain ⟨hhj, rfl⟩ := hcache J₀ B₀ hJ₀ hB₀ hB₀j hB₀J
      (hF J₀ ⟨hJ₀, by change m - 1 ≤ _; omega, fun J e => by cases e; exact .refl⟩)
    have hcon : ¬ (tr.state z k).fg.Contest := by
      rintro ⟨-, B, hB, -, hBh, hn⟩
      exact hph.2.2 ⟨z, hz, B, by rw [projFG_store_eq hrun hz]; exact hB,
        by rw [projFG_store_eq hrun hz, hBh, hmax], by rw [projFG_store_eq hrun hz]; exact hn⟩
    have hm1 : (tr.state z k).fg.hmax = (tr.state z k).fg.hj + 1 := by omega
    first
      | (simp only [Store.headHeightFloor, hcon, ↓reduceIte, hmax]; rfl)
      | (intro J e; cases e
         simp only [Store.fcRoot, hm1, hcon, not_false_eq_true, and_self, ↓reduceIte])
      | (intro h; exact absurd rfl (h _))
  | contest J₀ =>
    obtain ⟨-, hJ₀, ⟨B₀, hB₀, hB₀j, hB₀J⟩, B₁, hB₁, hB₁h, hn⟩ := hev
    obtain ⟨hJB, -⟩ := hJanc J₀ B₀ hJ₀ hB₀ hB₀J
    have hB₀h : ((tr.state z k).fg.σ B₀.root).h = m := by
      have := Store.hj_lt_h hR hB₀
      have := hge B₀ hB₀
      omega
    have hFB₀ := hF B₀ ⟨hB₀, by change m ≤ _; omega, fun J e => by cases e⟩
    have hFB₁ := hF B₁ ⟨hB₁, by change m ≤ _; omega, fun J e => by cases e⟩
    have hFJ : (tr.state z k).fg.Anc (tr.state z k).fg.F J₀ := by
      rcases Anc.total hcoh hFB₀ hJB with h | h
      · exact h
      · exact absurd (h.trans hFB₁) hn
    obtain ⟨hhj, rfl⟩ := hcache J₀ B₀ hJ₀ hB₀ hB₀j hB₀J hFJ
    have hcon : (tr.state z k).fg.Contest :=
      ⟨by omega, B₁, hB₁, hFB₁, by rw [hB₁h, hmax], hn⟩
    first
      | (simp only [Store.headHeightFloor, hcon, ↓reduceIte, hmax]; rfl)
      | (intro J e; cases e)
      | (intro _; simp only [Store.fcRoot, hcon, not_true_eq_false, and_false, ↓reduceIte])

end Runs

/-! ## The AC side: stamps, early votes, the proposal's parent -/

section SAFacts

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}

/-- **Where a block stamp comes from**: after an honest call, the stamp of a block of its frame is
genesis's, or the time of an earlier call of the node whose frame holds the block (the call that
accepted it, or a restart's replay). -/
theorem stamp_origin (h : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, ∃ ℓk : ACLabel (SA.goldilocksSA sp FGP ro),
        tr.CallAt y k ℓk ∧ X ∈ ℓk.frame.tree ∧
          (tr.post i).blockStamp X.root = SA.ETime.of (tr.time k) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc X hX
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hpost : tr.post i =
        ((SA.goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    obtain ⟨Φ, hok, hpre⟩ : ∃ Φ, (SA.goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call
        ℓ.frame ∧ ∀ X ∈ Φ.tree, X.root = sp.genesisRoot ∨ ∃ k ≤ i,
          ∃ ℓk : ACLabel (SA.goldilocksSA sp FGP ro), tr.CallAt y k ℓk ∧ X ∈ ℓk.frame.tree ∧
            (tr.state y i).blockStamp X.root = SA.ETime.of (tr.time k) := by
      rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, ⟨htree, hroot, -, -, -⟩, -, hok⟩ |
        ⟨j, ℓ', hj, hc', hnb, hok⟩
      · refine ⟨Φ₀, hok, fun X hX => Or.inl ?_⟩
        rw [htree, Set.mem_singleton_iff] at hX
        rw [hX, hroot]
      · refine ⟨ℓ'.frame, hok, fun X hX => ?_⟩
        rw [tr.state_of_lastCall hc' hj hnb]
        exact (ih j hj ℓ' hc' X hX).imp_right fun ⟨k, hk, ℓk, h1, h2, h3⟩ =>
          ⟨k, hk.trans hj.le, ℓk, h1, h2, h3⟩
    have hΦ' := hok.1
    obtain ⟨hblk, hrst, hoth⟩ := SA.step_blockStamp_eq ro y (tr.state y i) hΦ'.1
      (h.time_nonneg i) ℓ.call
    rw [hpost]
    generalize hcall : ℓ.call = c at hok hblk hrst hoth
    cases c with
    | block B =>
      rw [hblk B rfl, Function.update_apply]
      obtain ⟨hin, hs, -, -⟩ := hok
      split_ifs with hXB
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, hX, rfl⟩
      · rw [hs.tree_eq] at hX
        rcases hX.1 with rfl | hX'
        · exact absurd rfl hXB
        · exact hpre X hX'
    | restart =>
      rw [hrst rfl X hX]
      split_ifs with hg
      · exact Or.inl hg
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, hX, rfl⟩
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2.1 ▸ hX)

/-- The anchor of a walk is in the viable tree of the whole frame tree when `fc_root` is: it is
`fc_root` or the deepest live lock block, a candidate at least as deep as `fc_root`. -/
theorem getAnchor_viable {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n) (t : Time)
    (hfc : Φ.fcRoot ∈ Φ.viableTree Φ.tree) : SA.getAnchor sp A Φ t ∈ Φ.viableTree Φ.tree := by
  unfold SA.getAnchor
  rcases hD : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with _ | D
  · exact hfc
  · obtain ⟨hDS, hmax⟩ := SA.deepest_mem hD
    change D ∈ Φ.viableTree Φ.tree
    by_cases he : D = Φ.fcRoot
    · exact he ▸ hfc
    rcases hDS with hDl | hDf
    · rcases SA.liveLockBlock_candidate hΦ hDl with h | h
      · exact h
      · have h1 := SA.depth_lt_of_anc hΦ h he hΦ.fcRoot_mem
        rcases hmax Φ.fcRoot (Or.inr rfl) (Ne.symm he) with h2 | ⟨h2, -⟩ <;> omega
    · exact absurd (Set.mem_singleton_iff.1 hDf) he

/-- **The parent of an honest proposal is a viable head** of the proposer's frame when `fc_root`
has a viable head above it (requirement 1: the walk starts at the anchor, in the viable tree). -/
theorem proposal_head_viable (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .proposal) {σ : Nat}
    (hk : tr.time k = sp.toParams.slotTime σ) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n} (hp : (SA.acProposal sp (tr.state y k) ℓ.frame (tr.time k)).2 =
      some (d, pay)) (hfc : ℓ.frame.fcRoot ∈ ℓ.frame.viableTree ℓ.frame.tree) :
    d.head ∈ ℓ.frame.viableHeads := by
  obtain ⟨Φp, tp, hreach, htp, hok⟩ := Compose.pre_reachable hr hy hc
  have hΦp : ℓ.frame = Φp := by
    have := hok.2
    rw [hcall] at this
    exact this
  have hΦ : FrameOK ℓ.frame := hok.1.1
  have hOK := ((SA.interface_requirements sp FGP ro).1 y U hr.coherent _ _ _ hreach).1 σ
    (hk ▸ htp) d pay (by rw [← hk, ← hΦp]; exact hp)
  rw [← hΦp] at hOK
  refine hOK.2 ?_
  unfold SA.acProposal at hp
  dsimp only at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  exact getAnchor_viable hΦ _ _ hfc

end SAFacts

/-! ## The run: the proposal call of a tick -/

section RunCuts

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A} {proposer : Nat → Fin P.n}

/-- **An `ac_proposal` cut is the second cut of a tick** (C0.4): no other handler makes one, and
in a tick it follows `ac_on_tick` at once. -/
theorem proposal_call_tick (h : Node.LocalRun proposer dg H sg tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hp : ℓ.call = .proposal) :
    ∃ j, i = j + 1 ∧ tr.TickAt proposer dg y j (tr.time i) := by
  obtain ⟨j, e, q, hg, rfl, hq⟩ := Compose.call_in_group h hy hc
  have hm := List.mem_of_getElem? hq
  cases e with
  | tick x =>
    obtain ⟨ℓ0, pc, uc, h0, hcs, hpc, huc⟩ :=
      Compose.tick_order proposer dg y (tr.state y j) (tr.time (j + q)) x
    change (Node.onTick proposer dg y (tr.state y j) (tr.time (j + q)) x).2[q]? = some (.ac ℓ) at hq
    rw [hcs] at hq
    have hq1 : q = 1 := by
      obtain ⟨ℓu, hℓu, huc⟩ := huc
      rcases q with _ | _ | q
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hq
        subst hq
        simp only [h0, reduceCtorEq] at hp
      · rfl
      · exfalso
        rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓp, -, rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩⟩ <;>
          rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
          simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hq <;>
          have hmem := List.mem_of_getElem? hq <;>
          simp only [List.mem_cons, List.not_mem_nil, Cut.ac.injEq, reduceCtorEq, or_false,
            false_or] at hmem <;>
          rcases hmem with rfl | rfl <;> simp_all only [reduceCtorEq]
    exact ⟨j, by omega, x, hg⟩
  | block B =>
    exfalso
    simp only [Node.exec, Node.onBlock] at hm
    split_ifs at hm
    · simp at hm
    · split at hm
      · simp at hm
      · simp only [Node.acCall, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
          List.not_mem_nil, or_false] at hm
        subst hm
        cases hp
  | message m =>
    exfalso
    simp only [Node.exec, Node.onMessage, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    cases hp
  | attestation a => simp [Node.exec, Node.onAttestation] at hm
  | restart =>
    exfalso
    simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    cases hp

/-- **One `ac_proposal` cut per node and time.** -/
theorem proposal_call_unique (h : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {i i' : Nat} {ℓ ℓ' : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hc' : tr.CallAt y i' (.ac ℓ'))
    (hp : ℓ.call = .proposal) (hp' : ℓ'.call = .proposal) (ht : tr.time i = tr.time i') :
    i = i' := by
  obtain ⟨j, rfl, hj⟩ := proposal_call_tick h hy hc hp
  obtain ⟨j', rfl, hj'⟩ := proposal_call_tick h hy hc' hp'
  rw [ht] at hj
  rw [h.tick_unique y hy j j' _ hj hj']

end RunCuts

/-! ## `Geo` in a settled phase -/

section Main

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time} {proposer : Nat → Fin sp.n}

/-- Allowedness in the effective geometry moves between honest stores that hold the block. -/
theorem effAllowed_transfer (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j m : Nat}
    {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : EffAllowed (tr.state y i).fg m c X) (hX : X ∈ (tr.state z j).fg.tree) :
    EffAllowed (tr.state z j).fg m c X :=
  ⟨hX, by rw [σ_eq_honest hrun hnc hz hy hX h.1]; exact h.2.1, fun J hJ =>
    store_anc_of_honest_anc hrun hnc hz ((h.2.2 J hJ).mono fun Z hZ => ⟨y, hy, i, hZ⟩) hX⟩

/-- A held descendant of an allowed block is allowed (state heights do not decrease). -/
theorem effAllowed_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {m : Nat} {c : PhaseCase (NodeBlock P ACP)} {A W : NodeBlock P ACP}
    (h : EffAllowed st m c A) (hW : W ∈ st.tree) (hAW : st.Anc A W) : EffAllowed st m c W :=
  ⟨hW, h.2.1.trans (h_le_of_store_anc hr hAW), fun J hJ => (h.2.2 J hJ).trans hAW⟩

/-- **H.3 (c3), `Geo` in a settled phase**. Let `P` be the honest proposal of
slot `p` whose proposal and slot-`p` votes lie in one settled effective phase `(m, c)`. Every
honest node there reads the effective geometry (`viableHeads_iff`). The proposal's parent is a
viable head of the proposer (the walk starts in the viable tree, which holds the phase's frontier
block), so `P`, of no smaller state height, is allowed; each voter holds it (it is ready at an
early vote, and relayed by `t_p + Δ`), so `P` is a viable head at the vote. Every other block `X`
of the voter block tree is held by the proposer at its proposal: an ancestor of `P` is below the
parent, and a block stamped before the freeze `t_p − Δ` was accepted then and is relayed by `t_p`
(it extends the proposer's `Σ.F` when it is allowed, HS.1). An allowed block extends the `Σ.F` of
every honest node of the phase (HS.1), so viable-head membership agrees at the two reads. -/
theorem geo_of_settled (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (hP : HonestProposalRun tr H proposer p P) (hph : InSettledPhase tr H g p) :
    SA.Geo proposer tr.projAC H p P := by
  intro k ℓP hcP hcallP htk y hy iv ℓ e hce hslot
  obtain ⟨hpH, k₀, ℓ₀, d, pay, hc₀, hcall₀, hprop₀, ht₀, hpar, hPslot, hPprop, -, j, -, hacc,
    htj⟩ := hP
  obtain ⟨w, m, c, hset, hwp, hphase⟩ := hph
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hlt : ∀ a b, tr.time a < tr.time b → a < b := fun a b h => by
    by_contra hn
    exact absurd (hl.time_mono (not_lt.1 hn)) (not_le.2 h)
  -- the proposal call of `Geo` is the proposal's
  obtain rfl : k = k₀ := proposal_call_unique hl hpH (Compose.projAC_callAt.1 hcP)
    (Compose.projAC_callAt.1 hc₀) hcallP hcall₀ (htk.trans ht₀.symm)
  have ht₀' : tr.time k = sp.ts p := ht₀
  -- the vote is cast from `t_p` on
  have hvt : sp.ts p ≤ tr.time iv := by
    obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hce
    have h' : sp.slot (tr.time iv) = p := hys.symm.trans hslot
    exact (SA.ts_le_iff_le_slot sp (hl.time_nonneg iv) p).2 (by rw [h'])
  -- the settled cut and the phase window
  have hw2 : gbar g + 2 * sp.Δ ≤ w := (le_max_left _ _).trans hset.late
  have hw8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.late
  have hg0 := gbar_nonneg g
  obtain ⟨i₀, hi₀, hi₀k⟩ := exists_firstCutFrom_le (tr := tr) (t := w) (j := k)
    (by rw [ht₀']; exact hwp)
  have hle_i₀ : ∀ a, w ≤ tr.time a → i₀ ≤ a := fun a ha => by
    by_contra hn
    exact absurd (hi₀.2 a (not_le.1 hn)) (not_lt.2 ha)
  have hwin : ∀ k', i₀ ≤ k' → k' ≤ max k iv → PhaseAt tr.projFG H k' m c := by
    intro k' h1 h2
    refine hphase k' (hi₀.1.trans (hl.time_mono h1)) ?_
    rcases le_max_iff.1 h2 with h | h
    · exact Or.inl (by rw [← ht₀']; exact hl.time_mono h)
    · exact Or.inr ⟨y, hy, iv, e, h, ⟨ℓ, hce⟩, hslot⟩
  have hev : ∀ z ∈ H, ∀ k', i₀ ≤ k' → HoldsEvidence (tr.state z k').fg m c := by
    intro z hz k' hk'
    have := hset.evidence i₀ hi₀ m c (hwin i₀ le_rfl (hi₀k.trans (le_max_left _ _))) z hz
    rw [projFG_store_eq hrun hz] at this
    exact holdsEvidence_mono hrun hnc hz hk' this
  have hVH : ∀ z ∈ H, ∀ k', i₀ ≤ k' → k' ≤ max k iv → ∀ X ∈ (tr.state z k').fg.tree,
      X ∈ (Node.frame (tr.state z k')).viableHeads ↔
        (tr.state z k').fg.Anc (tr.state z k').fg.F X ∧ EffAllowed (tr.state z k').fg m c X :=
    fun z hz k' h1 h2 X hX => viableHeads_iff hrun hs hc hz (hwin k' h1 h2) (hev z hz k' h1) hX
  have hHS : ∀ i, i₀ ≤ i → ∀ x ∈ H, ∀ W, EffAllowed (tr.state x i).fg m c W → ∀ z ∈ H, ∀ k',
      i ≤ k' → k' ≤ max k iv → Anc (tr.HonestBlocks H) (tr.state z k').fg.F W :=
    fun i hi x hx W hW z hz k' h1 h2 => (viable_witness_retention_of hrun hs
      (fun k' h1 h2 => hwin k' (hi.trans h1) h2) hx hW hz h1 h2).1
  have hiv0 : i₀ ≤ iv := hle_i₀ iv (hwp.trans hvt)
  have hivK : iv ≤ max k iv := le_max_right _ _
  have hkK : k ≤ max k iv := le_max_left _ _
  have hfrv : ℓ.frame = Node.frame (tr.state y iv) := Compose.frame_of_projAC hrun hy hce.1
  have hfrp : ℓP.frame = Node.frame (tr.state (proposer p) k) :=
    Compose.frame_of_projAC hrun hpH hcP
  have hfr₀ : ℓ₀.frame = Node.frame (tr.state (proposer p) k) :=
    Compose.frame_of_projAC hrun hpH hc₀
  have hfU : ℓ.frame.tree ⊆ tr.HonestBlocks H := (SA.frameIn_of_callAt hr hy hce.1).2
  -- the proposal's parent is a viable head of the proposer
  have hΦ₀ := (SA.frameIn_of_callAt hr hpH hc₀).1
  have hfc₀ : ℓ₀.frame.fcRoot ∈ ℓ₀.frame.viableTree ℓ₀.frame.tree := by
    have hevk := hev _ hpH k hi₀k
    obtain ⟨Bm, hBm, hBmh⟩ : ∃ B ∈ (tr.state (proposer p) k).fg.tree,
        ((tr.state (proposer p) k).fg.σ B.root).h = m := by
      cases c with
      | gap => exact hevk
      | top J => exact hevk.1
      | contest J => exact hevk.1
    have hBe : EffAllowed (tr.state (proposer p) k).fg m c Bm := by
      refine ⟨hBm, ?_, fun J hJ => ?_⟩
      · cases c <;> (simp only [phaseFloor]; omega)
      · subst hJ
        by_contra hn
        exact (hwin k hi₀k hkK).2.2 ⟨_, hpH, Bm, by rw [projFG_store_eq hrun hpH]; exact hBm,
          by rw [projFG_store_eq hrun hpH]; exact hBmh, by rw [projFG_store_eq hrun hpH]; exact hn⟩
    have hBv : Bm ∈ ℓ₀.frame.viableHeads := by
      rw [hfr₀]
      exact (hVH _ hpH k hi₀k hkK Bm hBm).2 ⟨store_anc_of_honest_anc hrun hnc hpH
        (hHS k hi₀k _ hpH Bm hBe _ hpH k le_rfl hkK) hBm, hBe⟩
    exact ⟨hΦ₀.fcRoot_mem, .refl, Bm, hΦ₀.viableHeads_subset hBv, hBv,
      hΦ₀.fcRoot_anc_viableHeads Bm hBv⟩
  have hPrv : d.head ∈ ℓ₀.frame.viableHeads := proposal_head_viable hr hpH hc₀ hcall₀ (σ := p)
    (by rw [sp.slotTime_eq, ht₀]; rfl) hprop₀ hfc₀
  rw [hfr₀] at hPrv
  have hPrt : d.head ∈ (tr.state (proposer p) k).fg.tree := hPrv.1
  obtain ⟨-, hPrE⟩ := (hVH _ hpH k hi₀k hkK d.head hPrt).1 hPrv
  -- `P` is allowed wherever it is held
  have hPallow : ∀ z ∈ H, ∀ k', P ∈ (tr.state z k').fg.tree →
      EffAllowed (tr.state z k').fg m c P := by
    intro z hz k' hPz
    have hR := Compose.fg_reachable hl hz k'
    obtain ⟨Y, hY, hYr, -⟩ := Store.step_σ hR hPz hpar
    obtain rfl : Y = d.head := hU.1 ⟨z, hz, k', hY⟩ ⟨_, hpH, k, hPrt⟩ hYr
    exact effAllowed_of_anc hR (effAllowed_transfer hrun hnc hpH hz hPrE hY) hPz
      (Relation.ReflTransGen.single ⟨hY, hPz, hpar⟩)
  -- the slot-`p` block of an honest frame is `P`
  have hp1 : 1 ≤ p := by
    by_contra h0
    obtain rfl : p = 0 := by omega
    have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    linarith
  obtain ⟨jℓ, hcj, hcallj⟩ := hacc
  have hPj : P ∈ jℓ.frame.tree := (SA.accept_new sp hr hpH ⟨jℓ, hcj, hcallj⟩).1 jℓ hcj
  have hslotP : ∀ P' ∈ ℓ.frame.tree, P'.slot = p → P' = P := by
    intro P' hP' hP's
    have hfb : SA.HonestFrameBlock tr.projAC H P' := ⟨y, hy, iv, ℓ, hce.1, hP'⟩
    have hroot : P'.root ≠ sp.genesisRoot := by
      intro hg
      have hG := Store.genesis_mem (Compose.fg_reachable hl hy iv)
      obtain rfl := hU.1 (hfU hP') ⟨y, hy, iv, hG⟩ hg
      simp [Params.genesisBlock] at hP's
      omega
    exact (hac.honest.one_block P P' ⟨_, hpH, j, jℓ, hcj, hPj⟩ hfb (hPprop ▸ hpH)
      (by rw [hPprop, hac.honest.proposer P' hfb hroot, hP's]) (by rw [hPslot, hP's])).symm
  -- the voter holds `P`
  have hPy : P ∈ (tr.state y iv).fg.tree := by
    by_cases hearly : tr.time iv < sp.ts p + sp.Δ
    · obtain ⟨P', hP', hP's, -⟩ := SA.cast_ready hr hy hce (by rw [hslot]; exact hearly)
      rw [hslot] at hP's
      exact mem_tree_of_frame hrun hy hce.1 (hslotP P' hP' hP's ▸ hP')
    · push Not at hearly
      obtain ⟨kf, rfl, hkf, hkft⟩ := fg_accept_before hl hpH ⟨jℓ, hcj, hcallj⟩
      have htj' : tr.time (kf + 1) = sp.ts p := htj
      have hPk := mem_tree_of_frame hrun hpH hcj hPj
      obtain ⟨jv, hjv, hjviv⟩ := exists_firstCutFrom_le (tr := tr) hearly
      have hj0 : i₀ ≤ kf + 1 := hle_i₀ _ (by rw [htj']; exact hwp)
      have hjjv : kf + 1 ≤ jv := by
        by_contra hn
        have := hl.time_mono (not_le.1 hn).le
        linarith [hjv.1]
      have hF := hHS (kf + 1) hj0 _ hpH P (hPallow _ hpH _ hPk) y hy jv hjjv (hjviv.trans hivK)
      exact Compose.tree_mono hl hy hjviv (relay_held hl hs.healthy hs.noRestart hc hpH hy hkf
        (by linarith) (by rw [hkft, htj']) hjv hF)
  have hPyE := hPallow y hy iv hPy
  have hFP := store_anc_of_honest_anc hrun hnc hy (hHS iv hiv0 y hy P hPyE y hy iv le_rfl hivK) hPy
  refine ⟨by rw [hfrv]; exact (hVH y hy iv hiv0 hivK P hPy).2 ⟨hFP, hPyE⟩, ?_⟩
  intro X hX hXP
  have hXy : X ∈ (tr.state y iv).fg.tree := mem_tree_of_frame hrun hy hce.1 hX.1
  rw [hfrv, hfrp, hVH y hy iv hiv0 hivK X hXy]
  have hgen : X = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload →
      X ∈ (tr.state (proposer p) k).fg.tree := fun hg =>
    hg ▸ Store.genesis_mem (Compose.fg_reachable hl hpH k)
  constructor
  · rintro ⟨-, hXE⟩
    -- the proposer holds `X` at its proposal
    have hXp : X ∈ (tr.state (proposer p) k).fg.tree := by
      rcases hX.2 with hst | ⟨P', hP', hP's, hXP'⟩
      · rw [SA.readPoint_blockStamp_eq hr hy hce] at hst
        rcases stamp_origin hr hy iv ℓ hce.1 X hX.1 with hg | ⟨k₁, -, ℓ₁, hc₁, hX₁, hst₁⟩
        · exact hgen (hU.1 (hfU hX.1) ⟨_, hpH, k, Store.genesis_mem
            (Compose.fg_reachable hl hpH k)⟩ hg)
        rw [hst₁] at hst
        have ht₁ : tr.time k₁ < sp.ts p - sp.Δ := by
          have h := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
          have hfz : SA.freeze sp p = sp.ts p - sp.Δ := by
            unfold SA.freeze SAParams.ts
            ring
          rw [hfz] at h
          exact h
        have hX₁t := mem_tree_of_frame hrun hy hc₁ hX₁
        rcases Compose.tree_cases hl hy hX₁t with hg | ⟨m₁, hm₁, hacc₁⟩
        · exact hgen hg
        have hk₁k : k₁ ≤ k := (hlt _ _ (by rw [ht₀']; linarith)).le
        have hXi : X ∈ (tr.state y (max i₀ k₁)).fg.tree :=
          Compose.tree_mono hl hy (le_max_right _ _) hX₁t
        have hF := hHS (max i₀ k₁) (le_max_left _ _) y hy X
          (effAllowed_transfer hrun hnc hy hy hXE hXi) _ hpH k (max_le hi₀k hk₁k) hkK
        obtain ⟨jw, hjw, hjwk⟩ :=
          exists_firstCutFrom_le (tr := tr) (j := k) (le_of_eq ht₀'.symm)
        have hm₁t := hl.time_mono hm₁.le
        exact Compose.tree_mono hl hpH hjwk (relay_held hl hs.healthy hs.noRestart hc hy hpH
          hacc₁ (by linarith) (by linarith) hjw ((run_F_mono hl hpH hjwk).trans hF))
      · obtain rfl := hslotP P' hP' hP's
        rcases Relation.ReflTransGen.cases_tail hXP' with rfl | ⟨Y, hXY, hYP⟩
        · exact absurd rfl hXP
        · obtain rfl : Y = d.head := hU.1 (hfU hYP.1) ⟨_, hpH, k, hPrt⟩
            (Option.some.inj (hYP.2.2.symm.trans hpar))
          exact mem_of_honest_anc hrun hnc hpH (Anc.mono hfU hXY) hPrt
    have hXpE := effAllowed_transfer hrun hnc hy hpH hXE hXp
    exact (hVH _ hpH k hi₀k hkK X hXp).2 ⟨store_anc_of_honest_anc hrun hnc hpH
      (hHS k hi₀k _ hpH X hXpE _ hpH k le_rfl hkK) hXp, hXpE⟩
  · intro hXv
    have hXp : X ∈ (tr.state (proposer p) k).fg.tree := hXv.1
    obtain ⟨-, hXE⟩ := (hVH _ hpH k hi₀k hkK X hXp).1 hXv
    have hXyE := effAllowed_transfer hrun hnc hpH hy hXE hXy
    exact ⟨store_anc_of_honest_anc hrun hnc hy (hHS iv hiv0 y hy X hXyE y hy iv le_rfl hivK) hXy,
      hXyE⟩

end Main

end Consensus.Goldilocks.Healing

end
