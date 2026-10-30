module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Healing, HS.3: the ready proposal is frozen-viable at every slot-`s` vote

`hs234-exact-interface.md` §4 ("use `P` itself as frozen witness for every ancestor"): at every
honest slot-`s` vote, `P` is held, allowed in the effective geometry, a viable head of the voter
and in its viable voter block tree (`proposal_frozen_viable`). As `Geo.geo_of_settled`: the
proposal's parent is a viable head of the proposer (its walk starts in the viable tree), so `P`
is allowed wherever it is held; the voter holds it (ready at an early vote, relayed by `t_s + Δ`
otherwise); HS.1 (`viableHead_of_allowed`) makes it a viable head of the voter. The proposal's
cut precedes every slot-`s` vote (`proposal_before_vote`: an early voter holds `P`, accepted
after its proposer's own block call, the tick of the proposal), so the phase holds at it.

The aligned-reader facts of `Geo` (`JMax`, `viableHeads_iff`, `cast_ready`,
`proposal_head_viable`, `proposal_call_tick`) are private copies here: `Geo` imports `Service`,
which imports this file. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## Stores (as `Geo`) -/

section Stores

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- One accepted block keeps the justification or justifies its parent's entry. -/
private theorem step_J' {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;>
    simp [FG.ChainState.advance]

/-- The justification of a held block's state names a held block whose state height is at least
the justified height. -/
private theorem J_entry_h {st : Store P ACP} (hr : st.Reachable acp₀) {W : NodeBlock P ACP}
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
    rcases step_J' ht with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, h2⟩ := ih
      exact ⟨E, hE, h1.trans hJ.symm, hj ▸ h2⟩
    · obtain ⟨⟨E, hE, h1, -, h2, -⟩, -⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      exact ⟨E, hE, h1.trans hJ.symm, by rw [hj, h2]⟩

/-- **The justification cache is maximal**: `Σ.h_j` is at least the justified height of every
held state whose justification is a held block extending `Σ.F` (`update_finality` takes the
lex-greatest such justification, and `Σ.F` only moves up). -/
private def JMax (st : Store P ACP) : Prop :=
  ∀ B ∈ st.tree, ∀ X ∈ st.tree, X.root = (st.σ B.root).J → st.Anc st.F X →
    (st.σ B.root).hj ≤ st.hj

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
private theorem jMax_of_reachable {st : Store P ACP} (hr : st.Reachable acp₀) : JMax st := by
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

/-! ## Runs: aligned readers (as `Geo`) -/

section Runs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time}

private theorem projFG_store_eq (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- The FG projection of a run under the HS shared premises is an FG trace, with `f < 2q − n`. -/
private theorem fg_run_of_hs (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
  obtain ⟨-, -, hf⟩ := hs.healthy
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hn := sp.toParams.hn
  exact ⟨Compose.fg_projection _ _ dg H _ tr hreq hs.genesisRoot hrun.toLocalRun hs.noColl,
    by change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n; omega⟩

/-- The evidence of a phase, once held, stays held (stores keep their blocks and states, and
ancestry of a held block does not change). -/
private theorem holdsEvidence_mono (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
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

/-- **Aligned readers** (`phase-service.md` §2): at a cut where the effective phase is `(m, c)`
and an honest node holds the phase's evidence, a block it holds is a viable head of its frame
exactly when it extends its `Σ.F` and is allowed in the effective phase geometry. The head height
floor is the phase floor and `fc_root` is `Σ.F`, or the phase's `J` in the top-`J` case: the
node's `Σ.h_max` is `m`; its `Σ.h_j` is `m − 1` exactly when the phase has a justification there
(`JMax`, with `Σ.F ⪯ J` from HS.1), its `Σ.J` is then the phase's `J` (HR.2 (a)), and its local
contest test agrees with the phase case (the contest witness extends `Σ.F` by HS.1). -/
private theorem viableHeads_iff (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {z : Fin sp.n} (hz : z ∈ H) {k m : Nat}
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
      (finalized_anc_of_allowed hrun hs (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hph) hz hW
        hz le_rfl le_rfl) hW.1
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

/-! ## The AC side (as `Geo`) -/

section SAFacts

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}


private theorem tryVote_ready (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) {e : SA.Em sp FGP} (he : e ∈ (SA.tryVote sp x A Φ t).2)
    (ht : t < sp.ts (sp.slot t) + sp.Δ) : SA.voteReady sp Φ (sp.slot t) := by
  unfold SA.tryVote at he
  dsimp only at he
  split_ifs at he with h1 h2
  · simp at he
  · simp at he
  all_goals
    by_contra hn
    exact h2 ⟨ht, Or.inr hn⟩

private theorem step_ready (self : Fin sp.n) (A : SA.SAState sp.n) {Φ : SA.Frm sp.n FGP}
    {t : Time} (hΦ : FrameOK Φ) (ht0 : 0 ≤ t) (c : (SA.goldilocksSA sp FGP ro).Call)
    {e : SA.Em sp FGP} (he : e ∈ ((SA.goldilocksSA sp FGP ro).step self A Φ t c).2)
    (ht : t < sp.ts (sp.slot t) + sp.Δ) : SA.voteReady sp Φ (sp.slot t) := by
  cases c with
  | tick =>
    change e ∈ (SA.acOnTick sp self A Φ t).2 at he
    have htt : t = sp.ts (sp.slot t) + sp.Δ := by
      unfold SA.acOnTick at he
      dsimp only at he
      split_ifs at he <;> first | assumption | simp at he
    linarith
  | message m => exact tryVote_ready self _ Φ t he ht
  | block B => exact tryVote_ready self _ Φ t he ht
  | proposal => simp [ACInterface.step] at he
  | toFG => simp [ACInterface.step] at he
  | restart =>
    change e ∈ (SA.acRestart sp ro self A Φ t).2 at he
    rw [(SA.restart_state sp FGP ro self A Φ t hΦ ht0).1] at he
    simp at he

/-- **An early vote is ready**: an honest vote cast before `t_s + Δ` has a block of its slot in
its frame (`vote_ready`). -/
private theorem cast_ready (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (ht : tr.time i < sp.ts e.msg.slot + sp.Δ) :
    SA.voteReady sp ℓ.frame e.msg.slot := by
  obtain ⟨hcall, he⟩ := hc
  have hx := hr.exec i ℓ hcall.2 (hcall.1 ▸ hy)
  rw [hcall.1] at hx
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hy hcall
  have he' : e ∈ ((SA.goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by rw [hx]; exact he
  have hs := (SA.castAt_spec hr hy ⟨hcall, he⟩).2.1
  rw [hs] at ht ⊢
  exact step_ready y _ hΦ (hr.time_nonneg i) ℓ.call he' ht

/-- The anchor of a walk is in the viable tree of the whole frame tree when `fc_root` is: it is
`fc_root` or the deepest live lock block, a candidate at least as deep as `fc_root`. -/
private theorem getAnchor_viable {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n)
    (t : Time)
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
private theorem proposal_head_viable (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
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
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- **An `ac_proposal` cut is the second cut of a tick** (C0.4): no other handler makes one, and
in a tick it follows `ac_on_tick` at once. -/
private theorem proposal_call_tick (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat}
    {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hp : ℓ.call = .proposal) :
    ∃ j, i = j + 1 ∧ tr.TickAt dg y j (tr.time i) := by
  obtain ⟨j, e, q, hg, rfl, hq⟩ := Compose.call_in_group h hy hc
  have hm := List.mem_of_getElem? hq
  cases e with
  | tick x =>
    obtain ⟨ℓ0, pc, uc, h0, hcs, hpc, huc⟩ :=
      Compose.tick_order dg y (tr.state y j) (tr.time (j + q)) x
    change (Node.onTick dg y (tr.state y j) (tr.time (j + q)) x).2[q]? = some (.ac ℓ) at hq
    rw [hcs] at hq
    have hq1 : q = 1 := by
      obtain ⟨ℓu, hℓu, huc⟩ := huc
      rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓp, -, rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩⟩ <;>
        rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
        rcases q with _ | _ | _ | _ | _ | _ | _ | q <;> (try simp at hq) <;>
        first | rfl | (subst hq; simp_all)
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

end RunCuts


section Main

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

private theorem effAllowed_transfer (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j m : Nat}
    {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : EffAllowed (tr.state y i).fg m c X) (hX : X ∈ (tr.state z j).fg.tree) :
    EffAllowed (tr.state z j).fg m c X :=
  ⟨hX, by rw [σ_eq_honest hrun hnc hz hy hX h.1]; exact h.2.1, fun J hJ =>
    store_anc_of_honest_anc hrun hnc hz ((h.2.2 J hJ).mono fun Z hZ => ⟨y, hy, i, hZ⟩) hX⟩

/-- A held descendant of an allowed block is allowed (state heights do not decrease). -/
private theorem effAllowed_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {m : Nat} {c : PhaseCase (NodeBlock P ACP)} {A W : NodeBlock P ACP}
    (h : EffAllowed st m c A) (hW : W ∈ st.tree) (hAW : st.Anc A W) : EffAllowed st m c W :=
  ⟨hW, h.2.1.trans (h_le_of_store_anc hr hAW), fun J hJ => (h.2.2 J hJ).trans hAW⟩

private theorem exists_firstCutFrom' {t : Time} {j : Nat} (hj : t ≤ tr.time j) :
    ∃ j₁, tr.FirstCutFrom j₁ t ∧ j₁ ≤ j := by
  classical
  have hex : ∃ k, t ≤ tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩,
    Nat.find_min' hex hj⟩

/-- **The proposal's cut precedes every honest holder of `P`**: an honest node holding `P` at a
cut `k` accepted it at an earlier cut, after its proposer's own block call (unforgeable blocks),
which is the cut after the proposal's `ac_proposal` cut (one tick per node and time). -/
private theorem proposal_before_holder
    (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) (hs1 : 1 ≤ s)
    (hPprop : P.proposer = p) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    (hPz : P ∈ (tr.state z k).fg.tree) : iP < k := by
  have hl := hS.run.toLocalRun
  have hpH : p ∈ H := hS.ready.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  rcases Compose.tree_cases hl hz hPz with hg | ⟨a, hak, ha⟩
  · have := congrArg (·.slot) hg
    simp only [Params.genesisBlock] at this
    omega
  obtain ⟨j', hj'a, hown⟩ := hl.block_unforgeable z hz a P ⟨true, ha⟩ (hPprop ▸ hpH)
  rw [hPprop] at hown
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  rcases Compose.blockCall_cases hl hpH hc with hg |
    ⟨j'', x, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hS.call)
    hS.call_proposal
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [hS.time, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by rw [← ht]; exact ⟨x, hg⟩)
  omega

/-- **`P` is frozen-viable at every honest slot-`s` vote** (`hs234-exact-interface.md` §4, "use
`P` itself as frozen witness"): `P` is held by the voter (ready at an early vote, `cast_ready`;
relayed by `t_s + Δ` otherwise, `relay_held`), allowed (its parent is a viable head of the
proposer, whose walk starts in the viable tree, `proposal_head_viable`, read with the aligned
readers at the proposal cut, which precedes the vote), so a viable head of the voter (HS.1,
`viableHead_of_allowed`), and in the voter block tree as the slot-`s` block. -/
theorem proposal_frozen_viable (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  have hrun := hS.run
  have hs := hS.shared
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  have hpar := hS.parent
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hPprop, -, ja, -, hacc, htja⟩ :=
    honestProposalRun_of_ready hrun hnc hS.ready
  rw [← hS.ready.2.1] at hPprop hacc
  -- times: the settled time and the vote are around `t_s`
  have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
  have hvt : sp.ts s ≤ tr.time j := by
    obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hcy
    exact (SA.ts_le_iff_le_slot sp (hl.time_nonneg j) s).2
      (by have := hys.le; rw [hes] at this; exact_mod_cast this)
  have hwi : w ≤ tr.time i := hS.settled.2.1.1.trans (hl.time_mono hS.settled_le)
  have hws : w < sp.ts s := by linarith [hS.start_time]
  have hs1 : 1 ≤ s := by
    by_contra h0
    obtain rfl : s = 0 := by omega
    have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    have := gbar_nonneg g
    have := (le_max_right _ _).trans hS.settled.1.late
    linarith
  have hiP0 : i₀ ≤ iP := le_of_settledIn hS.settled (by rw [hS.time]; exact hws.le)
  -- the slot-`s` block of the voter's frame is `P`
  obtain ⟨jℓ, hcj, hcallj⟩ := hacc
  have hPj : P ∈ jℓ.frame.tree := (SA.accept_new sp hr hpH ⟨jℓ, hcj, hcallj⟩).1 jℓ hcj
  have hfU : ℓy.frame.tree ⊆ tr.HonestBlocks H := (SA.frameIn_of_callAt hr hy hcy.1).2
  have hslotP : ∀ P' ∈ ℓy.frame.tree, P'.slot = s → P' = P := by
    intro P' hP' hP's
    have hfb : SA.HonestFrameBlock tr.projAC H P' := ⟨y, hy, j, ℓy, hcy.1, hP'⟩
    have hroot : P'.root ≠ sp.genesisRoot := by
      intro hg
      have hG := Store.genesis_mem (Compose.fg_reachable hl hy j)
      obtain rfl := hU.1 (hfU hP') ⟨y, hy, j, hG⟩ hg
      simp [Params.genesisBlock] at hP's
      omega
    exact (hac.honest.one_block P P' ⟨_, hpH, ja, jℓ, hcj, hPj⟩ hfb (hPprop ▸ hpH)
      (by rw [hPprop, hac.honest.proposer P' hfb hroot, hP's, hS.ready.2.1])
      (by rw [hPs, hP's])).symm
  -- an early voter holds `P`; the proposal's cut precedes the vote
  have hiPj : iP < j := by
    by_cases hlate : tr.time iP < tr.time j
    · by_contra hn
      exact absurd (hl.time_mono (not_lt.1 hn)) (not_le.2 hlate)
    · have hearly : tr.time j < sp.ts e.msg.slot + sp.Δ := by
        rw [hes]; rw [hS.time] at hlate; linarith
      obtain ⟨P', hP', hP's, -⟩ := cast_ready hr hy hcy hearly
      rw [hes] at hP's
      exact proposal_before_holder hS hs1 hPprop hy
        (mem_tree_of_frame hrun hy hcy.1 (hslotP P' hP' hP's ▸ hP'))
  -- the phase on `[i₀, j]`, and the evidence held from `i₀` on
  have hwin : PhaseOn tr.projFG H i₀ j m c :=
    phaseOn_voter hrun hs hS.settled (start_le_voter hrun hnc hS.start_time hy hcy hes)
      (hS.phase y hy j ℓy e hcy hes)
  have hev : ∀ z ∈ H, ∀ k', i₀ ≤ k' → HoldsEvidence (tr.state z k').fg m c := by
    intro z hz k' hk'
    have := hS.settled.1.evidence i₀ hS.settled.2.1 m c hS.settled.2.2 z hz
    rw [projFG_store_eq hrun hz] at this
    exact holdsEvidence_mono hrun hnc hz hk' this
  have hphP := hwin iP hiP0 hiPj.le
  -- the proposal's parent is a viable head of the proposer, so allowed
  have hfr₀ : ℓp.frame = Node.frame (tr.state p iP) := Compose.frame_of_projAC hrun hpH hS.call
  have hΦ₀ := (SA.frameIn_of_callAt hr hpH hS.call).1
  have hfc₀ : ℓp.frame.fcRoot ∈ ℓp.frame.viableTree ℓp.frame.tree := by
    have hevk := hev p hpH iP hiP0
    obtain ⟨Bm, hBm, hBmh⟩ : ∃ B ∈ (tr.state p iP).fg.tree,
        ((tr.state p iP).fg.σ B.root).h = m := by
      cases c with
      | gap => exact hevk
      | top J => exact hevk.1
      | contest J => exact hevk.1
    have hBe : EffAllowed (tr.state p iP).fg m c Bm := by
      refine ⟨hBm, ?_, fun J hJ => ?_⟩
      · cases c <;> (simp only [phaseFloor]; omega)
      · subst hJ
        by_contra hn
        exact hphP.2.2 ⟨_, hpH, Bm, by rw [projFG_store_eq hrun hpH]; exact hBm,
          by rw [projFG_store_eq hrun hpH]; exact hBmh, by rw [projFG_store_eq hrun hpH]; exact hn⟩
    have hBv : Bm ∈ ℓp.frame.viableHeads := by
      rw [hfr₀]
      exact viableHead_of_allowed hrun hs (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hphP) hpH
        hBe hpH le_rfl le_rfl hBm
    exact ⟨hΦ₀.fcRoot_mem, .refl, Bm, hΦ₀.viableHeads_subset hBv, hBv,
      hΦ₀.fcRoot_anc_viableHeads Bm hBv⟩
  have hPrv : d.head ∈ ℓp.frame.viableHeads := proposal_head_viable hr hpH hS.call
    hS.call_proposal (σ := s) (by rw [sp.slotTime_eq]; exact hS.time) hS.payload hfc₀
  rw [hfr₀] at hPrv
  have hPrt : d.head ∈ (tr.state p iP).fg.tree := hPrv.1
  obtain ⟨-, hPrE⟩ :=
    (viableHeads_iff hrun hs hpH hphP (hev p hpH iP hiP0) hPrt).1 hPrv
  -- `P` is allowed wherever it is held
  have hPallow : ∀ z ∈ H, ∀ k', P ∈ (tr.state z k').fg.tree →
      EffAllowed (tr.state z k').fg m c P := by
    intro z hz k' hPz
    have hR := Compose.fg_reachable hl hz k'
    obtain ⟨Y, hY, hYr, -⟩ := Store.step_σ hR hPz hpar
    obtain rfl : Y = d.head := hU.1 ⟨z, hz, k', hY⟩ ⟨_, hpH, iP, hPrt⟩ hYr
    exact effAllowed_of_anc hR (effAllowed_transfer hrun hnc hpH hz hPrE hY) hPz
      (Relation.ReflTransGen.single ⟨hY, hPz, hpar⟩)
  -- the voter holds `P`
  have hPy : P ∈ (tr.state y j).fg.tree := by
    by_cases hearly : tr.time j < sp.ts s + sp.Δ
    · obtain ⟨P', hP', hP's, -⟩ := cast_ready hr hy hcy (by rw [hes]; exact hearly)
      rw [hes] at hP's
      exact mem_tree_of_frame hrun hy hcy.1 (hslotP P' hP' hP's ▸ hP')
    · push Not at hearly
      obtain ⟨kf, rfl, hkf, hkft⟩ := fg_accept_before hl hpH ⟨jℓ, hcj, hcallj⟩
      have htj' : tr.time (kf + 1) = sp.ts s := htja
      have hPk := mem_tree_of_frame hrun hpH hcj hPj
      obtain ⟨jv, hjv, hjvj⟩ := exists_firstCutFrom' (tr := tr) hearly
      have hj0 : i₀ ≤ kf + 1 := le_of_settledIn hS.settled (by rw [htj']; exact hws.le)
      have hjjv : kf + 1 ≤ jv := by
        by_contra hn
        have := hl.time_mono (not_le.1 hn).le
        linarith [hjv.1]
      have hF := finalized_anc_of_allowed hrun hs (fun k' h1 h2 => hwin k' (hj0.trans h1) h2)
        hpH (hPallow _ hpH _ hPk) hy hjjv hjvj
      exact Compose.tree_mono hl hy hjvj (relay_held hl hs.healthy hs.noRestart hS.catchUp hpH hy
        hkf (by linarith [hS.gbar_le]) (by rw [hkft, htj']) hjv hF)
  have hPv := viableHead_of_allowed hrun hs (fun k' h1 h2 => hwin k' (hiP0.trans
    (hiPj.le.trans h1)) h2) hy (hPallow y hy j hPy) hy le_rfl le_rfl hPy
  have hfrv : ℓy.frame = Node.frame (tr.state y j) := Compose.frame_of_projAC hrun hy hcy.1
  have hΦy := (SA.frameIn_of_callAt hr hy hcy.1).1
  rw [hfrv] at hΦy ⊢
  have hPt : P ∈ (Node.frame (tr.state y j)).tree := hΦy.viableHeads_subset hPv
  have hPV : P ∈ SA.voterBlockTree sp e.readPoint (Node.frame (tr.state y j)) s :=
    ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩
  exact ⟨hPV, hΦy.fcRoot_anc_viableHeads P hPv, P, hPV, hPv, .refl⟩

end Main

end Consensus.Goldilocks.Healing

end
