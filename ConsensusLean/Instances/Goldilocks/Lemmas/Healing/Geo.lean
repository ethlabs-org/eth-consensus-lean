module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: settled-phase geometry (H.3 (c3))

The pieces of the settled-phase geometry that remain; the geometry itself, its aligned readers
and its relay to the proposer are removed with HS.4 and HR.3 (retired, owner decision):

* **`JMax`**: `Σ.h_j` is at least the justified height of every held state whose `J` is a held
  block extending `Σ.F`, an FG store invariant (`jMax_of_reachable`).
* **The voter block tree**: a block stamped before the freeze was held by the voter at an earlier
  call (`stamp_origin`, `readPoint_blockStamp_eqU`).
* **The proposal**: the walk starts at an anchor in the viable tree (`getAnchor_viable`), and the
  proposal's parent is a viable head (`proposal_head_viable`); an `ac_proposal` cut is the second
  cut of a tick (`proposal_call_tick`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload gbar)

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

end Stores

/-! ## Runs: aligned readers in a settled phase -/

section Runs

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF : Time}
  {proposer : Nat → Fin sp.n}

end Runs

/-! ## The AC side: stamps, early votes, the proposal's parent -/

section ACFacts

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {tr : AC.GTrace sp FGP ro}

/-- **Where a block stamp comes from**: after an honest call, the stamp of a block of its frame is
genesis's, or the time of an earlier call of the node whose frame holds the block (the call that
accepted it, or a restart's replay). -/
theorem stamp_origin {ini} (h : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    {y : Fin sp.n}
    (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (AC.goldilocksAC sp FGP ro)), tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, ∃ ℓk : ACLabel (AC.goldilocksAC sp FGP ro),
        tr.CallAt y k ℓk ∧ X ∈ ℓk.frame.tree ∧
          (tr.post i).blockStamp X.root = AC.ETime.of (tr.time k) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc X hX
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hpost : tr.post i =
        ((AC.goldilocksAC sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    obtain ⟨Φ, hok, hpre⟩ : ∃ Φ, (AC.goldilocksAC sp FGP ro).CallOK U Φ (tr.time i) ℓ.call
        ℓ.frame ∧ ∀ X ∈ Φ.tree, X.root = sp.genesisRoot ∨ ∃ k ≤ i,
          ∃ ℓk : ACLabel (AC.goldilocksAC sp FGP ro), tr.CallAt y k ℓk ∧ X ∈ ℓk.frame.tree ∧
            (tr.state y i).blockStamp X.root = AC.ETime.of (tr.time k) := by
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
    obtain ⟨hblk, hrst, hoth⟩ := AC.step_blockStamp_eq ro y (tr.state y i) hΦ'.1
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
theorem getAnchor_viable {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : AC.ACState sp.n) (t : Time)
    (hfc : Φ.fcRoot ∈ Φ.viableTree Φ.tree) : AC.getAnchor sp A Φ t ∈ Φ.viableTree Φ.tree := by
  unfold AC.getAnchor
  rcases hD : AC.deepest Φ (AC.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with _ | D
  · exact hfc
  · obtain ⟨hDS, hmax⟩ := AC.deepest_mem hD
    change D ∈ Φ.viableTree Φ.tree
    by_cases he : D = Φ.fcRoot
    · exact he ▸ hfc
    rcases hDS with hDl | hDf
    · rcases AC.liveLockBlock_candidate hΦ hDl with h | h
      · exact h
      · have h1 := AC.depth_lt_of_anc hΦ h he hΦ.fcRoot_mem
        rcases hmax Φ.fcRoot (Or.inr rfl) (Ne.symm he) with h2 | ⟨h2, -⟩ <;> omega
    · exact absurd (Set.mem_singleton_iff.1 hDf) he

/-- **The parent of an honest proposal is a viable head** of the proposer's frame when `fc_root`
has a viable head above it (requirement 1: the walk starts at the anchor, in the viable tree), for
starts up to the vote permission. -/
theorem proposal_head_viable {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y k ℓ) (hcall : ℓ.call = .proposal) {σ : Nat}
    (hk : tr.time k = sp.toParams.slotTime σ) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n} (hp : (AC.acProposal sp (tr.state y k) ℓ.frame (tr.time k)).2 =
      some (d, pay)) (hfc : ℓ.frame.fcRoot ∈ ℓ.frame.viableTree ℓ.frame.tree) :
    d.head ∈ ℓ.frame.viableHeads := by
  obtain ⟨Φp, tp, hreach, htp, hok⟩ := Compose.pre_reachable hr hy hc
  have hΦp : ℓ.frame = Φp := by
    have := hok.2
    rw [hcall] at this
    exact this
  have hΦ : FrameOK ℓ.frame := hok.1.1
  have hOK := ((AC.interface_requirements_from sp FGP ro (hini y)).1 y U hr.coherent _ _ _
    (ACInterface.reachableAtFrom_iff.1 hreach)).1 σ (hk ▸ htp) d pay
    (by rw [← hk, ← hΦp]; exact hp)
  rw [← hΦp] at hOK
  refine hOK.2 ?_
  unfold AC.acProposal at hp
  dsimp only at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  exact getAnchor_viable hΦ _ _ hfc

end ACFacts

/-! ## The run: the proposal call of a tick -/

section RunCuts

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A} {proposer : Nat → Fin P.n}

/-- **An `ac_proposal` cut is the second cut of a tick** (C0.4): no other handler makes one, and
in a tick it follows `ac_on_tick` at once. -/
theorem proposal_call_tick {ini} (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel A} (hc : tr.CallAt y i (.ac ℓ)) (hp : ℓ.call = .proposal) :
    ∃ j, i = j + 1 ∧ tr.TickAt proposer dg y j (tr.time i) := by
  obtain ⟨j, e, q, hg, rfl, hq⟩ := Compose.call_in_group h hy hc
  have hm := List.mem_of_getElem? hq
  cases e with
  | tick x fgDue =>
    have hq1 : q = 1 := (onTick_ac_index y (tr.state y j)
      (tr.time (j + q)) x fgDue hq).1 hp
    exact ⟨j, by omega, x, fgDue, hg⟩
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

/-! ## `Geo` in a settled phase -/

section Main

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF : Time}
  {proposer : Nat → Fin sp.n}

end Main

end Consensus.Goldilocks.Healing

end
