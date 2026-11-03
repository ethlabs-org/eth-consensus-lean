module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # Goldilocks under `Sleepy`: honest-store frame geometry

workbench#11 §3 (S3). With the source origins relevant at a cut compatible with an origin `C` and
with each other, every target or progress quorum has an honest row (`q > f`), whose named entry is
on the origin chain; comparable sources of one height name one entry, so there is no contest from
genesis, the floor is `max(1, h_max − 1)`, and `fc_root` (`Σ.J` or `Σ.F`) is compatible with `C`.

Both are stated for a block `B` with the hypotheses the argument uses, not only for origins, so
that the proposal-adoption bootstrap (workbench#12 §4, S3P) applies them to the protected
proposal.

`FrameFrozen` proves the frozen witness and `FrameLabels` assembles the following consequences:

* **Full reads** (`held_origin_viable`): a held block compatible with every origin, above
  `fc_root`, is in the full viable tree: it is viable itself, or a maximal-height carrier extends
  the named entry of an honest crossing source above it.
* **Votes** (`vote_frame`): at an honest slot-`(s+1)` vote, a block compatible with the origins of
  labels `≤ s` and extended by an honest slot-`s` vote is in the viable tree of the voter block
  tree, or at or below `fc_root` (inside the honest blocks). The
  sources the voter's FG has seen have labels at most `s` (a label-`(s+1)` source is reported at
  the earliest in the tick at `t_{s+1} + Δ`, after the votes there), so `P_{s+1}` compares them;
  the frozen witness is an honest head (of a crossing source when the floor is above `B`, the
  honest slot-`s` head extending `B` otherwise), accepted before the freeze. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-! ### Chain geometry in one honest store -/

section Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {ftr : FGTrace P ACP}

/-- An ancestor of a member is a member. -/
theorem anc_mem {S : Set (NodeBlock P ACP)} {A W : NodeBlock P ACP} (h : Anc S A W)
    (hW : W ∈ S) : A ∈ S := by
  by_cases hne : A = W
  · exact hne ▸ hW
  · exact (Goldilocks.Anc.mem h hne).1

/-- A held block that names a parent has its parent held. -/
private theorem parent_held (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (ftr.store y m).tree) {r : Nat} (hp : B.parent = some r) :
    ∃ Y, ParentIn (ftr.store y m).tree Y B := by
  rcases ((Store.accepted_tree P ACP acp₀ _ (Store.store_reachable hr hy m)).2.2.2 B hB).cases_tail
    with rfl | ⟨Y, -, hY⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · exact ⟨Y, hY⟩

/-- Ancestry inside `U` below a held block is ancestry inside the store. -/
private theorem anc_store (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {A W : NodeBlock P ACP} (h : Anc U A W) (hW : W ∈ (ftr.store y m).tree) :
    (ftr.store y m).Anc A W := by
  induction h with
  | refl => exact .refl
  | tail _ hYW ih =>
    obtain ⟨Z, hZ⟩ := parent_held hr hy hW hYW.2.2
    obtain rfl : Z = _ := hr.coherent.1 (hr.tree_subset y hy m hZ.1) hYW.1
      (Option.some.inj (hZ.2.2.symm.trans hYW.2.2))
    exact (ih hZ.1).tail hZ

/-- Along ancestry the height does not decrease; while it stays, the entry stays. -/
private theorem anc_height (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
    {m : Nat} {A W : NodeBlock P ACP} (h : (ftr.store y m).Anc A W) :
    ((ftr.store y m).σ A.root).h ≤ ((ftr.store y m).σ W.root).h ∧
      (((ftr.store y m).σ W.root).h = ((ftr.store y m).σ A.root).h →
        ((ftr.store y m).σ W.root).Th = ((ftr.store y m).σ A.root).Th) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => rfl⟩
  | tail _ hYW ih =>
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _
      (Store.store_reachable hr hy m) _ hYW.1
    obtain ⟨h1, -, -, h4, -⟩ := FG.height_step P.fg _ _ _ _ hc (Store.step_σ hr hy hYW.2.1 hYW.2.2)
    have := ih.1
    rcases h1 with h1 | h1
    · exact ⟨by omega, fun _ => (h4 h1).1.trans (ih.2 (by omega))⟩
    · exact ⟨by omega, fun _ => by omega⟩

/-- Every progress bit of a held block's state has its row on the block's chain, naming the
entry. -/
private theorem prog_rows (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (ftr.store y m).tree) :
    ∀ v ∈ ((ftr.store y m).σ W.root).prog, ∃ X ∈ (ftr.store y m).tree,
      (ftr.store y m).Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧
        a.T = ((ftr.store y m).σ W.root).Th := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy]
    intro v hv
    exact absurd hv (Finset.notMem_empty v)
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hR W' h1
    obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog (Store.step_σ hr hy h2 hp)
      (FG.chain_invariants P.fg _ _ hc).2.2.2.2.2.2.2.2.2
    rcases hcase with ⟨-, hT, hpe⟩ | ⟨-, he⟩
    · intro v hv
      rw [hpe] at hv
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨X, hX, hXW, a, ha, hav, haT⟩ := ih v hv
        exact ⟨X, hX, hXW.tail ⟨h1, h2, hp⟩, a, ha, hav, haT.trans hT.symm⟩
      · exact ⟨W, h2, .refl, a, ha, hav, haT.trans hT.symm⟩
    · intro v hv
      rw [he] at hv
      exact absurd hv (Finset.notMem_empty v)

/-- **Crossing quorums**: every height `1 ≤ j` that a held block's chain left has an entry block
`E` (height `j`, its own entry) on the chain and a quorum of validators with a row on the chain
naming `E`. -/
private theorem crossing_quorum (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
    {m : Nat} {W : NodeBlock P ACP} (hW : W ∈ (ftr.store y m).tree) :
    ∀ j, 1 ≤ j → j < ((ftr.store y m).σ W.root).h →
      ∃ E ∈ (ftr.store y m).tree, (ftr.store y m).Anc E W ∧
        ((ftr.store y m).σ E.root).h = j ∧ ((ftr.store y m).σ E.root).Th = E.root ∧
        ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ X ∈ (ftr.store y m).tree,
          (ftr.store y m).Anc X W ∧ ∃ a ∈ X.fgPayload, a.val = v ∧ a.T = E.root := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro j h1 h2
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy] at h2
    simp [FG.ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    have hst := Store.step_σ hr hy h2 hp
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hR W' h1
    obtain ⟨hstep, -⟩ := FG.height_step P.fg _ _ _ _ hc hst
    have lift : ∀ X, (ftr.store y m).Anc X W' → (ftr.store y m).Anc X W :=
      fun X hX => hX.tail ⟨h1, h2, hp⟩
    intro j hj1 hj2
    by_cases hlt : j < ((ftr.store y m).σ W'.root).h
    · obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ := ih j hj1 hlt
      exact ⟨E, hE, lift E hEW, hEh, hET, Q, hQ, fun v hv' =>
        let ⟨X, hX, hXW, a, ha, h⟩ := hv v hv'; ⟨X, hX, lift X hXW, a, ha, h⟩⟩
    · have hjeq : j = ((ftr.store y m).σ W'.root).h := by rcases hstep with h | h <;> omega
      have hh : ((ftr.store y m).σ W.root).h = ((ftr.store y m).σ W'.root).h + 1 := by
        rcases hstep with h | h <;> omega
      obtain ⟨-, p, hpv, hcase⟩ := Store.step_prog hst
        (FG.chain_invariants P.fg _ _ hc).2.2.2.2.2.2.2.2.2
      have hq : P.fg.q ≤ p.card := by
        rcases hcase with ⟨he, -⟩ | ⟨hq, -⟩
        · omega
        · exact hq
      obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        Store.entry_state_of_source P ACP acp₀ _ hR W' h1
      refine ⟨E, hE, lift E hEW', hEh.trans hjeq.symm, hET.trans hEr.symm, p, hq, fun v hv => ?_⟩
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨X, hX, hXW, a, ha, hav, haT⟩ := prog_rows hr hy h1 v hv
        exact ⟨X, hX, lift X hXW, a, ha, hav, haT.trans hEr.symm⟩
      · exact ⟨W, h2, .refl, a, ha, hav, haT.trans hEr.symm⟩

/-- One accepted block keeps the justification or justifies its parent's entry. -/
private theorem step_J {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;>
    simp [FG.ChainState.advance]

/-- **The justification of a held block is an entry block** on its chain, of the justified
height. -/
private theorem J_entry (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀) {m : Nat}
    {Z : NodeBlock P ACP} (hZ : Z ∈ (ftr.store y m).tree) :
    1 ≤ ((ftr.store y m).σ Z.root).hj → ∃ E ∈ (ftr.store y m).tree,
      E.root = ((ftr.store y m).σ Z.root).J ∧ (ftr.store y m).Anc E Z ∧
      ((ftr.store y m).σ E.root).h = ((ftr.store y m).σ Z.root).hj ∧
      ((ftr.store y m).σ E.root).Th = E.root := by
  have hR := Store.store_reachable hr hy m
  have hg := (Store.accepted_tree P ACP acp₀ _ hR).2.2.2 Z hZ
  clear hZ
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr hy]
    intro h
    simp [FG.ChainState.init] at h
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    intro hj
    rcases step_J (Store.step_σ hr hy h2 hp) with ⟨hJ, hhj⟩ | ⟨hJ, hhj⟩
    · obtain ⟨E, hE, hEr, hEW, hEh, hET⟩ := ih (by omega)
      exact ⟨E, hE, hEr.trans hJ.symm, hEW.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm, hET⟩
    · obtain ⟨⟨E, hE, hEr, hEW', hEh, hET⟩, -⟩ :=
        Store.entry_state_of_source P ACP acp₀ _ hR W' h1
      exact ⟨E, hE, hEr.trans hJ.symm, hEW'.tail ⟨h1, h2, hp⟩, hEh.trans hhj.symm,
        hET.trans hEr.symm⟩

/-- **Entry constancy on a height plateau**: two entry blocks of one height below one held block
are equal. -/
private theorem entry_unique (hr : FGLocalRun acp₀ H₀ U ftr) {y : Fin P.n} (hy : y ∈ H₀)
    {m : Nat} {E E' W : NodeBlock P ACP} (hW : W ∈ (ftr.store y m).tree)
    (hE : (ftr.store y m).Anc E W) (hE' : (ftr.store y m).Anc E' W)
    (hh : ((ftr.store y m).σ E.root).h = ((ftr.store y m).σ E'.root).h)
    (hT : ((ftr.store y m).σ E.root).Th = E.root)
    (hT' : ((ftr.store y m).σ E'.root).Th = E'.root) : E = E' := by
  have coh : Coherent (ftr.store y m).tree := hr.coherent.mono (hr.tree_subset y hy m)
  apply coh.1 (anc_mem hE hW) (anc_mem hE' hW)
  rcases Goldilocks.Anc.total coh hE hE' with h | h
  · exact hT.symm.trans (((anc_height hr hy h).2 hh.symm).symm.trans hT')
  · exact hT.symm.trans (((anc_height hr hy h).2 hh).trans hT')

end Store

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The FG projection of a run -/

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9). -/
private theorem requirements (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- The FG projection of a Goldilocks run is an FG local run inside the honest blocks. -/
theorem projFG_localRun (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  fg_projection _ _ dg H _ tr proposer (requirements sp ro)
    hrun.genesis_root_ok hrun.toLocalRun hnc

theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [projFG_state hrun.toLocalRun hy i]

/-- The tree of an honest node is among the honest blocks. -/
theorem fg_tree_subset_honest {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocks H :=
  fun _ hZ => ⟨y, hy, i, hZ⟩

/-- Ancestry inside the honest blocks below a held block is ancestry in the holder's store. -/
theorem honest_held_anc (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {A W : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A W) (hW : W ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.Anc A W := by
  rw [← store_eq hrun hy i] at hW ⊢
  exact anc_store (projFG_localRun hrun hnc) hy h hW

/-- State heights do not decrease along ancestry in an honest store, and equal heights have equal
`Th`. -/
theorem honest_held_height (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {A W : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : (tr.state y i).fg.Anc A W) :
    ((tr.state y i).fg.σ A.root).h ≤ ((tr.state y i).fg.σ W.root).h ∧
      (((tr.state y i).fg.σ W.root).h = ((tr.state y i).fg.σ A.root).h →
        ((tr.state y i).fg.σ W.root).Th = ((tr.state y i).fg.σ A.root).Th) := by
  rw [← store_eq hrun hy i] at h ⊢
  exact anc_height (projFG_localRun hrun hnc) hy h

private theorem held_σ_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root := by
  rw [← store_eq hrun hy i] at hBy ⊢
  rw [← store_eq hrun hz j] at hBz ⊢
  exact Store.σ_eq_of_held (projFG_localRun hrun hnc) hy hz hBy hBz

/-- Two entries of one state height below one held block are equal. -/
theorem held_entry_unique (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {E E' W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y i).fg.tree)
    (hE : (tr.state y i).fg.Anc E W) (hE' : (tr.state y i).fg.Anc E' W)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state y i).fg.σ E'.root).Th = E'.root) : E = E' := by
  rw [← store_eq hrun hy i] at hW hE hE' hh hT hT'
  exact entry_unique (projFG_localRun hrun hnc) hy hW hE hE' hh hT hT'

/-- The chain invariants of a held block's state. -/
theorem honest_held_chain (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree) :
    1 ≤ ((tr.state y i).fg.σ B.root).h ∧
      ((tr.state y i).fg.σ B.root).hj < ((tr.state y i).fg.σ B.root).h ∧
      (((tr.state y i).fg.σ B.root).hj = 0 → ((tr.state y i).fg.σ B.root).J = sp.genesisRoot) := by
  obtain ⟨c, -, -, -, hc⟩ :=
    Store.chain_state_of_chain _ _ _ _ (fg_reachable hrun.toLocalRun hy i) B hB
  obtain ⟨h1, -, h2, h3, -⟩ := FG.chain_invariants _ _ _ hc
  exact ⟨h1, h2, h3⟩

/-- With `f < n/2`, a quorum has an honest member (`f < n/2 < q`). -/
private theorem honest_mem (hf : 2 * Hᶜ.ncard < sp.n) {Q : Finset (Fin sp.n)}
    (hQ : sp.toParams.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  have hsub : (↑Q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hc
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  omega

/-- An honest row on the chain of a held block was signed by its signer before the node accepted
the block, before the cut. -/
theorem honest_row_signed_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y i).fg.tree) {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a := by
  rw [← store_eq hrun hy i] at hX
  rcases Store.tree_accepted (projFG_localRun hrun hnc) hy hX with rfl | ⟨m, hm, hA⟩
  · simp [Params.genesisBlock] at ha
  · exact ⟨m, hm, projFG_callAt.1 hA,
      hrun.att_unforgeable y hy m a (Or.inr ⟨X, ⟨true, projFG_callAt.1 hA⟩, ha⟩) hav⟩

/-! ### Honest sources -/

/-- The target of an attestation that `create_attestation` signs is the entry of its entry
state. (As `Persist/Attest`'s `createAtt_T`.) -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

/-- `D` is an honest source naming the entry `T`: a block of an honest node's tree whose state
has the entry `T`. -/
def IsHonestSource (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (T : Nat) : Prop :=
  ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSource_iff {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} :
    IsHonestSource tr H D T ↔
      ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T :=
  Iff.rfl

/-- Every honest row on a block of `y`'s tree before cut `i` has a source satisfying `G`. -/
def HonestRowsSourced (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem honestRowsSourced_iff {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n}
    {i : Nat} : HonestRowsSourced tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
        ∃ D, G D ∧ IsHonestSource tr H D a.T :=
  Iff.rfl

/-- Every honest row on a block of `y`'s tree before cut `i` whose named entry has height at
least `h₀` (in `y`'s states) has a source satisfying `G`: the rows the geometry reads at the
crossing heights `≥ h₀`. -/
def RowsAbove (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i h₀ : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
    h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T

theorem HonestRowsSourced.above {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {y : Fin sp.n} {i : Nat} (h : HonestRowsSourced tr H G y i) (h₀ : Nat) :
    RowsAbove tr H G y i h₀ :=
  fun X hX a ha hav _ => h X hX a ha hav

/-- The entry an honest source names is its ancestor, an entry block of the source's height. -/
theorem honest_source_entry (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} (hD : IsHonestSource tr H D T)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ tr.HonestBlocks H) (hET : E.root = T) :
    ∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧ E ∈ (tr.state x k).fg.tree ∧
      (tr.state x k).fg.Anc E D ∧
      ((tr.state x k).fg.σ E.root).h = ((tr.state x k).fg.σ D.root).h ∧
      ((tr.state x k).fg.σ E.root).Th = E.root := by
  obtain ⟨x, hx, k, hDt, hDT⟩ := hD
  obtain ⟨⟨E', hE', hE'r, hE'D, hE'h, hE'T⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hrun.toLocalRun hx k) D hDt
  obtain rfl : E' = E :=
    (projFG_localRun hrun hnc).coherent.1 ⟨x, hx, k, hE'⟩ hE (hE'r.trans (hDT.trans hET.symm))
  exact ⟨x, hx, k, hDt, hE', hE'D, hE'h, hE'T.trans hE'r.symm⟩

/-- **An honest attestation names the entry of its source**, a block of the signer's tree below
an origin whose event precedes the signing (the source is a live fast lock block,
`lock_origin`). -/
theorem attestation_source (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {a : FG.Att sp.n} (h : tr.SignAt x k a) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C l, OriginBefore tr H C l k ∧ Anc (tr.HonestBlocks H) D C := by
  obtain ⟨src, hcall⟩ := h
  obtain ⟨j, rfl, ℓ, hcj, -, -, hC, hfg⟩ := attest_source hrun.toLocalRun hx hcall
  rw [(hrun.cutLaw x hx j _ hcj).1] at hC
  have hΦ : FrameOK (Node.frame (tr.state x j)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hx j)).1
  -- the source is the deepest candidate: the viable ancestor of a stored fast lock block
  have hcand : src ∈ SA.toFGCandidates sp (tr.state x j).ac (Node.frame (tr.state x j))
      (tr.time j) := by
    have hC' : (SA.acToFG sp (tr.state x j).ac (Node.frame (tr.state x j)) (tr.time j)).2 =
        some src := hC
    unfold SA.acToFG at hC'
    rcases hd : SA.deepest (Node.frame (tr.state x j))
      (SA.toFGCandidates sp (tr.state x j).ac (Node.frame (tr.state x j)) (tr.time j)) with
      _ | D
    · simp only [hd] at hC'
      split_ifs at hC'
    · simp only [hd] at hC'
      split_ifs at hC'
      cases hC'
      exact (SA.deepest_mem hd).1
  obtain ⟨hsv, l, hl, hlb, -, -⟩ := hcand
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hl
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : src = (Node.frame (tr.state x j)).viableAncestor B :=
    hΦ.coherent.1 hsv.1 hVt hlb.symm
  obtain ⟨L, hL, hLr, C, hCo, hLC⟩ := lock_origin hrun hnc hx j l₀ hl₀
  obtain rfl : L = B :=
    (projFG_localRun hrun hnc).coherent.1 ⟨x, hx, j, hL⟩ ⟨x, hx, j, hB.1⟩ (hLr.trans hBr.symm)
  -- the attestation names the entry of the source's state
  have hatt := (hrun.cutLaw x hx (j + 1) _ hcall).1
  have hT := createAtt_T hatt
  have hst : (Node.frame (tr.state x j)).viableAncestor L ∈ (tr.state x (j + 1)).fg.tree := by
    rw [hfg]; exact hVt.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hrun.toLocalRun hx (j + 1)) _ hst
  rw [← hEr, hET] at hT
  obtain ⟨z, hz, c, hc, CV, ho⟩ := originBefore_iff.1 hCo
  exact ⟨_, ⟨x, hx, j, hVt.1⟩, ⟨x, hx, j + 1, hst, hT.symm⟩, C, l₀.slot,
    originBefore_iff.2 ⟨z, hz, c, by omega, CV, ho⟩,
    (Anc.mono (T := tr.HonestBlocks H) (fun _ hZ => ⟨x, hx, j, hZ.1⟩) hVB).trans hLC⟩

/-! ### The store of an honest node whose honest rows have compatible sources -/

section Geometry

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

include hrun hnc hf hy in
/-- A crossing quorum has an honest row, whose source satisfies `G`. -/
private theorem frame_crossing_source_of {h₀ : Nat} (hsrc : RowsAbove tr H G y i h₀)
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y i).fg.tree) {j : Nat} (hj0 : h₀ ≤ j) (hj1 : 1 ≤ j)
    (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  rw [← store_eq hrun hy i] at hW hj2
  obtain ⟨E, hE, hEW, hEh, hET, Q, hQ, hv⟩ :=
    crossing_quorum (projFG_localRun hrun hnc) hy hW j hj1 hj2
  rw [store_eq hrun hy i] at hE hEW hEh hET hv
  obtain ⟨v, hvQ, hvH⟩ := honest_mem hf hQ
  obtain ⟨X, hX, -, a, ha, rfl, haT⟩ := hv v hvQ
  obtain ⟨D, hD, hDs⟩ := hsrc X hX a ha hvH (by rw [haT, hEh]; exact hj0)
  exact ⟨E, hE, hEW, hEh, hET, D, hD, haT ▸ hDs⟩

include hrun hnc hy in
/-- **Comparable sources of one height name one entry.** -/
private theorem source_entry_eq {D D' E E' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDD' : Compatible (tr.HonestBlocks H) D D') (hD : IsHonestSource tr H D E.root)
    (hD' : IsHonestSource tr H D' E'.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hE' : E' ∈ (tr.state y i).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h) : E = E' := by
  have key : ∀ {D D' E E' : SA.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocks H) D D' →
      IsHonestSource tr H D E.root → IsHonestSource tr H D' E'.root → E ∈ (tr.state y i).fg.tree →
      E' ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h → E = E' := by
    intro D D' E E' hDD hD hD' hE hE' hh
    obtain ⟨x, hx, k, -, hEt, hED, hEh, hET⟩ := honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
    obtain ⟨x', hx', k', hD't, hE't, hE'D', hE'h, hE'T⟩ :=
      honest_source_entry hrun hnc hD' ⟨y, hy, i, hE'⟩ rfl
    have hED' : (tr.state x' k').fg.Anc E D' :=
      honest_held_anc hrun hnc hx' ((hED.mono (fg_tree_subset_honest hx k)).trans hDD) hD't
    have hEt' := anc_mem hED' hD't
    refine held_entry_unique hrun hnc hx' hD't hED' hE'D' ?_ ?_ hE'T
    · rw [held_σ_eq hrun hnc hx' hy hEt' hE, held_σ_eq hrun hnc hx' hy hE't hE']
      exact hh
    · rw [held_σ_eq hrun hnc hx' hx hEt' hEt]
      exact hET
  rcases hDD' with h | h
  · exact key h hD hD' hE hE' hh
  · exact (key h hD' hD hE' hE hh.symm).symm

include hrun hnc hy in
/-- A block held below a source's entry height is below the entry. -/
private theorem below_entry {B D E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H D E.root) (hDB : Compatible (tr.HonestBlocks H) D B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  have hU := (projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height hrun hnc hy (honest_held_anc hrun hnc hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hU h hEDU with h' | h'
    · exact honest_held_anc hrun hnc hy h' hE
    · exact absurd h' no

include hrun in
/-- With `h_j = 0`, `Σ.J` is genesis. -/
theorem justified_genesis (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
  have hR := fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  obtain ⟨-, hcoh, hg, -⟩ := Store.accepted_tree _ _ _ _ hR
  exact hcoh.1 hJ hg (hZJ.symm.trans ((honest_held_chain hrun hy hZ).2.2 (hZj.trans h0)))

include hrun hnc hf hy in
/-- **The justification has an honest source**: at `h_j ≥ 1`, `Σ.J` is an entry block of height
`h_j`, and an honest row of its target quorum has a source satisfying `G`. -/
private theorem justified_honest_source_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hR := fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, hJ, -, ⟨Z, hZ, hZJ, hZj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hZ' := hZ
  rw [← store_eq hrun hy i] at hZ'
  obtain ⟨E, hE, hEr, hEZ, hEh, hET⟩ := J_entry (projFG_localRun hrun hnc) hy hZ' (by
    rw [store_eq hrun hy i]; omega)
  rw [store_eq hrun hy i] at hE hEr hEZ hEh hET
  have hEJ : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hZJ)
  obtain ⟨E', -, hE'Z, hE'h, hE'T, D, hD, hDs⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hZ (j := ((tr.state y i).fg.σ Z.root).hj)
      hZj.ge (by omega)
      (honest_held_chain hrun hy hZ).2.1
  have hEE' : E = E' := held_entry_unique hrun hnc hy hZ hEZ hE'Z (hEh.trans hE'h.symm) hET hE'T
  rw [← hEJ]
  exact ⟨hEh.trans hZj, hET, D, hD, hEE' ▸ hDs⟩

include hrun hnc hf hy in
/-- **No contest from genesis.** -/
private theorem frame_no_contest_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D') :
    ¬ (tr.state y i).fg.Contest := by
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable hrun.toLocalRun hy i
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hrun h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  obtain ⟨hJh, hJT, D, hD, hDs⟩ := justified_honest_source_of hrun hnc hf hy hsrc (by omega)
  obtain ⟨E, hE, hEX, hEh, hET, D', hD', hD's⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hX (j := (tr.state y i).fg.hj) le_rfl (by omega)
      (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ hR).2.1
  rw [source_entry_eq hrun hnc hy (hGG D D' hD hD') hDs hD's hJ hE (hJh.trans hEh.symm)] at hJX
  exact hJX hEX

include hrun hnc hf hy in
/-- **`Σ.J` is compatible with a block compatible with every source satisfying `G`.** -/
theorem J_compatible (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  have hU := (projFG_localRun hrun hnc).coherent
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hrun h0 hy]
    obtain ⟨z, hz, j, hBt⟩ := hB
    exact Or.inl (((Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hz j)).2.2.2 B
      hBt).mono (fg_tree_subset_honest hz j))
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of hrun hnc hf hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D := hJD.mono (fg_tree_subset_honest hx k)
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hU hJDU h

include hrun hnc hf hy in
/-- **The floor, or a crossing source above the block**: with no contest the floor is
`h_max − 1`; when it is above a held block `B`, a carrier of height `h_max` crossed it with an
honest source `D`, whose entry `E` of height `h_max − 1` extends `B`. -/
theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    split_ifs with h
    · exact absurd h (frame_no_contest_of hrun hnc hf hy hsrc hGG)
    · rfl
  by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl hle
  right
  obtain ⟨-, -, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨X, hX, hXh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  have hB1 := (honest_held_chain hrun hy hB).1
  have hZ1 := (honest_held_chain hrun hy hZ).2.1
  have hZ2 := hZm Z hZ
  obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ :=
    frame_crossing_source_of hrun hnc hf hy hsrc hX (j := (tr.state y i).fg.hmax - 1) (by omega)
      (by omega) (by omega)
  refine ⟨D, E, X, hD, hDs, hE, below_entry hrun hnc hy hB hE hDs (hGB D hD) (by omega),
    hEh.trans hfl.symm, hX, hEX, ?_⟩
  change (tr.state y i).fg.headHeightFloor ≤ _
  omega

end Geometry

/-- The scoped floor argument needs a fault bound, not the Sleepy regime. Only honest rows
whose entry height is at least the reader's `h_j` need source witnesses. -/
theorem floor_or_crossing_scoped (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      ∃ D, G D ∧ IsHonestSource tr H D a.T)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧
        (tr.state y i).fg.IsViable X :=
  floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hB

section Wrappers

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

/-- Justification provenance uses only the numerical fault bound and the supplied row sources. -/
theorem justified_honest_source_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourced tr H G y i)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root :=
  justified_honest_source_of hrun hnc hf hy (hsrc.above _) hj

/-- `frame_crossing_source` with the numerical fault bound in place of `Sleepy`. -/
theorem frame_crossing_source_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root :=
  frame_crossing_source_of hrun hnc hf hy (hsrc.above 0) hW (Nat.zero_le j) hj1 hj2

/-- **`Σ.J` is compatible with a block compatible with every source satisfying `G`**, with the
numerical fault bound; no pairwise premise on the sources. -/
theorem J_compatible_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B :=
  J_compatible hrun hnc hf hy (hsrc.above _) hGB hB

end Wrappers

end Consensus.Goldilocks.Compose

end
