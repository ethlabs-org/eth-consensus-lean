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

-- The frame geometry is proved once over a source predicate (private `RowsAbove`) for the run,
-- the prefix up to a horizon and the induction from `s₀`; splitting would expose its cores.
set_option linter.style.longFile 1700

public section

/-! # Goldilocks under `Sleepy`: frame geometry and the frozen witness

workbench#11 §3 (S3). With the source origins relevant at a cut compatible with an origin `C` and
with each other, every target or progress quorum has an honest row (`q > f`), whose named entry is
on the origin chain; comparable sources of one height name one entry, so there is no contest from
genesis, the floor is `max(1, h_max − 1)`, and `fc_root` (`Σ.J` or `Σ.F`) is compatible with `C`.

Both are stated for a block `B` with the hypotheses the argument uses, not only for origins, so
that the proposal-adoption bootstrap (workbench#12 §4, S3P) applies them to the protected
proposal.

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
private theorem anc_mem {S : Set (NodeBlock P ACP)} {A W : NodeBlock P ACP} (h : Anc S A W)
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

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
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
private def RowsAbove (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i h₀ : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
    h₀ ≤ ((tr.state y i).fg.σ a.T).h → ∃ D, G D ∧ IsHonestSource tr H D a.T

private theorem HonestRowsSourced.above {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
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
private theorem J_compatible (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
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
private theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
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

/-! ### The frozen witness: an honest head relayed before the freeze -/

/-- Through the restarts up to cut `c`, the latest wake is at most a bound of those restarts. -/
private theorem lastWake_le {y : Fin sp.n} {a : Time} :
    ∀ {c : Nat}, (∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) →
      ∀ w : Time, tr.lastWake y c = (w : WithBot Time) → w ≤ a
  | 0, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h 0 le_rfl hr
    · simp at hw
  | c + 1, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h _ le_rfl hr
    · exact lastWake_le (fun k hk => h k (hk.trans (Nat.le_succ c))) w hw

/-- With every restart up to cut `c` at or before `a`, the deadline of `τ` is at most
`max(τ, a) + Δ'`. -/
theorem deadline_le_of_restarts {y : Fin sp.n} {c : Nat} {a : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) (τ Δ' : Time) :
    tr.deadline y c τ Δ' ≤ max τ a + Δ' := by
  unfold RunTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · change τ + Δ' ≤ max τ a + Δ'
    linarith [le_max_left τ a]
  · change max τ w + Δ' ≤ max τ a + Δ'
    linarith [max_le_max (le_refl τ) (lastWake_le h w hw)]

private theorem admitVote_stamp (A : SA.SAState sp.n) (t : Time) (v : Vote sp.n) :
    (SA.admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold SA.admitVote
  split_ifs <;> rfl

private theorem optimistic_stamp (A : SA.SAState sp.n) (Φ : SA.Frm sp.n (List (FG.Att sp.n)))
    (t : Time) : (SA.optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- At an honest slot-`(s+1)` vote, the voter's restarts up to the vote were at or before `t_s`,
and the vote is cast from `t_{s+1} = t_s + 4Δ` on. -/
theorem honest_vote_restarts (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.projAC.RestartAt y c → tr.time c ≤ sp.ts s) ∧ sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨-, hslot, hjoin, -⟩ := SA.castAt_spec hr hy hc
  have hti : sp.slot (tr.projAC.time i) = s + 1 := hslot ▸ hs
  have hjp : SA.joined sp (tr.projAC.post i) (tr.projAC.time i) := by
    unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hjoin
  refine ⟨fun c hc' hrc => ?_, ?_⟩
  · have h := ((SA.joined_awake sp) _ ro H _ tr.projAC hr y hy i ℓ hc.1 hjp).2 c hc' hrc
    rw [hti, show (((s + 1 : Nat) : Int) - 1) = (s : Int) by push_cast; ring] at h
    exact h
  · have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s : Int) + 1)).2
      (by rw [hti]; push_cast; rfl)
    have e4 : sp.ts ((s : Int) + 1) = sp.ts s + 4 * sp.Δ := by simp only [SAParams.ts]; ring
    rw [e4] at h
    exact h

/-- **An honest head of a slot at most `s` is accepted before the freeze** by an honest
slot-`(s+1)` voter whose `Σ.F` it extends: its voter accepted it (or it is genesis) by
`t_m + Δ ≤ t_s + Δ`, and `Sync` relays the acceptance (from `t_{s₀}` on; an earlier one by
`hold`) to the voter, awake since its last restart at or before `t_s`, by `t_s + 2Δ`. -/
private theorem honest_head_accepted (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s₀ : Nat} {b : Time} (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e')
    (hs' : e'.msg.slot ≤ s) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocks H) (hHdr : Hd.root = e'.msg.head)
    (hFHd : Anc (tr.HonestBlocks H) ℓ.frame.F Hd) :
    SA.AcceptedBefore tr.projAC y Hd (sp.ts s + 3 * sp.Δ) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓ', hcx, hex⟩ := hv
  -- the head is in its voter's tree, and the vote is cast by `t_m + Δ ≤ t_s + Δ`
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hcx, hex⟩
  rw [frame_of_projAC hrun hx hcx] at hHd't
  obtain rfl : Hd = Hd' :=
    ((projFG_localRun hrun hnc).coherent.1 ⟨x, hx, k, hHd't.1⟩ hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts s + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 : sp.ts (e'.msg.slot : Int) ≤ sp.ts (s : Int) := by
      unfold SAParams.ts
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs') (by linarith)
    linarith
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s := fun c hc' ⟨ℓr, hcr, hrr⟩ =>
    hrs c hc' ⟨ℓr, projAC_callAt.2 hcr, hrr⟩
  -- its voter accepted it (or it is genesis)
  have hHdx := hHd't.1
  rw [← store_eq hrun hx k] at hHdx
  rcases Store.tree_accepted (projFG_localRun hrun hnc) hx hHdx with hg | ⟨m, hm, hA⟩
  · exact Or.inl (by rw [hg]; rfl)
  have hmt : tr.time m ≤ sp.ts s + sp.Δ := (hrun.time_mono hm.le).trans hkt'
  have hFy : Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd := by
    rw [frame_of_projAC hrun hy hc.1] at hFHd; exact hFHd
  have hdl : ∀ c ≤ i, tr.deadline y c (tr.time m) sp.Δ ≤ sp.ts s + 2 * sp.Δ := fun c hc' => by
    have := deadline_le_of_restarts (fun k hk hr' => hrs' k (hk.trans hc') hr') (tr.time m) sp.Δ
    have := max_le hmt (show sp.ts s ≤ sp.ts s + sp.Δ by linarith)
    linarith
  -- `Sync` relays the acceptance to `y` before `t_s + 2Δ`
  by_cases hm₀ : sp.ts s₀ ≤ tr.time m
  swap
  · exact hold x hx m Hd (projFG_callAt.1 hA) (not_le.1 hm₀) hFHd
  have hdi : tr.deadline y i (tr.time m) sp.Δ ≤ tr.time i := by
    linarith [hdl i le_rfl]
  have delivered := hservice.elim
    (fun hwin => (sleepyWindow_iff.1 hwin).2.1.relay x hx m Hd
      (projFG_callAt.1 hA) ⟨hm₀, by linarith⟩ y hy i ⟨_, projAC_callAt.1 hc.1⟩ hdi hFy)
    (fun hsync => hsync.relay x hx m Hd (projFG_callAt.1 hA) (hrun.time_nonneg m)
      y hy i ⟨_, projAC_callAt.1 hc.1⟩ (hdi.trans hib) hdi hFy)
  obtain ⟨k', hk'i, hAy, hk't⟩ := delivered
  obtain ⟨ℓy, hcy, hby, hty⟩ := accept_next hrun.toLocalRun hy hAy
  have hk't' : tr.time k' < tr.deadline y k' (tr.time m) sp.Δ := hk't
  have := hdl k' hk'i
  exact Or.inr ⟨k' + 1, ⟨ℓy, projAC_callAt.2 hcy, hby⟩, by
    change tr.time (k' + 1) < _; rw [hty]; linarith⟩

/-- The emissions of `ac_on_tick` are made at `t_σ + Δ` only. -/
private theorem acOnTick_emits {self : Fin sp.n} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {t : Time} {e : SA.Em sp (List (FG.Att sp.n))}
    (he : e ∈ (SA.acOnTick sp self A Φ t).2) : t = sp.ts (sp.slot t) + sp.Δ := by
  unfold SA.acOnTick at he
  dsimp only at he
  split_ifs at he <;> first | assumption | simp at he

/-- **The calls that cast an honest vote**: a tick at `t_σ + Δ`, a block or a message; never a
restart, `ac_proposal` or `ac_to_fg`. -/
theorem honest_vote_call (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) :
    (ℓ.call = .tick → tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ) ∧ ℓ.call ≠ .proposal ∧
      ℓ.call ≠ .toFG ∧ ℓ.call ≠ .restart := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have he' : e ∈ ((SA.goldilocksSA sp _ ro).step y (tr.projAC.state y i) ℓ.frame
      (tr.projAC.time i) ℓ.call).2 := by rw [hx]; exact hc.2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at he'
  · exact acOnTick_emits (self := y) (A := tr.projAC.state y i) (Φ := ℓ.frame) he'
  · simp [ACInterface.step] at he'
  · simp [ACInterface.step] at he'
  · change e ∈ (SA.acRestart sp ro y _ ℓ.frame _).2 at he'
    rw [((SA.restart_state sp) _ ro y _ ℓ.frame _ hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **A block accepted before the freeze is in the voter block tree** of an honest
slot-`(s+1)` vote whose `Σ.F` it extends: it is in the voter's frame, and its stamp at the read
point is below `t_s + 3Δ` (the voter's restarts were before, and this call does not receive
it). -/
theorem accepted_voter_tree (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXU : X ∈ tr.HonestBlocks H) (hacc : SA.AcceptedBefore tr.projAC y X (sp.ts s + 3 * sp.Δ))
    (hFX : Anc (tr.HonestBlocks H) ℓ.frame.F X) :
    X ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hT : sp.ts s + 3 * sp.Δ < tr.projAC.time i := by
    change sp.ts s + 3 * sp.Δ < tr.time i; linarith
  -- in the voter's frame
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy _ _ hc.1
  have hXt : X ∈ ℓ.frame.tree := by
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · obtain rfl : X = G := hU.1 hXU hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFX
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k ≤ i := by
        by_contra h
        have := hr.time_mono (le_of_not_ge h)
        linarith
      exact SA.mem_tree_of_acceptAt sp hr hy hk hki hc.1 hFX
  -- its stamp before the call is below the freeze
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hXt hacc
    (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk) (by linarith)) (Or.inl hT.le)
  -- the call does not receive `X`, so the read point keeps that stamp
  have hne : ∀ B, ℓ.call = .block B → X.root ≠ B.root := by
    intro B hcall hXB
    have hai : tr.projAC.AcceptAt y i B := ⟨ℓ, hc.1, hcall⟩
    obtain rfl : B = X := hΦ.coherent.1 ((SA.accept_new sp hr hy hai).1 ℓ hc.1) hXt hXB.symm
    rcases hacc with hg | ⟨k, hk, hkT⟩
    · exact SA.accept_ne_genesis sp hr hy hai hg
    · obtain rfl := SA.accept_unique sp hr hy hk hai
      exact absurd hkT (not_lt.2 hT.le)
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have hnr := (honest_vote_call hrun hnc hy hc).2.2.2
  have hrp : e.readPoint.blockStamp X.root = (tr.projAC.state y i).blockStamp X.root := by
    have h1 : (tr.projAC.post i).blockStamp = e.readPoint.blockStamp := by
      rw [SA.post_of_castAt hr hy hc, optimistic_stamp, admitVote_stamp]
    have hp : tr.projAC.post i = ((SA.goldilocksSA sp _ ro).step y (tr.projAC.state y i)
        ℓ.frame (tr.projAC.time i) ℓ.call).1 := by rw [hx]
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro y (tr.projAC.state y i) hΦ (hr.time_nonneg i) ℓ.call
    rw [← h1, hp]
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_of_ne (hne B hB)]
    · rw [hoth (fun B h => hb ⟨B, h⟩) hnr]
  have hfz : SA.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by simp [SA.freeze]
  exact ⟨hXt, Or.inl (by rw [hrp, hfz]; exact hbs)⟩

/-- **An honest head of a slot at most `s` is in the voter block tree** of an honest slot-`(s+1)`
vote (workbench#11 §3, the frozen witness): it was accepted by its voter by `t_m + Δ ≤ t_s + Δ`
and relayed to `y` (joined, so awake since `t_s`, with `Σ.F` below it) before the freeze
`t_s + 3Δ`. -/
private theorem honest_head_frozen (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s₀ : Nat} {b : Time} (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e')
    (hs' : e'.msg.slot ≤ s) {Z : SA.Blk sp.n (List (FG.Att sp.n))}
    (hZ : SA.VoteExtends (tr.HonestBlocks H) e'.msg Z)
    (hFZ : Anc (tr.HonestBlocks H) ℓ.frame.F Z) :
    ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) Z W := by
  obtain ⟨Hd, hHd, hHdr, hZHd⟩ := hZ
  have hFHd := hFZ.trans hZHd
  exact ⟨Hd, accepted_voter_tree hrun hnc hy hc hs hHd
    (honest_head_accepted hrun hnc hservice hy hc hs hib hold hx hv hs' hHd hHdr hFHd) hFHd, hZHd⟩

/-! ### The source labels at a vote -/

/-- An honest signing is at a public time (a cut of a tick). (As `Persist/Attest`'s
`sign_public`.) -/
private theorem sign_at_public (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) : sp.toParams.IsPublic (tr.time j) := by
  obtain ⟨j₀, e, k, hg, -, hk⟩ := call_in_group hrun.toLocalRun hy hc
  obtain ⟨xt, rfl⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg y
    (tr.state y j₀) (tr.time j) e C a (List.mem_of_getElem? hk)
  exact hrun.tick_public y hy j₀ (tr.time j) ⟨xt, hg⟩

/-- At `t = t_{slot(t)} + Δ`, `ac_on_tick` of a joined node that has not voted in the slot casts
a vote. (As `Persist/Attest`'s `acOnTick_votes`.) -/
private theorem tick_votes (self : Fin sp.n) (A : SA.SAState sp.n)
    (Φ : SA.Frm sp.n (List (FG.Att sp.n))) {t : Time} (hj : SA.joined sp A t)
    (hv : A.votedSlot ≠ sp.slot t) (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step self A Φ t .tick).2 ≠ [] := by
  change (SA.acOnTick sp self A Φ t).2 ≠ []
  unfold SA.acOnTick
  dsimp only
  have hc : (t = sp.ts (sp.slot t) + sp.Δ) = True := eq_true ht
  simp only [hj, not_true_eq_false, hc, ↓reduceIte]
  unfold SA.tryVote
  dsimp only
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact absurd h hv
    · linarith
  · linarith [h₂.1]
  all_goals simp

/-- The AC calls of a tick: `ac_on_tick`, `ac_proposal`, `ac_to_fg`, and the own block's
`ac_on_block` when the node proposes. -/
private theorem tick_ac_call {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)} {t : Time}
    {x : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (Node.exec proposer dg y st t (.tick x)).2) :
    ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG ∨ Node.Proposes proposer y t := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y st t x
  have h' : Cut.ac ℓ ∈ (Node.onTick proposer dg y st t x).2 := h
  rw [hcs] at h'
  rcases List.mem_cons.1 h' with h' | h'
  · rw [Cut.ac.inj h']
    exact Or.inl hlt
  rcases List.mem_append.1 h' with h' | h'
  · rcases hpc with ⟨-, rfl⟩ | ⟨hp, -⟩
    · exact absurd h' List.not_mem_nil
    · exact Or.inr (Or.inr (Or.inr hp))
  · right; right; left
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> rcases List.mem_cons.1 h' with h' | h'
    all_goals first
      | (rw [Cut.ac.inj h']; exact hlu)
      | (simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false] at h')

/-- `no_optimistic_before_held_row` with `f < n/2`. -/
theorem no_optimistic_before_held_row_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} {m : Nat} (hm : tr.AcceptAt y m X) (hmi : m < i)
    {a : FG.Att sp.n} (hav : a.val ∈ H) {k : Nat} (hkm : k < m) (hsg : tr.SignAt a.val k a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hck : c < k) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hO : SA.OptimisticLockAt tr.projAC z c (s + 1) C CV) : False := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hti' : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith
  have hsi : sp.slot (tr.time i) = s + 1 := ((SA.castAt_spec hr hy hc).2.1.symm.trans hs)
  have hvi : SA.VoteAt tr.projAC y i e := ⟨ℓ, hc.1, hc.2⟩
  -- the selection is in slot `s + 1`
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hc0 : sp.ts s + 4 * sp.Δ ≤ tr.time c := by
    have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) ((s + 1 : Nat) : Int)).2
      (le_of_eq (by rw [hslc]))
    have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time c := h
    simp only [SAParams.ts] at h' ⊢
    push_cast at h'
    linarith
  have hck' := hrun.time_mono hck.le
  have hkm' := hrun.time_mono hkm.le
  have hmi' := hrun.time_mono hmi.le
  -- the row is signed at a public time, `t_{s+1}` or `t_{s+1} + Δ`
  obtain ⟨src, hsgc⟩ := hsg
  obtain ⟨q, hq⟩ := sign_at_public hrun hav hsgc
  have hq' : tr.time k = sp.Δ * q := hq
  have hq1 : 4 * (s : Int) + 4 ≤ q := by
    by_contra h
    have : q + 1 ≤ 4 * (s : Int) + 4 := by omega
    simp only [SAParams.ts] at hc0
    linarith [mul_le_mul_of_nonneg_left this hΔ.le]
  have hq2 : q ≤ 4 * (s : Int) + 5 := by
    by_contra h
    have : 4 * (s : Int) + 6 ≤ q := by omega
    simp only [SAParams.ts] at hti'
    linarith [mul_le_mul_of_nonneg_left this hΔ.le]
  rcases (show q = 4 * (s : Int) + 5 ∨ q = 4 * (s : Int) + 4 by omega) with hq5 | hq4
  · -- at `t_{s+1} + Δ`: the voter's tick there votes before the block arrives
    have hT : tr.time k = sp.ts s + 5 * sp.Δ := by
      rw [hq', hq5]; simp only [SAParams.ts]; ring
    have htm : tr.time m = sp.ts s + 5 * sp.Δ := le_antisymm (hmi'.trans hti') (hT ▸ hkm')
    have hti5 : tr.time i = tr.time m := le_antisymm (hti'.trans htm.ge) hmi'
    have hslm : sp.slot (tr.time m) = s + 1 := hti5 ▸ hsi
    rcases blockCall_cases hl hy hm with hgm | ⟨-, -, -, -, hp, -⟩
    swap
    · obtain ⟨-, hpt', -⟩ := hp
      have h1 : sp.toParams.slotOf (tr.time m) = s + 1 := hslm
      rw [h1, sp.slotTime_eq, htm] at hpt'
      simp only [SAParams.ts] at hpt'
      push_cast at hpt'
      linarith
    obtain ⟨jt, xt, hgt⟩ := hl.tick_of_awake y hy (tr.time m) (hl.time_nonneg m)
      ⟨q, by rw [htm, ← hT, hq']⟩ (hl.awake_of_call y hy m ⟨_, hm⟩)
    have hjm : jt < m := by
      rcases lt_trichotomy jt m with h | rfl | h
      · exact h
      · have := group_phase hgm hgt
        simp [Node.Event.phase] at this
      · have := hl.phase_order y hy y hy m jt _ _ _ hgm hgt h
        simp [Node.Event.phase] at this
    -- the tick's first cut is `ac_on_tick`
    obtain ⟨ℓt, pc, uc, hlt, hcs, -, -⟩ :=
      @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y (tr.state y jt) (tr.time m) xt
    have hlen : 0 < (Node.exec proposer dg y (tr.state y jt) (tr.time m) (.tick xt)).2.length := by
      change 0 < (Node.onTick proposer dg y (tr.state y jt) (tr.time m) xt).2.length
      rw [hcs]; simp
    obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hgt.2.1 0 hlen
    have hct : tr.CallAt y jt (.ac ℓt) := by
      refine ⟨hn₀, ?_⟩
      simp only [Nat.add_zero] at hl₀
      rw [hl₀]
      change some (Node.onTick proposer dg y (tr.state y jt) (tr.time m) xt).2[0] = _
      simp [hcs]
    simp only [Nat.add_zero] at ht₀
    have hpt0 : tr.projAC.CallAt y jt ℓt := projAC_callAt.2 hct
    by_cases hvs : (tr.projAC.state y jt).votedSlot = ((s + 1 : Nat) : Int)
    · obtain ⟨j, hj, e', hv', hes'⟩ := SA.cast_of_votedSlot hr hy jt (s + 1) hvs
      have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr y hy j i e' e hv' hvi
        (hes'.trans hs.symm)).1
      omega
    -- joined at the tick: its restarts are at or before `t_s`
    have hjr : tr.JoinedAt y (tr.time m) := by
      intro k' hk' hk'T
      refine ⟨by change 0 < sp.slot (tr.time m); omega, ?_⟩
      change tr.time k' ≤ sp.toParams.slotTime (sp.slot (tr.time m) - 1)
      rw [hslm, Nat.add_sub_cancel, sp.slotTime_eq]
      rcases le_or_gt k' i with hki | hki
      · have := hrs k' hki (projAC_restartAt.2 hk')
        simp only [SAParams.ts] at this
        exact this
      · obtain ⟨u, -, hu, -, hbefore⟩ := hl.sleep_of_restart y hy k' hk'
        have := hbefore i hki ⟨_, projAC_callAt.1 hc.1⟩
        linarith
    have hnr : ¬ tr.RestartAt y jt := by
      rintro ⟨ℓk, hck, hkr⟩
      have h₁ := hck.2
      rw [hct.2] at h₁
      cases h₁
      rw [hlt] at hkr
      cases hkr
    have hjoined : SA.joined sp (tr.projAC.state y jt) (tr.time m) := by
      rw [projAC_state hl hy]
      exact ((joined_projection sp ro dg H tr proposer hrun y hy (tr.time m)).2.1 jt ⟨_, hct⟩ hnr
        ht₀).mp hjr
    have hexec := hr.exec jt ℓt hpt0.2 (hpt0.1 ▸ hy)
    rw [hpt0.1, hlt] at hexec
    have hne := tick_votes (ro := ro) y (tr.projAC.state y jt) ℓt.frame hjoined
      (by rw [hslm]; exact hvs)
      (by rw [hslm, htm]; simp only [SAParams.ts]; push_cast; ring)
    rw [show tr.projAC.time jt = tr.time m from ht₀] at hexec
    rw [hexec] at hne
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
    have hsl₀ : e₀.msg.slot = sp.slot (tr.time m) := (SA.castAt_spec hr hy ⟨hpt0, he₀⟩).2.1.trans
      (by rw [show tr.projAC.time jt = tr.time m from ht₀])
    have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr y hy jt i e₀ e ⟨ℓt, hpt0, he₀⟩ hvi
      (hsl₀.trans (hslm.trans hs.symm))).1
    omega
  · -- at `t_{s+1}`: the honest optimistic voters are the slot's proposer
    have hT0 : tr.time k = sp.ts s + 4 * sp.Δ := by
      rw [hq', hq4]; simp only [SAParams.ts]; ring
    have htc : tr.time c = tr.time k := le_antisymm hck' (hT0 ▸ hc0)
    obtain ⟨gx, ex, kx, hgx, hkeq, hkx⟩ := call_in_group hl hav hsgc
    obtain ⟨xt, rfl⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg a.val
      (tr.state a.val gx) (tr.time k) ex src a (List.mem_of_getElem? hkx)
    have hklen := (List.getElem?_eq_some_iff.1 hkx).1
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (SA.deepest_mem hsel).1.2.1
    rw [hslc] at h34
    have hprop : ∀ u ∈ SA.optimisticVoters sp AO ℓO.frame (s + 1) C, u ∈ H →
        u = proposer (sp.toParams.slotOf (tr.time k)) ∧
          ∃ j' ≤ c, ∃ e', SA.VoteAt tr.projAC u j' e' ∧ e'.msg.slot = s + 1 := by
      rintro u ⟨v, hv, hvu, -⟩ huH
      subst hvu
      obtain ⟨hvs, j', hj', e', ⟨ℓ', hc', he'⟩, rfl⟩ :=
        SA.optimisticPoint_pool_vote hr' hz hpt hv huH
      refine ⟨?_, j', hj', e', ⟨ℓ', hc', he'⟩, hvs⟩
      -- the vote is cast at `t_{s+1}`
      have hsl' : sp.slot (tr.time j') = s + 1 :=
        (SA.castAt_spec hr huH ⟨hc', he'⟩).2.1.symm.trans hvs
      have htj : tr.time j' = tr.time k := by
        refine le_antisymm ((hrun.time_mono hj').trans (htc ▸ le_rfl)) ?_
        have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg j') ((s + 1 : Nat) : Int)).2
          (le_of_eq (congrArg (Nat.cast : Nat → Int) hsl'.symm))
        have h' : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time j' := h
        simp only [SAParams.ts] at h'
        push_cast at h'
        rw [hT0]; simp only [SAParams.ts]; linarith
      -- in a tick or a restart: before the signer's tick, or in it
      obtain ⟨g, eu, k₁, hg, hjeq, hk₁⟩ := call_in_group hl huH (projAC_callAt.1 hc')
      rw [htj] at hg hk₁
      have hph : eu.phase ≤ 1 := by
        rcases lt_trichotomy g gx with h | rfl | h
        · have := hl.phase_order _ huH _ hav g gx (tr.time k) eu _ hg hgx h
          simpa [Node.Event.phase] using this
        · obtain ⟨_, hn₁⟩ := (group_call hg).1
          obtain ⟨_, hn₂⟩ := (group_call hgx).1
          have hnode : (e'.msg).val = a.val := hn₁.1.symm.trans hn₂.1
          rw [hnode] at hg
          rw [group_phase hg hgx]
          simp [Node.Event.phase]
        · exact absurd (group_start hgx hg h.le (by omega)) h.ne'
      have hmem := List.mem_of_getElem? hk₁
      obtain ⟨htick, hnp, hnt, hnr⟩ := honest_vote_call hrun hnc huH ⟨hc', he'⟩
      cases eu with
      | tick xu =>
        rcases tick_ac_call hmem with h | h | h | hp
        · have h5 := htick h
          rw [hsl', htj, hT0] at h5
          simp only [SAParams.ts] at h5
          push_cast at h5
          linarith
        · exact absurd h hnp
        · exact absurd h hnt
        · exact hp.2.2.symm
      | restart =>
        simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hmem
        exact absurd (by rw [hmem]) hnr
      | _ => simp [Node.Event.phase] at hph
    -- counting: `3n ≤ 4(f + 1)` and `2f < n` leave `n = 1`
    have hsub : SA.optimisticVoters sp AO ℓO.frame (s + 1) C ⊆
        Hᶜ ∪ {proposer (sp.toParams.slotOf (tr.time k))} := fun u hu => by
      by_cases huH : u ∈ H
      · exact Or.inr (hprop u hu huH).1
      · exact Or.inl huH
    have hcard := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (by rw [Set.ncard_singleton]))
    have hn1 : sp.n = 1 := by omega
    obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero
      (show (SA.optimisticVoters sp AO ℓO.frame (s + 1) C).ncard ≠ 0 by omega)
    have huH : u ∈ H := by
      by_contra h
      have := (Set.ncard_pos (Set.toFinite Hᶜ)).2 ⟨u, h⟩
      omega
    obtain ⟨-, j', hj', e', hv', hs'⟩ := hprop u hu huH
    obtain rfl : u = y := Fin.ext (by have := u.isLt; have := y.isLt; omega)
    have := (SA.one_vote_per_slot sp _ ro H _ tr.projAC hr u huH j' i e' e hv' hvi
      (hs'.trans hs.symm)).1
    omega

/-- **Sources at a vote have labels at most `s`** (workbench#11 §3, R4; §4 "Extend the vote
frontier"): at an honest slot-`(s+1)` vote, every honest row on a block the voter holds has a
source below an origin of label at most `s`. A regular origin of label `l` is written at
`t_l + 6Δ`, after the vote unless `l < s`; an optimistic one of label `l ≥ s + 2` after
`t_{s+2}`; label `s + 1` is `no_optimistic_before_held_row`. -/
private theorem vote_row_source (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C j, OriginBefore tr H C j i ∧ j ≤ s ∧ Anc (tr.HonestBlocks H) D C := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨m, hmi, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, hDU, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  obtain ⟨z, hz, c, hck, CV, hRO⟩ := originBefore_iff.1 hC
  refine ⟨D, hDU, hDs, C, l, originBefore_iff.2 ⟨z, hz, c, by omega, CV, hRO⟩, ?_, hDC⟩
  -- the vote is cast by `t_{s+1} + Δ`, after the origin's event
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith
  have hci : tr.time c ≤ tr.time i := hrun.time_mono (by omega)
  by_contra hl
  have hl' : (s : Int) + 1 ≤ (l : Int) := by exact_mod_cast Nat.lt_of_not_le hl
  rcases hRO with ⟨ℓR, ⟨-, -, htR, -⟩, -⟩ | hO
  · -- a regular origin of label `l > s` is written at `t_l + 6Δ ≥ t_{s+1} + 6Δ`
    have htR' : tr.time c = sp.ts (l : Int) + 6 * sp.Δ := htR
    simp only [SAParams.ts] at htR' hti
    linarith [mul_le_mul_of_nonneg_left hl' hΔ.le]
  · rcases Nat.lt_or_ge l (s + 2) with hl2 | hl2
    · obtain rfl : l = s + 1 := by omega
      exact no_optimistic_before_held_row_of hrun hnc hf hy hc hs hm hmi hav hkm hsg hz hck hO
    · -- an optimistic origin of label `l ≥ s + 2` is selected from `t_l ≥ t_s + 8Δ` on
      obtain ⟨ℓO, A, -, hslot, -⟩ := hO
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) (l : Int)).2
        (le_of_eq (by rw [hslot]))
      have h' : sp.ts (l : Int) ≤ tr.time c := h
      have hl2' : (s : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl2
      simp only [SAParams.ts] at h' hti
      linarith [mul_le_mul_of_nonneg_left hl2' hΔ.le]

/-- **S3 at full reads, over sources `G`**: with `f < n/2`, the honest rows at heights `≥ h_j`
sourced by `G`, the sources pairwise compatible and compatible with `B`, a held block `B` is at or
below `fc_root` or in the full viable tree. -/
private theorem held_viable_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  -- the frame
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `fc_root` (`Σ.J` or `Σ.F`) is compatible with `B`
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact J_compatible hrun hnc hf hy hsrc hGB (hsU hBt.1)
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt.1 with hle | ⟨-, E, X, -, -, -, hBE,
    -, hX, hEX, hXv⟩
  · exact ⟨hBt, hΦfB, B, hBt, ⟨hBt.1, hBt.2, Anc.mono hΦs hΦfB, hle⟩, .refl⟩
  · have hBX := hBE.trans hEX
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩

/-- Sources below pairwise compatible tips (`Q`) are pairwise compatible, and compatible with a
block compatible with every tip. -/
private theorem below_tips_compatible (hU : Coherent (tr.HonestBlocks H))
    {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hQQ : ∀ C C', Q C → Q C' → Compatible (tr.HonestBlocks H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hQB : ∀ C, Q C → Compatible (tr.HonestBlocks H) B C) :
    (∀ D D', (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D C) → (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D' C) →
      Compatible (tr.HonestBlocks H) D D') ∧
    ∀ D, (∃ C, Q C ∧ Anc (tr.HonestBlocks H) D C) → Compatible (tr.HonestBlocks H) D B := by
  refine ⟨?_, ?_⟩
  · rintro D D' ⟨C, hC, hDC⟩ ⟨C', hC', hDC'⟩
    rcases hQQ C C' hC hC' with h | h
    · exact Anc.total hU (hDC.trans h) hDC'
    · exact Anc.total hU hDC (hDC'.trans h)
  · rintro D ⟨C, hC, hDC⟩
    rcases hQB C hC with h | h
    · exact Anc.total hU hDC h
    · exact Or.inl (hDC.trans h)

/-- `held_origin_viable` with `f < n/2` and the origins whose event precedes the cut pairwise
compatible. -/
private theorem held_origin_viable_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hP : ∀ C s C' s', OriginBefore tr H C s i → OriginBefore tr H C' s' i →
      Compatible (tr.HonestBlocks H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ l, OriginBefore tr H C l i) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    intro X hX a ha hav
    obtain ⟨m, hm, -, k, hk, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
    obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
    obtain ⟨z, hz, k', hk', CV, h⟩ := originBefore_iff.1 hC
    exact ⟨D, ⟨C, ⟨l, originBefore_iff.2 ⟨z, hz, k', by omega, CV, h⟩⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU (Q := fun C => ∃ l, OriginBefore tr H C l i)
    (fun C C' ⟨l, hC⟩ ⟨l', hC'⟩ => hP C l C' l' hC hC') (fun C ⟨l, hC⟩ => hBc C l hC)
  exact held_viable_of hrun hnc hf hy i (hsrc.above _) hGG hGB hBt

/-- **S3 at full reads**: once all origins compare, a block `B` that an honest node holds before
cut `i` and that is compatible with every origin whose event precedes the cut (an origin itself;
a protected proposal before its update, workbench#12 §4 S3P) is at or below its `fc_root` or in
its full viable tree. -/
theorem held_origin_viable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (hP : ∀ s, OriginsBelow tr H s) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_sleepy hsl) hy i
    (fun C l C' l' hC hC' => originsBelow_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) hC.origin hC'.origin) hBc hBt

/-- **S3 at full reads up to `b`**: at a cut within `b`, once the origins within `b` compare, a
block `B` that an honest node holds before the cut and that is compatible with every origin whose
event precedes the cut is at or below its `fc_root` or in its full viable tree. -/
theorem held_origin_viable_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_prefix hpre) hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- Full-read viability uses the finite frontier and fault bound, with no service premise. -/
theorem held_origin_viable_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc hf hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- **S3 at votes, over sources `G`, on a window**: at an honest slot-`(s+1)` vote at a time
`≤ b`, with the honest rows at heights `≥ h_j` sourced by `G` (sources pairwise compatible,
compatible with `B`, each extended by an honest vote of a slot `≤ s`) and the heads accepted
before `t_{s₀}` caught up (`hold`), a block `B` that an honest slot-`s` vote extends is in the
viable tree of the voter block tree, or at or below `fc_root`. -/
private theorem vote_frame_of {s₀ : Nat} {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    (hGW : ∀ D, G D → ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot ≤ s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hfr := frame_of_projAC hrun hy hc.1
  have hΦ : FrameOK ℓ.frame := by
    rw [hfr]; exact (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rw [hfr]; exact fun X hX => ⟨y, hy, i, hX.1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `Σ.J`, `Σ.F` and `fc_root` are compatible with `B`
  have hJ := J_compatible hrun hnc hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.2.1).mono
      hsU
    rcases hJ with h | h
    · exact Or.inl (hFJ.trans h)
    · exact Anc.total hU hFJ h
  have hfc : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  have hv := vote_viable hrun hnc hy hc (B := B) ⟨hF, hJ⟩
  rw [hs] at hv
  apply hv
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  left
  have hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
  -- the relayed honest slot-`s` head extending `B`
  obtain ⟨x, hx, k, e', hve, hs', hext⟩ := hw
  obtain ⟨W, hW, hBW⟩ :=
    honest_head_frozen hrun hnc hservice hy hc hs hib hold hx hve hs'.le hext hFB
  have hWt : W ∈ (tr.state y i).fg.tree := by
    have := hW.1; rw [hfr] at this; exact this.1
  have hBW' := honest_held_anc hrun hnc hy hBW hWt
  have hBt := anc_mem hBW' hWt
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt with hle | ⟨D, E, X, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact ⟨W, hW, hBW, hle.trans (honest_held_height hrun hnc hy hBW').1⟩
  · -- the honest head of a vote extending the crossing source
    obtain ⟨x', hx', k', e'', hve', hs'', hext'⟩ := hGW D hD
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    have hFD : Anc (tr.HonestBlocks H) ℓ.frame.F D := hFB.trans ((hBE.mono hsU).trans hEDU)
    obtain ⟨W', hW', hDW'⟩ := honest_head_frozen hrun hnc hservice hy hc hs hib hold hx' hve' hs''
      hext' hFD
    have hW't : W' ∈ (tr.state y i).fg.tree := by
      have := hW'.1; rw [hfr] at this; exact this.1
    have hEW' := honest_held_anc hrun hnc hy (hEDU.trans hDW') hW't
    refine ⟨W', hW', (hBE.mono hsU).trans (hEDU.trans hDW'), ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    rw [← hEh]
    exact (honest_held_height hrun hnc hy hEW').1

/-- **S3 at votes up to `b` (the frozen witness)**: at an honest slot-`(s+1)` vote at a time
`≤ b`, a block `B` of the honest blocks that is compatible with every origin within `b` of label
at most `s` and that some honest slot-`s` vote extends is in the viable tree of the voter block
tree, or at or below `fc_root` (inside the honest blocks). -/
theorem vote_frame_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf := two_faults_lt_of_prefix hpre
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of hrun hnc (Or.inl hpre.window) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB
    (let ⟨x, hx, k, e', hv, hs', hext⟩ := hw; ⟨x, hx, k, e', hv, hs', hext⟩)
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_upTo hrun hnc hpre hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

/-- The frozen witness at a vote needs only recipient service within its finite horizon. -/
theorem vote_frame_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of (s₀ := 0) hrun hnc (Or.inr hsync) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB hw
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_before hrun hnc hb hsync hfb hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

end Consensus.Goldilocks.Compose

end
