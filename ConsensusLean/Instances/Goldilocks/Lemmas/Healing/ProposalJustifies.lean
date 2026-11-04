module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live

public section

/-! # Goldilocks Healing: an honest proposal justifies its parent's entry (Lemma 3′)

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §4, Lemma 3′, steps 3–6, at trace level.

* `justify_step'` (one held block): a block `X` on the parent `Pr`, and a set `S` of weight `≥ q`
  of validators, each with a target row (no timeout) for `Pr`'s entry `(h, T_h)` in `X`'s payload
  or on `Pr`'s chain, and with the finality pair `(h_j, J)` when `Pr`'s state has its previous
  height justified (pending there): `X`'s state justifies `(h, T_h)`, and at a height whose
  previous height is justified it finalizes `h_j`. A row on the chain has its bits in `σ[Pr]`
  (`Store.rows_counted`); one in the payload sets them in the counting (`Store.foldl_bits`); then
  `FGParams.justify_of_target_previousHeightNotJustified` or
  `FGParams.justify_of_target_previousHeightJustified`.
* `justify_of_rows'` (the run): an honest proposal `X` on `Pr`, where the proposer has processed
  each row before its proposal cut (the delivery premise, M1): every row is in the pool, so it is
  on `Pr`'s chain or in `proposal_attestations` (it is valid against `σ[Pr]`: it names the entry).
  Honest rows are not equivocations; the weight is that of the honest signers, no `2q − n` slack.
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Chain

open _root_.Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- **Lemma 3′ at one block** (s5 §4, steps 4–6): a held block `X` on the held parent `Pr`, and a
set `S` of weight `≥ q` of validators, each with a target row for `Pr`'s entry in `X`'s payload or
on `Pr`'s chain (with the finality pair `(h_j, J)` when `Pr`'s state has its previous height
justified and the pair is pending): `X`'s state justifies `Pr`'s entry, and at a height whose
previous height is justified it has `h_F = h_j`. By W2 (`FGParams.justify_of_target_chain`) a height
whose previous height is justified has `(h_j, J)` pending or `h_F = h_j`; in the second case the
target quorum alone passes the loose-BJ gate. -/
theorem justify_step' (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X Pr : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) (hPr : Pr ∈ (tr.store y i).tree)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = ((tr.store y i).σ Pr.root).h ∧
      a.T = ((tr.store y i).σ Pr.root).Th ∧ a.timeout = false ∧
      (((tr.store y i).σ Pr.root).previousHeightJustified →
        (((tr.store y i).σ Pr.root).hj, ((tr.store y i).σ Pr.root).J) ∈
          ((tr.store y i).σ Pr.root).pending →
        a.fin = some (((tr.store y i).σ Pr.root).hj, ((tr.store y i).σ Pr.root).J)) ∧
      (a ∈ X.fgPayload ∨ (tr.store y i).OnChain Pr a)) :
    ((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h ∧
      ((tr.store y i).σ X.root).J = ((tr.store y i).σ Pr.root).Th ∧
      (((tr.store y i).σ Pr.root).previousHeightJustified →
        ((tr.store y i).σ X.root).hF = ((tr.store y i).σ Pr.root).hj) := by
  classical
  set σ := (tr.store y i).σ Pr.root
  have hstep := step_σ hr hy hX hpar
  obtain ⟨bf, bt, brow⟩ := foldl_bits { σ with s := X.slot } X.fgPayload
  have credit : ∀ v ∈ S,
      v ∈ (X.fgPayload.foldl FG.ChainState.processAtt { σ with s := X.slot }).target ∧
      (σ.previousHeightJustified → (σ.hj, σ.J) ∈ σ.pending →
        v ∈ (X.fgPayload.foldl FG.ChainState.processAtt { σ with s := X.slot }).fin σ.hj) := by
    intro v hv
    obtain ⟨a, rfl, hah, haT, hto, hfin, hin | ⟨Z, -, hZ, haZ⟩⟩ := hrow v hv
    · obtain ⟨h1, h2⟩ := brow a hin hah haT
      exact ⟨h1 hto, fun hb hp => h2 _ (hfin hb hp) hp⟩
    · obtain ⟨h1, h2⟩ := (rows_counted hr hy i hPr Z hZ a haZ).2 hah haT
      exact ⟨bt (h1 hto), fun hb hp => bf _ (h2 _ (hfin hb hp) hp)⟩
  obtain ⟨c, -, -, -, hc⟩ :=
    chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) Pr hPr
  exact P.fg.justify_of_target_chain hc hstep
    (hS.trans (Finset.card_le_card fun v hv => (credit v hv).1))
    fun hb hp => hS.trans (Finset.card_le_card fun v hv => (credit v hv).2 hb hp)

end Chain

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An honest validator signs its own attestations. -/
theorem signAt_val (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) : att.val = y := by
  obtain ⟨src, hc⟩ := hs
  have h := (hrun.cutLaw y hy k _ hc).1
  unfold _root_.Consensus.Goldilocks.Store.attest FG.Record.createAtt at h
  split at h
  · cases h
  · split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

/-- **The rows of an honest proposal** (s5 §4, step 3): for an honest proposal `X` at the cut `kX`
on the held parent `Pr`, the FG projection is a local run, the store after the cut holds `X` and
`Pr` with the same states, and every row that the proposer processed before `kX` and that names
`Pr`'s entry is in `X`'s payload or on `Pr`'s chain. -/
theorem proposal_rows_placed (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      X ∈ (tr.projFG.store p (kX + 1)).tree ∧ Pr ∈ (tr.projFG.store p (kX + 1)).tree ∧
      (tr.post kX).fg.σ X.root = (tr.projFG.store p (kX + 1)).σ X.root ∧
      (tr.state p kX).fg.σ Pr.root = (tr.projFG.store p (kX + 1)).σ Pr.root ∧
      ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
        att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
        att ∈ X.fgPayload ∨ (tr.projFG.store p (kX + 1)).OnChain Pr att := by
  classical
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hacc, hXt, hpost⟩ := accept_of_proposesAt hrun hnc hp hX
  have hst := Compose.store_eq hrun hp (kX + 1)
  have hmono := Compose.tree_mono hrun.toLocalRun hp (Nat.le_succ kX)
  have hPrU : Pr ∈ tr.HonestBlocks H := ⟨p, hp, kX, hPr⟩
  have hXU : X ∈ tr.HonestBlocks H := ⟨p, hp, kX + 1, hXt⟩
  -- `X` is `propose_block`'s block on `d.head`, with the pool before the tick
  rcases Compose.blockCall_cases hrun.toLocalRun hp hacc with hg |
    ⟨j, x, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hX.1.2
  have hpay : X.fgPayload = (tr.state p kX).fg.proposalAttestations d.head := by
    rw [hfgj, hB]; rfl
  have hdroot : d.head.root = Pr.root := by
    have : X.parent = some d.head.root := by rw [hB]; rfl
    exact Option.some.inj (this.symm.trans hpar)
  -- `σ[Pr]` before the proposal cut
  have hσPr : (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root := by
    obtain ⟨_, _, _, _, _, _, _, hsf, _⟩ :=
      Goldilocks.Store.onBlock_fields (hrun.cutLaw p hp kX _ hacc).2.1
    have hne : Pr.root ≠ X.root := fun he => by
      obtain rfl : Pr = X := hU.1 hPrU hXU he
      exact lt_irrefl _ (hU.2 _ hPrU _ hPrU hpar)
    rw [tr.state_succ_of_call hacc, hsf, Function.update_of_ne hne]
  refine ⟨Compose.projFG_localRun hrun hnc, by rw [hst]; exact hXt, by rw [hst]; exact hmono hPr,
    by rw [hpost, hst], by rw [hst, hσPr], fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
  have hpool := processed_att_retained hrun hp hproc hk'
  rw [hst]
  by_cases hon : (tr.state p kX).fg.OnChain d.head att
  · right
    obtain ⟨Z, hZ, hZd, haZ⟩ := hon
    have hdt := mem_of_anc_right hZd hZ
    obtain rfl : d.head = Pr := hU.1 ⟨p, hp, kX, hdt⟩ hPrU hdroot
    exact ⟨Z, hmono hZ, hZd.mono hmono, haZ⟩
  · left
    rw [hpay]
    refine List.mem_filter.2 ⟨hpool, decide_eq_true ⟨Or.inl ⟨?_, ?_⟩, hon⟩⟩
    · rw [hdroot, hah]
    · rw [hdroot, haT]

/-- **Lemma 3′ at an honest proposal** (s5 §4): an honest proposal `X` at the cut `kX` on the parent
`Pr` of the proposer's tree, with parent state `σ = σ[Pr]` (the proposer's, at `kX`), and a set `S ⊆
H` of weight `≥ q` of honest validators, each of which signed a target row for `(σ.h, σ.T_h)` (with
the finality pair `(σ.h_j, σ.J)` at a height whose previous height is justified where it is pending)
that the proposer processed before `kX` (delivery): `X`'s state justifies `(σ.h, σ.T_h)`, and at a
height whose previous height is justified it has `h_F = σ.h_j`. -/
theorem justify_of_rows' (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hdel : ∀ v ∈ S, ∃ k att, tr.SignAt v k att ∧ att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
      (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
          ((tr.state p kX).fg.σ Pr.root).pending →
        att.fin = some (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J)) ∧
      ∃ k' < kX, tr.ProcessAttAt p k' att) :
    ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h ∧
      ((tr.post kX).fg.σ X.root).J = ((tr.state p kX).fg.σ Pr.root).Th ∧
      (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  classical
  obtain ⟨hfg, hXt, hPrt, hσX, hσPr, hplace⟩ := proposal_rows_placed hrun hnc hp hX hpar hPr
  have := justify_step' hfg hp hXt hPrt hpar S hS fun v hv => by
    obtain ⟨k, att, hsig, hah, haT, hto, hfin, hproc⟩ := hdel v hv
    rw [← hσPr]
    exact ⟨att, signAt_val hrun (hSH v hv) hsig, hah, haT, hto, hfin, hplace att hproc hah haT⟩
  rw [hσX, hσPr]
  exact this

end Run

end Consensus.Goldilocks.Healing

end
