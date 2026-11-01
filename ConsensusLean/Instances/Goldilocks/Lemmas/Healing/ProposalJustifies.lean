module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live

public section

/-! # Goldilocks Healing: an honest proposal justifies its parent's entry (Lemma 3′)

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §4, Lemma 3′, steps 3–6, at trace level.

* `justify_step` (one held block): a block `X` on the parent `Pr`, and a set `S` of weight `≥ q`
  of validators, each with a target row (no timeout) for `Pr`'s entry `(h, T_h)` in `X`'s payload
  or on `Pr`'s chain, and with the finality pair `(h_j, J)` when `Pr`'s state is bound (pending
  there): `X`'s state justifies `(h, T_h)`, and at a bound height it finalizes `h_j`. A row on
  the chain has its bits in `σ[Pr]` (`Store.rows_counted`); one in the payload sets them in the
  counting (`Store.foldl_bits`); then `FGParams.justify_of_target_unbound` or
  `FGParams.justify_of_target_bound`.
* `justify_of_rows` (the run): an honest proposal `X` on `Pr`, where the proposer has processed
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

/-- **Lemma 3′ at one block** (s5 §4, steps 4–6): a held block `X` on the held parent `Pr`, with
`(h_j, J)` pending at `Pr` when `Pr`'s state is bound, and a set `S` of weight `≥ q` of
validators, each with a target row for `Pr`'s entry in `X`'s payload or on `Pr`'s chain (with the
finality pair `(h_j, J)` at a bound height): `X`'s state justifies `Pr`'s entry, and at a bound
height it finalizes `h_j`. -/
theorem justify_step (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X Pr : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) (hPr : Pr ∈ (tr.store y i).tree)
    (hpar : X.parent = some Pr.root)
    (hpend : ((tr.store y i).σ Pr.root).bound →
      (((tr.store y i).σ Pr.root).hj, ((tr.store y i).σ Pr.root).J) ∈
        ((tr.store y i).σ Pr.root).pending)
    (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = ((tr.store y i).σ Pr.root).h ∧
      a.T = ((tr.store y i).σ Pr.root).Th ∧ a.timeout = false ∧
      (((tr.store y i).σ Pr.root).bound →
        a.fin = some (((tr.store y i).σ Pr.root).hj, ((tr.store y i).σ Pr.root).J)) ∧
      (a ∈ X.fgPayload ∨ (tr.store y i).OnChain Pr a)) :
    ((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h ∧
      ((tr.store y i).σ X.root).J = ((tr.store y i).σ Pr.root).Th ∧
      (((tr.store y i).σ Pr.root).bound →
        ((tr.store y i).σ X.root).hF = ((tr.store y i).σ Pr.root).hj) := by
  classical
  set σ := (tr.store y i).σ Pr.root
  have hstep := step_σ hr hy hX hpar
  obtain ⟨bf, bt, brow⟩ := foldl_bits { σ with s := X.slot } X.fgPayload
  have credit : ∀ v ∈ S,
      v ∈ (X.fgPayload.foldl FG.ChainState.processAtt { σ with s := X.slot }).target ∧
      (σ.bound → v ∈ (X.fgPayload.foldl FG.ChainState.processAtt { σ with s := X.slot }).fin
        σ.hj) := by
    intro v hv
    obtain ⟨a, rfl, hah, haT, hto, hfin, hin | ⟨Z, -, hZ, haZ⟩⟩ := hrow v hv
    · obtain ⟨h1, h2⟩ := brow a hin hah haT
      exact ⟨h1 hto, fun hb => h2 _ (hfin hb) (hpend hb)⟩
    · obtain ⟨h1, h2⟩ := (rows_counted hr hy i hPr Z hZ a haZ).2 hah haT
      exact ⟨bt (h1 hto), fun hb => bf _ (h2 _ (hfin hb) (hpend hb))⟩
  have hq : P.fg.q ≤
      (X.fgView.atts.foldl FG.ChainState.processAtt { σ with s := X.fgView.slot }).target.card :=
    hS.trans (Finset.card_le_card fun v hv => (credit v hv).1)
  by_cases hb : σ.bound
  · have hf : P.fg.q ≤
        ((X.fgView.atts.foldl FG.ChainState.processAtt { σ with s := X.fgView.slot }).fin
          σ.hj).card :=
      hS.trans (Finset.card_le_card fun v hv => (credit v hv).2 hb)
    obtain ⟨c, -, -, -, hc⟩ :=
      chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) Pr hPr
    obtain ⟨h1, h2, h3⟩ := P.fg.justify_of_target_bound hc hstep (hpend hb) hq hf
    exact ⟨h1, h2, fun _ => h3⟩
  · obtain ⟨h1, h2⟩ := P.fg.justify_of_target_unbound hstep hq hb
    exact ⟨h1, h2, fun h => absurd h hb⟩

end Chain

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- The FG projection of a run without block collisions. -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG := by
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  exact Compose.fg_projection _ _ dg H _ tr proposer hreq hrun.genesis_root_ok hrun.toLocalRun hnc

/-- An honest validator signs its own attestations. -/
private theorem signAt_val (hrun : GoldilocksRun proposer dg H tr)
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

/-- **Lemma 3′ at an honest proposal** (s5 §4): an honest proposal `X` at the cut `kX` on the
parent `Pr` of the proposer's tree, with parent state `σ = σ[Pr]` (the proposer's, at `kX`), with
`(h_j, J)` pending at `σ` when `σ` is bound, and a set `S ⊆ H` of weight `≥ q` of honest
validators, each of which signed a target row for `(σ.h, σ.T_h)` (with the finality pair
`(σ.h_j, σ.J)` at a bound height) that the proposer processed before `kX` (delivery): `X`'s state
justifies `(σ.h, σ.T_h)`, and at a bound height it finalizes `σ.h_j`. -/
theorem justify_of_rows (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (hpend : ((tr.state p kX).fg.σ Pr.root).bound →
      (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
        ((tr.state p kX).fg.σ Pr.root).pending)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hdel : ∀ v ∈ S, ∃ k att, tr.SignAt v k att ∧ att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
      (((tr.state p kX).fg.σ Pr.root).bound →
        att.fin = some (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J)) ∧
      ∃ k' < kX, tr.ProcessAttAt p k' att) :
    ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h ∧
      ((tr.post kX).fg.σ X.root).J = ((tr.state p kX).fg.σ Pr.root).Th ∧
      (((tr.state p kX).fg.σ Pr.root).bound →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  classical
  have hfg := fg_run hrun hnc
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hacc, hXt, hpost⟩ := accept_of_proposesAt hrun hnc hp hX
  rw [hpost]
  have hst := store_eq hrun hp (kX + 1)
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
  -- the rows
  have hrow : ∀ v ∈ S, ∃ a : FG.Att sp.n, a.val = v ∧
      a.h = ((tr.projFG.store p (kX + 1)).σ Pr.root).h ∧
      a.T = ((tr.projFG.store p (kX + 1)).σ Pr.root).Th ∧ a.timeout = false ∧
      (((tr.projFG.store p (kX + 1)).σ Pr.root).bound → a.fin =
        some (((tr.projFG.store p (kX + 1)).σ Pr.root).hj,
          ((tr.projFG.store p (kX + 1)).σ Pr.root).J)) ∧
      (a ∈ X.fgPayload ∨ (tr.projFG.store p (kX + 1)).OnChain Pr a) := by
    intro v hv
    obtain ⟨k, att, hsig, hah, haT, hto, hfin, k', hk', hproc⟩ := hdel v hv
    rw [hst, ← hσPr]
    refine ⟨att, signAt_val hrun (hSH v hv) hsig, hah, haT, hto, hfin, ?_⟩
    have hpool := processed_att_retained hrun hp hproc hk'
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
  have := justify_step hfg hp (i := kX + 1) (by rw [hst]; exact hXt)
    (by rw [hst]; exact hmono hPr) hpar (by rw [hst, ← hσPr]; exact hpend) S hS hrow
  rw [hst, ← hσPr] at this
  exact this

end Run

end Consensus.Goldilocks.Healing

end
