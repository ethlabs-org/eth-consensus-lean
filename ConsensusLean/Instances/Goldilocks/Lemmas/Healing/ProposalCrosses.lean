module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned

public section

/-! # Goldilocks Healing: an honest proposal crosses the entry

The handoff of `E_0`, at block and trace level. The paper-conditional inputs stay premises: the
set `S` of honest reporters of the entry, their attestations, and the slot `s**` of the
proposal.

* `rows_prog`: the attestations on the chain of a held block that name its entry have set their
  progress bits (targets and timeouts), as `Store.rows_counted` does for the target bits.
* `cross_step` (one held block): attestations of weight `≥ q` that name `Pr`'s entry, in `X`'s
  payload or on `Pr`'s chain, and `X.slot ≥ ThSlot + δ_t`: `X` enters the next height
  (`FGParams.cross_of_progress`), as its own entry; the new height has its previous height justified
  exactly when `X` justified the old one, and then, at an old height whose previous height
  is justified, `h_F = h_j`.
* `cross_of_rows`, `cross_of_signed_rows`: the same at an honest proposal, with the attestations
  processed before the cut, or signed by `v` with `v ≥ ḡ`, `v + Δ_F ≤ t_{kX}` (`rows_delivered`).
* `handoff_slot_le`: `s** ≤ s_h + δ_t + g` when `δ_t ≥ c + g − 1`.

An early crossing (`X.slot < ThSlot + δ_t`) justifies: `FGParams.early_cross_justifies`, and with
target attestations `justify_of_signed_rows'`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Chain

open _root_.Consensus.Goldilocks.Store

/-- Counting an attestation only adds progress bits; one on the entry sets its bit. -/
private theorem processAtt_prog {n : Nat} (σ : FG.ChainState n) (a : FG.Att n) :
    σ.prog ⊆ (σ.processAtt a).prog ∧
      (a.h = σ.h → a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
  unfold FG.ChainState.processAtt
  rcases a.fin with _ | pr
  · dsimp only
    split_ifs <;> simp_all
  · dsimp only
    split_ifs <;> simp_all

/-- Counting a list of attestations only adds progress bits; each one on the entry sets its
bit. -/
private theorem foldl_prog {n : Nat} (σ : FG.ChainState n) (atts : List (FG.Att n)) :
    σ.prog ⊆ (atts.foldl FG.ChainState.processAtt σ).prog ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.Th →
        a.val ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact ⟨subset_rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨p1, r1⟩ := processAtt_prog σ b
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [b]
    have hh : (σ.processAtt b).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt b).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    obtain ⟨p2, r2⟩ := ih (σ.processAtt b)
    refine ⟨p1.trans p2, fun a ha hah haT => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact p2 (r1 hah haT)
    · exact r2 a ha (hah.trans hh.symm) (haT.trans hT.symm)

/-- An accepted block's attestations are not above its parent's height; the block keeps the height
and entry, with the progress bits of the counting, or enters the next height. -/
private theorem step_prog {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (∀ a ∈ B.atts, a.h ≤ σ.h) ∧
      ((σ'.h = σ.h ∧ σ'.Th = σ.Th ∧
        σ'.prog = (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).prog) ∨
      σ'.h = σ.h + 1) := by
  obtain ⟨⟨-, hv⟩, he⟩ := gp.stateTransition_eq_some.1 h
  refine ⟨fun a ha => ?_, ?_⟩
  · rcases (hv a ha).2 with ⟨h1, -⟩ | ⟨pr, -, -, -, h2⟩
    · exact h1.le
    · exact h2.le
  obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he ⊢
  subst he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases _
  rcases hcase with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨rfl, rfl, rfl⟩

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- The attestations on the chain of a held block are not above its height, and those on its entry
(targets and timeouts) have set their progress bits. -/
theorem rows_prog (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat)
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y m).tree) :
    ∀ X, (tr.store y m).Anc X W → ∀ r ∈ X.fgPayload, r.h ≤ ((tr.store y m).σ W.root).h ∧
      (r.h = ((tr.store y m).σ W.root).h → r.T = ((tr.store y m).σ W.root).Th →
        r.val ∈ ((tr.store y m).σ W.root).prog) := by
  have hg := (accepted_tree P ACP acp₀ _ (store_reachable hr hy m)).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨hle, hcase⟩ := step_prog (step_σ hr hy h2 hp)
    intro X hX r hrX
    have hX' := Store.anc_parent h1 hp hX
    have hrh : r.h ≤ ((tr.store y m).σ W'.root).h := by
      rcases hX' with rfl | hX'
      · exact hle r hrX
      · exact (ih X hX' r hrX).1
    rcases hcase with ⟨hh, hT, hpg⟩ | hh
    · refine ⟨hh ▸ hrh, fun hrh' hrT => ?_⟩
      rw [hh] at hrh'
      rw [hT] at hrT
      obtain ⟨bp, brow⟩ :=
        foldl_prog { (tr.store y m).σ W'.root with s := W.slot } W.fgView.atts
      rw [hpg]
      rcases hX' with rfl | hX'
      · exact brow r hrX hrh' hrT
      · exact bp ((ih X hX' r hrX).2 hrh' hrT)
    · exact ⟨by omega, fun h' => by omega⟩

/-- **The crossing at one block**: a held block `X` on the held parent `Pr`, at a slot at least
`δ_t` after `Pr`'s entry, and a set `S` of weight `≥ q` of validators, each with an attestation
(target or timeout) for `Pr`'s entry in `X`'s payload or on `Pr`'s chain: `X` enters the next height
as its own entry; it has its previous height justified exactly when `X` justified `Pr`'s entry, and
then, at a height whose previous height is justified, `h_F = h_j`. -/
theorem cross_step (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X Pr : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) (hPr : Pr ∈ (tr.store y i).tree)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = ((tr.store y i).σ Pr.root).h ∧
      a.T = ((tr.store y i).σ Pr.root).Th ∧ (a ∈ X.fgPayload ∨ (tr.store y i).OnChain Pr a))
    (hage : ((tr.store y i).σ Pr.root).ThSlot + P.fg.δt ≤ X.slot) :
    ((tr.store y i).σ X.root).h = ((tr.store y i).σ Pr.root).h + 1 ∧
      ((tr.store y i).σ X.root).Th = X.root ∧
      (((tr.store y i).σ X.root).previousHeightJustified ↔
        ((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h) ∧
      (((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h →
        ((tr.store y i).σ Pr.root).previousHeightJustified →
        ((tr.store y i).σ X.root).hF = ((tr.store y i).σ Pr.root).hj) := by
  classical
  set σ := (tr.store y i).σ Pr.root
  have hstep := step_σ hr hy hX hpar
  obtain ⟨bp, brow⟩ := foldl_prog { σ with s := X.slot } X.fgPayload
  have hq : P.fg.q ≤
      (X.fgView.atts.foldl FG.ChainState.processAtt { σ with s := X.fgView.slot }).prog.card :=
    hS.trans (Finset.card_le_card fun v hv => by
      obtain ⟨a, rfl, hah, haT, hin | ⟨Z, -, hZ, haZ⟩⟩ := hrow v hv
      · exact brow a hin hah haT
      · exact bp ((rows_prog hr hy i hPr Z hZ a haZ).2 hah haT))
  have hh := P.fg.cross_of_progress hstep hq hage
  obtain ⟨c, -, -, -, hc⟩ :=
    chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) Pr hPr
  obtain ⟨-, -, -, -, h5⟩ := FG.height_step P.fg _ _ _ _ hc hstep
  obtain ⟨hT, hiff, -⟩ := h5 hh
  exact ⟨hh, hT, hiff, fun hj hb => P.fg.previousHeightJustified_justify_finalizes hstep hb hj⟩

end Chain

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The crossing at an honest proposal**: an honest proposal `X` at the cut `kX` on the parent
`Pr` of the proposer's tree, `σ = σ[Pr]`, at a slot `≥ σ.ThSlot + δ_t`, and a set `S ⊆ H` of weight
`≥ q` of honest validators, each of which signed an attestation (target or timeout) for
`(σ.h, σ.T_h)` that the proposer processed before `kX`: `X` enters the next height as its own entry;
it has its previous height justified exactly when `X` justified `(σ.h, σ.T_h)`, and then, at a
height whose previous height is justified, `h_F = σ.h_j`. -/
theorem cross_of_rows (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hdel : ∀ v ∈ S, ∃ k att, tr.SignAt v k att ∧ att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ ∃ k' < kX, tr.ProcessAttAt p k' att)
    (hage : ((tr.state p kX).fg.σ Pr.root).ThSlot + sp.toParams.fg.δt ≤ X.slot) :
    ((tr.post kX).fg.σ X.root).h = ((tr.state p kX).fg.σ Pr.root).h + 1 ∧
      ((tr.post kX).fg.σ X.root).Th = X.root ∧
      (((tr.post kX).fg.σ X.root).previousHeightJustified ↔
        ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h) ∧
      (((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h →
        ((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  obtain ⟨hfg, hXt, hPrt, hσX, hσPr, hplace⟩ := proposal_rows_placed hrun hnc hp hX hpar hPr
  have := cross_step hfg hp hXt hPrt hpar S hS (fun v hv => by
      obtain ⟨k, att, hsig, hah, haT, hproc⟩ := hdel v hv
      rw [← hσPr]
      exact ⟨att, signAt_val hrun (hSH v hv) hsig, hah, haT, hplace att hproc hah haT⟩)
    (by rw [← hσPr]; exact hage)
  rw [hσX, hσPr]
  exact this

end Run

end Consensus.Goldilocks.Healing

end
