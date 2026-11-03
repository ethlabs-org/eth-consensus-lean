module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.HealedClient
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Justified

public section

/-! # Goldilocks Refinement: the finality pair of an entry state (L5.4, fin-pair link)

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §5, L5.4. The premise `hsig` of
`window_justifies_of_lock` asks that each honest target row for `(h, T)` carries, as its finality
pair, `(σ.h_j, σ.J)` of every held honest state `σ` with `σ.T_h = T` that has its previous height
justified with that pair pending. The row from `awake_signs_target` carries `Λ.finality_pair(σe)` of
the entry state `σe = σ[T]`. These agree exactly when the record permits `(σ.h_j, σ.J)`:

* `J_hj_eq_of_anc`: along ancestry at one height, `J` and `h_j` stay (only a justification, which
  advances the height, sets them). `pending` is not constant within a height (the prune of
  `finalize` drops pairs), but `finality_pair` at an entry whose previous height is justified does
  not read it.
* `entry_J_hj`: the entry block of a held block has the same `h`, `T_h`, `J`, `h_j`.
* `finalityPair_eq_iff_of_previousHeightJustified`: for two states with the same `h`, `h_j`, `J`,
  previous height justified, `finality_pair(σe) = (σ.h_j, σ.J)` iff the record permits `(σ.h_j,
  σ.J)`.
* `finalityPair_entry_iff`: the trace form (honest `y`, `p`, any cuts); the pending premise of
  `hsig` is not needed.
* `finalityPair_entry_healed`: under `HealedRecords`, with `h₀ ≤ σ.h_j` and `σ.J = E σ.h_j`.
* `J_eq_entry_of_healed`: under `HealedRecords` and `f < q`, `σ.J = E σ.h_j` when
  `h₀ ≤ σ.h_j` and `1 ≤ σ.h_j` (an honest row of the target quorum names `E σ.h_j`).
* `finalityPair_entry_healed'`: `finalityPair_entry_healed` without the `J` premise.

Counterexample shape for dropping `permits`: `y`'s record has `target[σ.h_j] = some T' ≠ σ.J`
(an own target row at `h_j` for another block, possible below `h₀`), so `finality_pair(σe)` is
`⊥` while `σ` has its previous height justified. -/

namespace Consensus.Goldilocks.Healing

/-- One accepted block that keeps the height keeps `J` and `h_j`. -/
private theorem step_J_of_h {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') (hh : σ'.h = σ.h) :
    σ'.J = σ.J ∧ σ'.hj = σ.hj := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hh ⊢
  dsimp only at hh ⊢
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at hh ⊢
  · simp [FG.ChainState.advance] at hh
  · simp [FG.ChainState.advance] at hh
  · exact ⟨rfl, rfl⟩

/-- **Along ancestry at one height, `J` and `h_j` stay.** -/
theorem J_hj_eq_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) :
    (st.σ W.root).J = (st.σ A.root).J ∧ (st.σ W.root).hj = (st.σ A.root).hj := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail hAY hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    have h₁ := σ_h_le_of_anc hr hAY
    rcases stateTransition_bits ht with ⟨hh', -⟩ | ⟨hh', -⟩
    · obtain ⟨hJ, hj⟩ := step_J_of_h ht hh'
      rw [hJ, hj]
      exact ih (by omega)
    · omega

/-- **The entry block of a held block** has its height, entry, `J` and `h_j`. -/
theorem entry_J_hj {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).Th ∧ st.Anc E W ∧
      (st.σ E.root).h = (st.σ W.root).h ∧ (st.σ E.root).Th = (st.σ W.root).Th ∧
      (st.σ E.root).J = (st.σ W.root).J ∧ (st.σ E.root).hj = (st.σ W.root).hj := by
  obtain ⟨⟨E, hE, hEr, hEW, hEh, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr _ hW
  obtain ⟨hJ, hj⟩ := J_hj_eq_of_anc hr hEW hEh.symm
  exact ⟨E, hE, hEr, hEW, hEh, hET, hJ.symm, hj.symm⟩

/-- **`finality_pair` at an entry whose previous height is justified.** For states with the same
`h`, `h_j` and `J`, with `σ` whose previous height is justified, `finality_pair(σe) = (σ.h_j, σ.J)`
iff the record permits `(σ.h_j, σ.J)`. -/
theorem finalityPair_eq_iff_of_previousHeightJustified {n : Nat} {Λ : FG.Record}
    {σe σ : FG.ChainState n}
    (hh : σe.h = σ.h) (hj : σe.hj = σ.hj) (hJ : σe.J = σ.J) (hb : σ.previousHeightJustified) :
    Λ.finalityPair σe = some (σ.hj, σ.J) ↔ Λ.permits σ.hj σ.J := by
  have hb' : σe.previousHeightJustified := by
    unfold FG.ChainState.previousHeightJustified at hb ⊢
    omega
  by_cases hp : Λ.permits σ.hj σ.J <;> simp [FG.Record.finalityPair, hb', hj, hJ, hp]

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The fin-pair link (trace form).** Let `σe = σ_y[σ_y[C].T_h]` be the entry state of a held
block `C` of an honest `y` at cut `k`, and `σ = σ_p[Pr]` a held honest state (any `p`, `k'`) with
`σ.T_h = σe.T_h`, whose previous height is justified. Then `finality_pair(σe) = (σ.h_j, σ.J)` iff
the record permits `(σ.h_j, σ.J)`, for every record `Λ`. -/
theorem finalityPair_entry_iff (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state y k).fg.tree)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree)
    (hT : ((tr.state p k').fg.σ Pr.root).Th =
      ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)
    (hb : ((tr.state p k').fg.σ Pr.root).previousHeightJustified) (Λ : FG.Record) :
    Λ.finalityPair ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th) =
        some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) ↔
      Λ.permits ((tr.state p k').fg.σ Pr.root).hj ((tr.state p k').fg.σ Pr.root).J := by
  obtain ⟨Ey, hEy, hEyr, -, -, hEyT, -, -⟩ :=
    Healing.entry_J_hj (Compose.fg_reachable hrun.toLocalRun hy k) hC
  obtain ⟨Ep, hEp, hEpr, -, hEph, -, hEpJ, hEpj⟩ :=
    Healing.entry_J_hj (Compose.fg_reachable hrun.toLocalRun hp k') hPr
  rw [← hEyr] at hT hEyT ⊢
  have hroot : Ep.root = Ey.root := hEpr.trans (hT.trans hEyT)
  obtain rfl : Ep = Ey := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1
    ⟨p, hp, k', hEp⟩ ⟨y, hy, k, hEy⟩ hroot
  rw [Healing.σ_eq_honest hrun hnc hy hp hEy hEp]
  exact Healing.finalityPair_eq_iff_of_previousHeightJustified hEph hEpj hEpJ hb

/-- **The fin-pair link under `HealedRecords`.** With the entry state `σe` of `C` as in
`finalityPair_entry_iff`, a held honest state `σ` whose previous height is justified, at the same
entry with `h₀ ≤ σ.h_j` and `σ.J = E σ.h_j` has `finality_pair(σe) = (σ.h_j, σ.J)` for the record of
`y` at any cut. -/
theorem finalityPair_entry_healed (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state y k).fg.tree)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree)
    (hT : ((tr.state p k').fg.σ Pr.root).Th =
      ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)
    (hb : ((tr.state p k').fg.σ Pr.root).previousHeightJustified)
    (hj₀ : h₀ ≤ ((tr.state p k').fg.σ Pr.root).hj)
    (hJ : ((tr.state p k').fg.σ Pr.root).J = (E ((tr.state p k').fg.σ Pr.root).hj).root)
    (i : Nat) :
    (tr.state y i).record.finalityPair ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th) =
      some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) := by
  refine (finalityPair_entry_iff hrun hnc hy hC hp hPr hT hb _).2 ?_
  rw [hJ]
  exact hR.permits_entry hrun hy i _ hj₀

/-- **The justification of a held honest state is the entry (WI-18).** Under `HealedRecords`
and `f < q`, a held honest state `σ = σ_p[Pr]` with `h₀ ≤ σ.h_j` and `1 ≤ σ.h_j` has
`σ.J = (E σ.h_j).root`: its target quorum for `(σ.h_j, σ.J)` (`justified_evidence`) has an
honest row, signed (`att_unforgeable`), which names `E σ.h_j` (C2*⁺ (i)). -/
theorem J_eq_entry_of_healed (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree)
    (hj₀ : h₀ ≤ ((tr.state p k').fg.σ Pr.root).hj) (hj1 : 1 ≤ ((tr.state p k').fg.σ Pr.root).hj) :
    ((tr.state p k').fg.σ Pr.root).J = (E ((tr.state p k').fg.σ Pr.root).hj).root := by
  obtain ⟨c, hcT, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hp k') Pr hPr
  obtain ⟨Q, hQ, hQv⟩ := (FG.FGParams.justified_evidence _ hc).2 hj1
  have hv : ∃ v ∈ Q, v ∈ H := by
    by_contra hn
    push Not at hn
    have := Set.ncard_le_ncard (s := (Q : Set (Fin sp.toParams.fg.n))) (t := Hᶜ) hn
      (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    exact lt_irrefl _ (lt_of_lt_of_le hq (hQ.trans this))
  obtain ⟨v, hvQ, hvH⟩ := hv
  obtain ⟨a, ha, rfl, hah, haT, -⟩ := hQv v hvQ
  obtain ⟨B, hB, ha⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hB
  change a ∈ X.fgPayload at ha
  rcases Healing.tree_accepted hrun.toLocalRun hp (hcT X hX) with hg | ⟨i', -, hA⟩
  · rw [hg] at ha
    cases ha
  obtain ⟨d, -, hsd⟩ := hrun.att_unforgeable p hp i' a (Or.inr ⟨X, ⟨true, hA⟩, ha⟩) hvH
  rw [← haT, hR.rows _ hvH d a hsd (hah ▸ hj₀), hah]

/-- **The fin-pair link under `HealedRecords`, without the `J` premise (WI-18).**
`finalityPair_entry_healed` with `σ.J = E σ.h_j` from `J_eq_entry_of_healed` (`f < q`,
`1 ≤ σ.h_j`). -/
theorem finalityPair_entry_healed' (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hq : Hᶜ.ncard < sp.toParams.fg.q) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state y k).fg.tree)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree)
    (hT : ((tr.state p k').fg.σ Pr.root).Th =
      ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)
    (hb : ((tr.state p k').fg.σ Pr.root).previousHeightJustified)
    (hj₀ : h₀ ≤ ((tr.state p k').fg.σ Pr.root).hj) (hj1 : 1 ≤ ((tr.state p k').fg.σ Pr.root).hj)
    (i : Nat) :
    (tr.state y i).record.finalityPair ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th) =
      some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) :=
  finalityPair_entry_healed hrun hnc hR hy hC hp hPr hT hb hj₀
    (J_eq_entry_of_healed hrun hq hR hp hPr hj₀ hj1) i

end Consensus.Goldilocks.Refinement

end
