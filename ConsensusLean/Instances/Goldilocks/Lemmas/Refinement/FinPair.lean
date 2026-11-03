module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

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

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.Refinement

end
