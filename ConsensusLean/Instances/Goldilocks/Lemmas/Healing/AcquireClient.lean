module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.FinalityPair

public section

/-! # Goldilocks Healing: HS.4 (b), the client subclaim

Client progress (P1/P2). HS.4 is retired (owner decision) and this subclaim is no longer proved;
the lemmas here, which its proof used, remain. At an honest
`fg_attest(C)` in the effective phase `(m, c)`, whose source `C` has state height `h ≥ ℓ`, entry
`E` and is allowed in the phase geometry, the client signs a matching attestation `(h, E)` (target
or timeout), or it signed one at an earlier cut:

* `height_pair` does not refuse. A lock at `h` naming `X ≠ E` was written by an earlier honest
  signing whose finality pair is `(h, X)` (`client_record_origin_from`, the record's only writer is
  `record_attestation`); that pair is a justification `(h, X)` of a state held by the signer
  (`finalityPair_justified`), so the node holds a block of state height `> h`: `h ≤ m − 1`, and
  with `h ≥ ℓ` the phase is not a contest and `h = m − 1`. A gap has no justification at `m − 1`;
  in the top-`J` case `J = X` (HR.2 (a)) and the allowed `C` extends `J`, so `X` and `E` are the
  entries of `C`'s chain at `h`: `X = E`.
* If `create_attestation` refuses without a conflicting lock, the target or timeout entry already
  names `E`. Its origin is an earlier signing (`client_record_origin_from`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

/-! ## Justifications and finality pairs of a reachable store -/

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Along one block, a pending pair of the new state is old or is the new state's
justification. -/
private theorem step_pending_just {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ∀ p ∈ σ'.pending, p ∈ σ.pending ∨ p = (σ'.hj, σ'.J) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, pr, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := pr, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;> intro q hq
  · simp only [FG.ChainState.advance] at hq ⊢
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact Or.inl (List.mem_filter.1 hq).1
    · exact Or.inr (List.mem_singleton.1 hq)
  · simp only [FG.ChainState.advance] at hq
    exact Or.inl (List.mem_filter.1 hq).1
  · exact Or.inl (List.mem_filter.1 hq).1

/-- **Every pending pair of a held state is the justification of a held state.** -/
theorem pending_justified (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ p ∈ (st.σ W.root).pending, ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧
      (st.σ B.root).J = p.2 := by
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    intro p hp
    simp [FG.ChainState.init] at hp
  | @tail Y W' _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    intro p hp
    rcases step_pending_just ht p hp with hp | rfl
    · exact ih p hp
    · exact ⟨W', hYW.2.1, rfl, rfl⟩

/-- The newest-pair fold returns its start or a member of the list. -/
private theorem foldl_newest_mem {l : List (Nat × Nat)} {acc : Option (Nat × Nat)}
    {p : Nat × Nat}
    (h : l.foldl (fun acc p => match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) acc = some p) :
    acc = some p ∨ p ∈ l := by
  exact FG.Record.foldl_newest_mem_or_initial h

/-- **A finality pair of a held state is the justification of a held state** (the entry's own
justification at an entry whose previous height is justified, or a pending pair). -/
theorem finalityPair_justified (hr : st.Reachable acp₀) {W : NodeBlock P ACP}
    (hW : W ∈ st.tree) {Λ : FG.Record} {p : Nat × Nat}
    (hp : Λ.finalityPair (st.σ W.root) = some p) :
    ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧ (st.σ B.root).J = p.2 := by
  unfold FG.Record.finalityPair at hp
  split_ifs at hp
  · cases hp
    exact ⟨W, hW, rfl, rfl⟩
  · rcases foldl_newest_mem hp with h' | h'
    · cases h'
    · exact pending_justified hr hW p (List.mem_filter.1 h').1

/-- State heights are at least `1`. -/
theorem one_le_h (hr : st.Reachable acp₀) {B : NodeBlock P ACP} (hB : B ∈ st.tree) :
    1 ≤ (st.σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hr B hB
  exact (FG.chain_invariants P.fg _ _ hc).1

end Store

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}

end Consensus.Goldilocks.Healing

end
