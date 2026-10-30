module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks FG store: what an FG trace gives at one honest node

Over an FG trace with its contract (`FGLocalRun`), at an honest node: the store before every
cut is reachable (`store_reachable`), so part 1 applies to it; a block of its tree other than
genesis was accepted by the node at an earlier cut (`tree_accepted`); and the attestations that
an honest validator signs before a cut are the output of one client run from the empty record
over entry states of chains (`signed_run`), so client safety (G0.5) applies to them. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- A labelled cut of an honest node executes its call. -/
private theorem call_step (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    (hn : tr.node i = y ∧ tr.label i ≠ none) :
    ∃ ℓ, tr.label i = some ℓ ∧ FGLabel.Step y (tr.state y i) ℓ (tr.post i) := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
  refine ⟨ℓ, hℓ, ?_⟩
  rw [← hn.1]
  exact hr.exec i ℓ hℓ (hn.1 ▸ hy)

/-- The store of an honest node before every cut is reachable. -/
theorem store_reachable (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.store y i).Reachable acp₀ := by
  induction i with
  | zero =>
    change (tr.init y).1.Reachable acp₀
    rw [hr.init y hy]
    exact .refl
  | succ i ih =>
    rw [FGTrace.store, Trace.state]
    split_ifs with hnode
    · obtain ⟨ℓ, -, hs⟩ := call_step hr hy hnode
      cases ℓ with
      | block B acc =>
        rcases hs with ⟨-, h, -⟩ | ⟨-, -, he⟩
        exacts [ih.tail (Or.inl ⟨B, h⟩), he ▸ ih]
      | attestation a =>
        rw [hs]
        exact ih.tail (Or.inr ⟨a, rfl⟩)
      | attest src signed =>
        rw [hs.1]
        exact ih
    · exact ih

/-- A block of an honest node's tree before cut `i` is genesis or was accepted by the node at
an earlier cut. -/
theorem tree_accepted (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    B = P.genesisBlock acp₀ ∨ ∃ k < i, tr.AcceptAt y k B := by
  induction i generalizing B with
  | zero =>
    left
    change (tr.init y).1.blocks B.root = some B at hB
    rw [hr.init y hy] at hB
    change (if B.root = P.genesisRoot then some (P.genesisBlock acp₀) else none) = some B at hB
    split_ifs at hB
    exact (Option.some.inj hB).symm
  | succ i ih =>
    have hR := store_reachable hr hy i
    have old (h : B ∈ (tr.store y i).tree) : B = P.genesisBlock acp₀ ∨ ∃ k < i + 1,
        tr.AcceptAt y k B :=
      (ih h).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans (Nat.lt_succ_self i), h⟩
    rw [FGTrace.store, Trace.state] at hB
    split_ifs at hB with hnode
    · obtain ⟨ℓ, hℓ, hs⟩ := call_step hr hy hnode
      cases ℓ with
      | block X acc =>
        rcases hs with ⟨rfl, h, -⟩ | ⟨-, -, he⟩
        · rw [(tree_grows P ACP acp₀ _ hR).1 X _ h] at hB
          rcases hB with rfl | hB
          exacts [Or.inr ⟨i, Nat.lt_succ_self i, hnode.1, hℓ⟩, old hB]
        · rw [he] at hB
          exact old hB
      | attestation a =>
        rw [hs] at hB
        exact old ((tree_grows P ACP acp₀ _ hR).2 a ▸ hB)
      | attest src signed =>
        rw [hs.1] at hB
        exact old hB
    · exact old hB

/-- A client run over a list with one entry state appended: the run over the list, then one
`create_attestation` step. -/
private theorem run_append {n : Nat} (v : Fin n) (Λ : FG.Record) (l : List (FG.ChainState n))
    (σe : FG.ChainState n) :
    FG.Record.run v Λ (l ++ [σe]) = match (FG.Record.run v Λ l).1.createAtt v σe with
      | none => FG.Record.run v Λ l
      | some (a, Λ') => (Λ', (FG.Record.run v Λ l).2 ++ [a]) := by
  induction l generalizing Λ with
  | nil =>
    rcases h : Λ.createAtt v σe with _ | ⟨a, Λ'⟩ <;> simp [FG.Record.run, h]
  | cons x l ih =>
    rcases h : Λ.createAtt v x with _ | ⟨a, Λ'⟩ <;>
      simp only [List.cons_append, FG.Record.run, h, ih]
    split <;> rfl

/-- An unheld root of a reachable store has the initial chain state. -/
private theorem σ_of_unheld {st : Store P ACP} (h : st.Reachable acp₀) {r : Nat}
    (hn : st.blocks r = none) : st.σ r = FG.ChainState.init P.fg := by
  revert hn
  induction h with
  | refl => exact fun _ => rfl
  | @tail st _ _ hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := onBlock_eq_some hB
      obtain ⟨atts, he⟩ := addAtts_eq (updateFinality { st with
        blocks := Function.update st.blocks B.root (some B),
        σ := Function.update st.σ B.root σ' } σ') B.fgPayload
      obtain ⟨hb, hσ, -⟩ := updateFinality_spec { st with
        blocks := Function.update st.blocks B.root (some B),
        σ := Function.update st.σ B.root σ' } σ'
      intro hn
      rw [he] at hn ⊢
      simp only [hb, hσ, Function.update_apply] at hn ⊢
      split_ifs at hn ⊢
      exact ih hn
    · obtain ⟨atts, he⟩ := st.onAttestation_eq a
      rw [he]
      exact ih

/-- The state of every root of a reachable store is a valid client input. -/
private theorem entry_input {st : Store P ACP} (h : st.Reachable acp₀) (r : Nat) :
    1 ≤ (st.σ r).h ∧ (st.σ r).hj < (st.σ r).h ∧ ∀ p ∈ (st.σ r).pending, p.1 < (st.σ r).h := by
  obtain ⟨c, hc⟩ : ∃ c, P.fg.chainState c = some (st.σ r) := by
    rcases hb : st.blocks r with _ | X
    · exact ⟨[], by rw [σ_of_unheld h hb]; rfl⟩
    · have hX := h.blocks_root hb
      obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st h X (by
        change st.blocks X.root = some X
        rwa [hX])
      exact ⟨_, hX ▸ hc⟩
  obtain ⟨h1, -, h2, -, -, -, -, h3, -⟩ := FG.chain_invariants P.fg c _ hc
  exact ⟨h1, h2, fun p hp => (h3 p hp).2.trans_lt h2⟩

/-- `signed_run` with the record: the record of an honest validator before cut `i` is that of
the run. -/
private theorem signed_run_record (hr : FGLocalRun acp₀ H U tr) {v : Fin P.n} (hv : v ∈ H)
    (i : Nat) : ∃ inputs : List (FG.ChainState P.n), FG.EntryInputs P.fg inputs ∧
      (tr.state v i).2 = (FG.Record.run v FG.Record.empty inputs).1 ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 := by
  induction i with
  | zero =>
    refine ⟨[], fun _ h => absurd h List.not_mem_nil, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    change (tr.init v).2 = _
    rw [hr.init v hv]
    rfl
  | succ i ih =>
    obtain ⟨inputs, hin, hrec, hsign⟩ := ih
    have sign_of (h₀ : ∀ a src, tr.node i = v → tr.label i ≠ some (.attest src (some a))) :
        ∀ j < i + 1, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 :=
      fun j hj a h => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim (hsign j · a h) fun e => by
        obtain ⟨src, hn, h⟩ := h
        subst e
        exact absurd h (h₀ a src hn)
    rw [Trace.state]
    split_ifs with hnode
    · obtain ⟨ℓ, hℓ, hs⟩ := call_step hr hv hnode
      cases ℓ with
      | block B acc =>
        refine ⟨inputs, hin, ?_, sign_of fun a src _ h => by rw [hℓ] at h; cases h⟩
        rcases hs with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h, hrec]
      | attestation a =>
        exact ⟨inputs, hin, hs ▸ hrec, sign_of fun a src _ h => by rw [hℓ] at h; cases h⟩
      | attest src signed =>
        obtain ⟨-, hs⟩ := hs
        set σe := (tr.state v i).1.σ ((tr.state v i).1.σ src.root).Th
        rw [show (tr.state v i).1.attest (tr.state v i).2 v src =
          (tr.state v i).2.createAtt v σe from rfl] at hs
        refine ⟨inputs ++ [σe], fun σ hσ => ?_, ?_⟩
        · rcases List.mem_append.1 hσ with h | h
          · exact hin σ h
          · rw [List.mem_singleton.1 h]
            exact entry_input (store_reachable hr hv i) _
        rw [run_append, ← hrec]
        rcases hc : (tr.state v i).2.createAtt v σe with _ | ⟨a, Λ'⟩ <;> rw [hc] at hs
        · exact ⟨hs.2.trans hrec, sign_of fun a src' _ h => by simp [hℓ, hs.1] at h⟩
        refine ⟨hs.2, fun j hj b h => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim
          (fun hj => List.mem_append_left _ (hsign j hj b h)) fun e => ?_⟩
        obtain ⟨src', -, h⟩ := h
        subst e
        obtain ⟨-, rfl⟩ : src = src' ∧ a = b := by simpa [hℓ, hs.1] using h
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ⟨inputs, hin, hrec, sign_of fun a src hn h => hnode ⟨hn, by simp [h]⟩⟩

/-- The attestations that an honest validator signs before cut `i` are among the output of one
client run from the empty record over entry states of chains. -/
theorem signed_run (hr : FGLocalRun acp₀ H U tr) {v : Fin P.n} (hv : v ∈ H) (i : Nat) :
    ∃ inputs, FG.EntryInputs P.fg inputs ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 :=
  let ⟨inputs, h₁, _, h₂⟩ := signed_run_record hr hv i
  ⟨inputs, h₁, h₂⟩

end Consensus.Goldilocks.Store

end
