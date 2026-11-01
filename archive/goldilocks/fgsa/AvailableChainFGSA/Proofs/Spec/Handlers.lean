module
public import AvailableChainFGSA.Model.Spec.Transitions
public import AvailableChainFGSA.Proofs.Spec.Codec
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Spec

/-- A failed signature decode is refused by the unchanged delivery handler. -/
theorem process_decode_refused (p : Params) (st : State p.n) (o : Wire p.n)
    (h : o.decode = none) : process p st o.embed = st := by
  delta process
  rw [decode_embedding, h]
  rfl

/-- Even if called directly, Lean admission refuses a non-increasing parent slot. -/
theorem process_parent_slot_refused (p : Params) (st : State p.n) (o : Wire p.n)
    (h : parentSlotValid o = false) : process p st o.embed = st := by
  unfold parentSlotValid at h
  delta process
  rw [decode_embedding]
  cases hd : o.decode with
  | none => simp [hd] at h
  | some x =>
      cases x with
      | vote s i r => simp [hd] at h
      | row i a => simp [hd] at h
      | block s B =>
          change admitBlock p st s B.embed = st
          have refuse (N : NamedProposal p.n)
              (ha : ∀ Q, blockAccepted p st s N Q = false) : admitBlock p st s N = st := by
            delta admitBlock
            split
            · rfl
            · cases hp : parentFG st N.erase with
              | none => rfl
              | some Q => simp only [ha, Bool.false_eq_true, ↓reduceIte]
          apply refuse
          intro Q
          cases B with
          | genesis => rfl
          | node P t i r rows raw support =>
              simp only [hd] at h
              have hp : (Block.node P t i r rows raw support).embed.erase.parent.slot =
                  P.slot := by
                change P.embed.erase.slot = P.slot
                rw [named_erase_slot, embed_slot]
              have hs : (Block.node P t i r rows raw support).embed.erase.slot = t := rfl
              delta blockAccepted
              simp only [hp, hs, h, Bool.and_false, Bool.false_and]

/-- A non-assigned proposer has no state effect under the explicit refusal adapter. -/
theorem process_proposer_refused (p : Params) (assigned : Slot → Fin p.n)
    (st : State p.n) (o : Wire p.n) (h : proposerAllowed assigned o = false) :
    process p st (deliveryWire assigned o) = st := by
  rw [deliveryWire, h]
  rfl

/-- Exact parent membership uses the complete representation on arbitrary inputs. -/
theorem parent_membership (B : Block n) (held : List (Block n)) :
    B.parent.representation ∈ held.map Block.representation ↔ B.parent ∈ held := by
  simp [embed_injective.eq_iff]

/-- Once authenticated, the attestation handler is the spec's ordered set insert. -/
theorem admitRow_pool (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : a.decode?.isSome = true) :
    (admitRow p st a).rowPool = insertRow st.rowPool a := by
  unfold admitRow insertRow
  cases hd : a.decode? with
  | none => simp [hd] at h
  | some x =>
      simp only
      split <;> rfl

/-- Lean normalization represents the core record, before the read-time head clamp. -/
theorem normalized_record (st : State n) :
    (normalizeS st).base.stableRecord = normalizeRecord (eraseFG st.fg.F) st.base.stableRecord := by
  unfold normalizeS normalizeRecord
  split <;> rfl

theorem advance_embedding (tree : List AvailableChain.Block)
    (old C : AvailableChain.Block) (h : old ∈ tree) :
    advance tree old (some C) = GridCO.advance old C := by
  delta GridCO.advance
  simp [advance, h]

/-- Normalization also covers an old record outside the current tree. -/
theorem advance_outside_embedding (tree : List AvailableChain.Block)
    (F old C : AvailableChain.Block) (hout : old ∉ tree)
    (hnorm : normalizeRecord F old = F) (hFC : AvailableChain.Block.Preceq F C) :
    normalizeRecord F (advance tree old (some C)) =
      GridCO.advance (normalizeRecord F old) C := by
  simp only [advance, hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hnorm]
  change AvailableChain.Block.preceq F C = true at hFC
  delta GridCO.advance
  simp only [normalizeRecord, hFC, ↓reduceIte]
  split
  · exact (Gen.Pure.block_preceq_antisymm hFC (by assumption)).symm
  · rfl

/-- An absent candidate keeps the old record, with the same normalization on both sides. -/
theorem advance_absent_embedding (tree : List AvailableChain.Block)
    (F old : AvailableChain.Block) :
    normalizeRecord F (advance tree old none) = normalizeRecord F old := rfl

theorem onBlock_future {σ α : Type} (fg : σ → Option σ) (ac : α → α) (state : σ × α) :
    onBlock true fg ac state = state := rfl

theorem onBlock_refused {σ α : Type} (fg : σ → Option σ) (ac : α → α) (state : σ × α)
    (h : fg state.1 = none) : onBlock false fg ac state = state := by
  simp [onBlock, h]

theorem onBlock_accepted {σ α : Type} (fg : σ → Option σ) (ac : α → α)
    (state : σ × α) (next : σ) (h : fg state.1 = some next) :
    onBlock false fg ac state = (next, ac state.2) := by
  simp [onBlock, h]

/-- The separated confirmation walk is the unchanged Lean walk kernel.
The all-pool/late-pool and resolved-score bridges are separate obligations. -/
theorem getConfirmation_walk_embedding (p : Params) (st : GridCO.State p.n .root)
    (F : AvailableChain.Block) (s : Slot) :
    getConfirmation st.blocks F (GridCO.voterCount (GridCO.lateVotes p.toParams.engine st s))
      (GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
        (GridCO.cleanSupport p.toParams.engine st s)
        (GridCO.cleanSupport p.toParams.engine st s)) =
      SA.Root.confirmationFrom p.toParams F st s := by
  dsimp only [getConfirmation, SA.Root.confirmationFrom, GridCO.confirmationFrom]
  simp only [decide_eq_true_eq]

/-- Saving precedes both the empty-result return and the live-lock veto. -/
theorem updateConfirmation_saved (tree : List AvailableChain.Block) (F : AvailableChain.Block)
    (Δ : Time) (k committeeSize : Nat) (s : Int) (t : Time)
    (score : AvailableChain.Block → Nat) (A : ACState n) :
    (updateConfirmation tree F Δ k committeeSize s t score A).saved s =
      getConfirmation tree F (confirmationVoters (A.pool s)).length score := by
  delta updateConfirmation
  cases hr : getConfirmation tree F (confirmationVoters (A.pool s)).length score with
  | none => exact ite_eq_left rfl
  | some C =>
      dsimp only
      split <;> exact ite_eq_left rfl

end AvailableChain.FGSA.Spec
end
