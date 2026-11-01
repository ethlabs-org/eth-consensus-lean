module
public import AvailableChainSAPC.Proofs.RunCleanTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Every canonical source is available at an honest input in its own
event prefix. Authority sources use their admitted PC paths, without a cap. -/
theorem cleanRunPath_accessible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (index : Nat) (b : Block)
    (hb : cleanRunPath p rho index b) : b = .genesis ∨
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true := by
  set_option backward.isDefEq.respectTransparency false in
  by_cases hg : b = .genesis
  · exact Or.inl hg
  right
  have stored (v : V) (hv : v ∈ rho.honest) (i : Nat) (hi : i ≤ index)
      (c : Block) (hc : c ∈ (Run.stateBefore (sapc p) rho i v).base.blocks)
      (hp : Block.Preceq b c) :
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true := by
    exact ⟨v, hv, i, hi, stored_pathKnown_at_fold p (rho.events.take i) v b
      ((paths_at_fold p _ v).1 c hc b hg hp)⟩
  have known (v : V) (hv : v ∈ rho.honest) (i : Nat) (hi : i ≤ index)
      (c : Block) (hc : pathKnown (Run.stateBefore (sapc p) rho i v) c = true)
      (hp : Block.Preceq b c) :
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true := by
    have hm : c ∈ (Run.stateBefore (sapc p) rho i v).base.blocks := by
      cases c with
      | genesis => exact of_decide_eq_true hc
      | node parent slot r_slot root => exact of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    exact stored v hv i hi c hm hp
  have pc (v : V) (hv : v ∈ rho.honest) (i : Nat) (hi : i ≤ index)
      (c : PC p.n) (hc : pcValid p (Run.stateBefore (sapc p) rho i v) c = true)
      (hp : Block.Preceq b c.target) :
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true :=
    known v hv i hi c.target
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2).1 hp
  rcases hb with hgen | ⟨c, source, hp⟩
  · exact (hg hgen).elim
  cases source with
  | genuine j hj v hv r c _ hc =>
    rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ r c hc
      with hgen | hm
    · subst c
      exact (hg (by simpa [Block.Preceq, Block.preceq] using hp)).elim
    · exact stored v hv j (by omega) c hm hp
  | timely r c _ source =>
    obtain ⟨v, hv, j, hj, _, saved⟩ := source
    obtain ⟨k, hk, _, candidate⟩ := savedTimely_origin_before p rho (j + 1) v r c saved
    have candidate := timelyCandidate_of_timelyInput p _
      (base_receiptStamped_at_fold p _ v) (archiveStamped_at_fold p _ v) r c _ candidate
    have path := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp candidate).1).2
    have mem : c ∈ (Run.stateBefore (sapc p) rho k v).base.blocks := by
      cases c with
      | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp path).1
      | node parent slot r_slot root =>
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp path).1).1
    exact stored v hv k (by omega) c mem hp
  | gate j hj v hv _ c _ _ hc =>
    exact pc v hv j hj.le c (installedPC_valid_before p rho v j c hc) hp
  | proposal j hj v hv _ c _ _ hc =>
    rw [clock_bestPC] at hc
    exact pc v hv j hj.le c (installedPC_valid_before p rho v j c hc) hp
  | head j hj v hv r c _ _ hc =>
    have valid := certificates_valid_at_fold p (rho.events.take j) v
    have hc' := selectedPC_valid p _ (clock_frozenPC_valid p _ _ valid.2 valid.1) r c hc
    rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc'
    exact pc v hv j hj.le c hc' hp

/-- A capped source path is available at an actual honest input in its
own event prefix. Stored unrelated proposals do not supply this source. -/
theorem cleanRunPath_accessible_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (_hx : ExecutionValid (sapc p) E rho)
    (_cap : FaultBound (sapc p) (pcFaultCap p) rho) (index : Nat) (b : Block)
    (hb : cleanRunPath p rho index b) : b = .genesis ∨
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true :=
  cleanRunPath_accessible p rho index b hb

/-- Source and receipt facts are independent of clean comparability.
Only the chain and actual genuine continuation need induction. -/
theorem cleanPathFacts_of_chain_and_transfer
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (ha : (faulty rho).card < pcQuorum p) (index : Nat)
    (chain : CleanPath (cleanRunPath p rho index))
    (transfer : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
      rho.events[j]? = some (.tick v (gateTime p r)) →
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
      ∀ k, k < index → ∀ w ∈ rho.honest, ∀ s, r < s →
        rho.events[k]? = some (.tick w (voteTime p s)) →
        Block.Preceq b (headTarget p
          (clock p (Run.stateBefore (sapc p) rho k w) (voteTime p s)) s)) :
    CleanPathFacts p E rho index (cleanRunPath p rho index) := by
  refine ⟨chain, ?_, cleanRunPath_accessible p rho index,
    ?_, ?_, transfer, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v hv
    have h := state_on_cleanRunPath p rho i v hv
    exact ⟨cleanRunPath_mono p rho hi h.stable, cleanRunPath_mono p rho hi h.goldfish,
      fun b g d hm => cleanRunPath_mono p rho hi (h.finite b g d hm),
      fun r b hm => cleanRunPath_mono p rho hi (h.saved r b hm)⟩
  · intro v _ b g d hm
    exact run_target_genuine_origin p rho index v b g d hm
  · intro j hj v hv r b ht raw
    exact Or.inr ⟨b, .genuine j hj v hv r b ht raw, GridCO.block_preceq_self b⟩
  · intro i hi v _ c hc
    obtain ⟨w, hw, j, hj, ht, saved⟩ := validPC_prior_timely p E rho hx
      ha i v c hc
    exact ⟨⟨w, hw, j, by omega, ht, saved⟩, fun cap =>
      cleanRunPath_mono p rho hi (validPC_on_cleanRunPath p E rho hx cap i v c hc)⟩
  · intro i hi v hv r b saved
    obtain ⟨j, hj, ht, saved⟩ := savedTimely_first_save p E rho hx.toScheduleWellFormed
      i v r b saved
    exact ⟨⟨v, hv, j, hj, ht, saved⟩, fun cap => Or.inr ⟨b,
      .timely r b cap ⟨v, hv, j, hj.trans_le hi, ht, saved⟩, GridCO.block_preceq_self b⟩⟩
  · intro cap i _ v _
    exact capBroken_false_before p E rho hx cap v i
  · intro i _ v _
    exact archive_authenticated_before p E rho hx.toUnforgeableSignatures i v
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .gate i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .head i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .proposal i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩

/-- Source and receipt facts are independent of clean comparability.
Only the chain and actual genuine continuation need induction. -/
theorem cleanPathFacts_capped_of_chain_and_transfer
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) (index : Nat)
    (chain : CleanPath (cleanRunPath p rho index))
    (transfer : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
      rho.events[j]? = some (.tick v (gateTime p r)) →
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
      ∀ k, k < index → ∀ w ∈ rho.honest, ∀ s, r < s →
        rho.events[k]? = some (.tick w (voteTime p s)) →
        Block.Preceq b (headTarget p
          (clock p (Run.stateBefore (sapc p) rho k w) (voteTime p s)) s)) :
    CleanPathFacts p E rho index (cleanRunPath p rho index) :=
  cleanPathFacts_of_chain_and_transfer p E rho hx (capped_quorum_above_faults p rho cap)
    index chain transfer

/-- Restrict the actual invariant to an earlier event prefix. The earlier
path is its own source closure, not the current path reused at that time. -/
theorem JointCleanInvariant.restrict {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {rho : Run V (sapc p)}
    (hx : ExecutionValid (sapc p) E rho)
    (ha : (faulty rho).card < pcQuorum p) {i j : Nat} (hle : j ≤ i)
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho j := by
  constructor
  · apply cleanPathFacts_of_chain_and_transfer p E rho hx ha j
    · exact ⟨Or.inl rfl, cleanRunPath_closed p rho j,
        fun a b ha hb => h.facts.chain.comparable a b
          (cleanRunPath_mono p rho hle ha) (cleanRunPath_mono p rho hle hb)⟩
    · intro k hk v hv r b ht raw l hl w hw s hrs tick
      exact h.facts.transferred k (hk.trans_le hle) v hv r b ht raw
        l (hl.trans_le hle) w hw s hrs tick
  · intro k hk l hl
    exact h.ordered k (hk.trans_le hle) l (hl.trans_le hle)

/-- Restrict the actual invariant to an earlier event prefix. The earlier
path is its own source closure, not the current path reused at that time. -/
theorem JointCleanInvariant.restrict_capped {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {rho : Run V (sapc p)}
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) {i j : Nat} (hle : j ≤ i)
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho j :=
  h.restrict hx (capped_quorum_above_faults p rho cap) hle

end AvailableChain.SAPC
end
