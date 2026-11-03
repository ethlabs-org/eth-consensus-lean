module
public import ConsensusLean
@[expose] public section

/-! # Faulty-validator witnesses for the Goldilocks FG safety milestones

The other FG witnesses have `n ≤ 2` and no faulty validator. Here `n = 4`, so `q = 3` and
`2q − n = 2`, and the safety statements are exercised with a validator that signs on both sides
or with a faulty one. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `faulty_conflicting_finalizations`: two chains on which three of the four validators
  finalize conflicting blocks, validators `1` and `2` signing on both (the hypotheses of
  `AccountableSafety` at `n = 4`). Exactly `1` and `2` have a slashable pair among the
  attestations of the two chains, so `AccountableSafety`'s bound `2q − n = 2` is met with
  equality, and `faulty_conviction` is the proved statement's conclusion on these chains.
* (a) `faulty_localRun`: an `n = 4` FG trace with honest set `{0, 1, 2}` (one faulty validator,
  `1 < 2q − n`) is an `FGLocalRun`. Honest validator `0` processes two attestations of the faulty
  validator `3` that are slashable with each other (E2: two target votes at height `1`). The
  premises of `FinalizedSafety` therefore hold together with an actual equivocation
  (`faulty_equivocation_processed`), and `faulty_finalized_safety` is its conclusion. -/

namespace Consensus.Goldilocks.FaultyWitness

open FG

/-! ## Chain level: conviction at `n = 4` -/

/-- Four validators, `δt = 2`, genesis root `0`. -/
abbrev gp4 : FGParams := ⟨4, by decide, 2, 0⟩

/-- `q = 3` and `2q − n = 2` at `n = 4`. -/
theorem gp4_quorum : gp4.q = 3 ∧ 2 * gp4.q - gp4.n = 2 := by decide

/-- A target vote of validator `v` at height `h` for root `T`, with finality pair `f`. -/
def tv (v : Fin 4) (h T : Nat) (f : Option (Nat × Nat)) : Att 4 := ⟨v, h, T, false, f⟩

/-- The target votes of the validators `vs` at height `h` for root `T`, with finality pair `f`. -/
def tvs (vs : List (Fin 4)) (h T : Nat) (f : Option (Nat × Nat)) : List (Att 4) :=
  vs.map fun v => tv v h T f

/-- Branch A, signed by validators `0, 1, 2`: blocks `1, 2, 3` on genesis, each carrying a target
quorum for the current entry, with the predecessor as finality pair from height `2` on. -/
def chainA : List (FGBlock 4) :=
  [⟨1, 1, 0, tvs [0, 1, 2] 1 0 none⟩, ⟨2, 2, 0, tvs [0, 1, 2] 2 1 (some (1, 0))⟩,
   ⟨3, 3, 0, tvs [0, 1, 2] 3 2 (some (2, 1))⟩]

/-- Branch B, signed by validators `1, 2, 3`: blocks `11, 12, 13` on genesis, finalizing `11`. -/
def chainB : List (FGBlock 4) :=
  [⟨11, 1, 0, tvs [1, 2, 3] 1 0 none⟩, ⟨12, 2, 0, tvs [1, 2, 3] 2 11 (some (1, 0))⟩,
   ⟨13, 3, 0, tvs [1, 2, 3] 3 12 (some (2, 11))⟩]

/-- The attestations of the two chains. -/
def bothAtts : List (Att 4) := gp4.chainAtts chainA ++ gp4.chainAtts chainB

/-- The validators with a slashable pair among the attestations of the two chains. -/
def convicted : Finset (Fin 4) :=
  Finset.univ.filter fun v => ∃ a ∈ bothAtts, ∃ b ∈ bothAtts, a.val = v ∧ slashable a b

/-- (a) The hypotheses of `AccountableSafety` at `n = 4`: chain A finalizes `1`, chain B
finalizes `11`, and neither finalized block is on the other chain. Exactly validators `1` and
`2`, the two that signed on both branches, are convicted: `2q − n = 2` of them. -/
theorem faulty_conflicting_finalizations :
    (gp4.chainState chainA).map (fun σ => σ.F) = some 1 ∧
      (gp4.chainState chainB).map (fun σ => σ.F) = some 11 ∧
      1 ∉ gp4.roots chainB ∧ 11 ∉ gp4.roots chainA ∧
      convicted = {1, 2} ∧ convicted.card = 2 * gp4.q - gp4.n := by
  decide +kernel

/-- `AccountableSafety`'s conclusion on the two chains: a set of at least `2q − n = 2`
validators, each with a slashable pair among their attestations, is contained in
`convicted = {1, 2}`, so it is `{1, 2}`. -/
theorem faulty_conviction :
    ∃ S : Finset (Fin gp4.n), 2 * gp4.q - gp4.n ≤ S.card ∧ S = {1, 2} ∧
      ∀ v ∈ S, ∃ a ∈ bothAtts, ∃ b ∈ bothAtts, a.val = v ∧ slashable a b := by
  obtain ⟨hA, hB, h1, h11, hc, -⟩ := faulty_conflicting_finalizations
  obtain ⟨σA, hσA, -⟩ := Option.map_eq_some_iff.mp hA
  obtain ⟨σB, hσB, -⟩ := Option.map_eq_some_iff.mp hB
  have hFA : σA.F = 1 := by
    have := hA; rw [hσA] at this; simpa using this
  have hFB : σB.F = 11 := by
    have := hB; rw [hσB] at this; simpa using this
  obtain ⟨S, hS, hv⟩ := accountable_safety gp4 chainA chainB σA σB hσA hσB
    (by rw [hFA]; exact h1) (by rw [hFB]; exact h11)
  have hsub : S ⊆ convicted := fun v hvS =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv v hvS⟩
  rw [hc] at hsub
  have hS2 : 2 ≤ S.card := by simpa [gp4_quorum.2] using hS
  have hcard : S.card ≤ ({1, 2} : Finset (Fin 4)).card := Finset.card_le_card hsub
  have heq : S = {1, 2} :=
    Finset.eq_of_subset_of_card_le hsub (by simpa using hS2.trans' (by decide))
  exact ⟨S, hS, heq, hv⟩

/-! ## Trace level: a faulty equivocation under `FinalizedSafety`'s premises -/

/-- Four validators, `Δ = 1`, slot `s` starts at `s`, genesis root `0`, `δ_t = 2`. -/
def P₄ : Params where
  n := 4
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 2

/-- Honest validator `0`. -/
def v₀ : Fin P₄.n := ⟨0, by decide⟩

/-- The faulty validator `3`. -/
def v₃ : Fin P₄.n := ⟨3, by decide⟩

/-- The honest set `{0, 1, 2}`. -/
def H₄ : Set (Fin P₄.n) := {v | v.val < 3}

/-- One faulty validator, fewer than `2q − n = 2`. -/
theorem H₄_faults : H₄ᶜ.ncard < 2 * P₄.fg.q - P₄.n := by
  have h : H₄ᶜ = ((({v₃} : Finset (Fin P₄.n))) : Set (Fin P₄.n)) := by
    ext v
    change ¬ v.val < 3 ↔ v ∈ (({v₃} : Finset (Fin P₄.n)) : Set (Fin P₄.n))
    rw [Finset.mem_coe, Finset.mem_singleton]
    revert v; decide
  rw [h, Set.ncard_coe_finset]
  decide

/-- The faulty validator's target vote for genesis at height `1`. -/
def a₃ : Att P₄.n := ⟨v₃, 1, 0, false, none⟩

/-- The faulty validator's conflicting target vote for root `5` at height `1`. -/
def a₃' : Att P₄.n := ⟨v₃, 1, 5, false, none⟩

/-- The two votes are slashable with each other (E2). -/
theorem a₃_slashable : slashable a₃ a₃' := by decide

/-- Validator `0`'s FG state after processing `a₃`. -/
def st₁ : Store P₄ Unit := (Store.init ()).onAttestation a₃

/-- Validator `0`'s FG state after processing `a₃` and then `a₃'`. -/
def st₂ : Store P₄ Unit := st₁.onAttestation a₃'

/-- The `n = 4` trace at time `0`: honest validator `0` processes the faulty `a₃` (cut `0`) and the
conflicting `a₃'` (cut `1`); then it stutters. No other node has a labelled cut. -/
def trF : FGTrace P₄ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := v₀
  time _ := 0
  event _ := 0
  pos _ := 0
  label
    | 0 => some (.attestation a₃)
    | 1 => some (.attestation a₃')
    | _ => none
  post
    | 0 => (st₁, FG.Record.empty)
    | _ => (st₂, FG.Record.empty)
  awake _ _ := True

/-- The states of validator `0` in `trF` before its two labelled cuts and after them. -/
theorem trF_state :
    trF.state v₀ 0 = (Store.init (), FG.Record.empty) ∧ trF.state v₀ 1 = (st₁, FG.Record.empty) ∧
      trF.state v₀ 2 = (st₂, FG.Record.empty) := by
  simp [Trace.state, trF]

/-- Processing an attestation keeps the blocks. -/
theorem onAttestation_blocks (st : Store P₄ Unit) (a : Att P₄.n) :
    (st.onAttestation a).blocks = st.blocks := by
  unfold Store.onAttestation; split <;> rfl

/-- Every FG state of `trF` holds the blocks of the initial state. -/
theorem trF_blocks (y : Fin P₄.n) (i : Nat) :
    (trF.store y i).blocks = (Store.init (P := P₄) ()).blocks := by
  have hpost : ∀ i, (trF.post i).1.blocks = (Store.init (P := P₄) ()).blocks := fun i => by
    rcases i with _ | i
    · exact onAttestation_blocks _ _
    · change (st₁.onAttestation a₃').blocks = _
      rw [onAttestation_blocks]; exact onAttestation_blocks _ _
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [FGTrace.store, Trace.state]
    split
    · exact hpost i
    · exact ih

/-- (a) `trF` is an `FGLocalRun` for the honest set `{0, 1, 2}` inside `{genesis}`, in which
honest validator `0` processes two slashable attestations of the faulty validator `3`. -/
theorem faulty_localRun : FGLocalRun () H₄ {P₄.genesisBlock ()} trF where
  coherent := ⟨Set.injOn_singleton _ _, fun B hB C hC h => by
    simp only [Set.mem_singleton_iff] at hB hC; subst hB; subst hC
    simp [Params.genesisBlock] at h⟩
  init _ _ := rfl
  exec i ℓ h _ := by
    rcases i with _ | _ | i <;> simp only [trF, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · change FGLabel.Step v₀ (trF.state v₀ 0) _ (st₁, FG.Record.empty)
      rw [trF_state.1]; rfl
    · change FGLabel.Step v₀ (trF.state v₀ 1) _ (st₂, FG.Record.empty)
      rw [trF_state.2.1]; rfl
  tree_subset y _ i := by
    intro B hB
    change (trF.store y i).blocks B.root = some B at hB
    rw [trF_blocks] at hB
    simp only [Store.init] at hB
    split at hB
    · exact Set.mem_singleton_iff.mpr (Option.some_inj.mp hB).symm
    · exact absurd hB (by simp)
  time_nonneg _ := le_rfl
  time_mono _ _ _ := le_rfl
  attest_public y _ i src signed h := by
    rcases i with _ | _ | i <;> simp [Trace.CallAt, trF] at h
  own_first y _ i B h := by
    rcases i with _ | _ | i <;> simp [Trace.CallAt, trF] at h
  attest_order y _ j src signed h := by
    rcases j with _ | _ | j <;> simp [Trace.CallAt, trF] at h
  own_payload y _ i B h := by
    rcases i with _ | _ | i <;> simp [Trace.CallAt, trF] at h
  unforgeable y _ i a h ha := by
    obtain ⟨ℓ, hℓ, hp⟩ := h
    rcases i with _ | _ | i <;> simp [Trace.CallAt, trF] at hℓ <;>
      obtain ⟨-, rfl⟩ := hℓ <;> simp [FGLabel.processed] at hp <;> subst hp <;>
      simp [H₄, a₃, a₃', v₃] at ha

/-- The faulty validator's two slashable attestations are both in honest validator `0`'s pool
after cut `1`. -/
theorem faulty_equivocation_processed :
    v₀ ∈ H₄ ∧ v₃ ∉ H₄ ∧ a₃.val = v₃ ∧ a₃'.val = v₃ ∧ slashable a₃ a₃' ∧
      a₃ ∈ (trF.store v₀ 2).atts ∧ a₃' ∈ (trF.store v₀ 2).atts := by
  refine ⟨show v₀.val < 3 by decide, show ¬ v₃.val < 3 by decide, rfl, rfl, a₃_slashable,
    ?_, ?_⟩ <;>
    rw [FGTrace.store, trF_state.2.2] <;> decide

/-- `FinalizedSafety`'s conclusion on `trF`: the finalized tips of any two honest nodes at any two
cuts are compatible. -/
theorem faulty_finalized_safety :
    ∀ y ∈ H₄, ∀ z ∈ H₄, ∀ i j,
      Compatible {P₄.genesisBlock ()} (trF.store y i).F (trF.store z j).F :=
  Store.finalized_safety (P := P₄) (ACP := Unit) () H₄ _ trF faulty_localRun H₄_faults

end Consensus.Goldilocks.FaultyWitness

end
