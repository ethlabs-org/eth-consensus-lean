module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Settled locks above a slot floor

`LocksSettledU` with a slot floor `σ₀`: the floor restricts only which later honest votes and
proposal heads must extend a live lock's block (those of slots `≥ σ₀`). Lock liveness, the label
quantifier and the start time are unchanged. At floor `0` it is `LocksSettledU`
(`locksSettledFromU_zero_iff`). The H.1 consumers read settledness only at the proposal's slot,
so they take the floor-`p` form. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- Every honest vote of a slot after `j` and at least `σ₀` extends `B`. -/
def VotesExtendFrom (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (σ₀ j : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x ∈ H, ∀ i e, VoteAt tr x i e → j < e.msg.slot → σ₀ ≤ e.msg.slot → VoteExtends U e.msg B

/-- The head of every honest proposal under the oracle `u`, at the start of a slot after `j`
and at least `σ₀`, extends `B`. -/
def ProposalsExtendFromU (u : Nat → Set Lock) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (σ₀ j : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) (m : Nat) d pay, tr.CallAt x i ℓ →
    ℓ.call = .proposal → tr.time i = sp.ts m → j < m → σ₀ ≤ m →
    (acProposalWith sp (u i) (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) →
    Anc U B d.head

/-- **Settled locks from `T`, above the floor `σ₀`**: `LocksSettledU` with the floor restricting
only which later honest votes and proposal heads must extend the lock's block `L` (slots
`≥ σ₀`). Lock liveness, the label quantifier and `T` are unchanged. -/
def LocksSettledFromU (u : Nat → Set Lock) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (σ₀ : Nat) (T : Time) : Prop :=
  ∀ y ∈ H, ∀ i, T ≤ tr.time i → ∀ l ∈ (tr.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k →
    ∀ L ∈ U, L.root = l.block →
      VotesExtendFrom tr H U σ₀ l.slot L ∧ ProposalsExtendFromU u tr H U σ₀ l.slot L

theorem votesExtendFrom_iff {σ₀ j : Nat} {B : Blk sp.n FGP} :
    VotesExtendFrom tr H U σ₀ j B ↔
      ∀ x ∈ H, ∀ i e, VoteAt tr x i e → j < e.msg.slot → σ₀ ≤ e.msg.slot →
        VoteExtends U e.msg B := Iff.rfl

theorem proposalsExtendFromU_iff {u : Nat → Set Lock} {σ₀ j : Nat} {B : Blk sp.n FGP} :
    ProposalsExtendFromU u tr H U σ₀ j B ↔
      ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) (m : Nat) d pay, tr.CallAt x i ℓ →
        ℓ.call = .proposal → tr.time i = sp.ts m → j < m → σ₀ ≤ m →
        (acProposalWith sp (u i) (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) →
        Anc U B d.head := Iff.rfl

theorem locksSettledFromU_iff {u : Nat → Set Lock} {σ₀ : Nat} {T : Time} :
    LocksSettledFromU u tr H U σ₀ T ↔
      ∀ y ∈ H, ∀ i, T ≤ tr.time i → ∀ l ∈ (tr.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block →
          VotesExtendFrom tr H U σ₀ l.slot L ∧ ProposalsExtendFromU u tr H U σ₀ l.slot L :=
  Iff.rfl

/-- At floor `0`, the floored settledness is `LocksSettledU`. -/
theorem locksSettledFromU_zero_iff {u : Nat → Set Lock} {T : Time} :
    LocksSettledFromU u tr H U 0 T ↔ LocksSettledU u tr H U T := by
  rw [locksSettledFromU_iff, locksSettledU_iff]
  refine forall₂_congr fun y _ => forall₂_congr fun i _ => forall₂_congr fun l _ =>
    forall_congr' fun _ => forall₂_congr fun L _ => forall_congr' fun _ => and_congr ?_ ?_
  · rw [votesExtendFrom_iff, votesExtendAfter_iff]
    exact forall₂_congr fun x _ => forall₂_congr fun i e => forall₂_congr fun _ _ =>
      ⟨fun h => h (Nat.zero_le _), fun h _ => h⟩
  · rw [proposalsExtendFromU_iff, proposalsExtendAfterU_iff]
    refine forall₂_congr fun x _ => forall₂_congr fun i ℓ => forall₂_congr fun m d =>
      forall_congr' fun pay => forall₂_congr fun _ _ => forall₂_congr fun _ _ => ?_
    exact ⟨fun h => h (Nat.zero_le _), fun h _ => h⟩

/-- Settled locks are settled above every floor. -/
theorem LocksSettledU.toFrom {u : Nat → Set Lock} {T : Time} (h : LocksSettledU u tr H U T)
    (σ₀ : Nat) : LocksSettledFromU u tr H U σ₀ T := by
  rw [locksSettledFromU_iff]
  intro y hy i hi l hl hlive L hL hLr
  obtain ⟨hv, hp⟩ := locksSettledU_iff.1 h y hy i hi l hl hlive L hL hLr
  exact ⟨votesExtendFrom_iff.2 fun x hx j e he hs _ => votesExtendAfter_iff.1 hv x hx j e he hs,
    proposalsExtendFromU_iff.2 fun x hx j ℓ m d pay hc hcall ht hm _ hd =>
      proposalsExtendAfterU_iff.1 hp x hx j ℓ m d pay hc hcall ht hm hd⟩

theorem LocksSettledFromU.mono {u : Nat → Set Lock} {σ₀ : Nat} {T T' : Time}
    (h : LocksSettledFromU u tr H U σ₀ T) (hT : T ≤ T') : LocksSettledFromU u tr H U σ₀ T' :=
  locksSettledFromU_iff.2 fun y hy i hi => locksSettledFromU_iff.1 h y hy i (hT.trans hi)

/-- A higher floor is weaker. -/
theorem LocksSettledFromU.floor_mono {u : Nat → Set Lock} {σ₀ σ₁ : Nat} {T : Time}
    (h : LocksSettledFromU u tr H U σ₀ T) (hσ : σ₀ ≤ σ₁) : LocksSettledFromU u tr H U σ₁ T := by
  rw [locksSettledFromU_iff]
  intro y hy i hi l hl hlive L hL hLr
  obtain ⟨hv, hp⟩ := locksSettledFromU_iff.1 h y hy i hi l hl hlive L hL hLr
  exact ⟨votesExtendFrom_iff.2 fun x hx j e he hs hσs =>
      votesExtendFrom_iff.1 hv x hx j e he hs (hσ.trans hσs),
    proposalsExtendFromU_iff.2 fun x hx j ℓ m d pay hc hcall ht hm hσm hd =>
      proposalsExtendFromU_iff.1 hp x hx j ℓ m d pay hc hcall ht hm (hσ.trans hσm) hd⟩

end Consensus.Goldilocks.SA

end
