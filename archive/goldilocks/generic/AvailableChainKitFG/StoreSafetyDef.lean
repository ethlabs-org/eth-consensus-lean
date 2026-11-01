module
public import AvailableChainKitFG.CertificateCoreDef
public import AvailableChainKitFG.RootScopeDef
public import AvailableChainSimplexFG.Store
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

def NoSlashOutside (faulty : Finset V)
    (A B : Finset (Row V)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B,
    a.signer ∉ faulty → ¬ Slashable a b

omit [Fintype V] [RowCodec V] in
theorem NoSlashOutside_def (faulty : Finset V)
    (A B : Finset (Row V)) :
    NoSlashOutside faulty A B =
      (∀ a ∈ A, ∀ b ∈ B,
        a.signer ∉ faulty → ¬ Slashable a b) := rfl

/-- Structural store facts do not require a fault or no-slash premise. -/
structure FGStoreInvariant
    (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) : Prop where
  closed :
    ∀ B ∈ st.TF, B.parent ∈ st.TF
  gen :
    FGBlock.genesis ∈ st.TF
  Fmem :
    st.F ∈ st.TF
  hmax :
    st.h_max = st.TF.sup (fun B => (H B).h) ⊔ 1
  pair :
    (∃ C ∈ st.TF,
      FGBlock.Preceq st.F (H C).J ∧
      st.h_j = (H C).h_j ∧ st.J = (H C).J) ∧
    (∀ B ∈ st.TF, FGBlock.Preceq st.F (H B).J →
      lexKey ((H B).h_j, (H B).J) ≤ lexKey (st.h_j, st.J))
  FJ :
    FGBlock.Preceq st.F st.J
  Fcar :
    ∃ D ∈ st.TF, (f D).F = st.F

structure FGStoreSafety (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V)
    {S : Type}
    (read : S → Store V)
    (cache : S → FGBlock V → FGHeight V × FGFinality V)
    (initial : S)
    (step : S → FGBlock V → S)
    (Good : S → Prop) (StepOK : S → FGBlock V → Prop) : Prop where
  initial_good :
    Good initial

  invariant :
    ∀ s, Good s → FGStoreInvariant H f (read s)

  step_good :
    ∀ s B, Good s → StepOK s B → Good (step s B)

  tree_mono :
    ∀ s B, Good s →
      (read s).TF ⊆ (read (step s B)).TF

  accepted_F_mono :
    ∀ s B, Good s →
      FGBlock.Preceq (read s).F (read (step s B)).F

  cache_eq :
    ∀ s, Good s → ∀ B ∈ (read s).TF,
      cache s B = (H B, f B)

  -- The carrier D gives the threshold. W need not be in the store.
  F_lock_no_evidence :
    ∀ s, Good s → ∀ D W, RootInjectiveOn D W →
      D ∈ (read s).TF →
      (f D).F = (read s).F →
      (f D).h_F < (H W).h →
      ¬ HasSlashableWeightBetween E (chainRows D) (chainRows W) →
      FGBlock.Preceq (read s).F W

  F_lock_fault :
    ∀ s, Good s → ∀ D W, RootInjectiveOn D W → ∀ faulty : Finset V,
      D ∈ (read s).TF →
      (f D).F = (read s).F →
      (f D).h_F < (H W).h →
      E.weightOf faulty + E.totalWeight < 2 * E.q →
      NoSlashOutside faulty (chainRows D) (chainRows W) →
      FGBlock.Preceq (read s).F W

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] Roots on the inserted tree. -/
def StoreStepRoots (st : Store V) (B : FGBlock V) : Prop :=
  ViewRootInj (insert B st.TF)

omit [Fintype V] in
/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] The local step premise. -/
theorem StoreStepRoots_def (st : Store V) (B : FGBlock V) :
    StoreStepRoots st B = ViewRootInj (insert B st.TF) := rfl

/-- The accepted threshold is zero at genesis, even for a nonzero certificate height. -/
def acceptedThreshold (F : FGBlock V) (certificateHeight : Height) : Height :=
  if F = .genesis then 0 else certificateHeight

omit [Fintype V] [RowCodec V] in
theorem acceptedThreshold_def (F : FGBlock V) (certificateHeight : Height) :
    acceptedThreshold F certificateHeight =
      (if F = .genesis then 0 else certificateHeight) := rfl

end AvailableChain.KitFG
end
