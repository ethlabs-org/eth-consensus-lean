module
public import AvailableChainGeneric.Proofs.AC.RootVotes
public import AvailableChainGeneric.Proofs.Pure.BatchDominance
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

namespace AvailableChain.Gen.AC.Root

open AvailableChain AvailableChain.GridCO AvailableChain.Gen.Pure

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508; DGF/Adoption:415; INTENTIONAL: retain the eligible
compatible anchor and apply the shared count core to the stored suffix. -/
theorem batch_anchored : BatchStatement := by
  rw [BatchStatement_def]
  intro n tree D raw support Hon h m anchor X hraw hsupport hcard hclean hbatch
    hother hb hcompatible hpath hanchor
  have bounds := batch_counts tree D raw support Hon h m X
    hraw hsupport hcard hclean hbatch hother hb
  refine ⟨bounds, ?_⟩
  apply walk_covers_of_dominated_suffix_of_anchor_eligible anchor X tree
    (goldfishScore tree raw support)
    (fun B => decide (voterCount D < 2 * goldfishScore tree raw support B))
    hcompatible ?_ (decide_eq_true_eq.mpr hanchor)
  rw [DominatedSuffix_def]
  intro C hAC hCX
  have hscore := (bounds.2.2.1 C hCX).1
  have hpass := anchor_passes h m (voterCount D) (goldfishScore tree raw support C)
    hb bounds.2.1 hscore
  refine ⟨hpath C hAC hCX, hpass.2, ?_⟩
  intro Y _hY hp _hel hne
  have hdepth : C.depth = Y.depth := by
    cases C with
    | genesis =>
        cases Y with
        | genesis => rfl
        | node P s r_s id => change some P = none at hp; contradiction
    | node P s r_s id =>
        cases Y with
        | genesis => change none = some P at hp; contradiction
        | node Q t r_t jd =>
            change some Q = some P at hp
            cases Option.some.inj hp
            rfl
  have hconflict : Block.compatible C Y = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    rcases Bool.or_eq_true_iff.mp hc with hCY | hYC
    · exact hne (prefix_eq_of_depth C Y hCY (le_of_eq hdepth.symm)).symm
    · exact hne (prefix_eq_of_depth Y C hYC (le_of_eq hdepth))
  have hXY : Block.compatible X Y = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    have hCY := block_compatible_of_preceq_compatible hCX hc
    change Block.compatible C Y = true at hCY
    simp only [hconflict, Bool.false_eq_true] at hCY
  have hrest := bounds.2.2.2.1 Y hXY
  have hlt := hb.lt
  omega

end AvailableChain.Gen.AC.Root
