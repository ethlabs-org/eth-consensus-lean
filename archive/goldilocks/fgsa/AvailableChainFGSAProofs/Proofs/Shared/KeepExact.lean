module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover -- shake: keep (P3 M6 dependency)
public import AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry -- shake: keep (P3 M6 dependency)
public import AvailableChainFGSAClaims.Statements.ChannelProps

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.8, G31; 21 H.13–H.14; GLY F-25. Class (iii), composition.
DC: FGRootWitness.lean:548 `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`
is a root-compatibility ingredient, not an FJ retention theorem.
INTENTIONAL: FJ uses the duty's X and its witness W (F-25).
Source extraction for an incompatible control is an explicit supplier;
this lemma does not prove the run-level certificate provenance (21 H.13).
A floor witness rules out band exclusion, including the two-source case.
RExcl/H.13 must prove the band, contested and two-source cause cases outside this lemma (21
:2599–2627). -/
theorem kept_or_conflict (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hC : C ∈ X) (hW : W ∈ X) (hCW : FGBlock.Preceq C W)
    (hlo : (R_at p c E rho i x).lo ≤ hOf p.E p.cfg W)
    (hcontrolSource : ∀ K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z],
      ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K) →
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        FGBlock.Preceq K C' ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') :
    Kept p c E rho i x X C ∨
      (∃ C' s, SourceBefore p c E rho i C' s ∧
        ¬ Block.Compatible (eraseFG C) (eraseFG C') ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') := by
  delta Kept D_at
  simp only [domainR_def]
  have cause (K : FGBlock (Fin p.n))
      (hK : K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z])
      (hbad : ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K)) :
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        ¬ Block.Compatible (eraseFG C) (eraseFG C') ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C' := by
    obtain ⟨C', s, hsrc, hKC', hh⟩ := hcontrolSource K hK hbad
    refine ⟨C', s, hsrc, ?_, hh⟩
    intro hc
    have hKC : Block.Compatible (eraseFG K) (eraseFG C) :=
      block_compatible_of_preceq_compatible (eraseFG_preceq hKC')
        (by
          change Block.compatible (eraseFG C') (eraseFG C) = true
          rw [block_compatible_comm]
          exact hc)
    have hfg : FGBlock.compatible K C = true := by
      rcases Bool.or_eq_true_iff.mp hKC with hKC | hCK
      · exact Bool.or_eq_true_iff.mpr (Or.inl (eraseFG_preceq_iff.mp hKC))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq_iff.mp hCK))
    exact hbad (Bool.or_eq_true_iff.mp hfg)
  by_cases hF : FGBlock.Preceq (storeAt p c E rho i x).fg.F C ∨
      FGBlock.Preceq C (storeAt p c E rho i x).fg.F
  · by_cases hZ : FGBlock.Preceq (R_at p c E rho i x).Z C ∨
        FGBlock.Preceq C (R_at p c E rho i x).Z
    · apply Or.inl
      rcases hF with hFC | hCF
      · rcases hZ with hZC | hCZ
        · apply Or.inr ∘ Or.inl
          rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hlo
          exact (KitFG.mem_filteredFromView (heightView p) _ _ C).mpr
            ⟨hC, hFC, hZC, W, hW, hCW, hlo⟩
        · exact Or.inl hCZ
      · exact Or.inr (Or.inr hCF)
    · exact Or.inr (cause _ (by simp) hZ)
  · exact Or.inr (cause _ (by simp) hF)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.8, G31; 21 H.13–H.14; GLY F-25. Class (iii), composition.
DC: FGRootWitness.lean:548 `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`
is a root-compatibility ingredient, not an FJ retention theorem.
INTENTIONAL: FJ uses the duty's X and its witness W (F-25).
Source extraction for an incompatible control is an explicit supplier;
this lemma does not prove the run-level certificate provenance (21 H.13).
A floor witness rules out band exclusion, including the two-source case.
RExcl/H.13 must prove the band, contested and two-source cause cases outside this lemma (21
:2599–2627). -/
theorem kept_or_cause (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hC : C ∈ X) (hW : W ∈ X) (hCW : FGBlock.Preceq C W)
    (hlo : (R_at p c E rho i x).lo ≤ hOf p.E p.cfg W)
    (hcontrolSource : ∀ K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z],
      ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K) →
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        FGBlock.Preceq K C' ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') :
    KeepOrCause p c E rho i x X C := by
  rcases kept_or_conflict p c E rho i x X C W hC hW hCW hlo hcontrolSource with hk | hc
  · exact Or.inl hk
  · apply Or.inr ∘ Or.inl
    simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
      using hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
F1b.5a closure at a later pivot in the same FG-SA duty domain.
DC: Goldfish/Walk.lean:433 `ghost_reaches` uses a path in its tree.
INTENTIONAL: this local corollary moves FJ filtered closure from A to T
for F1b.8 (21 H.17); it adds no generic walk declaration. -/
theorem fgsa_domain_anchorClosed_mono (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (A T : Block)
    (hAT : Block.Preceq A T)
    (hclosed : Gen.Pure.AnchorClosed A (erasedList st (domainR p st X))) :
    Gen.Pure.AnchorClosed T (erasedList st (domainR p st X)) := by
  intro B hB hTB C hTC hCB
  exact hclosed B hB (block_preceq_trans hAT hTB) C (block_preceq_trans hAT hTC) hCB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. P3 F1b.8, G33; class (iii), conditional pivot composition.
DC: ProposalWalkTransportCore.lean:162 `ghost_transport_of_source` and
Goldfish/Walk.lean:433 `ghost_reaches`. INTENTIONAL: FJ uses a common pivot,
not equal live roots (21 H.17:2798–2825). This theorem applies to each target read.
Premise suppliers (S1b `a0-s1b-reuse-21.md`:118–134):
* `hstart`: E1:122–123, both start orders; H.17:2798–2801.
* `hTP`: common pivot:119–121, the T-to-A_P path in H.17.
* `hprefix`: E2:124–125, the honest-supported path below T; H.17:2800–2801.
* `hancestry`, membership: E3/E5:126–132, K ⪯ X and st_ρ ⪯ X; H.17:2820–2823.
* `hancestry`, eligibility: E5:131–132; H.17:2821–2823.
* `hancestry`, score bound and root tie: E4/E5:128–132; bp21:789 and
  H.17:2823–2824 (equal retained scores, eligibility and root tie order).
  Below a source start above T, no proposer-chosen child exists on [T, source start);
  the order there comes from the ordinary proposer walk (H.17:2780–2784).
  H.17:2810–2819 excludes old children conflicting with high F_p between T and A_P.
* `hlast`: E6:133–134; H.17:2824–2825, P = Q or the only eligible child Q.
* `hstop`: E6:133–134; H.17:2824–2825, Q has no valid child.
The ancestry premise subsumes source coverage, persistence, reflection and score
agreement. Thus source-store parameters and their E1/E2 premises are not needed here;
apply `hstart` separately to each compared store. Closure is also not needed once
`hlast` and `hstop` are supplied. The old two-store form is `exactHead_of_pivot`.
This local result does not produce ExactService or identify a scheduled HEAD read. -/
theorem exactHead_of_pivot_ancestry (p : Params) (st : State p.n)
    (Y : Finset (FGBlock (Fin p.n)))
    (raw support : List (GridCO.Wire p.n .root)) (T P Q : Block)
    (hroot : ∀ A ∈ erasedList st (domainR p st Y),
      ∀ B ∈ erasedList st (domainR p st Y), A.root = B.root → A = B)
    (hstart : (Block.Preceq (liveRoot p st) T ∧
      DominatedSuffix (liveRoot p st) T (erasedList st (domainR p st Y))
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) ∨
      (Block.Preceq T (liveRoot p st) ∧ Block.Preceq (liveRoot p st) P))
    (hTP : Block.Preceq T P)
    (hancestry : ∀ X, Block.Preceq T X → Block.Preceq (liveRoot p st) X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ erasedList st (domainR p st Y) ∧ eligible p st raw support C = true ∧
        ∀ D ∈ erasedList st (domainR p st Y), D.parent? = some X →
          eligible p st raw support D = true →
          GridCO.goldfishScore st.base.blocks raw support D ≤
            GridCO.goldfishScore st.base.blocks raw support C ∧
          (GridCO.goldfishScore st.base.blocks raw support D =
            GridCO.goldfishScore st.base.blocks raw support C → D.root ≤ C.root))
    (hlast : P = Q ∨
      (Q ∈ erasedList st (domainR p st Y) ∧ Q.parent? = some P ∧
        eligible p st raw support Q = true ∧
        ∀ C ∈ erasedList st (domainR p st Y), C.parent? = some P →
          eligible p st raw support C = true → C = Q))
    (hstop : NoEligibleChild (erasedList st (domainR p st Y)) (eligible p st raw support) Q) :
    headInTree p st (erasedList st (domainR p st Y)) raw support = Q := by
  rw [fgsa_headInTree_reanchor_of_pivot p st _ raw support T P
    hroot hstart hTP hancestry]
  rcases hlast with rfl | ⟨hm, hp, hel, honly⟩
  · apply walk_exact_of_dominated_suffix _ _ _ _ _ (block_preceq_refl _) _ hstop
    intro C hPC hCP
    have he := block_preceq_antisymm (Bool.and_eq_true_iff.mp hPC).2 hCP
    subst C
    change ((!decide (P = P)) && Block.preceq P P) = true at hPC
    simp only [decide_true, Bool.not_true, Bool.false_and] at hPC
    cases hPC
  · have hPQ : Block.Preceq P Q := by
      cases Q with
      | genesis => cases hp
      | node R s root r =>
          have he : R = P := Option.some.inj hp
          subst R
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
    apply walk_exact_of_dominated_suffix _ _ _ _ _ hPQ _ hstop
    intro C hPC hCQ
    have hC : C = Q := by
      cases Q with
      | genesis => cases hp
      | node R s root r =>
          have he : R = P := Option.some.inj hp
          subst R
          rcases Bool.or_eq_true_iff.mp hCQ with he | hCP
          · exact of_decide_eq_true he
          · have he := block_preceq_antisymm (Bool.and_eq_true_iff.mp hPC).2 hCP
            subst C
            change ((!decide (P = P)) && Block.preceq P P) = true at hPC
            simp only [decide_true, Bool.not_true, Bool.false_and] at hPC
            cases hPC
    subst C
    refine ⟨hm, hel, ?_⟩
    intro D hD hpD helD hne
    exact (hne (honly D hD (hpD.trans hp) helD)).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Lower-start corollary with target-tree root uniqueness.
DC: ProposalWalkTransportCore.lean:162 and Goldfish/Walk.lean:433.
INTENTIONAL: S1b E1's lower branch and the original G11 suppliers derive the
ancestry premise of `exactHead_of_pivot_ancestry` (21 H.17:2820–2825).
`hclosed` is retained for source compatibility; the generalized proof does not need it. -/
theorem exactHead_of_pivot (p : Params) (st st' : State p.n)
    (X Y : Finset (FGBlock (Fin p.n)))
    (raw support raw' support' : List (GridCO.Wire p.n .root)) (T P Q : Block)
    (hroot : ∀ A ∈ erasedList st' (domainR p st' Y),
      ∀ B ∈ erasedList st' (domainR p st' Y), A.root = B.root → A = B)
    (hAT : Block.Preceq (liveRoot p st) T) (hAT' : Block.Preceq (liveRoot p st') T)
    (hTP : Block.Preceq T P)
    (hprefix : DominatedSuffix (liveRoot p st) T (erasedList st (domainR p st X))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support))
    (hprefix' : DominatedSuffix (liveRoot p st') T (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st'.base.blocks raw' support') (eligible p st' raw' support'))
    (hcover : Block.Preceq P (headInTree p st (erasedList st (domainR p st X)) raw support))
    (hkeep : SuffixPersists T P
      (erasedList st (domainR p st X)) (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st.base.blocks raw support)
      (eligible p st raw support) (eligible p st' raw' support'))
    (hreflect : SuffixReflects T P
      (erasedList st (domainR p st X)) (erasedList st' (domainR p st' Y))
      (eligible p st raw support) (eligible p st' raw' support'))
    (hscore : SuffixScoresAgree T P (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishScore st'.base.blocks raw' support') (eligible p st' raw' support'))
    (hlast : P = Q ∨
      (Q ∈ erasedList st' (domainR p st' Y) ∧ Q.parent? = some P ∧
        eligible p st' raw' support' Q = true ∧
        ∀ C ∈ erasedList st' (domainR p st' Y), C.parent? = some P →
          eligible p st' raw' support' C = true → C = Q))
    (hclosed : AnchorClosed T (erasedList st' (domainR p st' Y)))
    (hstop : NoEligibleChild (erasedList st' (domainR p st' Y)) (eligible p st' raw' support') Q) :
    headInTree p st' (erasedList st' (domainR p st' Y)) raw' support' = Q := by
  have _hclosed := hclosed
  have hs := walk_reanchor_of_dominated_suffix _ _ _ _ _ hAT hprefix
  change Block.Preceq P (GridCO.ghost _ _ _ _) at hcover
  rw [hs] at hcover
  have hc := ghost_transfer_sfx _ _ _ _ _ _ _ _ hTP hcover hkeep hreflect hscore
  exact exactHead_of_pivot_ancestry p st' Y raw' support' T P Q hroot (Or.inl ⟨hAT', hprefix'⟩) hTP
    (fun X hTX _ => walk_best_ancestry_of_cover _ _ _ _ _ hc X hTX) hlast hstop

end AvailableChain.FGSA.Run
