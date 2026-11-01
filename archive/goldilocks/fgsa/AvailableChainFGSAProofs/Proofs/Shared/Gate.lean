module
public import AvailableChainFGSARun.Proofs.AC
public import AvailableChainGeneric.Proofs.AC.Duty.Transfer
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

/-! G32 gate family (P3 F1b.7). The transfer proofs instantiate Gen AC
with T7.15 reads and gate effects. No ACLaws premise is required.
The source-selector proof is lane-local until GLY adds a Gen source-selector read
(lean-framework 2026-09-30). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
G32 covering service, with the atomic count and walk premises of Gen. -/
theorem fgsa_gate_of_coveringBatch (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (s : Slot) (x : V) (D : Block)
    (ht : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hEnabled : enabledGateAt p c E rho i x s)
    (hcover : ∃ C, (fgsaAC E rho).raw i s x = some C ∧ Block.Preceq D C)
    (hguard : ∀ C, (fgsaAC E rho).raw i s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C)
    (hne : D ≠ .genesis) (hmem : D ∈ ((fgsaAC E rho).gateView i x s).blocks)
    (hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s D)
    (hlevel : SA.releaseThreshold p.toParams ∈ (fgsaAC E rho).gateLevels i x s D) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x D := by
  have hf : (fgsaAC E rho).saved i x s = none := fgsa_gate_fresh E rho hs ht
  rcases (fgsaAC_gate_write E rho i s x
    (by rw [clockPre_joined]
        exact fgsa_gate_joined_of_enabled E rho hEnabled) ht).effects with hskip | hrun
  · obtain ⟨⟨result, hr⟩, _⟩ := hskip
    rw [hf] at hr
    cases hr
  · exact Gen.AC.Duty.gate_of_coveringBatch (fgsaAC E rho) i s x D
      (fun C hC hg => (hrun.accept C hC hg).2) hcover hguard hne hmem hsupport hlevel

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
G32 exact service. The old output has no strict extension of X. -/
theorem fgsa_S_eq_of_exact (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (s : Slot) (x : V) (X : Block) (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hEnabled : enabledGateAt p c E rho i x s)
    (hraw : (fgsaAC E rho).raw i s x = some X)
    (hguard : ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) X)
    (hold : Block.Preceq X ((fgsaAC E rho).output i x) → (fgsaAC E rho).output i x = X)
    (hanchor : Block.Preceq ((fgsaAC E rho).anchor i x) X) :
    (fgsaAC E rho).output (i + 1) x = X ∧
      ∀ lease ∈ (fgsaAC E rho).leases (i + 1) x,
        (fgsaAC E rho).now (i + 1) x < Gen.AC.Lease.deadline lease →
          Block.Preceq (Gen.AC.Lease.target lease) X := by
  have hf : (fgsaAC E rho).saved i x s = none := fgsa_gate_fresh E rho hs ht
  rcases (fgsaAC_gate_write E rho i s x
    (by rw [clockPre_joined]
        exact fgsa_gate_joined_of_enabled E rho hEnabled) ht).effects with hskip | hrun
  · obtain ⟨⟨result, hr⟩, _⟩ := hskip
    rw [hf] at hr
    cases hr
  · exact Gen.AC.Duty.S_eq_of_exact (fgsaAC E rho) i s x X
      (fun hr hg => (hrun.accept X hr hg).1) hraw hguard hold hanchor
      (fgsaAC_lease_le_output E rho (i + 1) x hx)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
COVERING SELECTOR STEP: G32 opening-source coverage from local retention and service facts
of S1b R15 and S1c P5. `sourceCandidates` requires the selected fast-write
label and a live lease. Retention in the full filtered domain is separate. -/
theorem openingSource_extends_served (i : Nat) (x : V) (r : Nat)
    (D : FGBlock (Fin p.n)) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    D ∈ domainR p st (treeT p st) →
    eraseFG D ∈ sourceCandidates p st →
    ∃ C, FGSA.fgSource p st = some C ∧ FGBlock.Preceq D C := by
  intro st hkept hserved
  have hbundle := storeBundle_postClock E rho i x (p.actionTime r)
  have hbelow : ∀ b ∈ sourceCandidates p st, Block.Preceq b st.base.stableRecord := by
    intro b hb
    rw [sourceCandidates_def] at hb
    have hlive := (Finset.mem_filter.mp hb).2
    change ((st.base.obligations.find? (fun row => row.1 == b)).map
      (fun row => row.2.2)).any (fun d => decide (st.base.now < d)) = true at hlive
    cases hf : st.base.obligations.find? (fun row => row.1 == b) with
    | none => simp only [hf, Option.map_none, Option.any_none, Bool.false_eq_true] at hlive
    | some lease =>
      have ht : st.base.now < lease.2.2 := by
        simpa only [hf, Option.map_some, Option.any_some, decide_eq_true_eq] using hlive
      have he : lease.1 = b := by simpa using List.find?_some hf
      exact he ▸ hbundle.lease lease (List.mem_of_find?_eq_some hf) ht
  let candidates := (domainR p st (treeT p st)).filter
    (fun B => decide (eraseFG B ∈ sourceCandidates p st))
  have hD : D ∈ candidates := Finset.mem_filter.mpr ⟨hkept, by simpa using hserved⟩
  have hsub : candidates ⊆ st.fg.TF := by
    intro B hB
    have hd := (Finset.mem_filter.mp hB).1
    rw [domainR_def, treeT_def] at hd
    exact ((KitFG.mem_filteredFromView (heightView p) _ _ B).mp hd).1
  have hinv : CStoreInv p st := hbundle.cstore
  obtain ⟨C, hC, hmem, hmax⟩ := deepest_spec p st hinv candidates hsub ⟨D, hD⟩
  refine ⟨C, ?_, ?_⟩
  · rw [fgSource_eq_jointSource p st, jointSource_def]
    exact hC
  · have hcandidate : eraseFG C ∈ sourceCandidates p st := by
      simpa using (Finset.mem_filter.mp hmem).2
    have hdepth : (eraseFG D).depth ≤ (eraseFG C).depth := by
      rcases hmax D hD with hlt | ⟨heq, _⟩ <;> omega
    apply preceq_of_eraseFG_preceq (viewRootInj_TF p st hinv)
      ⟨D, hsub hD, KitFG.preceq_refl D⟩ ⟨C, hsub hmem, KitFG.preceq_refl C⟩
    have hcompat := Gen.Pure.block_compatible_of_common (hbelow _ hserved) (hbelow _ hcandidate)
    rcases Bool.or_eq_true_iff.mp hcompat with hDC | hCD
    · exact hDC
    · rw [Gen.Pure.prefix_eq_of_depth _ _ hCD hdepth]
      exact Gen.Pure.block_preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
R15 EXACT selector step. No selected candidate strictly extends D.
The temporal first-opening composition is a separate consumer result. -/
theorem openingSource_eq_of_no_strict_extension (i : Nat) (x : V) (r : Nat)
    (D : FGBlock (Fin p.n)) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    D ∈ domainR p st (treeT p st) →
    eraseFG D ∈ sourceCandidates p st →
    (∀ C, C ∈ domainR p st (treeT p st) → eraseFG C ∈ sourceCandidates p st →
      FGBlock.Preceq D C → C = D) →
    FGSA.fgSource p st = some D := by
  intro st hkept hserved hmax
  obtain ⟨C, hC, hDC⟩ := openingSource_extends_served E rho i x r D hkept hserved
  have hm := hC
  rw [fgSource_eq_jointSource] at hm
  have hmem := (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hm).1)
  have heq := hmax C hmem.1 (of_decide_eq_true hmem.2) hDC
  exact heq ▸ hC

end AvailableChain.FGSA.Run
end
