module
public import AvailableChainPCSA.Model.FrameCore
public import AvailableChainFGSA.Proofs.WindowHeightBridge
public import AvailableChainFGSA.Proofs.WindowInvariant
public import AvailableChainGeneric.Proofs.Pure.PCQuorum
public import AvailableChainGeneric.Proofs.Pure.Quorum
public import AvailableChainKitFG.WeightsBridge

public section

/-! No FG height event with rows from fewer than q_A signers (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA
open SimplexFG

/-- The Generic count bound converts the PC fault bound to the FG quorum bound. -/
theorem pcsa_faults_lt_fg_quorum (p : Params) (F : Finset (Fin p.n))
    (hF : F.card < Gen.Pure.qA p.n) : p.E.weightOf F < p.E.q := by
  have htwo := (Gen.Pure.lt_qA_iff_two_mul_lt p.n F.card).mp hF
  have hclean := Gen.Pure.count_clean (n := p.n) (a := F.card) (h := p.n - F.card)
    (by omega) le_rfl
  have hw : p.E.weightOf F = F.card := by
    dsimp only [FGSA.Params.E, Electorate.weightOf]
    simp
  rw [hw, ← KitFG.toWeights_q]
  dsimp only [FGSA.Params.E]
  rw [KitFG.unit_toWeights_q]
  exact hclean.lt

/-- Without a quorum of row signers, each block keeps the initial FG height and frame. -/
theorem pcsa_window_no_quorum (p : Params) (F : Finset (Fin p.n))
    (hF : p.E.weightOf F < p.E.q) (B : FGBlock (Fin p.n))
    (hrows : ∀ W, FGBlock.Preceq W B → ∀ a ∈ W.rows, a.signer ∈ F) :
    (FGSA.Window.derive p p.K_W B).h = 1 ∧
    (FGSA.Window.derive p p.K_W B).h_j = 0 ∧
    (FGSA.Window.derive p p.K_W B).J = .genesis ∧
    (FGSA.Window.derive p p.K_W B).F = .genesis := by
  have H := FGSA.Window.windowHeightLaws p p.K_W p.kWLarge
  have hh : (FGSA.Window.derive p p.K_W B).h = 1 := by
    have hlo := H.one_le_h B
    by_contra hn
    have hhi : 1 < (FGSA.Window.projectHeight (FGSA.Window.derive p p.K_W B)).h := by
      change 1 ≤ (FGSA.Window.derive p p.K_W B).h at hlo
      change 1 < (FGSA.Window.derive p p.K_W B).h
      unfold Height at *
      omega
    obtain ⟨X, _, _, Q, hQ, hcert⟩ := H.height_crossing B 1 le_rfl hhi
    have hcap : p.E.toWeights.weightOf F < p.E.toWeights.q := by
      rw [KitFG.toWeights_weightOf, KitFG.toWeights_q]
      exact hF
    obtain ⟨i, hi, hif⟩ := Gen.Pure.quorum_honest p.E.toWeights F
      ((KitFG.isQuorum_toWeights_iff p.E Q).mpr hQ) hcap
    obtain ⟨W, a, hW, ha, hai, _⟩ := hcert i hi
    exact hif (hai ▸ hrows W hW a ha)
  have hj : (FGSA.Window.derive p p.K_W B).h_j = 0 := by
    have h := H.justified_below_height B
    change (FGSA.Window.derive p p.K_W B).h_j < (FGSA.Window.derive p p.K_W B).h at h
    unfold Height at *
    omega
  have ht : (FGSA.Window.derive p p.K_W B).T_h = .genesis := by
    have h := H.entry_plateau (KitFG.genesis_preceq B) (by exact hh.symm)
    exact h.symm
  have hJ : (FGSA.Window.derive p p.K_W B).J = .genesis := by
    apply KitFG.preceq_genesis.mp
    have h := H.justified_preceq_entry B
    change FGBlock.Preceq (FGSA.Window.derive p p.K_W B).J
      (FGSA.Window.derive p p.K_W B).T_h at h
    rwa [ht] at h
  refine ⟨hh, hj, hJ, ?_⟩
  exact KitFG.preceq_genesis.mp (hJ ▸ FGSA.Window.window_F_preceq_J p p.K_W p.kWLarge B)

end AvailableChain.PCSA
end
