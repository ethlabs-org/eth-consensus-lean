module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGate

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Clean history bounds the exact enabled pre-gate store, including saved rows.
The P-Cl1 history supplier carries restart and suppressed-gate cases. -/
theorem inclusion_preGate_bounds [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x pt.s)
    (hstrat : RStrat p c E rho) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams pt.s)
    Block.Preceq (eraseFG pre.fg.F) pt.P ∧ Block.Preceq (eraseFG pre.fg.J) pt.P ∧
      Block.Preceq (S_at p c E rho i x) pt.P ∧
      (∀ row ∈ pre.base.obligations, Block.Preceq row.1 pt.P) ∧
      (∀ r C, GridCO.savedGenuine pre.base r = some (some C) → Block.Preceq C pt.P) ∧
      (∀ r X, X ∈ (fastWriteAt pre r).getD [] → Block.Preceq X pt.P) := by
  let d := SA.gateTime p.toParams pt.s
  let k := V2.D.Run.idxBefore rho d
  let pre := clockPre p (storeAt p c E rho i x) d
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have hhead := inclusion_headAtLabel (hstrat := hstrat) E rho ΔF hset hInputs
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor
  have hpos : 0 < pt.s := hprop.1.1
  have hresults := inclusion_prior_results_below E rho hset hordered hnonempty htransfer
    pt.s pt.P hpos hhor hhead hx
  have hcut : k ≤ timeIdx rho rho.horizon := inclusion_idxBefore_le_timeIdx rho hhor
  have hbelow {X : Block} {r : Slot} (hX : BelowLabel p c E rho k r X) :
      Block.Preceq X pt.P := by
    rcases hX with rfl | ⟨q, B, hB, _, hXB⟩
    · exact block_genesis_preceq _
    · exact block_preceq_trans hXB (hresults q B hB)
  have hb := hHistory.below k x hcut hx
  have heq : storeAt p c E rho i x = storeAt p c E rho k x := by
    unfold storeAt
    rw [inclusion_preTick_eq_timeRead_enabled E rho hs hG,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
  have hfpre : Block.Preceq (eraseFG pre.fg.F) pt.P := by
    dsimp only [pre]
    rw [clockPre_fg, heq]
    exact hbelow hb.1
  have hjpre : Block.Preceq (eraseFG pre.fg.J) pt.P := by
    dsimp only [pre]
    rw [clockPre_fg, heq]
    exact hbelow hb.2.1
  have hsavepre : ∀ r C, GridCO.savedGenuine pre.base r = some (some C) →
      Block.Preceq C pt.P := by
    intro r C hC
    dsimp only [pre] at hC
    rw [savedGenuine_congr (clockPre_genuine p _ d) r, heq] at hC
    exact hbelow (hb.2.2.2.2 r C hC)
  refine ⟨hfpre, hjpre, ?_, ?_, hsavepre, ?_⟩
  · rw [S_at_def, heq]
    exact hbelow hb.2.2.1
  · intro row hr
    have hm := (clockPre_obligations_sublist p (storeAt p c E rho i x) d).subset hr
    rw [heq] at hm
    exact hbelow (hb.2.2.2.1 row hm)
  · intro r X hX
    have hinv : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) d
    cases hf : pre.fastWrite.find? (fun row => row.1 == r) with
    | none =>
      change X ∈ ((pre.fastWrite.find? _).map Prod.snd).getD [] at hX
      simp only [hf, Option.map_none, Option.getD_none, List.not_mem_nil] at hX
    | some row =>
      have hm := List.mem_of_find?_eq_some hf
      change X ∈ ((pre.fastWrite.find? _).map Prod.snd).getD [] at hX
      simp only [hf, Option.map_some, Option.getD_some] at hX
      rcases hinv.fastOrigin row hm X hX with ⟨C, hC, hXC⟩ | hXF
      · exact block_preceq_trans hXC (hsavepre row.1 C hC)
      · exact block_preceq_trans hXF hfpre

end AvailableChain.FGSA.Run
end
