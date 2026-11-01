module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAClaims.Statements.FrameNext
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
F1.1 snapshot: T7.5 (via Gen E-10) and the FG-SA active-view library. -/
theorem fgsa_rStore : RStore p c E rho := by
  intro i x _
  have h := cstoreInv_stateBefore E rho i x
  have hg := actView_genesis_F p _ h
  have hf := actView_fields (storeAt p c E rho i x)
  exact ⟨h, actView_blocks _, hg.1, hg.2,
    fun _ hb _ ha => actView_ancestor_closed p _ h hb ha, hf.1, hf.2.2.1, hf.2.1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
D24 cumulative channel, separate from the FG bounds channel. -/
theorem fgsa_rStoreCumul : RStoreCumul p c E rho := by
  intro hnr i j x _ hij _
  have h := fgsa_store_cumulative p c E rho hnr hij x
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Durable trees and signed rows persist through restarts. -/
theorem fgsa_rStoreDurable : RStoreDurable p c E rho :=
  fun _ _ x _ hij _ => fgsa_store_durable p c E rho hij x

/-- Stamp prefixes use the exact local restart-free event interval. -/
theorem fgsa_rStoreEpoch : RStoreEpoch p c E rho := by
  intro i j x _ hij _ hrf
  have h := fgsa_store_cumulative_on p c E rho hij x hrf
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
D24 FG bounds persist through the retained FG store at every restart. -/
theorem fgsa_rMonoAll : RMonoAll p c E rho := by
  intro i j x _ hij
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => FGBlock.Preceq a.fg.F nd.st.fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey (nd.st.fg.h_j, nd.st.fg.J) ∧
      a.fg.h_max ≤ nd.st.fg.h_max)
    ?_ ?_ (fun _ _ h => h) E rho hij x ?_
    ⟨KitFG.preceq_refl _, le_rfl, le_rfl⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (clock p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey ((clock p nd.st t).fg.h_j, (clock p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (clock p nd.st t).fg.h_max
    rw [clock_fg]
    exact h
  · intro nd o h
    exact ⟨KitFG.preceq_trans h.1 (process_F_mono p nd.st (toWire p o)),
      le_trans h.2.1 (process_pair_mono p nd.st (toWire p o)),
      le_trans h.2.2 (process_hmax_mono p nd.st (toWire p o))⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (acRestart p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤
        lexKey ((acRestart p nd.st t).fg.h_j, (acRestart p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (acRestart p nd.st t).fg.h_max
    rwa [acRestart_fg]

/-- The legacy FG bounds follow from the all-restart companion. -/
theorem fgsa_rMono : RMono p c E rho :=
  fun _ => fgsa_rMonoAll p c E rho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The exact frame follows from T7.5 and FG store correspondence. -/
theorem fgsa_rFrameExactNext : RFrameExactNext p c E rho := by
  intro i x _
  exact ⟨fgsa_storeControls_eq_tree p _ (cstoreInv_stateBefore E rho i x), rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The active-view laws at every store, including conflict exclusion after F moves. -/
theorem fgsa_rActive : RActive p c E rho := by
  constructor
  · intro i x _
    exact ⟨fun _ h => actView_antitone _ h,
      fun _ _ hK hFB hBK => actView_path p _ (cstoreInv_stateBefore E rho i x) hK hFB hBK,
      (actView_fields _).2.2.2.1⟩
  · intro i j x b _ _
    dsimp only
    intro hF hn hb
    exact Gen.Pure.block_incompatible_of_preceq hn (eraseFG_preceq hF)
      ((actView_blocks _ b).mp hb).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Admitted-view injectivity from T7.5. The frozen root premise is retained. -/
theorem fgsa_rCarrierView : RCarrierView p c E rho :=
  fun _ i x _ => viewRootInj_TF p _ (cstoreInv_stateBefore E rho i x)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
L49 frame: the accepted FG step, stuttering steps, reconcile, and exact metadata reads.
T7.5 supplies MetaInv; cumulative metadata uses the same KitV2 lift as RStoreCumul. -/
theorem fgsa_rFrameNext : RFrameNext p c E rho := by
  intro i x _
  let st := storeAt p c E rho i x
  refine ⟨?_, ⟨(fun f => onView_fg f st), admitHead_fg p st, ?_, clock_fg p st, ?_, ?_⟩,
    ⟨congrArg (KitFG.treeStoreControlsView (heightView p)) (reconcile_frame st).1,
      fun X => domainR_congr_fg p _ _ X (reconcile_frame st).1⟩,
    metaInv_stateBefore E rho i x, ?_⟩
  · intro s N P hNamed hP ha
    obtain ⟨pool, he, _⟩ := admitBlock_accepted_eq p st s N P hNamed hP ha
    rw [he]
    dsimp only
    split_ifs <;> first | rfl | exact reconcile_fg _
  · intro a
    rcases admitRow_eq p st a with h | h <;> rw [h]
  · intro s N hr
    rw [admitBlock_refused p st s N hr]
  · intro o hn
    change (match o.decode with
      | some (.vote s k b) => admitHead p st s k b
      | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
      | some (.block s N) => admitBlock p st s N
      | none => st).fg = st.fg
    rw [hn]
  · refine ⟨?_, ?_, ?_, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    · intro s
      apply congrArg (fun f => List.filterMap f st.proposals)
      funext o
      cases o.decode with
      | none => rfl
      | some a => cases a <;> rfl
    · intro H
      apply congrArg List.flatten
      apply congrArg (fun f => List.filterMap f st.proposals)
      funext o
      cases o.decode with
      | none => rfl
      | some a => cases a <;> rfl
    · apply congrArg List.flatten
      apply congrArg (fun f => List.filterMap f st.proposals)
      funext o
      cases o.decode with
      | none => rfl
      | some a => cases a <;> rfl
    · intro hnr j hij _
      have h := fgsa_store_cumulative p c E rho hnr hij x
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2, h.2.2.1, h.2.2.2.1⟩

/-- The frame keeps durable prefixes across restarts and stamp prefixes in an epoch. -/
theorem fgsa_rFrameNextEpoch : RFrameNextEpoch p c E rho := by
  intro i x hx
  obtain ⟨ha, hb, hc, hm, hp, hw, hr, hv, hh, hs, hrows, _⟩ :=
    fgsa_rFrameNext p c E rho i x hx
  refine ⟨ha, hb, hc, hm, hp, hw, hr, hv, hh, hs, hrows, ?_⟩
  intro j hij _
  have hd := fgsa_store_durable p c E rho hij x
  refine ⟨hd.2.2.1, hd.2.2.2, ?_⟩
  intro hrf
  have he := fgsa_store_cumulative_on p c E rho hij x hrf
  exact ⟨he.2.2.1, he.2.2.2.1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 fixed stored-value seed: the predicate retains the same cut i and the
same stored data at every later cut. Gen.V2.Duty.kept_from_seed can consume it. -/
theorem fgsa_seed_stored (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) :
    Gen.V2.Duty.SeedAt E rho j (fun x nd =>
      let a := storeAt p c E rho i x
      a.fg.TF ⊆ nd.st.fg.TF ∧ a.base.blocks <+: nd.st.base.blocks ∧
      a.base.blockStamp <+: nd.st.base.blockStamp ∧ a.base.voteStamp <+: nd.st.base.voteStamp ∧
      a.proposals <+: nd.st.proposals ∧ a.rowPool <+: nd.st.rowPool) := by
  intro x
  exact fgsa_store_cumulative p c E rho hnr hij x

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 fixed FG-bound seed, with the reference cut fixed in the predicate. -/
theorem fgsa_seed_bounds (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) :
    Gen.V2.Duty.SeedAt E rho j (fun x nd => x ∈ rho.honest →
      let a := storeAt p c E rho i x
      FGBlock.Preceq a.fg.F nd.st.fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey (nd.st.fg.h_j, nd.st.fg.J) ∧
      a.fg.h_max ≤ nd.st.fg.h_max) := by
  intro x hx
  exact fgsa_rMono p c E rho hnr i j x hx hij

end AvailableChain.FGSA.Run
end
