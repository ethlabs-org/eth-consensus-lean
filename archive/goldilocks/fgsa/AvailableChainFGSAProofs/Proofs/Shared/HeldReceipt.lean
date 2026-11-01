module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAClaims.Statements.ComposeStmt -- shake: keep (ports)

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2.
DC: INTENTIONAL strict relay of an arbitrary held FG carrier, including old carriers.
The receiver ancestry is explicit at the deadline. Assembly supplies RMono.
Standalone rows use ΔF; this block object uses Δ. -/
theorem healing_held_block_receipt (mono : RMono p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x y : V} {t : Time} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some (.tick x t))
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hgst : E.t_GST ≤ t) (hhor : t + p.Δ ≤ rho.horizon)
    (hF : FGBlock.Preceq
      (storeAt p c E rho (V2.D.Run.idxBefore rho (t + p.Δ)) y).fg.F W)
    (hAwake : E.awake y (t + p.Δ) = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ nd.st.fg.TF) (t + p.Δ) y := by
  have hs := hvalid.toScheduleWellFormed
  change W ∈ (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st.fg.TF
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  by_cases hg : W = .genesis
  · exact hg ▸ (storeBundle_stateBefore E rho _ y).cstore.fg.gen
  have hb : eraseFG W ∈ (storeAt p c E rho i x).base.blocks :=
    (storeBundle_stateBefore E rho i x).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
  change eraseFG W ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks at hb
  rw [← (storeBundle_stateBefore E rho i x).«meta».stampKeys] at hb
  obtain ⟨⟨b, stamp⟩, hb, he⟩ := List.mem_map.mp hb
  dsimp only at he
  subst b
  rcases fgsa_block_stamp_source E rho hnr i x (eraseFG W) stamp hb with
      hgen | ⟨k, hki, u, o, ho, ha, _⟩
  · exact (hg (eraseFG_eq_genesis.mp hgen.1)).elim
  obtain ⟨parent, hk, _⟩ := ha.1
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  have htime := (List.pairwise_iff_getElem.mp hs.sorted) k i hkl hil hki
  rw [hie, hke] at htime
  have hut : u ≤ t := V2.D.Engine.time_le_of_key_le _ _ htime
  let dl := fun u => max u E.t_GST + p.Δ
  have hd : dl u ≤ t + p.Δ := Int.add_le_add_right (max_le hut hgst) p.Δ
  have hidx := fgsa_idxBefore_mono rho hd
  have hF' := (mono hnr _ _ y hy hidx).1
  have hcompat : Block.Compatible (eraseFG W)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (dl u) y).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (eraseFG_preceq (KitFG.preceq_trans hF' hF)))
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    cases he : o.payload <;> simp only [fgsaDelay_def, he, hdelta]
    exact (hn (by change (match o.payload with | .row _ => True | _ => False)
                  rw [he]; trivial)).elim
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    (fun o => ¬ isRowObject o) p.Δ delay
  have hu : u < dl u := (le_max_left u E.t_GST).trans_lt (lt_add_of_pos_right _ p.deltaPos)
  dsimp only [blockOf?] at ho
  cases hdec : (toWire p o).decode with
  | none => simp only [hdec, reduceCtorEq] at ho
  | some msg =>
    cases msg <;> simp only [hdec, reduceCtorEq, Option.some.injEq] at ho
    rename_i slot N
    have he : o = ofWire p ⟨.proposer slot, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hdec
    obtain ⟨Y, hY, hYW⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hdelta hvalid hnr dl
      rho.horizon
      slot N u y hD (Or.inr ⟨x, hx, k, he ▸ ha⟩) hy
      (hd.trans hhor) hu (by simpa only [ho] using hcompat) (hd.trans hhor)
      (by
        intro v huv hvd
        exact fgsa_awake_before_noRestart E rho hvalid hnr y hy (t + p.Δ)
          hhor hAwake v ((hs.in_horizon _ (List.mem_of_getElem? hk)).1.trans huv)
          (hvd.le.trans hd))
    have hYeq : Y = W := eraseFG_injective (hYW.trans ho)
    rw [hYeq, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
    exact (fgsa_store_cumulative p c E rho hnr hidx y).1 hY

/-- An exact named target service supplies a held carrier after restart.
Its receiver service keeps the retained object's safe history explicit. -/
theorem healing_held_block_receipt_on
    (hvalid : V2.D.ExecutionValid E rho)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (W : FGBlock (Fin p.n)) (D : Time) (y : V) (hy : y ∈ rho.honest)
    (hService : TargetReceiptService E rho (eraseFG W) D y) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ nd.st.fg.TF) D y := by
  change W ∈ (rho.stateBeforeTime E D y).st.fg.TF
  have hm := fgsa_target_receipt_on E rho hvalid.toScheduleWellFormed hroots
    (eraseFG W) D y hy hService
  obtain ⟨Y, hY, he⟩ := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree _).mp hm
  exact (eraseFG_injective he) ▸ hY

end AvailableChain.FGSA.Run
end
