module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSARun.Proofs.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- ROOT-DIGEST W2b. An honest stored FG block has held-body scope. -/
theorem rootScope_store {i : Nat} {x : V} (hx : x ∈ rho.honest)
    {B : FGBlock (Fin p.n)} (hB : B ∈ (storeAt p c E rho i x).fg.TF) :
    RootBlockInRun p c E rho (eraseFG B) :=
  rootBlockInRun_held E rho hx i
    ((cstoreInv_stateBefore E rho i x).baseTree _ |>.mpr ⟨B, hB, rfl⟩)

/-- ROOT-DIGEST W2b. FG ancestry preserves body scope. -/
theorem rootScope_ancestor {A B : FGBlock (Fin p.n)}
    (hB : RootBlockInRun p c E rho (eraseFG B)) (hAB : FGBlock.Preceq A B) :
    RootBlockInRun p c E rho (eraseFG A) :=
  rootBlockInRun_ancestor E rho hB (eraseFG_preceq hAB)

/-- ROOT-DIGEST W2b. Two scoped FG blocks are equal when their roots are equal. -/
theorem rootScope_eq (hr : NamedRootCollisionFree p c E rho) {A B : FGBlock (Fin p.n)}
    (hA : RootBlockInRun p c E rho (eraseFG A))
    (hB : RootBlockInRun p c E rho (eraseFG B)) (he : A.root = B.root) : A = B :=
  eraseFG_injective (rootBlockInRun_eq E rho hr hA hB
    (by simpa only [eraseFG_root] using he))

/-- ROOT-DIGEST W2b. An honest action source is selected from its held FG tree. -/
theorem rootScope_source {x : V} {r : Nat} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hB : actionSourceFG p c E rho x r = some (some B)) :
    RootBlockInRun p c E rho (eraseFG B) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hB
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hB; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hB
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hB).1).1
    have ht := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    apply rootScope_store hx (i := i)
    change B ∈ (clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)).fg.TF at ht
    simpa only [clock_fg, storeAt] using ht

/-- ROOT-DIGEST W2b. Every certified entry is an ancestor of its carrier. -/
theorem certified_preceq {W e : FGBlock (Fin p.n)} (he : e ∈ certified p W) :
    FGBlock.Preceq e W := by
  obtain ⟨U, hUW, hJ | hF | ⟨hT, _⟩⟩ := he
  · subst e
    exact KitFG.preceq_trans
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry U)
        ((fgCertificateLaws p).height.entry_preceq U)) hUW
  · subst e
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified U)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry U)
        (KitFG.preceq_trans ((fgCertificateLaws p).height.entry_preceq U) hUW))
  · subst e
    exact KitFG.preceq_trans ((fgCertificateLaws p).height.entry_preceq U) hUW

/-- ROOT-DIGEST W2b. The height entry is below its scoped carrier. -/
theorem rootScope_entry {B : FGBlock (Fin p.n)}
    (hB : RootBlockInRun p c E rho (eraseFG B)) :
    RootBlockInRun p c E rho (eraseFG (heightView p B).T_h) :=
  rootScope_ancestor hB ((fgCertificateLaws p).height.entry_preceq B)

/-- ROOT-DIGEST W2b. The justified entry is below its scoped carrier. -/
theorem rootScope_justified {B : FGBlock (Fin p.n)}
    (hB : RootBlockInRun p c E rho (eraseFG B)) :
    RootBlockInRun p c E rho (eraseFG (heightView p B).J) :=
  rootScope_ancestor (rootScope_entry hB)
    ((fgCertificateLaws p).height.justified_preceq_entry B)

/-- ROOT-DIGEST W2b. The finalized entry is below its scoped carrier. -/
theorem rootScope_finalized {B : FGBlock (Fin p.n)}
    (hB : RootBlockInRun p c E rho (eraseFG B)) :
    RootBlockInRun p c E rho (eraseFG (finalityView p B).F) :=
  rootScope_ancestor (rootScope_justified hB) ((fgCertificateLaws p).finalized_preceq_justified B)

/-- ROOT-DIGEST W2b. Certified entries have body scope when source names are used. -/
theorem srcFrameAbove_scoped (p : Params) (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : RStore p c E rho) (hstrat : RStrat p c E rho)
    (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat) (_hclosed : AncestorClosed p Φ)
    (hg : c₀ ≤ (heightView p (.genesis : FGBlock (Fin p.n))).h → Φ .genesis)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hrows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → c₀ ≤ (heightView p e).h → Φ e) :
    (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      c₀ ≤ (heightView p e).h → Φ e) ∧ FrameBelow p Φ c₀ (R_at p c E rho i x) := by
  have hcert : ∀ W ∈ (storeAt p c E rho i x).fg.TF,
      ∀ e ∈ certified p W, c₀ ≤ hOf p.E p.cfg e → Φ e := by
    intro W hW e he hheight
    by_cases hgen : e = .genesis
    · subst e; apply hg
      rwa [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
    · obtain ⟨y, r, a, ha, hname⟩ := hstrat i x W hx hW e he hgen
      apply hrows y r a e ha hname
        (rootScope_ancestor (rootScope_store hx hW) (certified_preceq he))
      rwa [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
  refine ⟨(by simpa only
    [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] using hcert), ?_⟩
  let st := storeAt p c E rho i x
  have hinv := (hS i x hx).1.fg
  obtain ⟨K, hK, hKF⟩ := hinv.Fcar
  have hF : c₀ ≤ hOf p.E p.cfg st.fg.F → Φ st.fg.F := by
    intro hh
    apply hcert K hK st.fg.F
    · exact ⟨K, KitFG.preceq_refl K, Or.inr (Or.inl hKF.symm)⟩
    · exact hh
  obtain ⟨D, hD, _, _, hJ⟩ := hinv.pair.1
  simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] at hJ
  have hj : c₀ ≤ hOf p.E p.cfg st.fg.J → Φ st.fg.J := by
    intro hh
    apply hcert D hD st.fg.J
    · simp only [certified_def, heightView_eq_simplex p,
        KitFG.simplexHeightView_def, KitFG.heightOf_def]
      exact ⟨D, KitFG.preceq_refl D, Or.inl hJ⟩
    · exact hh
  change FrameBelow p Φ c₀ (controls p st)
  simp only [FrameBelow_def, heightView_eq_simplex p,
    KitFG.simplexHeightView_def, KitFG.heightOf_def]
  refine ⟨hF, hj, ?_⟩
  change c₀ ≤ hOf p.E p.cfg (if (controls p st).rootIsJ then
      st.fg.J else st.fg.F) → Φ (if (controls p st).rootIsJ then
      st.fg.J else st.fg.F)
  cases (controls p st).rootIsJ <;> assumption

/-- ROOT-DIGEST W2b. A non-genesis gate result has earlier direct delivery provenance.
The genesis case uses the honest gate node's initial body store. -/
theorem rootScope_result (hv : V2.D.ExecutionValid E rho) {i r : Nat} {B : Block}
    (hB : (r, B) ∈ cleanResults p c E rho i) : RootBlockInRun p c E rho B := by
  obtain ⟨j, _, x, hgt, hres⟩ := hB
  have ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams r)) := hgt
  have hx := hv.honest_only _ (List.mem_of_getElem? ht)
  rcases hres with ⟨_, hres⟩
  rw [gateResultAt_eq_gateResult p c E rho hv.toScheduleWellFormed hgt] at hres
  have hraw := (fgsa_gate_raw_of_nonempty p c E rho hv.toScheduleWellFormed hgt hres).2
  have hinv := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x)
    (SA.gateTime p.toParams r)
  have hm := (compat_of_confirmation p _ hinv hraw).2
  rw [(clockPre_fields p _ _).2.1] at hm
  by_cases hgen : B = .genesis
  · exact rootBlockInRun_held E rho hx j hm
  · exact rootBlockInRun_stored E rho j x hm hgen

/-- ROOT-DIGEST W2b. A labelled result ancestor has body scope. -/
theorem rootScope_belowLabel (hv : V2.D.ExecutionValid E rho) {x : V}
    (hx : x ∈ rho.honest) {i r : Nat} {B : Block}
    (hB : BelowLabel p c E rho i r B) : RootBlockInRun p c E rho B := by
  rcases hB with rfl | ⟨s, D, hD, _, hBD⟩
  · exact rootScope_store hx (i := 0) (cstoreInv_stateBefore E rho 0 x).fg.gen
  · exact rootBlockInRun_ancestor E rho (rootScope_result hv hD) hBD

end AvailableChain.FGSA.Run
end
