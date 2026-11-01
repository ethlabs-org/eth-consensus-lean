module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- Blueprint 21:749–783, 918–1012, 1148–1252; plan S30, H-FRAME/F4.
DC: INTENTIONAL a witness retains its duty-specific suffix or supplies F/Z coverage.
The height witness is in the same supplied view. Raw full-store receipt does
not imply frozen membership. No walk or score equality follows from this lemma. -/
theorem healing_retained_path (st : State p.n) (hr : Reachable p st)
    (X : Finset (FGBlock (Fin p.n))) (_hX : X ⊆ st.fg.TF)
    (hclosed : ∀ W ∈ X, ∀ B, FGBlock.Preceq B W → B ∈ X)
    (W : FGBlock (Fin p.n)) (hW : W ∈ X)
    (_hFW : FGBlock.Preceq st.fg.F W) (hZW : FGBlock.Preceq (controls p st).Z W)
    (hlo : (controls p st).lo ≤ (heightView p W).h) :
    ∀ B, FGBlock.Preceq B W → FGBlock.Preceq B st.fg.F ∨
      FGBlock.Preceq B (controls p st).Z ∨
      (B ∈ KitFG.treeStoreFrameView (heightView p) st.fg X ∧
        ∀ A, FGBlock.Preceq (controls p st).Z A → FGBlock.Preceq A B →
          A ∈ KitFG.treeStoreFrameView (heightView p) st.fg X) := by
  have hi := (storeBundle_of_reachable p st hr).cstore
  have hFZ : FGBlock.Preceq st.fg.F (controls p st).Z := by
    unfold Controls.Z
    split
    · exact hi.fg.FJ
    · exact KitFG.preceq_refl _
  intro B hBW
  by_cases hBF : FGBlock.Preceq B st.fg.F
  · exact Or.inl hBF
  by_cases hBZ : FGBlock.Preceq B (controls p st).Z
  · exact Or.inr (Or.inl hBZ)
  have hZB : FGBlock.Preceq (controls p st).Z B :=
    (KitFG.preceq_total_of_common hZW hBW).resolve_right hBZ
  have mem (A : FGBlock (Fin p.n)) (hZA : FGBlock.Preceq (controls p st).Z A)
      (hAW : FGBlock.Preceq A W) : A ∈ KitFG.treeStoreFrameView (heightView p) st.fg X :=
    (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hclosed W hW A hAW, KitFG.preceq_trans hFZ hZA, hZA, W, hW, hAW, hlo⟩
  exact Or.inr (Or.inr ⟨mem B hZB hBW,
    fun A hZA hAB => mem A hZA (KitFG.preceq_trans hAB hBW)⟩)

/-- Blueprint 21:749–783, 918–1012, 1148–1252; plan S30, H-FRAME/F4.
DC: INTENTIONAL the current-slot proposal supplies a witness in the carried duty arm.
Actual proposal admission, its slot, the receiver's live start, and the parent
height are required. This arm does not require an old receipt stamp. -/
theorem healing_carried_path (src dst : State p.n) (hr : Reachable p dst)
    (s : Slot) (Q : Block) (B : FGBlock (Fin p.n))
    (hQ : Q ∈ dst.base.blocks) (hslot : Q.slot = s)
    (hB : B ∈ src.fg.TF) (hparent : eraseFG B = Q.parent)
    (hlo : (controls p dst).lo ≤ (heightView p B).h) :
    ∀ C, Block.Preceq (liveRoot p dst) C → Block.Preceq C Q →
      C ∈ RetainedWalk.T p dst s := by
  have hi := (storeBundle_of_reachable p dst hr).cstore
  intro C hstart hCQ
  exact fgsa_retained_path_mem p src dst hi.baseTree hi.fg.closed
    (F_preceq_liveRoot p dst hi) s Q C hQ hslot hstart hCQ ⟨B, Or.inl ⟨hB, hparent⟩, hlo⟩

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1148–1252; plan S30, H-FRAME/F4.
DC: INTENTIONAL each ancestor keeps its own original stamp through the HEAD clock. -/
private theorem frame_frozen_mem (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {y : V} {W : FGBlock (Fin p.n)} {d : Time}
    (hdpos : 0 < d) {s : Slot} {nd : Node p}
    (hdt : d ≤ SA.voteTime p.toParams s) (hdf : d ≤ SA.freezeTime p.toParams (s - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hpost : postClock E rho y (SA.voteTime p.toParams s) = some nd)
    (hFW : FGBlock.Preceq nd.st.fg.F W) :
    W ∈ voterBlocks p nd.st s := by
  rw [postClock_def, preTick_def] at hpost
  cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
  | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
  | some k =>
    rw [hk] at hpost
    have hnd := Option.some.inj hpost
    subst nd
    have htick := V2.D.Run.tickIdx?_spec hk
    have hjk : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick d).mp (by omega)
      exact (not_lt.mpr hdt) hlt
    let st := storeAt p c E rho (V2.D.Run.idxBefore rho d) y
    let st' := storeAt p c E rho k y
    have hc := fgsa_store_cumulative p c E rho hnr hjk y
    have hb : eraseFG W ∈ st.base.blocks :=
      (storeBundle_stateBefore E rho _ y).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
    have hkeys := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).«meta».stampKeys
    have hfind : ∃ stamp, st.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      have hm : eraseFG W ∈ st.base.blockStamp.map Prod.fst := hkeys ▸ hb
      cases hf : st.base.blockStamp.find? (fun row => row.1 == eraseFG W) with
      | none =>
        obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
        have hn := List.find?_eq_none.mp hf row hr
        rw [he, beq_self_eq_true] at hn
        contradiction
      | some row =>
        have he : row.1 = eraseFG W := by simpa only [beq_iff_eq] using List.find?_some hf
        exact ⟨row.2, by simp only [← he]⟩
    obtain ⟨stamp, hf⟩ := hfind
    have hstamp : stamp < d := by
      rcases fgsa_block_stamp_source E rho hnr _ y (eraseFG W) stamp
          (List.mem_of_find?_eq_some hf) with hg | ⟨l, hl, t, o, _, ha, hstamp⟩
      · exact hg.2 ▸ hdpos
      · obtain ⟨parent, he, _⟩ := ha.1
        have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).mp hl
        have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
          (fgsaRestoreTimeLaw p c) E rho hs he y
        rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l y)] at hn
        exact hstamp ▸ hn.trans_lt ht
    have hkept : st'.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      obtain ⟨tail, htail⟩ := hc.2.2.1
      change (storeAt p c E rho k y).base.blockStamp.find? _ = _
      rw [← htail, List.find?_append, hf]
      rfl
    change W ∈ voterBlocks p (clock p st' (SA.voteTime p.toParams s)) s
    apply Finset.mem_filter.mpr
    refine ⟨?_, Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by rw [(clock_cumulative p _ _).1]; exact hc.1 hW, hFW⟩
    · have he : GridCO.stampBlock (clock p st' (SA.voteTime p.toParams s)).base (eraseFG W) =
          stamp := by
        unfold GridCO.stampBlock
        rw [(clock_cumulative p _ _).2.2.1, hkept]
        rfl
      rw [he]
      exact hstamp.trans_le hdf

/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F4.
DC: INTENTIONAL strict receipt enters a later frozen arm only after its own cut.
Equality between the receipt deadline and the freeze is valid: each stamp is strict. -/
theorem healing_frozen_path (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {y : V} {q : Slot} {d : Time} {nd : Node p} {W : FGBlock (Fin p.n)}
    (hdpos : 0 < d) (hdvote : d ≤ SA.voteTime p.toParams q)
    (hdfreeze : d ≤ SA.freezeTime p.toParams (q - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hread : postClock E rho y (SA.voteTime p.toParams q) = some nd) :
    ∀ B, FGBlock.Preceq nd.st.fg.F B → FGBlock.Preceq B W →
      B ∈ voterBlocks p nd.st q := by
  intro B hFB hBW
  have hi := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).cstore
  obtain ⟨A, hA, he⟩ := eraseFG_ancestor_mem hi.fg.closed hW (eraseFG_preceq hBW)
  have hB : B ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF :=
    (eraseFG_injective he) ▸ hA
  exact frame_frozen_mem p c E rho hs hnr hdpos hdvote hdfreeze hB hread hFB

/-- Frozen membership uses the exact receiver epoch through its scheduled read. -/
private theorem frame_frozen_mem_on (hs : V2.D.ScheduleWellFormed E rho)
    {y : V} {W : FGBlock (Fin p.n)} {d : Time}
    (hdpos : 0 < d) {s : Slot} {nd : Node p}
    (hdt : d ≤ SA.voteTime p.toParams s) (hdf : d ≤ SA.freezeTime p.toParams (s - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hpost : postClock E rho y (SA.voteTime p.toParams s) = some nd)
    (hEpoch : ∀ i, rho.events[i]? = some (.tick y (SA.voteTime p.toParams s)) →
      V2.D.restartFree rho y (V2.D.Run.idxBefore rho d) i)
    (hFW : FGBlock.Preceq nd.st.fg.F W) :
    W ∈ voterBlocks p nd.st s := by
  rw [postClock_def, preTick_def] at hpost
  cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
  | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
  | some k =>
    rw [hk] at hpost
    have hnd := Option.some.inj hpost
    subst nd
    have htick := V2.D.Run.tickIdx?_spec hk
    have hjk : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick d).mp (by omega)
      exact (not_lt.mpr hdt) hlt
    let st := storeAt p c E rho (V2.D.Run.idxBefore rho d) y
    let st' := storeAt p c E rho k y
    have hc := fgsa_store_cumulative_on p c E rho hjk y (hEpoch k htick)
    have hb : eraseFG W ∈ st.base.blocks :=
      (storeBundle_stateBefore E rho _ y).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
    have hkeys := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).«meta».stampKeys
    have hfind : ∃ stamp, st.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      have hm : eraseFG W ∈ st.base.blockStamp.map Prod.fst := hkeys ▸ hb
      cases hf : st.base.blockStamp.find? (fun row => row.1 == eraseFG W) with
      | none =>
        obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
        have hn := List.find?_eq_none.mp hf row hr
        rw [he, beq_self_eq_true] at hn
        contradiction
      | some row =>
        have he : row.1 = eraseFG W := by simpa only [beq_iff_eq] using List.find?_some hf
        exact ⟨row.2, by simp only [← he]⟩
    obtain ⟨stamp, hf⟩ := hfind
    have hstamp : stamp < d := by
      have ht := fgsa_block_stamp_before_read E rho hs y d hdpos (eraseFG W) (by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
        exact hb)
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at ht
      change GridCO.stampBlock st.base (eraseFG W) < d at ht
      unfold GridCO.stampBlock at ht
      simpa only [hf, Option.map_some, Option.getD_some] using ht
    have hkept : st'.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      obtain ⟨tail, htail⟩ := hc.2.2.1
      change (storeAt p c E rho k y).base.blockStamp.find? _ = _
      rw [← htail, List.find?_append, hf]
      rfl
    change W ∈ voterBlocks p (clock p st' (SA.voteTime p.toParams s)) s
    apply Finset.mem_filter.mpr
    refine ⟨?_, Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by rw [(clock_cumulative p _ _).1]; exact hc.1 hW, hFW⟩
    · have he : GridCO.stampBlock (clock p st' (SA.voteTime p.toParams s)).base (eraseFG W) =
          stamp := by
        unfold GridCO.stampBlock
        rw [(clock_cumulative p _ _).2.2.1, hkept]
        rfl
      rw [he]
      exact hstamp.trans_le hdf

/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F4.
DC: INTENTIONAL strict receipt enters a later frozen arm only after its own cut.
Equality between the receipt deadline and the freeze is valid: each stamp is strict. -/
theorem healing_frozen_path_on (hs : V2.D.ScheduleWellFormed E rho)
    {y : V} {q : Slot} {d : Time} {nd : Node p} {W : FGBlock (Fin p.n)}
    (hdpos : 0 < d) (hdvote : d ≤ SA.voteTime p.toParams q)
    (hdfreeze : d ≤ SA.freezeTime p.toParams (q - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hread : postClock E rho y (SA.voteTime p.toParams q) = some nd)
    (hEpoch : ∀ i, rho.events[i]? = some (.tick y (SA.voteTime p.toParams q)) →
      V2.D.restartFree rho y (V2.D.Run.idxBefore rho d) i) :
    ∀ B, FGBlock.Preceq nd.st.fg.F B → FGBlock.Preceq B W →
      B ∈ voterBlocks p nd.st q := by
  intro B hFB hBW
  have hi := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).cstore
  obtain ⟨A, hA, he⟩ := eraseFG_ancestor_mem hi.fg.closed hW (eraseFG_preceq hBW)
  have hB : B ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF :=
    (eraseFG_injective he) ▸ hA
  exact frame_frozen_mem_on p c E rho hs hdpos hdvote hdfreeze hB hread hEpoch hFB

end AvailableChain.FGSA.Run
end
