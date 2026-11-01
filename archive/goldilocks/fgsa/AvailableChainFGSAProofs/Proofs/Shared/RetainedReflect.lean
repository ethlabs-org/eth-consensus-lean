module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedScores

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1350–1360.
Class (iii). DC: INTENTIONAL; the FG-SA stored-parent band is a separate arm. -/
def retainedBand (p : Params) (st : State p.n) (C : Block) : Prop :=
  ∃ P ∈ st.fg.TF, eraseFG P = C.parent ∧ (heightView p P).h < (controls p st).lo

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1290–1297, 1350–1360.
Class (iii). DC: INTENTIONAL; D3-1 removes caller-supplied source F/Z bounds.
The witness is stored at the source or strictly frozen at the target. -/
def ReflectedDomainWitness (p : Params) (src dst : State p.n)
    (s : Slot) (C : Block) : Prop :=
  ∃ B W : FGBlock (Fin p.n), B ∈ dst.fg.TF ∧ eraseFG B = C ∧
    FGBlock.Preceq B W ∧ (controls p src).lo ≤ (heightView p W).h ∧
    (W ∈ src.fg.TF ∨ (W ∈ dst.fg.TF ∧
      GridCO.stampBlock dst.base (eraseFG W) < SA.freezeTime p.toParams (s - 1)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1350–1360.
Class (iii). DC: INTENTIONAL; equation for this module's band predicate. -/
theorem retainedBand_def (p : Params) (st : State p.n) (C : Block) :
    retainedBand p st C = (∃ P ∈ st.fg.TF,
      eraseFG P = C.parent ∧ (heightView p P).h < (controls p st).lo) := by
  apply propext
  constructor <;> exact fun h => h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1290–1297.
Class (iii). DC: INTENTIONAL; equation for this module's witness predicate. -/
theorem ReflectedDomainWitness_def (p : Params) (src dst : State p.n) (s : Slot) (C : Block) :
    ReflectedDomainWitness p src dst s C =
      (∃ B W : FGBlock (Fin p.n), B ∈ dst.fg.TF ∧ eraseFG B = C ∧
        FGBlock.Preceq B W ∧ (controls p src).lo ≤ (heightView p W).h ∧
        (W ∈ src.fg.TF ∨ (W ∈ dst.fg.TF ∧
          GridCO.stampBlock dst.base (eraseFG W) < SA.freezeTime p.toParams (s - 1)))) := by
  apply propext
  constructor <;> exact fun h => h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1290–1297, 1330–1360.
Class (iii). DC: INTENTIONAL; actual starts, internal witnesses and band data.
D2-1 permits the parent or the proposal as the target height witness. -/
structure RetainedReadPremises (p : Params) (src dst : State p.n)
    (s : Slot) (D : FGBlock (Fin p.n)) (b Kc : Block) : Prop where
  pivot_parent : Block.Preceq (eraseFG D) b.parent
  ordinary_prefix : BestAncestry (z p src) (ap p src) (S p src) (ss src s) (es p src s)
  target_parent : Block.Preceq (ay p dst) b.parent
  source_cut : Block.Preceq (z p src) Kc
  target_cut : Block.Preceq (ay p dst) Kc
  cut_parent : Block.Preceq Kc b.parent
  target_prefix : BestAncestry (ay p dst) Kc (T p dst s) (ts p dst s) (et p dst s)
  parent_height : ∃ W : FGBlock (Fin p.n),
    ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
    (controls p dst).lo ≤ (heightView p W).h
  reflected_witness : ∀ X C, Block.Preceq Kc X → Block.Preceq X b.parent →
    C ∈ T p dst s → C.parent? = some X → C.slot < s → et p dst s C = true →
    ReflectedDomainWitness p src dst s C
  band_agrees : ∀ X C, Block.Preceq Kc X → Block.Preceq X b.parent →
    C ∈ S p src → C ∈ T p dst s → C.parent? = some X → C.slot < s →
    (retainedBand p src C ↔ retainedBand p dst C)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:942–953, H.17:2971–2984 (design 798–809,2832–2845); spec 1290–1297.
Class (iii). DC: INTENTIONAL; converse S3 gives a witness in the same view.
No store invariant is needed. -/
theorem fgsa_tree_domain_witness_of_mem (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) (C : Block)
    (hm : C ∈ erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg Vw)) :
    ∃ B ∈ Vw, eraseFG B = C ∧ FGBlock.Preceq st.fg.F B ∧
      FGBlock.Preceq (controls p st).Z B ∧
      ∃ W ∈ Vw, FGBlock.Preceq B W ∧ (controls p st).lo ≤ (heightView p W).h := by
  obtain ⟨B, hB, he⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  obtain ⟨hv, hf, hz, hw⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (controls p st) Vw B).mp hB
  exact ⟨B, hv, he, hf, hz, hw⟩

/-- Top retention permits the old-domain witness conclusion with canonical controls. -/
theorem fgsa_domain_witness_of_mem_of_top_retained (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) (C : Block)
    (hTop : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W)
    (hm : C ∈ erasedList st (KitFG.storeFrameView (heightView p) st.fg Vw)) :
    ∃ B ∈ Vw, eraseFG B = C ∧ FGBlock.Preceq st.fg.F B ∧
      FGBlock.Preceq (controls p st).Z B ∧
      ∃ W ∈ Vw, FGBlock.Preceq B W ∧ (controls p st).lo ≤ (heightView p W).h := by
  apply fgsa_tree_domain_witness_of_mem p st Vw C
  simpa only [KitFG.treeStoreFrameView_eq (heightView p) st.fg Vw hTop] using hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:371–373; 21 H.6:942–958 (design 798–814); spec 1290–1297.
Class (iii). DC: INTENTIONAL; view-form full-domain SR adapter. -/
theorem fgsa_walkRun_full_domain_view (p : Params) (st : State p.n)
    (h : CStoreInv p st) (D : FGBlock (Fin p.n)) (C : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hC : C ∈ st.base.blocks) (hDC : Block.Preceq (eraseFG D) C) :
    C ∈ S p st := by
  exact fgsa_walkRun_full_domain p st h D C hF hZ
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hC hDC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:350–354, 364–366; 21 H.6:942–953 (design 798–809); spec 1290–1297.
Class (iii). DC: INTENTIONAL; view-form path-domain SR adapter. -/
theorem fgsa_walkRun_path_domain_view (p : Params) (st : State p.n)
    (h : CStoreInv p st) (s : Slot) (D : FGBlock (Fin p.n)) (C P : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hP : P ∈ st.base.blocks) (hs : P.slot = s)
    (hDC : Block.Preceq (eraseFG D) C) (hCP : Block.Preceq C P) :
    C ∈ T p st s := by
  dsimp only [T]
  change C ∈ erasedList st (KitFG.filteredFromView (heightView p) (controls p st) _)
  rw [← KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  exact fgsa_walkRun_path_domain_filtered p st h s D C P hF hZ
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hP hs hDC hCP

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:356–360, 373; 21 H.5:891–902 (design 747–758); spec 1350–1360.
Class (iii). DC: INTENTIONAL; view-form majority-only SR adapter. -/
theorem fgsa_walkRun_eligible_iff_view (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n .root)) (D : FGBlock (Fin p.n)) (C : Block)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hparent : Block.Preceq (eraseFG D) C.parent) (hs : C.slot ≠ st.slot p) :
    eligible p st raw sup C = true ↔
      GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup C := by
  exact fgsa_walkRun_eligible_iff p st raw sup D C
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hparent hs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:891–902, H.6:942–958, H.17:2986–3006
(design 747–758,798–814,2847–2867); spec 1350–1360.
Class (iii). DC: INTENTIONAL; all three eligibility arms in view form. -/
theorem fgsa_eligible_eq_of_retainedBand_score
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n .root)) (C : Block)
    (hband : retainedBand p src C ↔ retainedBand p dst C)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  rw [fgsa_eligible_eq, fgsa_eligible_eq]
  simp only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  have hb := propext hband
  dsimp only [retainedBand] at hb
  simp only [hb, hcount, hscore, hslot]

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; inclusive S4.
The witness itself reaches the source. Closure then gives the candidate,
including candidates below lo. Neither source F/Z bound is a premise. -/
private theorem reflect_witness_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (hp : C.parent? = some X)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨B, W, -, heB, hBW, hlo, hW⟩ := hw
  have hZB : FGBlock.Preceq (controls p src).Z B :=
    eraseFG_preceq_iff.mp
      (heB ▸ block_preceq_trans hcut (block_preceq_trans hKX (fgsa_parent_preceq_of_some hp)))
  have hFB := KitFG.preceq_trans (fgsa_F_preceq_Z p src hs) hZB
  have hWsrc : W ∈ src.fg.TF := by
    rcases hW with hW | ⟨hW, hstamp⟩
    · exact hW
    · obtain ⟨Q, -, heQ, hFQ, -⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hm
      have hFdst : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := by
        rw [heB, ← heQ]
        exact eraseFG_preceq hFQ
      have hmW : eraseFG W ∈ (rho.stateBefore E ih y).st.base.blocks := by
        have hb := (ht.baseTree _).mpr ⟨W, hW, rfl⟩
        change eraseFG W ∈ (clock p _ _).base.blocks at hb
        rwa [clock_base_blocks] at hb
      rw [fgsa_clock_block_stamp E rho ih y _ (eraseFG W) hmW] at hstamp
      have hgeom : ScoreRunGeometry src dst (eraseFG B) := ⟨eraseFG_preceq hFB, hFdst⟩
      have hr := fgsa_walkRun_frozen_block (hroots := hroots) E rho hE hN hDelta s hSync hx hy hip
        (eraseFG B) (eraseFG W) hgeom (eraseFG_preceq hBW) hmW
        (by simpa only [Nat.add_sub_cancel] using hstamp)
      have hb := ((actView_blocks src (eraseFG W)).mp hr).1
      obtain ⟨Q, hQ, heQ⟩ := (hs.baseTree _).mp hb
      exact (eraseFG_injective heQ) ▸ hQ
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hWsrc (eraseFG_preceq hBW)
  have hBsrc : B ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  rw [← heB]
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨B, hBsrc, rfl⟩,
    decide_eq_true ⟨B, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF B).mpr ⟨hBsrc, hFB, hZB, W, hWsrc, hBW, hlo⟩, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; S4 at X ≤ A.
The old-slot guard includes X = A and excludes the current proposal.
The stronger witness relay needs no strict-parent split. -/
theorem fgsa_walkRun_reflected_old_child
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (_hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (_hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (_hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (_hXA : Block.Preceq X N.erase.parent)
    (hp : C.parent? = some X) (_hold : C.slot < s + 1)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) :=
  reflect_witness_on_run (hroots := hroots)
    E rho hE hN hDelta s hSync hx hy hip Kc X C hcut hKX hp hm hw

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; supplies exactly
W.reflects and E.old_reflects. Strict-parent rivals are old by the landed
N.raw reflection and proposal-slot bound. G25 then compares each common
candidate, and the band adapter transports all eligibility arms. -/
theorem fgsa_retained_old_child_reflects_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    SuffixReflects Kc N.erase.parent (S p src) (T p dst (s + 1))
      (es p src (s + 1)) (et p dst (s + 1)) ∧
    (∀ C ∈ T p dst (s + 1), C.parent? = some N.erase.parent → C.slot < s + 1 →
      et p dst (s + 1) C = true → C ∈ S p src ∧ es p src (s + 1) C = true) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hK : ScoreRunGeometry src dst Kc :=
    ⟨block_preceq_trans (eraseFG_preceq (fgsa_F_preceq_Z p src hs)) h.source_cut,
      block_preceq_trans (F_preceq_liveRoot p dst ht) h.target_cut⟩
  have hA : ScoreRunGeometry src dst N.erase.parent :=
    ⟨block_preceq_trans hK.source_floor h.cut_parent,
      block_preceq_trans hK.target_floor h.cut_parent⟩
  have scores := fgsa_score_eq_on_candidates_on_run (hroots := hroots) E rho hE hN hDelta (s + 1)
    hScoreSync hx hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1)) hA
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2)
  have reflect (X C : Block) (hKX : Block.Preceq Kc X) (hXA : Block.Preceq X N.erase.parent)
      (hm : C ∈ T p dst (s + 1)) (hp : C.parent? = some X) (hold : C.slot < s + 1)
      (he : et p dst (s + 1) C = true) : C ∈ S p src ∧ es p src (s + 1) C = true := by
    have hc := fgsa_walkRun_reflected_old_child (hroots := hroots) E rho hE hN hDelta s hWalkSync
      hx hy hip hih hseat N hem Kc X C h.source_cut hKX hXA hp hold hm
      (h.reflected_witness X C hKX hXA hm hp hold he)
    refine ⟨hc, ?_⟩
    have hel := fgsa_eligible_eq_of_retainedBand_score p src dst
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1))
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) C
      (h.band_agrees X C hKX hXA hc hm hp hold) scores.1 (scores.2 C ⟨hc, hm⟩)
      ((fgsa_proposal_slot (c := c) _ (s + 1)).trans
        (fgsa_vote_slot (c := c) _ (s + 1)).symm)
    exact hel.trans he
  constructor
  · intro X C hKX hXA hm hp he
    have hCpre : C ∈ (rho.stateBefore E ih y).st.base.blocks := by
      simpa only [dst, clock_base_blocks] using (List.mem_filter.mp hm).1
    have hn := fgsa_preTick_now_le E rho hE.toScheduleWellFormed hih
    have hslot := Internal.slotOf_mono (p := p) hn
    have htick : p.slotOf (SA.voteTime p.toParams (s + 1)) = s + 1 := by
      simpa only [(fgsa_postClock_slot (c := c) (rho.stateBefore E ih y) _).2] using
        fgsa_vote_slot (c := c) (rho.stateBefore E ih y) (s + 1)
    have hle := ((fgsa_stateBefore_bounds E rho hE.toScheduleWellFormed ih y).1 C hCpre).trans
      (htick ▸ hslot)
    have hold : C.slot < s + 1 := lt_of_le_of_ne hle (by
      intro he
      have hCN := fgsa_walkRun_current_block_eq E rho hE (s + 1) (Nat.succ_pos s)
        hx hip hseat N hem C hCpre he
      have hX : X = N.erase.parent := by
        simpa only [hCN] using (fgsa_parent_eq_of_some hp).symm
      have hn := (Bool.and_eq_true_iff.mp hXA).1
      simp only [hX, decide_true, Bool.not_true, Bool.false_eq_true] at hn)
    exact reflect X C hKX (Bool.and_eq_true_iff.mp hXA).2 hm hp hold he
  · intro C hm hp hold he
    exact reflect N.erase.parent C h.cut_parent (block_preceq_refl _) hm hp hold he

private theorem reflect_witness_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (_hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (hp : C.parent? = some X)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C)
    (hScopes : ∀ D, ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) D →
      ScoreServiceScope E rho ip ih x y (s + 1) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨B, W, -, heB, hBW, hlo, hW⟩ := hw
  have hZB : FGBlock.Preceq (controls p src).Z B :=
    eraseFG_preceq_iff.mp
      (heB ▸ block_preceq_trans hcut (block_preceq_trans hKX (fgsa_parent_preceq_of_some hp)))
  have hFB := KitFG.preceq_trans (fgsa_F_preceq_Z p src hs) hZB
  have hWsrc : W ∈ src.fg.TF := by
    rcases hW with hW | ⟨hW, hstamp⟩
    · exact hW
    · obtain ⟨Q, -, heQ, hFQ, -⟩ := fgsa_tree_domain_witness_of_mem p dst _ C hm
      have hFdst : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := by
        rw [heB, ← heQ]
        exact eraseFG_preceq hFQ
      have hmW : eraseFG W ∈ (rho.stateBefore E ih y).st.base.blocks := by
        have hb := (ht.baseTree _).mpr ⟨W, hW, rfl⟩
        change eraseFG W ∈ (clock p _ _).base.blocks at hb
        rwa [clock_base_blocks] at hb
      rw [fgsa_clock_block_stamp E rho ih y _ (eraseFG W) hmW] at hstamp
      have hgeom : ScoreRunGeometry src dst (eraseFG B) := ⟨eraseFG_preceq hFB, hFdst⟩
      have hr := fgsa_scoreRun_block_backward_on (hroots := hroots) E rho hE s hx hip
        (eraseFG B) (eraseFG W) (hScopes _ hgeom) hgeom.source_floor (eraseFG_preceq hBW) hmW
        (by simpa only [Nat.add_sub_cancel] using hstamp)
      have hb := ((actView_blocks src (eraseFG W)).mp hr).1
      obtain ⟨Q, hQ, heQ⟩ := (hs.baseTree _).mp hb
      exact (eraseFG_injective heQ) ▸ hQ
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hWsrc (eraseFG_preceq hBW)
  have hBsrc : B ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  rw [← heB]
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨B, hBsrc, rfl⟩,
    decide_eq_true ⟨B, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF B).mpr ⟨hBsrc, hFB, hZB, W, hWsrc, hBW, hlo⟩, rfl⟩⟩

theorem fgsa_walkRun_reflected_old_child_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (_hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (_hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (_hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (_hXA : Block.Preceq X N.erase.parent)
    (hp : C.parent? = some X) (_hold : C.slot < s + 1)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C)
    (hScope : RetainedServiceScope E rho ip ih x y (s + 1) N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) :=
  reflect_witness_on_run_on (hroots := hroots)
    E rho hE s hx hy hip Kc X C hcut hKX hp hm hw hScope.scores

theorem fgsa_retained_old_child_reflects_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hScope : RetainedServiceScope E rho ip ih x y (s + 1) N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    SuffixReflects Kc N.erase.parent (S p src) (T p dst (s + 1))
      (es p src (s + 1)) (et p dst (s + 1)) ∧
    (∀ C ∈ T p dst (s + 1), C.parent? = some N.erase.parent → C.slot < s + 1 →
      et p dst (s + 1) C = true → C ∈ S p src ∧ es p src (s + 1) C = true) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hK : ScoreRunGeometry src dst Kc :=
    ⟨block_preceq_trans (eraseFG_preceq (fgsa_F_preceq_Z p src hs)) h.source_cut,
      block_preceq_trans (F_preceq_liveRoot p dst ht) h.target_cut⟩
  have hA : ScoreRunGeometry src dst N.erase.parent :=
    ⟨block_preceq_trans hK.source_floor h.cut_parent,
      block_preceq_trans hK.target_floor h.cut_parent⟩
  have scores := fgsa_score_eq_on_candidates_on_run_on (hroots := hroots) E rho hE (s + 1) hx
    hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1)) hA
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2) hScope
  have reflect (X C : Block) (hKX : Block.Preceq Kc X) (hXA : Block.Preceq X N.erase.parent)
      (hm : C ∈ T p dst (s + 1)) (hp : C.parent? = some X) (hold : C.slot < s + 1)
      (he : et p dst (s + 1) C = true) : C ∈ S p src ∧ es p src (s + 1) C = true := by
    have hc := fgsa_walkRun_reflected_old_child_on (hroots := hroots) E rho hE s
      hx hy hip hih hseat N hem Kc X C h.source_cut hKX hXA hp hold hm
      (h.reflected_witness X C hKX hXA hm hp hold he) hScope
    refine ⟨hc, ?_⟩
    have hel := fgsa_eligible_eq_of_retainedBand_score p src dst
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1))
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) C
      (h.band_agrees X C hKX hXA hc hm hp hold) scores.1 (scores.2 C ⟨hc, hm⟩)
      ((fgsa_proposal_slot (c := c) _ (s + 1)).trans
        (fgsa_vote_slot (c := c) _ (s + 1)).symm)
    exact hel.trans he
  constructor
  · intro X C hKX hXA hm hp he
    have hCpre : C ∈ (rho.stateBefore E ih y).st.base.blocks := by
      simpa only [dst, clock_base_blocks] using (List.mem_filter.mp hm).1
    have hn := fgsa_preTick_now_le E rho hE.toScheduleWellFormed hih
    have hslot := Internal.slotOf_mono (p := p) hn
    have htick : p.slotOf (SA.voteTime p.toParams (s + 1)) = s + 1 := by
      simpa only [(fgsa_postClock_slot (c := c) (rho.stateBefore E ih y) _).2] using
        fgsa_vote_slot (c := c) (rho.stateBefore E ih y) (s + 1)
    have hle := ((fgsa_stateBefore_bounds E rho hE.toScheduleWellFormed ih y).1 C hCpre).trans
      (htick ▸ hslot)
    have hold : C.slot < s + 1 := lt_of_le_of_ne hle (by
      intro he
      have hCN := fgsa_walkRun_current_block_eq E rho hE (s + 1) (Nat.succ_pos s)
        hx hip hseat N hem C hCpre he
      have hX : X = N.erase.parent := by
        simpa only [hCN] using (fgsa_parent_eq_of_some hp).symm
      have hn := (Bool.and_eq_true_iff.mp hXA).1
      simp only [hX, decide_true, Bool.not_true, Bool.false_eq_true] at hn)
    exact reflect X C hKX (Bool.and_eq_true_iff.mp hXA).2 hm hp hold he
  · intro C hm hp hold he
    exact reflect N.erase.parent C h.cut_parent (block_preceq_refl _) hm hp hold he

end AvailableChain.FGSA.Run
end
