module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head

public section
namespace Consensus.Goldilocks.Refinement

variable {sp : SA.SAParams} {FGP : Type} {U : Set (SA.Blk sp.n FGP)}

/-- An exposed prefix survives exactly when both inputs to the new LCA extend it. -/
theorem exposed_prefix_preserved_of_record_head (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {t : Time} {O : SA.Blk sp.n FGP} :
    Anc U O (SA.acConfirmed sp A Φ t) ↔
      Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Anc U O (SA.acHead sp A Φ t) := by
  constructor
  · intro h
    have hC : (SA.lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
      cases he : SA.lookup Φ A.latestConfirmed with
      | none => exact hΦ.rooted.1
      | some C => exact (SA.lookup_eq_some he).1
    have hH : SA.acHead sp A Φ t ∈ Φ.tree :=
      SA.getHead_mem' hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    unfold SA.acConfirmed at h
    cases hd : SA.deepest Φ {X | X ∈ Φ.tree ∧
        Φ.Anc X ((SA.lookup Φ A.latestConfirmed).getD Φ.F) ∧
        Φ.Anc X (SA.acHead sp A Φ t)} with
    | none =>
      simp only [hd, Option.getD_none] at h
      exact ⟨h.trans ((hΦ.rooted.2 _ hC).mono hΦU),
        h.trans ((hΦ.rooted.2 _ hH).mono hΦU)⟩
    | some D =>
      simp only [hd, Option.getD_some] at h
      exact ⟨h.trans ((SA.deepest_mem hd).1.2.1.mono hΦU),
        h.trans ((SA.deepest_mem hd).1.2.2.mono hΦU)⟩
  · exact fun h => SA.anc_acConfirmed_of_frame hU hΦ hΦU h.1 h.2

/-- Compatibility with a write candidate preserves a prefix, even when the old record
and the candidate themselves need not be comparable. -/
theorem effective_record_update_of_compatible (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O D : SA.Blk sp.n FGP}
    (hO : Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F))
    (hD : D ∈ Φ.tree) (hcomp : Compatible U O D) :
    Anc U O ((SA.lookup Φ (SA.updateLatestConfirmed sp A Φ D).latestConfirmed).getD Φ.F) := by
  classical
  unfold SA.updateLatestConfirmed
  split_ifs with hguard
  · exact hO
  have hOD : Anc U O D := by
    rcases hcomp with h | h
    · exact h
    cases he : SA.lookup Φ A.latestConfirmed with
    | none =>
      simp only [he, Option.getD_none] at hO
      exact hO.trans ((hΦ.rooted.2 _ hD).mono hΦU)
    | some C =>
      simp only [he, Option.getD_some] at hO
      obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
      exact False.elim (hguard ⟨C, hC, hr,
        SA.anc_tree_of_anc_U hU hΦ hΦU hD (h.trans hO) hC⟩)
  change Anc U O ((SA.lookup Φ D.root).getD Φ.F)
  cases he : SA.lookup Φ D.root with
  | none => exact False.elim (SA.lookup_eq_none he ⟨D, hD, rfl⟩)
  | some C =>
    obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
    have : C = D := hU.1 (hΦU hC) (hΦU hD) hr
    simpa [this] using hOD

/-- Endpoint head compatibility transports back along the monotone floor chain. -/
theorem intermediate_F_compatible_of_endpoint_head (hU : Coherent U)
    {Fq Fk H O : SA.Blk sp.n FGP} (hqk : Anc U Fq Fk) (hkH : Anc U Fk H)
    (hOH : Compatible U O H) : Compatible U Fq O := by
  rcases hOH with h | h
  · exact SA.anc_total hU (hqk.trans hkH) h
  · exact Or.inl (hqk.trans (hkH.trans h))

/-- Retention covers every ancestor of a high origin at later-label votes. -/
theorem covered_vote_suffix
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {r l k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r l B) (hCB : Anc (tr.HonestBlocks H) C B)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    (hl : l < e.msg.slot) :
    Compatible (tr.HonestBlocks H) ell.frame.F C ∧
      Compatible (tr.HonestBlocks H) ell.frame.fcRoot C ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C ∧
      (C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) C ell.frame.fcRoot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨hv, hvi⟩ := Healing.voteInv_iff.1 (Healing.retention_inv hp k).1
    x r l B ho y hy ell e hc hl
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
    rcases hvi with hvi | hvi
    · exact Or.inl (hvi.2.1.mono hΦU)
    · exact Or.inr hvi
  have hrootC : Compatible (tr.HonestBlocks H) ell.frame.fcRoot C := by
    rcases hroot with h | h
    · exact SA.anc_total hr.coherent h hCB
    · exact Or.inr (hCB.trans h)
  refine ⟨intermediate_F_compatible_of_endpoint_head hr.coherent
    (hΦ.F_anc_fcRoot.mono hΦU) (.refl) ?_, hrootC, ?_, ?_⟩
  · exact hrootC.symm
  · obtain ⟨Hd, hHd, he, hBH⟩ := hv
    exact ⟨Hd, hHd, he, hCB.trans hBH⟩
  rcases hvi with hvi | hvi
  swap
  · exact Or.inr (hCB.trans hvi)
  rcases hrootC with hfC | hCf
  swap
  · exact Or.inr hCf
  have hCt := SA.frame_mem_of_between sp hr.coherent hΦ hΦU hvi.1.1 hCB
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hfC)
  have hCB' := SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hCt hCB hvi.1.1
  obtain ⟨D, hD, hvD, hBD⟩ := hvi.2.2
  exact Or.inl ⟨SA.voterBlockTree_anc hr hy hc B hvi.1 C hCB',
    SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hΦ.fcRoot_mem hfC hCt,
    D, hD, hvD, hCB'.trans hBD⟩

/-- A fixed archival record survives a frame change when blocks above the new floor
remain available. The retention premise concerns membership, not viable heads. -/
theorem effective_record_frame_of_compatible (hU : Coherent U)
    {Φ Ψ : SA.Frm sp.n FGP} (hΨ : FrameOK Ψ) (hΦU : Φ.tree ⊆ U) (hΨU : Ψ.tree ⊆ U)
    {r : Nat} {O : SA.Blk sp.n FGP} (hFF : Anc U Φ.F Ψ.F)
    (hFO : Compatible U Ψ.F O)
    (hretain : ∀ C ∈ Φ.tree, Anc U Ψ.F C → C ∈ Ψ.tree)
    (hO : Anc U O ((SA.lookup Φ r).getD Φ.F)) :
    Anc U O ((SA.lookup Ψ r).getD Ψ.F) := by
  have floor : Anc U Ψ.F ((SA.lookup Ψ r).getD Ψ.F) := by
    cases he : SA.lookup Ψ r with
    | none => exact .refl
    | some C => exact (hΨ.rooted.2 _ (SA.lookup_eq_some he).1).mono hΨU
  rcases hFO with hFO | hOF
  swap
  · exact hOF.trans floor
  cases he : SA.lookup Φ r with
  | none =>
    simp only [he, Option.getD_none] at hO
    exact hO.trans (hFF.trans floor)
  | some C =>
    simp only [he, Option.getD_some] at hO
    obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
    have hC' := hretain C hC (hFO.trans hO)
    cases he' : SA.lookup Ψ r with
    | none => exact False.elim (SA.lookup_eq_none he' ⟨C, hC', hr⟩)
    | some D =>
      obtain ⟨hD, hrD⟩ := SA.lookup_eq_some he'
      have : D = C := hU.1 (hΨU hD) (hΦU hC) (hrD.trans hr.symm)
      simpa [this] using hO

/-- The frame adapter instantiated on actual states of one honest node. -/
theorem effective_record_frame_of_run
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j r : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocks H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hreach := Compose.fg_reachable hrun.toLocalRun hy j
  have hΨ := (Store.frame_realization _ _ _ _ hreach).1
  apply effective_record_frame_of_compatible hU (Φ := Node.frame (tr.state y i)) hΨ
    (fun X hX => ⟨y, hy, i, hX.1⟩) (fun X hX => ⟨y, hy, j, hX.1⟩)
    (Healing.run_F_mono hrun.toLocalRun hy hij) hFO ?_ hO
  intro C hC hFC
  have hCj := Compose.tree_mono hrun.toLocalRun hy hij hC.1
  obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree _ _ _ _ hreach
  have hfull : FrameOK (⟨(tr.state y j).fg.tree, _, _, ∅⟩ :
      Frame sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)) :=
    { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
      F_anc_fcRoot := .refl, viableHeads_subset := Set.empty_subset _
      fcRoot_anc_viableHeads := fun _ h => h.elim }
  exact ⟨hCj, SA.anc_tree_of_anc_U hU hfull (fun X hX => ⟨y, hy, j, hX⟩)
    hΨ.rooted.1.1 hFC hCj⟩

/-- Every guarded write in a call preserves a prefix compatible with its candidates. -/
theorem effective_record_writes_of_compatible (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {New : SA.Blk sp.n FGP → Prop} {r r' : Nat} {O : SA.Blk sp.n FGP}
    (hw : Compose.Writes Φ New r r')
    (hnew : ∀ D, New D → Compatible U O D)
    (hO : Anc U O ((SA.lookup Φ r).getD Φ.F)) :
    Anc U O ((SA.lookup Φ r').getD Φ.F) := by
  have hw' := Compose.writes_iff.1 hw
  clear hw
  induction hw' with
  | refl => exact hO
  | @tail r' r'' _ hs ih =>
    obtain ⟨D, hD, hn, hk | ⟨hg, rfl⟩⟩ := hs
    · simpa only [hk.2] using ih
    let A : SA.SAState sp.n := SA.SAState.initial r'
    have h := effective_record_update_of_compatible hU hΦ hΦU (A := A) ih hD (hnew D hn)
    simpa only [SA.updateLatestConfirmed, A, SA.SAState.initial, hg, ↓reduceIte] using h

/-- At an actual call, compatibility with each actual write candidate suffices. -/
theorem effective_record_call_of_compatible
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ell) {O : SA.Blk sp.n FGP}
    (hO : Anc U O ((SA.lookup ell.frame (tr.state y k).latestConfirmed).getD ell.frame.F))
    (hnew : ∀ D s CV, SA.ResultAt tr y k s D CV ∨ SA.OptimisticLockAt tr y k s D CV →
      Compatible U O D) :
    Anc U O ((SA.lookup ell.frame (tr.post k).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc
  exact effective_record_writes_of_compatible hr.coherent hΦ hΦU (Compose.call_writes hr hy hc)
    (fun D ⟨s, CV, h⟩ => hnew D s CV h) hO

/-- Writing a held candidate leaves that candidate or a strictly later descendant.
The guard can retain a record only above the candidate, never an older fork. -/
theorem effective_record_update_slot_growth
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {A : SA.SAState sp.n}
    {P : SA.Blk sp.n FGP} (hP : P ∈ Φ.tree) :
    let C := (SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F
    Φ.Anc P C ∧ (C = P ∨ P.slot < C.slot) := by
  classical
  dsimp only
  have lookup_self : ∀ D ∈ Φ.tree, SA.lookup Φ D.root = some D := by
    intro D hD
    cases he : SA.lookup Φ D.root with
    | none => exact False.elim (SA.lookup_eq_none he ⟨D, hD, rfl⟩)
    | some C =>
      obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
      exact congrArg some (hΦ.coherent.1 hC hD hr)
  have hanc : Φ.Anc P
      ((SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F) := by
    unfold SA.updateLatestConfirmed
    split_ifs with hg
    · obtain ⟨C, hC, hr, hPC⟩ := hg
      rw [← hr, lookup_self C hC]
      exact hPC
    · change Φ.Anc P ((SA.lookup Φ P.root).getD Φ.F)
      rw [lookup_self P hP]
      exact .refl
  refine ⟨hanc, ?_⟩
  by_cases he : (SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F = P
  · exact Or.inl he
  · exact Or.inr ((hanc.slot_le hΦ.coherent).2 (Ne.symm he))

/-- The conditional ready update flushes every non-descendant record. The post-state
is read in the actual call frame; frame evolution is handled by the separate adapter. -/
theorem ready_update_effective_record
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hS.run.localRun hy hu.1
  obtain ⟨-, -, hfast⟩ := Healing.ready_update_selection hp hc hP hR hgu hy hu hPt hnext
  obtain ⟨hconf, hnv, -, hpost⟩ := SA.first_update_post hS hgu
    (Healing.ready_unanimous hp hc hP hR) hy hu.1 hu.2.1 hu.2.2.1 hPt
    (Healing.ready_update_locks_compatible hp hc hP hR hgu hy hu hnext)
  refine ⟨?_, hfast⟩
  rw [hpost]
  unfold SA.updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  exact (effective_record_update_slot_growth (sp := sp) hΦ hPt).1.mono hΦU

/-- A raw result lies below a unanimous head when its pool has enough participants.
No fast test or absence of veto is required. -/
theorem raw_result_below_unanimous
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hr : SA.ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hparticipants : 2 * Hᶜ.ncard ≤ (SA.voters {v | v ∈ (tr.state x r).pool l}).ncard)
    (hP : P ∈ U)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → e.msg.head = P.root) :
    Anc U C P := by
  obtain ⟨z, hz, q, -, e, hv, -, hs, Hd, hHd, he, hCH⟩ :=
    SA.result_honest_supporter_of_participants sp hr hx hres (B := C) .refl hparticipants
  have : Hd = P := hr.localRun.coherent.1 hHd hP (he.trans (hvotes z hz q e hv hs))
  exact this ▸ hCH

/-- Conditional later-label transfer compares the raw result with the prefix extended
by that same honest counted vote. It does not orient the result below the prefix. -/
theorem raw_result_compatible_of_votes
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hr : SA.ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hparticipants : 2 * Hᶜ.ncard ≤ (SA.voters {v | v ∈ (tr.state x r).pool l}).ncard)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → SA.VoteExtends U e.msg P) :
    Compatible U C P := by
  obtain ⟨z, hz, q, -, e, hv, -, hs, Hd, hHd, he, hCH⟩ :=
    SA.result_honest_supporter_of_participants sp hr hx hres (B := C) .refl hparticipants
  obtain ⟨Hp, hHp, hep, hPH⟩ := hvotes z hz q e hv hs
  obtain rfl : Hp = Hd := hr.localRun.coherent.1 hHp hHd (hep.trans he.symm)
  exact SA.anc_total hr.localRun.coherent hCH hPH

/-- Healthy late updates need no separately supplied participant bound. -/
theorem raw_result_compatible_of_healthy_votes
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} {g : Time} (hS : SA.HealthyBase tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hgl : SA.gbar g + 4 * sp.Δ ≤ sp.ts l)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → SA.VoteExtends U e.msg P) :
    Compatible U C P := by
  obtain ⟨ell, hu, hC, -⟩ := hres
  obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hCH⟩ := SA.result_extended hS hgl hx hu.1
    (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
  obtain ⟨Hp, hHp, hep, hPH⟩ := hvotes z hz q e hv hs
  obtain rfl : Hp = Hd := hS.run.localRun.coherent.1 hHp hHd (hep.trans he.symm)
  exact SA.anc_total hS.run.localRun.coherent hCH hPH

/-- A raw result of the ready proposal's own label is below that proposal, including
vetoed or sub-fast results. Later labels require their own vote-extension premise. -/
theorem raw_result_below_ready
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr.projAC x r u C CV) :
    Anc (tr.HonestBlocks H) C P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨ell, hu, hC, -⟩ := hres
  obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hCH⟩ := SA.result_extended hS hgu hx hu.1
    (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
  obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, _⟩ :=
    Healing.honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm
  have : Hd = P := hS.run.localRun.coherent.1 hHd hPU
    (he.trans (Healing.ready_unanimous hp hc hP hR z hz q e hv hs))
  exact this ▸ hCH

/-- When the floor has passed a covering high origin, its crossing supplies a frozen
viable descendant of the target. Mere high state height is not an origin premise. -/
theorem covered_target_frozen_witness_of_high_floor
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hCB : Anc (tr.HonestBlocks H) C B)
    (hFC : Anc (tr.HonestBlocks H) ell.frame.F C)
    (hpair : ∀ v r l O, r < k → Healing.HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → Healing.HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → Healing.HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) C D ∧ (tr.state y k).fg.IsViable D := by
  obtain ⟨v, r, l, O, E, -, hO, hl, hE, hEO, hBO, hf⟩ :=
    Healing.high_floor_source_core hp ho hy hc hj hpair hcomp hfloor
  exact Healing.raw_target_frozen_witness hp hO hy hc hl hFC (hCB.trans hBO) hE hEO hf

/-- An actual earlier-label high cover gives a floor-reaching frozen witness or
root coverage. No claim is made for a merely high-height held block. -/
theorem covered_target_frozen_witness
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x i j B) (hCB : Anc (tr.HonestBlocks H) C B)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    (hj : j < e.msg.slot) :
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) C D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) C ell.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΦU := (SA.frameIn_of_callAt hr hy hc.1).2
  rcases (covered_vote_suffix hp ho hCB hy hc hj).2.2.2 with hv | hf
  · obtain ⟨D, hD, hvD, hCD⟩ := hv.2.2
    rw [Compose.frame_of_projAC hp.run hy hc.1] at hvD
    exact Or.inl ⟨D, hD, hCD.mono hΦU, hvD.2.2.2⟩
  · exact Or.inr hf

/-- Normalizing a held lock preserves any ancestor that remains a candidate. -/
theorem anc_viableAncestor_of_candidate {n : Nat} {FGP : Type} {Φ : SA.Frm n FGP}
    (hΦ : FrameOK Φ) {O B : SA.Blk n FGP} (hB : B ∈ Φ.tree)
    (hOB : Φ.Anc O B) (hO : Φ.AncestorCandidate O) :
    Φ.Anc O (Φ.viableAncestor B) :=
  (SA.viableAncestor_spec hΦ hB).2.2 O hOB hO

/-- An actual stored fast lock covering a high held prefix supplies an earlier high
origin. The source label is exactly the stored lock's label; no liveness is needed. -/
theorem high_cover_of_stored_fast_lock
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {l : SA.Lock}
    (hl : l ∈ (tr.state y k).ac.locks) (hf : l.fast = true)
    {O L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ (tr.state y k).fg.tree)
    (hrL : L.root = l.block) (hOL : Anc (tr.HonestBlocks H) O L)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ O.root).h) :
    ∃ r < k, ∃ B, Healing.HighOrigin tr H g y r l.slot B ∧
      Anc (tr.HonestBlocks H) O B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hl' : l ∈ (tr.projAC.state y k).locks := by
    rw [Compose.projAC_state hp.run.toLocalRun hy]; exact hl
  obtain ⟨r, hrk, CV, ell, D, hc, hfl, L', hL', hrL', hLB⟩ :=
    Healing.stored_fast_lock_provenance hr hy k l hl' hf
  obtain rfl : L' = L := hr.coherent.1 hL' ⟨y, hy, k, hL⟩ (hrL'.trans hrL.symm)
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  have he : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
  rw [he] at hD
  have hBt := (SA.viableAncestor_anc (SA.frameIn_of_callAt hr hy hc).1 hD).1
  have hBr := Healing.frame_tree_subset hp hy hc hBt
  have hBk := Compose.tree_mono hp.run.toLocalRun hy hrk.le hBr
  have hOB := hOL.trans hLB
  have hhB := Healing.σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (Healing.anc_tree_of_anc hp hy hOB hBk)
  have hhBr : Healing.HZ tr H g + 1 ≤
      ((tr.state y r).fg.σ (ell.frame.viableAncestor D).root).h := by
    rw [← Healing.σ_eq_run hp hy hy hBk hBr]
    exact hh.trans hhB
  exact ⟨r, hrk, ell.frame.viableAncestor D, ⟨hy,
    Healing.joinedAt_of_fastLockAt hp.run hp.noColl hy hfl,
    ⟨CV, ell, D, hc, hfl, rfl⟩, hhBr⟩, hOB⟩

/-- A real high report supplies an earlier high cover of every prefix below it.
The report's existence is a premise, not a consequence of heldness. -/
theorem high_cover_of_report
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {O R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC y k ell R)
    (hOR : Anc (tr.HonestBlocks H) O R)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ O.root).h) :
    ∃ r < k, ∃ l B, Healing.HighOrigin tr H g y r l B ∧ Anc (tr.HonestBlocks H) O B := by
  have hhR := hh.trans (Healing.σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (Healing.anc_tree_of_anc hp hy hOR (Healing.toFG_mem_tree hp.run hy hrep)))
  obtain ⟨r, hr, l, B, ho, hRB⟩ := Healing.high_report_origin hp hy hrep hhR
  exact ⟨r, hr, l, B, ho, hOR.trans hRB⟩

/-- A prefix with fewer than half opponents lies below the unlock target. -/
theorem anc_unlockTarget_of_opponents
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {O B : SA.Blk sp.n FGP}
    (hO : O ∈ Φ.tree) (_hB : B ∈ Φ.tree) (hOB : Φ.Anc O B)
    (V : SA.View sp.n) (s : Int)
    (hopp : 2 * (SA.opponents sp Φ V s O).ncard < sp.n) :
    Φ.Anc O (SA.unlockTarget sp Φ V s B) := by
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ
    (S := {X | X ∈ Φ.tree ∧ Φ.Anc X B ∧ 2 * (SA.opponents sp Φ V s X).ncard < sp.n})
    (fun X h => h.1) ⟨O, hO, hOB, hopp⟩
  unfold SA.unlockTarget
  rw [hD]
  exact SA.anc_deepest hΦ (fun X h => h.1)
    (fun X hX Y hY => SA.anc_total hΦ.coherent hX.2.1 hY.2.1) hD O ⟨hO, hOB, hopp⟩

/-- Unlock preserves a prefix of an already-live normalized lock when its label is
not challenged, or the prefix has fewer than half opponents. -/
theorem unlock_preserves_prefix
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set SA.Lock} {t : Time}
    {V : SA.View sp.n} {s : Int} {l : SA.Lock} {O B : SA.Blk sp.n FGP}
    (hl : l ∈ SA.liveLocks sp L Φ t) (hB : B ∈ Φ.tree) (hr : B.root = l.block)
    (hO : O ∈ Φ.tree) (hOB : Φ.Anc O B)
    (hguard : s ≤ (l.slot : Int) ∨ 2 * (SA.opponents sp Φ V s O).ncard < sp.n) :
    ∃ l' ∈ SA.unlock sp L Φ t s V, ∃ B' ∈ Φ.tree,
      B'.root = l'.block ∧ Φ.Anc O B' ∧ l'.slot = l.slot ∧ l'.fast = l.fast := by
  classical
  by_cases hs : (l.slot : Int) < s
  · have hopp := hguard.resolve_left (not_le.mpr hs)
    obtain ⟨hT, -⟩ := SA.unlockTarget_anc sp hΦ V s hB
    refine ⟨⟨(SA.unlockTarget sp Φ V s B).root, l.slot, l.fast⟩,
      ⟨l, hl, B, hB, hr, by simp only [hs, ↓reduceIte]⟩,
      SA.unlockTarget sp Φ V s B, hT, rfl, ?_, rfl, rfl⟩
    exact anc_unlockTarget_of_opponents hΦ hO hB hOB V s hopp
  · exact ⟨l, ⟨l, hl, B, hB, hr, by simp only [hs, ↓reduceIte]⟩,
      B, hB, hr, hOB, rfl, rfl⟩

/-- A head certificate is checked at the actual read clock. Floor coverage also
allows the prefix to lie outside the current frame. -/
theorem anc_acHead_of_current_certificate
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O : SA.Blk sp.n FGP} {t : Time}
    (hhead : Anc U O Φ.F ∨ (O ∈ Φ.tree ∧
      Compatible Φ.tree (SA.getAnchor sp A Φ t) O ∧
      (Φ.Anc O (SA.getAnchor sp A Φ t) ∨ (O ∈ Φ.viableTree Φ.tree ∧
        (SA.voters (SA.latestView sp A Φ t).1.votes).ncard <
          2 * (SA.supporters Φ (SA.latestView sp A Φ t).1
            (SA.latestView sp A Φ t).2 O).ncard)))) :
    Anc U O (SA.acHead sp A Φ t) := by
  rcases hhead with hF | ⟨hO, hcomp, hsup⟩
  · have hH : SA.acHead sp A Φ t ∈ Φ.tree :=
      SA.getHead_mem' hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    exact hF.trans ((hΦ.rooted.2 _ hH).mono hΦU)
  · exact (SA.anc_acHead hΦ hO hcomp hsup).mono hΦU

/-- Fixed-record reads preserve the prefix with a fresh head certificate, even if
the old lock expired. This supplies no certificate from an earlier view or clock. -/
theorem exposed_prefix_preserved_at_clock (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O : SA.Blk sp.n FGP} {t : Time}
    (hE : Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F))
    (hhead : Anc U O Φ.F ∨ (O ∈ Φ.tree ∧
      Compatible Φ.tree (SA.getAnchor sp A Φ t) O ∧
      (Φ.Anc O (SA.getAnchor sp A Φ t) ∨ (O ∈ Φ.viableTree Φ.tree ∧
        (SA.voters (SA.latestView sp A Φ t).1.votes).ncard <
          2 * (SA.supporters Φ (SA.latestView sp A Φ t).1
            (SA.latestView sp A Φ t).2 O).ncard)))) :
    Anc U O (SA.acConfirmed sp A Φ t) :=
  (exposed_prefix_preserved_of_record_head hU hΦ hΦU).mpr
    ⟨hE, anc_acHead_of_current_certificate hΦ hΦU hhead⟩

section CoveredPrefix

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

/-- An actual earlier-label high cover makes later raw and optimistic candidates comparable
with the exposed prefix. This gives compatibility, not a direction or a read-head certificate. -/
theorem covered_candidates_compatible
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {r b : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    {y : Fin sp.n} (hy : y ∈ H) {k s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hbs : b < s)
    (hD : (SA.ResultAt tr.projAC y k s D CV ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧
        Healing.CatchRun tr H g (2 * sp.Δ)) ∨ SA.OptimisticLockAt tr.projAC y k s D CV) :
    Compatible (tr.HonestBlocks H) D O := by
  have hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
    intro z hz q e hv hs
    obtain ⟨ell, hcast⟩ := hv
    exact (covered_vote_suffix hp ho hOB hz hcast (hs ▸ hbs)).2.2.1
  rcases hD with ⟨hres, hlate, hc⟩ | hopt
  · exact raw_result_compatible_of_healthy_votes
      (Healing.healthy_base_of_reset_catch hp hc) hy hres hlate hvotes
  · have hf : 2 * Hᶜ.ncard < sp.n := by
      have := hp.healthy.2.2
      have := Fin.pos y
      have hn : sp.n = sp.toParams.n := rfl
      omega
    exact SA.optimisticLock_compatible
      (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl) hf hy hopt hvotes

/-- A stored fast lock covering a high exposed prefix supplies both historic vote geometry
and later candidate compatibility. Only labels are ordered: the queried cast may precede
the cut at which the stored lock is observed. Liveness of that lock is not required. -/
theorem stored_fast_lock_covers_exposed_prefix
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {lock : SA.Lock}
    (hl : lock ∈ (tr.state x k).ac.locks) (hf : lock.fast = true)
    {O L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ (tr.state x k).fg.tree)
    (hrL : L.root = lock.block) (hOL : Anc (tr.HonestBlocks H) O L)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state x k).fg.σ O.root).h) :
    (∀ y ∈ H, ∀ q ell v, SA.CastAt tr.projAC y q ell v → lock.slot < v.msg.slot →
      Compatible (tr.HonestBlocks H) ell.frame.F O ∧
      Compatible (tr.HonestBlocks H) ell.frame.fcRoot O ∧
      SA.VoteExtends (tr.HonestBlocks H) v.msg O ∧
      (O ∈ ell.frame.viableTree (SA.voterBlockTree sp v.readPoint ell.frame v.msg.slot) ∨
        Anc (tr.HonestBlocks H) O ell.frame.fcRoot)) ∧
    (∀ y ∈ H, ∀ q s D CV, lock.slot < s →
      ((SA.ResultAt tr.projAC y q s D CV ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧
        Healing.CatchRun tr H g (2 * sp.Δ)) ∨ SA.OptimisticLockAt tr.projAC y q s D CV) →
      Compatible (tr.HonestBlocks H) D O) := by
  obtain ⟨r, -, B, ho, hOB⟩ := high_cover_of_stored_fast_lock hp hx hl hf hL hrL hOL hh
  constructor
  · intro y hy q ell v hv hs
    exact covered_vote_suffix hp ho hOB hy hv hs
  · intro y hy q s D CV hs hD
    exact covered_candidates_compatible hp ho hOB hy hs hD

end CoveredPrefix

/-- The literal ready-reader endpoint, conditional only on cross-read input compatibility
and preservation of the earlier output in both inputs of each later read. The producer
scopes match `ReadySafeOn`, including boundary cuts and the actual read clocks. -/
theorem readySafeOn_of_read_producers
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (c t₀ t₁ : Time)
    (hagree : ∀ y z i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr z j →
      t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c z t' →
      let Φ := Node.frame (tr.state y i)
      let Ψ := Node.frame (tr.state z j)
      let E := (SA.lookup Φ (tr.state y i).ac.latestConfirmed).getD Φ.F
      let E' := (SA.lookup Ψ (tr.state z j).ac.latestConfirmed).getD Ψ.F
      let head := SA.acHead sp (tr.state y i).ac Φ t
      let head' := SA.acHead sp (tr.state z j).ac Ψ t'
      ∃ X Y, (X = E ∨ X = head) ∧ (Y = E' ∨ Y = head') ∧
        Compatible (tr.HonestBlocks H) X Y)
    (hmono : ∀ y i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr y j →
      i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c y t' →
      let Ψ := Node.frame (tr.state y j)
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        ((SA.lookup Ψ (tr.state y j).ac.latestConfirmed).getD Ψ.F) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y j).ac Ψ t')) :
    Regimes.ReadySafeOn tr H c t₀ t₁ := by
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hsub : ∀ y ∈ H, ∀ i, (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun y hy i _ hX => ⟨y, hy, i, hX.1⟩
  have hinputs : ∀ y ∈ H, ∀ i t,
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
          (Node.frame (tr.state y i)).F) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y i).ac (Node.frame (tr.state y i)) t) := by
    intro y hy i t
    exact (exposed_prefix_preserved_of_record_head hU
      (Compose.frameOK_state hrun.toLocalRun hy i) (hsub y hy i)).mp .refl
  constructor
  · intro y z i j t t' hi hj hbi hbj ht ht₁ ht' ht₁' hy hz
    obtain ⟨X, Y, hX, hY, hXY⟩ := hagree y z i j t t' hi hj hbi hbj ht ht₁ ht' ht₁' hy hz
    have hOX : Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t) X := by
      rcases hX with rfl | rfl
      · exact (hinputs y hy.1 i t).1
      · exact (hinputs y hy.1 i t).2
    have hOY : Anc (tr.HonestBlocks H) (Regimes.readAfter tr z j t') Y := by
      rcases hY with rfl | rfl
      · exact (hinputs z hz.1 j t').1
      · exact (hinputs z hz.1 j t').2
    rcases hXY with h | h
    · exact SA.anc_total hU (hOX.trans h) hOY
    · exact SA.anc_total hU hOX (hOY.trans h)
  · intro y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy'
    exact (exposed_prefix_preserved_of_record_head hU
      (Compose.frameOK_state hrun.toLocalRun hy'.1 j) (hsub y hy'.1 j)).mpr
        (hmono y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy')

end Consensus.Goldilocks.Refinement
end
