module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo

public section

/-! # Shadow P-U: left-entry provenance

The stock RowSource and LeftEntry arguments over the shadow run. AC-only facts use the
stock AC projection; store facts use the finality-parametric cache transport.
-/

namespace Consensus.Goldilocks.Healing.ShadowLeft

open AC (ACParams ReplayOrder Payload)
open Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

private theorem frame_mem {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    {v : Fin sp.n} (hv : v ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt v i ell) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) : B ∈ (tr.state v i).fg.tree := by
  rw [Node.frame_of_projAC_at' hrun.toLocalRun' hv hc, Node.frame'_eq,
    toFrame'_tree] at hB
  exact hB.1

private theorem mem_of_anc {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {v : Fin sp.n} (hv : v ∈ H) {i : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocks H) B C)
    (hC : C ∈ (tr.state v i).fg.tree) : B ∈ (tr.state v i).fg.tree := by
  by_cases he : B = C
  · exact he ▸ hC
  · exact (Anc.mem (Coherence.honest_held_anc' hrun hnc hv h hC) he).1

private theorem sign_entry {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) :
    ∃ E ∈ (tr.state v d).fg.tree, E.root = att.T ∧
      ((tr.state v d).fg.σ E.root).h = att.h := by
  obtain ⟨src, hc⟩ := hs
  exact exists_entry_of_createAtt_with finalitySpec_updateFinality'
    (Node.fg_reachable_at' hrun.toLocalRun' hv d).reachableWith
    ((Node.cutStep'_attest_some _ _ _ _ _ _).1 (hrun.cutLaw v hv d _ hc)).1

private theorem fast_mem {v : Fin sp.n} {i s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (h : AC.FastLockAt tr.projAC v i s D CV) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt v i ell) : D ∈ ell.frame.tree := by
  rcases h with ⟨ell', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ell', A, ⟨hc', -⟩, -, hs, -⟩
  · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (AC.deepest_mem hD).1.1.1
  · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold AC.optimisticSelect at hs
    dsimp only at hs
    split_ifs at hs
    exact (AC.deepest_mem hs).1.1

/-- The stock local RowSource extraction, keeping joinedness as the AC trace predicate. -/
theorem signed_entry_source {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {v : Fin sp.n} (hv : v ∈ H) {d : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt v d att)
    (hfast : ∀ d' ell C, d' < d → AC.ToFGAt tr.projAC v d' ell C →
      att.h ≤ ((tr.state v d').fg.σ C.root).h →
      C ∈ AC.toFGCandidates sp (tr.projAC.state v d') ell.frame (tr.time d')) :
    ∃ r < d, ∃ l O, AC.joined sp (tr.projAC.state v r) (tr.time r) ∧
      (∃ CV, Compose.StoredFastLockAt tr v r l O CV) ∧
      att.h ≤ ((tr.state v r).fg.σ O.root).h ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨d', rfl, ell, hc', hto, -, hC, hfgeq⟩ :=
    Compose.attest_source' hrun.toLocalRun' hv hcall
  have hpc : tr.projAC.CallAt v d' ell := Compose.projAC_callAt.mpr hc'
  have hC' : (AC.acToFG sp (tr.projAC.state v d') ell.frame (tr.time d')).2 = some C := by
    rw [Compose.projAC_state' hrun.toLocalRun' hv]
    exact hC
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hv hpc
  have hCt : C ∈ ell.frame.tree := (AC.toFG_source hC').1.1
  let st := (tr.state v (d' + 1)).fg
  have hreach := (Node.fg_reachable_at' hrun.toLocalRun' hv (d' + 1)).reachableWith
  have hCst : C ∈ st.tree := by
    change C ∈ (tr.state v (d' + 1)).fg.tree
    rw [hfgeq]
    exact frame_mem hrun hv hpc hCt
  have hcut := ((Node.cutStep'_attest_some _ _ _ _ _ _).1
    (hrun.cutLaw v hv (d' + 1) _ hcall)).1
  obtain ⟨hah, haT⟩ := Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ :=
    entry_state_of_source_with finalitySpec_updateFinality' hreach _ hCst
  have hEh' : (st.σ E.root).h = att.h := by rw [hah, hEr]
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  have hCh : att.h ≤ ((tr.state v d').fg.σ C.root).h := by
    have := h_le_of_store_anc_with finalitySpec_updateFinality' hreach hEC
    rw [hEh'] at this
    change _ ≤ ((tr.state v (d' + 1)).fg.σ C.root).h at this
    rwa [← hfgeq]
  obtain ⟨-, l, hl, hlb, hlf, -⟩ := hfast d' ell C (by omega) ⟨hpc, hto, hC'⟩ hCh
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨r, hrd, CV, ellw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    Healing.stored_fast_lock_provenance hr hrun.vstart hv d' l₀ hl₀ hlf
  obtain ⟨hPhiw, -⟩ := AC.frameIn_of_callAt hr hv hcw
  obtain ⟨hvat, hva⟩ := AC.viableAncestor_anc hPhi hB₀
  obtain rfl : C = ell.frame.viableAncestor B₀ := hU.1 (hPhiU hCt) (hPhiU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)
  set O := ellw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) O :=
    (hva.mono hPhiU).trans hLO
  have hOt : O ∈ (tr.state v r).fg.tree :=
    frame_mem hrun hv hcw (AC.viableAncestor_anc hPhiw (fast_mem hfl hcw)).1
  have hOst : O ∈ st.tree := Compose.tree_mono' hrun.toLocalRun' hv (by omega) hOt
  have hCOst := Coherence.honest_held_anc' hrun hnc hv hCO hOst
  have hσO := Healing.σ_eq_honest' hrun hnc hv hv hOst hOt
  have hOh : att.h ≤ ((tr.state v r).fg.σ O.root).h := by
    rw [← hσO]
    have := h_le_of_store_anc_with finalitySpec_updateFinality' hreach hCOst
    change _ ≤ ((tr.state v (d' + 1)).fg.σ O.root).h at this
    rw [hfgeq] at this
    rw [hfgeq]
    exact hCh.trans this
  have hsub : st.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨v, hv, d' + 1, hX⟩
  have hEO : Anc (tr.HonestBlocks H) E O := (hEC.mono hsub).trans hCO
  have hEt := mem_of_anc hrun hnc hv hEO hOt
  have hσE := Healing.σ_eq_honest' hrun hnc hv hv hEt hE
  refine ⟨r, by omega, l₀.slot, O, (Healing.joined_of_fastLockAt hr hv hfl).1,
    ⟨CV, ellw, D, hcw, hfl, rfl⟩, hOh, E, hEt,
    Coherence.honest_held_anc' hrun hnc hv hEO hOt, hEr', ?_, ?_⟩
  · rw [hσE, hEh']
  · rw [hσE, hETh']

private theorem joined_fast {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {v : Fin sp.n} (hv : v ∈ H) {i s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (h : AC.FastLockAt tr.projAC v i s D CV) : tr.JoinedAt v (tr.time i) := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  obtain ⟨hj, ell, hc, hnr⟩ := Healing.joined_of_fastLockAt hr hv h
  have hp : AC.joined sp (tr.projAC.post i) (tr.time i) := by
    have he := hr.exec i ell hc.2 (hc.1 ▸ hv)
    rw [hc.1] at he
    rw [show (tr.projAC.post i) =
      ((AC.goldilocksAC sp _ ro).step v (tr.projAC.state v i) ell.frame
        (tr.time i) ell.call).1 from congrArg Prod.fst he.symm]
    change _ ≤ _
    rw [AC.step_restartTime _ _ _ _ _ hnr]
    exact hj
  apply (Compose.joinedAt_iff_restartCuts v _ (fun k _ => hrun.time_nonneg k)).2
  intro k hk hkt
  have hk' := Compose.projAC_restartAt.2 hk
  by_cases hki : k ≤ i
  · exact (AC.joined_awakeU sp _ _ _ _ _ hr.toU v hv i ell hc hp).2 k hki hk'
  · obtain ⟨ellk, hck, hres⟩ := hk'
    obtain ⟨u, -, huk, -, hb⟩ := hr.sleep_of_restart v hv k ellk hck hres
    have := hb i (by omega) ell hc
    exact False.elim ((not_lt_of_ge hkt) (this.trans huk))

end Consensus.Goldilocks.Healing.ShadowLeft

namespace Consensus.Goldilocks.Healing.Growing.ShadowLeft

open AC (ACParams ReplayOrder Payload)
open Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

/-- The stock RowSource wrapper, using the proved shadow deep quarantine. -/
theorem high_row_source_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} {v : Fin sp.n} {d : Nat}
    {att : FG.Att sp.n} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root := by
  have ht := hrun.time_nonneg d
  have hv := hrun.antitone (le_max_right _ _) hvz
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨r, hrd, l, O, -, hstored, hOh, E, hE, hEO, hEr, hEh, hETh⟩ :=
    Healing.ShadowLeft.signed_entry_source (hrun.upTo ht) (hnc.upTo _) hv hs'
      fun d' ell C hd' hto hCh => by
        have hd't : tr.time d' ≤ tr.time d := hrun.time_mono hd'.le
        have hto' := (toFGAt_upTo_iff hrun.time_mono hd't).mp hto
        rw [RunTrace.upTo_state_of_le hrun.time_mono hd't] at hCh
        have hv' : v ∈ H (max (cutZ sp.toParams g) (tr.time d')) :=
          hrun.antitone (max_le_max le_rfl hd't) hvz
        have hc := Goldilocks.Shadow.PU.Growing.high_toFG_fast_at' hrun hnc hsnap hv'
          hto' (hh.trans hCh) (fun D hD => hd't.trans (hq D hD))
        rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC v
          (fun _ hk => (hrun.time_mono hk.le).trans hd't),
          Goldilocks.Shadow.PU.Growing.projAC_state_at' hrun
            (hrun.antitone (le_max_right _ _) hv'), Trace.upTo_time]
        exact hc
  have hrt : tr.time r ≤ tr.time d := hrun.time_mono hrd.le
  have he : (tr.upTo (tr.time d)).state v r = tr.state v r :=
    Trace.upTo_state tr v (fun k hk => hrun.time_mono (by omega))
  rw [he] at hOh hE hEO hEh hETh
  obtain ⟨CV, ell, D, hc, hfl, hO⟩ := hstored
  have hj := Healing.ShadowLeft.joined_fast (hrun.upTo ht) (hnc.upTo _) hv hfl
  have hj' : tr.JoinedAt v (tr.time r) := by
    intro k hk hkr
    exact hj k ((RunTrace.upTo_restartAt tr).mpr ⟨hkr.trans hrt, hk⟩) hkr
  have hc' : tr.projAC.CallAt v r ell := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hfl' : AC.FastLockAt tr.projAC v r l D CV :=
    (fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl
  exact ⟨r, hrd, l, O, ⟨hrun.antitone (max_le_max le_rfl hrt) hvz, hj',
    ⟨CV, ell, D, hc', hfl', hO⟩, hh.trans hOh⟩, E, hE, hEO, hEr, hEh, hETh⟩

private theorem honest_att_of_left {P : Params} {ACP : Type} {acp₀ : ACP}
    {st : Store P ACP} (hr : st.Reachable' acp₀) {V : Set (Fin P.n)}
    (hq : Vᶜ.ncard < P.fg.q) {E C : NodeBlock P ACP}
    (hET : (st.σ E.root).Th = E.root) (hEC : st.Anc E C)
    (hlt : (st.σ E.root).h < (st.σ C.root).h) :
    ∃ W ∈ st.tree, ∃ att ∈ W.fgPayload, att.T = E.root ∧ att.val ∈ V := by
  by_contra hn
  push Not at hn
  have hcard : ∀ p : Finset (Fin P.n), (∀ v ∈ p, v ∉ V) → p.card < P.fg.q := by
    intro p hp
    have := Set.ncard_le_ncard (s := (p : Set (Fin P.n))) (t := Vᶜ) hp (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    omega
  have hr' := hr.reachableWith
  have hU : ∀ W, st.Anc (P.genesisBlock acp₀) W →
      (st.σ W.root).target ⊆ (st.σ W.root).prog ∧ ∀ v ∈ (st.σ W.root).prog,
        ∃ W' ∈ st.tree, st.Anc W' W ∧ ∃ a ∈ W'.fgPayload, a.val = v ∧
          a.T = (st.σ W.root).Th := by
    intro W hW
    induction hW with
    | refl =>
      rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl,
        σ_genesis_with finalitySpec_updateFinality' hr']
      exact ⟨fun _ h => h, fun v hv => (Finset.notMem_empty v hv).elim⟩
    | tail _ hpar ih =>
      obtain ⟨-, h2, hp⟩ := id hpar
      obtain ⟨-, -, -, ht⟩ := step_σ_with finalitySpec_updateFinality' hr' h2 hp
      obtain ⟨htp, p, hpv, hcase⟩ := Goldilocks.Store.step_prog ht ih.1
      refine ⟨htp, ?_⟩
      rcases hcase with ⟨-, hTh, hpe⟩ | ⟨-, hpe⟩
      · rw [hpe, hTh]
        intro v hv
        rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
        · obtain ⟨W', hW't, hW', a, ha, h'⟩ := ih.2 v hv
          exact ⟨W', hW't, hW'.tail hpar, a, ha, h'⟩
        · exact ⟨_, h2, .refl, a, ha, hav, haT⟩
      · rw [hpe]
        exact fun v hv => (Finset.notMem_empty v hv).elim
  have hg := (accepted_tree_with finalitySpec_updateFinality' hr').2.2.2
  have kept : (st.σ C.root).h = (st.σ E.root).h ∧ (st.σ C.root).Th = E.root := by
    clear hlt
    induction hEC with
    | refl => exact ⟨rfl, hET⟩
    | tail _ hpar ih =>
      obtain ⟨h1, h2, hp⟩ := hpar
      obtain ⟨-, -, -, ht⟩ := step_σ_with finalitySpec_updateFinality' hr' h2 hp
      obtain ⟨ihh, ihT⟩ := ih
      obtain ⟨-, p, hpv, hcase⟩ := Goldilocks.Store.step_prog ht (hU _ (hg _ h1)).1
      have hpn : ∀ v ∈ p, v ∉ V := by
        intro v hv
        rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
        · obtain ⟨W', hW't, -, a, ha, hav, haT⟩ := (hU _ (hg _ h1)).2 v hv
          exact hav ▸ hn W' hW't a ha (haT.trans ihT)
        · exact hav ▸ hn _ h2 a ha (haT.trans ihT)
      rcases hcase with ⟨hh, hTh, -⟩ | ⟨hq', -⟩
      · exact ⟨hh.trans ihh, hTh.trans ihT⟩
      · exact absurd hq' (not_le.2 (hcard p hpn))
  omega

private theorem attest_source {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {att : FG.Att sp.n}
    (hc : tr.CallAt v d (.fg (.attest C (some att)))) :
    ∃ j, d = j + 1 ∧ ∃ ell : ACLabel (goldilocksNode' sp ro),
      tr.CallAt v j (.ac ell) ∧ ell.call = .toFG ∧ tr.time j = tr.time d ∧
      ((goldilocksNode' sp ro).toFG (tr.state v j).ac ell.frame (tr.time j)).2 = some C ∧
      (tr.state v d).fg = (tr.state v j).fg := by
  obtain ⟨j, hj, ell, hc', hto, ht, hC, hs⟩ :=
    Compose.attest_source' (hrun.upTo (hrun.time_nonneg d)).toLocalRun' hv
      ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)
  change tr.time j = tr.time d at ht
  rw [RunTrace.upTo_state_of_le hrun.time_mono ht.le] at hC
  rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl,
    RunTrace.upTo_state_of_le hrun.time_mono ht.le] at hs
  exact ⟨j, hj, ell, ((Trace.upTo_callAt _).mp hc').2, hto, ht, hC, hs⟩

private theorem lock_label {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {t : Time}
    (h : Compose.Growing.LockWithin tr H C s t) : s ≤ sp.slot t := by
  obtain ⟨x, i, -, hit, hl⟩ := Compose.Growing.lockWithin_iff.1 h
  have hi0 := hrun.time_nonneg i
  have hm := AC.slot_mono sp hi0 hit
  have hupd : ∀ ell, AC.UpdateAt tr.projAC x i s ell → s ≤ sp.slot (tr.time i) := by
    intro ell hu
    have htime : tr.time i = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hts : sp.ts s ≤ tr.time i := by linarith [sp.toParams.hΔ]
    have := (AC.ts_le_iff_le_slot sp hi0 (s : Int)).1 hts
    omega
  rcases hl with ⟨-, ⟨ell, -, hu, -⟩ | ⟨-, -, -, hsl, -⟩⟩ | ⟨ell, -, hu, -⟩
  · exact (hupd ell hu).trans hm
  · have hs : sp.slot (tr.time i) = s := hsl
    omega
  · exact (hupd ell hu).trans hm

private theorem signed_row_lock_member {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g a b : Time} {v : Fin sp.n} {d : Nat}
    {att : FG.Att sp.n} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧ ∃ r < d, ∃ s C D,
      HealedMemberBefore tr H g a b C s d ∧
      Anc (tr.HonestBlocksAt H) E C ∧ Anc (tr.HonestBlocksAt H) C D ∧
      v ∈ H (tr.time r) ∧
      ((∃ CV, AC.FastLockAt tr.projAC v r s D CV) ∨ AC.SlowLockAt tr.projAC v r s D) := by
  have hv := hrun.antitone (le_max_right _ _) hvz
  by_cases hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ
  · obtain ⟨r, hrd, l, O, ho, E, hE, hEO, hEr, -⟩ :=
      high_row_source_at hrun hnc hvz hs hh hsnap hq
    have hO := hrun.antitone (le_max_right _ _) ho.1
    have hr0 := hrun.time_nonneg r
    have hler : ∀ q < r, tr.time q ≤ tr.time r := fun q hq => hrun.time_mono hq.le
    obtain ⟨CV, ell, D', hcl, hfl, hOD⟩ := ho.2.2.1
    have hOD' : Anc (tr.HonestBlocksAt H) O D' := by
      rw [hOD]
      exact Anc.mono (Goldilocks.Shadow.PU.Growing.frame_tree_subset_at' hrun hnc hO hcl).2
        (AC.anc_viableAncestor _ D') |>.mono
          (fun X hX => ⟨v, r, tr.time r, hr0, hler, hO, hX⟩)
    exact ⟨E, ⟨v, r, tr.time r, hr0, hler, hO, hE⟩, hEr, r, hrd, l, O, D',
      healedMemberBefore_iff.2
        (Or.inr (Or.inr ⟨v, r, hrd, (hrun.time_mono hrd.le).trans hdb, ho⟩)),
      hEO.mono (fun X hX => ⟨v, r, tr.time r, hr0, hler, hO, hX⟩), hOD', hO,
      Or.inl ⟨CV, hfl⟩⟩
  push Not at hq
  obtain ⟨Dd, hD, hlt⟩ := hq
  have hdrain := hc.drain_le Dd hD
  have hΔ := sp.toParams.hΔ
  obtain ⟨src, hcall⟩ := hs
  obtain ⟨d', rfl, ell, hc', hto, htd, hC, hfgeq⟩ := attest_source hrun hv hcall
  have hv' : v ∈ H (tr.time d') := htd ▸ hv
  have hrep : AC.ToFGAt tr.projAC v d' ell src :=
    ⟨Compose.projAC_callAt.mpr hc', hto, by
      rw [Goldilocks.Shadow.PU.Growing.projAC_state_at' hrun hv']; exact hC⟩
  have hdt : drainTime sp a ≤ tr.time d' := by rw [htd]; linarith
  have hdb' : tr.time d' ≤ b := htd ▸ hdb
  have hk0 := hrun.time_nonneg d'
  have hleR : ∀ q < d', tr.time q ≤ tr.time d' := fun _ hq => hrun.time_mono hq.le
  obtain ⟨-, A, ⟨hAt, l, hl, hlA⟩, hCA⟩ := AC.toFG_source_below_lock hrep.2.2
  have hU' := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hk0
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo hk0) (hnc.upTo _)).localRun
  have hst : (tr.upTo (tr.time d')).projAC.state v d' = tr.projAC.state v d' := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC v hleR
  have hck : (tr.upTo (tr.time d')).projAC.CallAt v d' ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hrep.1
  have hwf := AC.locksWF_stateU (hr := hr.toU) hrun.vstart hv' d'
  rw [hst] at hwf
  have hlab : healedLockFloor sp a ≤ l.slot := Healing.drain_live_locks (a := a) hwf hdt l hl
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  change healedLockFloor sp a ≤ l₀.slot at hlab
  have hl₀' : l₀ ∈ ((tr.upTo (tr.time d')).projAC.state v d').locks := by rw [hst]; exact hl₀
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hv' hck
  have hvB := AC.viableAncestor_anc hPhi hB₀
  obtain rfl : A = ell.frame.viableAncestor B₀ :=
    hr.coherent.1 (hPhiU hAt) (hPhiU hvB.1) hlA.symm
  obtain ⟨r', hrk, D, hsrc, hXD⟩ : ∃ r' < d', ∃ D,
      ((∃ CV, AC.FastLockAt tr.projAC v r' l₀.slot D CV) ∨
        AC.SlowLockAt tr.projAC v r' l₀.slot D) ∧
      Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B₀) D := by
    cases hlf : l₀.fast
    · obtain ⟨r', hrk, D, ⟨ellu, C', hu, hC', hD'⟩, L, hL, hLr, hLD⟩ :=
        AC.slow_lock_provenance hr hrun.vstart hv' d' l₀ hl₀' hlf
      rw [hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)] at hLD
      rw [RunTrace.upTo_projAC] at hu hC' hD'
      obtain ⟨hrt, hu⟩ := (AC.upTo_updateAt hrun.time_mono).1 hu
      have hs' : (tr.projAC.upTo (tr.time d')).state v r' = tr.projAC.state v r' :=
        Trace.upTo_state _ v fun _ hq => (hrun.time_mono hq.le).trans hrt
      rw [hs'] at hC' hD'
      rw [Trace.upTo_time] at hD'
      exact ⟨r', hrk, D, Or.inr ⟨ellu, C', hu, hC', hD'⟩,
        Anc.mono hU' ((hvB.2.mono hPhiU).trans hLD)⟩
    · obtain ⟨r', hrk, CV, ell', D, hcr, hfl, L, hL, hLr, hLD⟩ :=
        Healing.stored_fast_lock_provenance hr hrun.vstart hv' d' l₀ hl₀' hlf
      rw [hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)] at hLD
      have hrt : tr.time r' ≤ tr.time d' := hrun.time_mono hrk.le
      have hfl' := (fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl
      have hD' := Healing.ShadowLeft.fast_mem hfl hcr
      obtain ⟨hPhi', hPhiU'⟩ := AC.frameIn_of_callAt hr hv' hcr
      exact ⟨r', hrk, D, Or.inl ⟨CV, hfl'⟩,
        Anc.mono hU' ((hvB.2.mono hPhiU).trans
          (hLD.trans ((AC.viableAncestor_anc hPhi' hD').2.mono hPhiU')))⟩
  have hvr : v ∈ H (tr.time r') := hrun.antitone (hrun.time_mono hrk.le) hv'
  have hd0 := hrun.time_nonneg (d' + 1)
  have hle1 : ∀ q < d' + 1, tr.time q ≤ tr.time (d' + 1) := fun q hq => hrun.time_mono hq.le
  have hreach := (Compose.Growing.reachable_at' hrun hd0 hv hle1).reachableWith
  set st := (tr.state v (d' + 1)).fg with hst'
  have hCst : src ∈ st.tree := by
    rw [hfgeq]
    have h := (AC.toFG_source hrep.2.2).1.1
    rw [Goldilocks.Shadow.PU.Growing.frame_of_projAC_at' hrun hv' hrep.1,
      Node.frame'_eq, toFrame'_tree] at h
    exact h.1
  have hcut := ((Node.cutStep'_attest_some _ _ _ _ _ _).1
    (hrun.cutLaw v (d' + 1) _ hcall hv)).1
  obtain ⟨-, haT⟩ := Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, -, hETh⟩, -⟩ :=
    entry_state_of_source_with finalitySpec_updateFinality' hreach _ hCst
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  have hECU : Anc (tr.HonestBlocksAt H) E src :=
    hEC.mono (fun X hX => ⟨v, d' + 1, _, hd0, hle1, hv, hX⟩)
  have hED : Anc (tr.HonestBlocksAt H) E D :=
    hECU.trans
      ((Anc.mono hU' (hCA.mono hPhiU)).trans hXD)
  exact ⟨E, ⟨v, d' + 1, _, hd0, hle1, hv, hE⟩, hEr', r', by omega, l₀.slot, D, D,
    healedMemberBefore_iff.2
      (Or.inr (Or.inl ⟨hlab, v, r', by omega, hvr, (hrun.time_mono hrk.le).trans hdb', hsrc⟩)),
    hED, .refl, hvr, hsrc⟩

private theorem signed_row_covered {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g a b : Time} {v : Fin sp.n} {d : Nat}
    {att : FG.Att sp.n} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧
      CoveredUpTo tr H g a b (sp.slot (tr.time d)) E := by
  obtain ⟨E, hE, hEr, r, hrd, s, C, D, hC, hEC, -, hvr, hlock⟩ :=
    signed_row_lock_member hrun hnc hvz hs hh hsnap hc hdb
  exact ⟨E, hE, hEr, coveredUpTo_iff.2 ⟨hc, C, s, hC.healedOrigin,
    (lock_label hrun (Compose.Growing.lockWithin_iff.2 ⟨v, r, hvr, le_rfl, hlock⟩)).trans
      (AC.slot_mono sp (hrun.time_nonneg r) (hrun.time_mono hrd.le)), hEC⟩⟩

end Consensus.Goldilocks.Healing.Growing.ShadowLeft

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- Inside the deep quarantine a left high entry has a prior high origin above it. -/
theorem ResetPremisesUpTo'.left_entry_origin_of_quarantine_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q := by
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have h3 := hp.faults _ (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) htb)
    have hn := sp.toParams.hn
    have he : sp.n = sp.toParams.n := rfl
    change (H (max (cutZ sp.toParams g) t))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  have hU := Coherence.honest_blocks_coherent_at' hrun hnc
  obtain ⟨W, hW, att, ha, haT, haHz⟩ := ShadowLeft.honest_att_of_left
    (Compose.Growing.reachable_at' hrun ht hy hle) hq hET hEC hlt
  have haH := hrun.antitone (le_max_right _ _) haHz
  have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by
    rwa [Trace.upTo_state tr y hle]
  rcases Coherence.tree_accepted' (hrun.upTo ht).toLocalRun' hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.att_unforgeable y i att
    (hrun.antitone (hle i hik) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hle i hik) haH)
  have hdk : d < k := hdi.trans hik
  have hv := hrun.antitone (hle d hdk) haH
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.ShadowLeft.sign_entry
    (hrun.upTo (hrun.time_nonneg d)) hv hs'
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hE' hE'h
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  have heq : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
  rw [heq] at hE' hE'h
  have hσ := σ_eq_honest_at' hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
  obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
    ShadowLeft.high_row_source_at hrun hnc
      (hrun.antitone (max_le_max le_rfl (hle d hdk)) haHz) hs
      (by rw [← hE'h, hσ]; exact hEh) (hp.snapshot.imp fun _ h => h.1)
      (fun D hD => (hle d hdk).trans (htb.trans (hpre D hD)))
  have hOr := hrun.antitone (le_max_right _ _) ho.1
  have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
      fun q hq => hrun.time_mono hq.le, hOr, h⟩
  obtain rfl : E₀ = E := hU.1 (hsub₀ hE₀) (hsub hE) (hE₀r.trans haT)
  exact ⟨W, hW, att, ha, att.val, d, haH, hdk, hs, haT, r, hrd, l, O, ho,
    hE₀O.mono hsub₀⟩

/-- A left high entry has an earlier high origin, or is covered after the deep quarantine.
This is the stock left-entry contract over the shadow execution. -/
theorem ResetPremisesUpTo'.left_entry_origin_or_covered_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ((∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O) ∨
          (v ∈ H (max (cutZ sp.toParams g) t) ∧ CoveredUpTo tr H g a b (sp.slot t) E)) := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q := by
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have h3 := hp.faults _ (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) htb)
    have hn := sp.toParams.hn
    have he : sp.n = sp.toParams.n := rfl
    change (H (max (cutZ sp.toParams g) t))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  have hU := Coherence.honest_blocks_coherent_at' hrun hnc
  obtain ⟨W, hW, att, ha, haT, haHz⟩ := ShadowLeft.honest_att_of_left
    (Compose.Growing.reachable_at' hrun ht hy hle) hq hET hEC hlt
  have haH := hrun.antitone (le_max_right _ _) haHz
  have he := Trace.upTo_state tr y hle
  have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
  rcases Coherence.tree_accepted' (hrun.upTo ht).toLocalRun' hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.att_unforgeable y i att
    (hrun.antitone (hle i hik) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hle i hik) haH)
  have hdk : d < k := hdi.trans hik
  have hv := hrun.antitone (hle d hdk) haH
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.ShadowLeft.sign_entry
    (hrun.upTo (hrun.time_nonneg d)) hv hs'
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hE' hE'h
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  have heq : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
  rw [heq] at hE' hE'h
  have hσ := σ_eq_honest_at' hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
  have hh : HZ tr H g + 1 ≤ att.h := by rw [← hE'h, hσ]; exact hEh
  have hvz := hrun.antitone (max_le_max le_rfl (hle d hdk)) haHz
  have hsnap := hp.snapshot.imp fun _ h => h.1
  have hcases :
      (∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · refine Or.inl fun D' hD' => ?_
        cases hD'
        exact (hle d hdk).trans (htb.trans hb)
      · exact Or.inr hc
  refine ⟨W, hW, att, ha, att.val, d, haH, hdk, hs, haT, ?_⟩
  rcases hcases with hpre | hc
  · obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      ShadowLeft.high_row_source_at hrun hnc hvz hs hh hsnap hpre
    have hOr := hrun.antitone (le_max_right _ _) ho.1
    have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
        fun q hq => hrun.time_mono hq.le, hOr, h⟩
    obtain rfl : E₀ = E := hU.1 (hsub₀ hE₀) (hsub hE) (hE₀r.trans haT)
    exact Or.inl ⟨r, hrd, l, O, ho, hE₀O.mono hsub₀⟩
  · obtain ⟨E₀, hE₀, hE₀r, hcov⟩ :=
      ShadowLeft.signed_row_covered hrun hnc hvz hs hh hsnap hc ((hle d hdk).trans htb)
    obtain rfl : E₀ = E := hU.1 hE₀ (hsub hE) (hE₀r.trans haT)
    exact Or.inr ⟨haHz, hcov.mono (AC.slot_mono sp (hrun.time_nonneg d) (hle d hdk))⟩

end Consensus.Goldilocks.Healing.Growing

end
