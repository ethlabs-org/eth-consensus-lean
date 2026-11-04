module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Outcome
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: outcome service from actual reports

The report supplier is an explicit input; this module does not import its implementation.
A higher report is converted to an actual first justification before timeout, preserving the
previous-height finalization gate. Same-height reports supply the literal good-window rows.
-/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload)

section FG

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- A higher descendant before the timeout contains the first justification of the entry,
including the predecessor-finalization gate, not merely an arbitrary height crossing. -/
private theorem justification_before_timeout (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {T C : NodeBlock P ACP}
    (hT : T ∈ (tr.store y i).tree) (hentry : ((tr.store y i).σ T.root).Th = T.root)
    (hTC : (tr.store y i).Anc T C)
    (hheight : ((tr.store y i).σ T.root).h < ((tr.store y i).σ C.root).h)
    (hslot : C.slot < T.slot + P.δt) :
    ∃ X, Goldilocks.Store.JustifiesEntry P ACP (tr.store y i) T
        ((tr.store y i).σ T.root).h X ∧ (tr.store y i).Anc X C ∧
      (((tr.store y i).σ T.root).previousHeightJustified →
        ((tr.store y i).σ X.root).F = ((tr.store y i).σ T.root).J ∧
        ((tr.store y i).σ X.root).hF = ((tr.store y i).σ T.root).hj) := by
  let st := tr.store y i
  let ε := st.σ T.root
  have hreach := Goldilocks.Store.store_reachable hr hy i
  have hcoh := hr.coherent.mono (hr.tree_subset y hy i)
  obtain ⟨hTs, hPE⟩ := Goldilocks.Store.entry_facts hr hy hT hentry
  have walk : ∀ W, st.Anc T W → st.Anc W C →
      ((st.σ W.root).h = ε.h ∧ (st.σ W.root).Th = T.root ∧
        (st.σ W.root).ThSlot = T.slot ∧ (st.σ W.root).hj = ε.hj ∧
        (st.σ W.root).J = ε.J ∧
        (0 < ε.hj ∧ ε.hj + 1 = ε.h → (ε.hj, ε.J) ∈ (st.σ W.root).pending ∨
          (st.σ W.root).hF = ε.hj ∧ (st.σ W.root).F = ε.J)) ∧
        (∀ Y ∈ st.tree, st.Anc T Y → st.Anc Y W →
          (st.σ Y.root).h = ε.h ∧ (st.σ Y.root).Th = T.root) ∨
      ∃ X, Goldilocks.Store.JustifiesEntry P ACP st T ε.h X ∧ st.Anc X C ∧
        (ε.previousHeightJustified → (st.σ X.root).F = ε.J ∧ (st.σ X.root).hF = ε.hj) := by
    intro W hTW
    induction hTW with
    | refl =>
      refine fun _ => Or.inl ⟨⟨rfl, hentry, hTs, rfl, rfl, fun hb => Or.inl (hPE hb)⟩,
        fun Y _ hTY hYT => ?_⟩
      obtain rfl := hTY.antisymm hcoh hYT
      exact ⟨rfl, hentry⟩
    | @tail W' W hTW' hpW ih =>
      intro hWC
      obtain ⟨hW', hW, hpar⟩ := hpW
      rcases ih (Relation.ReflTransGen.head ⟨hW', hW, hpar⟩ hWC) with
        ⟨⟨hh, hTh, hu, hj, hJ, hP⟩, hkeep⟩ | hgoal
      swap
      · exact Or.inr hgoal
      obtain ⟨c, _, _, _, hc⟩ :=
        Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hreach W' hW'
      have hWs : W.slot < T.slot + P.fg.δt :=
        lt_of_le_of_lt (hWC.slot_le hcoh).1 hslot
      have hkeep' : ∀ Y ∈ st.tree, st.Anc T Y → st.Anc Y W → Y ≠ W →
          (st.σ Y.root).h = ε.h ∧ (st.σ Y.root).Th = T.root := by
        intro Y hY hTY hYW hne
        rcases Relation.ReflTransGen.cases_tail hYW with he | ⟨Z, hYZ, hZ, _, hZpar⟩
        · exact False.elim (hne he.symm)
        · have he : Z = W' := hcoh.1 hZ hW' (Option.some.inj (hZpar.symm.trans hpar))
          subst Z
          exact hkeep Y hY hTY hYZ
      rcases (Goldilocks.Store.step_current hc (Goldilocks.Store.step_σ hr hy hW hpar)
          hh hTh hu hj hJ hP).1 hWs with
        hcur | ⟨_, _, hj', hJ', _, hfin⟩
      · refine Or.inl ⟨hcur, fun Y hY hTY hYW => ?_⟩
        by_cases he : Y = W
        · subst Y
          exact ⟨hcur.1, hcur.2.1⟩
        · exact hkeep' Y hY hTY hYW he
      · exact Or.inr ⟨W, ⟨hW, hTW'.tail ⟨hW', hW, hpar⟩, hj', hJ', hkeep'⟩,
          hWC, hfin⟩
  rcases walk C hTC .refl with ⟨⟨hh, _⟩, _⟩ | h
  · exact False.elim (Nat.lt_irrefl _ (hh ▸ hheight))
  · exact h

/-- A pre-timeout higher descendant certifies an actual earlier acceptance of the first
justifying block. The conclusion is read at that acceptance, not at a later replay. -/
theorem accepted_justification_before_timeout (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {T C : NodeBlock P ACP}
    (hT : T ∈ (tr.store y i).tree) (hentry : ((tr.store y i).σ T.root).Th = T.root)
    (hpos : 0 < T.slot) (hTC : (tr.store y i).Anc T C)
    (hheight : ((tr.store y i).σ T.root).h < ((tr.store y i).σ C.root).h)
    (hslot : C.slot < T.slot + P.δt) :
    ∃ k < i, ∃ X, tr.AcceptAt y k X ∧
      Goldilocks.Store.JustifiesEntry P ACP (tr.store y (k + 1)) T
        ((tr.store y i).σ T.root).h X ∧ (tr.store y i).Anc X C ∧
      (((tr.store y i).σ T.root).previousHeightJustified →
        ((tr.store y (k + 1)).σ X.root).F = ((tr.store y i).σ T.root).J ∧
        ((tr.store y (k + 1)).σ X.root).hF = ((tr.store y i).σ T.root).hj) := by
  obtain ⟨X, hX, hXC, hgate⟩ := justification_before_timeout hr hy hT hentry hTC hheight hslot
  have hcoh := hr.coherent.mono (hr.tree_subset y hy i)
  have hXng : X ≠ P.genesisBlock acp₀ := by
    intro he
    have hs := (hX.2.1.slot_le hcoh).1
    rw [he] at hs
    change T.slot ≤ 0 at hs
    omega
  obtain ⟨k, hki, hk⟩ := (Goldilocks.Store.tree_accepted hr hy hX.1).resolve_left hXng
  have hXp : X ∈ (tr.store y (k + 1)).tree := by
    rw [(Goldilocks.Store.tree_grows _ _ _ _ (Goldilocks.Store.store_reachable hr hy k)).1 X _
      (Goldilocks.Store.accept_onBlock hr hy hk)]
    exact Set.mem_insert _ _
  have hmono : ∀ {Z}, Z ∈ (tr.store y (k + 1)).tree →
      Z ∈ (tr.store y i).tree ∧ (tr.store y (k + 1)).σ Z.root = (tr.store y i).σ Z.root := by
    intro Z hZ
    obtain ⟨hm, he⟩ := Goldilocks.Store.held_mono hr hy (Nat.succ_le_iff.mpr hki) hZ
    exact ⟨hm, he.symm⟩
  have hTX := Goldilocks.Store.anc_of_U hr hy (hX.2.1.mono (hr.tree_subset y hy i)) hXp
  have hXe := (hmono hXp).2
  refine ⟨k, hki, X, hk, ⟨hXp, hTX, ?_, ?_, ?_⟩, hXC, ?_⟩
  · rw [hXe]; exact hX.2.2.1
  · rw [hXe]; exact hX.2.2.2.1
  · intro Y hY hTY hYX hne
    have hYold := (hmono hY).1
    have hsub : (tr.store y (k + 1)).tree ⊆ (tr.store y i).tree := fun _ h => (hmono h).1
    have hkeep := hX.2.2.2.2 Y hYold (hTY.mono hsub) (hYX.mono hsub) hne
    rw [(hmono hY).2]
    exact hkeep
  · rw [hXe]; exact hgate

end FG

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- A carrier below a high origin is accepted everywhere before the deadline. If the
receiver's finalized block has already passed the carrier, ancestor closure supplies its
earlier acceptance; otherwise the ordinary acceptance relay applies. -/
theorem carrier_below_origin_before (hp : ResetPremises tr H proposer dg g ΔF a)
    (hnr : NoRestartAfter tr H (SA.gbar g)) (hc : CatchRun tr H g (2 * sp.Δ))
    {x z : Fin sp.n} {io jo k : Nat} {O X : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x io jo O) (hz : z ∈ H) (hacc : tr.AcceptAt z k X)
    (hXO : Anc (tr.HonestBlocks H) X O)
    (hng : X ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
    {w : Time} (hmature : sp.ts (jo + 1 : Nat) ≤ w)
    (hcatch : SA.gbar g + 2 * sp.Δ ≤ w) (hdeadline : tr.time k + sp.Δ ≤ w) :
    ∀ y ∈ H, ∃ j, tr.AcceptAt y j X ∧ tr.time j < w := by
  intro y hy
  have hΔ := sp.toParams.hΔ
  obtain ⟨q, _, hq⟩ := hp.run.awake_in_horizon y hy w
    (hp.healthy.2.1 y hy w (by change SA.gbar g ≤ w; linarith))
  obtain ⟨i, hi, _⟩ := exists_firstCutFrom_le (tr := tr) (show w ≤ tr.time q by linarith)
  have hcomp := (vote_state_caches hp i (fun r _ => retention_inv hp r) ho hy
    (hmature.trans hi.1)).1
  have hheld : X ∈ (tr.state y i).fg.tree := by
    rcases hcomp with hFO | hOF
    · rcases SA.anc_total (honest_coherent hp) hFO hXO with hFX | hXF
      · exact relay_held hp.run.toLocalRun hp.healthy hnr hc hz hy hacc hcatch hdeadline hi hFX
      · exact mem_tree_of_anc hp hy hXF
          (Goldilocks.Store.cache_invariants _ _ _ _
            (Compose.fg_reachable hp.run.toLocalRun hy i)).1
    · exact mem_tree_of_anc hp hy (hXO.trans hOF)
        (Goldilocks.Store.cache_invariants _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hy i)).1
  obtain ⟨j, hji, hj⟩ := (Compose.tree_cases hp.run.toLocalRun hy hheld).resolve_left hng
  exact ⟨j, hj, hi.2 j hji⟩

/-- A higher actual report by the inclusive `6Δ` deadline gives the exact early-outcome
alternative, including strict carrier acceptance everywhere. No lower report time is needed. -/
theorem higher_report_early_outcome (hp : ResetPremises tr H proposer dg g ΔF a)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ))
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {m r cF kF : Nat}
    {T C : SA.Blk sp.n (List (FG.Att sp.n))} {ell : ACLabel (goldilocksNode sp ro)}
    (hT : T ∈ (tr.state y m).fg.tree) (he : ((tr.state y m).fg.σ T.root).Th = T.root)
    (hpos : 0 < T.slot) (hhigh : HZ tr H g + 1 ≤ ((tr.state y m).fg.σ T.root).h)
    (hg : SA.gbar g + 2 * sp.Δ ≤ sp.ts T.slot)
    (hcf : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time))
    (hrep : SA.ToFGAt tr.projAC z r ell C)
    (hrt : tr.time r ≤ sp.ts T.slot + 6 * sp.Δ)
    (hTC : Anc (tr.HonestBlocks H) T C)
    (hh : ((tr.state z r).fg.σ T.root).h < ((tr.state z r).fg.σ C.root).h) :
    Compose.EarlyOutcome tr H T ((tr.state y m).fg.σ T.root).h
      (decide ((tr.state y m).fg.σ T.root).previousHeightJustified)
      ((tr.state y m).fg.σ T.root).J (sp.ts (T.slot + cF + kF + 1 : Nat)) := by
  classical
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hΔF : (0 : Int) < ΔF := hp.healthy.1.1
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hCr : C ∈ ell.frame.tree := by
    have hh := hrep.2.2
    unfold SA.acToFG at hh
    split_ifs at hh
    split at hh
    · cases hh
    · rename_i C' hC'
      split_ifs at hh
      cases hh
      exact (SA.deepest_mem hC').1.1.1
  have hC := frame_tree_subset hp hz hrep.1 hCr
  have hTr := mem_tree_of_anc hp hz hTC hC
  have hσ := σ_eq_run hp hz hy hTr hT
  have hCt : sp.ts C.slot ≤ tr.time r := (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) _).2
    (by exact_mod_cast SA.frame_slot_le sp hr hz hrep.1 C hCr)
  have hslot : C.slot < T.slot + sp.toParams.δt := by
    have hlt : sp.ts C.slot < sp.ts (T.slot + sp.toParams.δt : Nat) := by
      simp only [SAParams.ts] at hCt hrt ⊢
      push_cast
      nlinarith [hs.timeoutDelay]
    exact_mod_cast (SA.ts_lt_iff sp).1 hlt
  have hfg : FGLocalRun (goldilocksNode sp ro).genesisPayload H
      (tr.HonestBlocks H) tr.projFG :=
    Compose.fg_projection _ _ dg H _ tr proposer
      ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
        (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
        SA.proposal_payload_valid sp _ ro⟩ hs.genesisRoot hp.run.toLocalRun hp.noColl
  have hstore : ∀ j, tr.projFG.store z j = (tr.state z j).fg := fun j =>
    congrArg Prod.fst (Compose.projFG_state hp.run.toLocalRun hz j)
  obtain ⟨k, hkr, X, hk, hj, hXC, hgate⟩ := accepted_justification_before_timeout hfg hz
    (by rw [hstore]; exact hTr) (by rw [hstore, hσ]; exact he) hpos
    (by rw [hstore]; exact anc_tree_of_anc hp hz hTC hC)
    (by rw [hstore]; exact hh) hslot
  have hacc := Compose.projFG_callAt.1 hk
  simp only [hstore, tr.state_succ_of_call hacc, hσ] at hj hgate
  rw [hstore] at hXC
  have hXU : Anc (tr.HonestBlocks H) X C := hXC.mono fun B hB => ⟨z, hz, r, hB⟩
  have hng : X ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
    intro hX
    have hTX' := hj.2.1.slot_le
      ((honest_coherent hp).mono (fun B hB => (⟨z, hz, k + 1,
        by rwa [tr.state_succ_of_call hacc]⟩ : B ∈ tr.HonestBlocks H)))
    have heq : X.slot = 0 := by rw [hX]; rfl
    omega
  have hbefore : sp.ts T.slot + 6 * sp.Δ < sp.ts (T.slot + cF + kF + 1 : Nat) := by
    simp only [SAParams.ts]
    push_cast
    nlinarith [Nat.cast_nonneg (α := Int) kF]
  have hXt := (hp.run.time_mono hkr.le).trans hrt
  obtain ⟨io, hior, jo, O, ho, hCO⟩ := high_report_origin hp hz hrep
    (by rw [← hσ] at hhigh; omega)
  have hio : sp.ts jo ≤ tr.time io := by
    obtain ⟨CV, ell, D, _, hfl, _⟩ := ho.2.2.1
    rcases hfl with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
    · change tr.time io = sp.ts jo + 6 * sp.Δ at ht
      linarith
    · exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg io) _).2 (by
        change sp.slot (tr.time io) = jo at hsl
        omega)
  have hio' := hio.trans ((hp.run.time_mono hior.le).trans hrt)
  refine ⟨z, hz, k, X, hacc, hXt.trans_lt hbefore, hj, ?_, ?_⟩
  · intro hb
    have hb' := of_decide_eq_true hb
    obtain ⟨hF, hhF⟩ := hgate hb'
    exact ⟨by rw [hhF]; exact hb'.2, hF⟩
  · apply carrier_below_origin_before hp hs.noRestart hc ho hz hacc (hXU.trans hCO) hng
    · simp only [SAParams.ts] at hio' ⊢
      push_cast at *
      nlinarith [Nat.cast_nonneg (α := Int) kF]
    · linarith
    · linarith

/-- The post-drain entry starts after the reset and the GST service margin. -/
theorem drain_margins (hp : ResetPremises tr H proposer dg g ΔF a) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    0 < u ∧ a ≤ sp.ts u ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts u := by
  have hΔ := sp.toParams.hΔ
  have hcut := lt_cutZ sp g
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have ha0 : 0 ≤ a := by linarith [SA.gbar_nonneg g]
  have ha : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  rw [drainTime_eq] at hR
  have hu := (SA.ts_le_iff sp).1 hR
  have hau : a ≤ sp.ts u := ha.le.trans ((SA.ts_le_iff sp).2 (by push_cast at hu; omega))
  exact ⟨by push_cast at hu; omega, hau, by linarith⟩

/-- The supplier's actual reports yield either an identity quorum of exact entry rows
signed by `t_u + 6Δ`, or the full early outcome with its strict carrier deadline. -/
theorem rows_or_early_outcome (supply : ReadyProposalReportSupply tr H proposer dg g ΔF a)
    (hp : ResetPremises tr H proposer dg g ΔF a) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p y : Fin sp.n} {k u m cF kF : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u T) (hR : drainTime sp a ≤ sp.ts u)
    (hy : y ∈ H) (hT : T ∈ (tr.state y m).fg.tree)
    (he : ((tr.state y m).fg.σ T.root).Th = T.root)
    (hhigh : HZ tr H g + 1 ≤ ((tr.state y m).fg.σ T.root).h)
    (hhj : ((tr.state y m).fg.σ T.root).previousHeightJustified →
      HZ tr H g + 1 ≤ ((tr.state y m).fg.σ T.root).hj)
    (hcf : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) :
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
        att.h = ((tr.state y m).fg.σ T.root).h ∧ att.T = T.root ∧ att.timeout = false ∧
        tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
        (((tr.state y m).fg.σ T.root).previousHeightJustified →
          att.fin = some (((tr.state y m).fg.σ T.root).hj, ((tr.state y m).fg.σ T.root).J))) ∨
      Compose.EarlyOutcome tr H T ((tr.state y m).fg.σ T.root).h
        (decide ((tr.state y m).fg.σ T.root).previousHeightJustified)
        ((tr.state y m).fg.σ T.root).J (sp.ts (u + cF + kF + 1 : Nat)) := by
  classical
  have hslot := hP.2.2.2.2.1
  obtain ⟨hu, hau, hgu⟩ := drain_margins hp hR
  have hΔ := sp.toParams.hΔ
  have hp' := hp.toUpTo tr H (show a ≤ sp.ts u + 6 * sp.Δ by linarith)
  by_cases hearly : Compose.EarlyOutcome tr H T ((tr.state y m).fg.σ T.root).h
      (decide ((tr.state y m).fg.σ T.root).previousHeightJustified)
      ((tr.state y m).fg.σ T.root).J (sp.ts (u + cF + kF + 1 : Nat))
  · exact Or.inr hearly
  have nohigher : ∀ z ∈ H, ∀ r ell C, SA.ToFGAt tr.projAC z r ell C →
      tr.time r ≤ sp.ts u + 6 * sp.Δ → Anc (tr.HonestBlocks H) T C →
      ¬ ((tr.state z r).fg.σ T.root).h < ((tr.state z r).fg.σ C.root).h := by
    intro z hz r ell C hr ht hTC hh
    apply hearly
    have ho := higher_report_early_outcome hp hs hc hy hz hT he
      (by rw [hslot]; exact hu) hhigh (by rw [hslot]; linarith) hcf hr
      (by rwa [hslot]) hTC hh (kF := kF)
    simpa only [hslot] using ho
  rcases supply.report_cover hp hc p k u T hP hR with hreports | ⟨z, hz, r, ell, C, hr, ht, hTC, hh⟩
  · left
    apply hp'.row_signers_of_reports hy hT rfl he hhigh hhj le_rfl
    intro z hz
    obtain ⟨r, ell, C, hr, ht, hTC⟩ := hreports z hz
    have hCr : C ∈ (tr.state z r).fg.tree := by
      have ht' := hr.2.2
      unfold SA.acToFG at ht'
      split_ifs at ht'
      split at ht'
      · cases ht'
      · rename_i C' hC'
        split_ifs at ht'
        cases ht'
        exact frame_tree_subset hp hz hr.1 (SA.deepest_mem hC').1.1.1
    have hσ := σ_eq_run hp hz hy (mem_tree_of_anc hp hz hTC hCr) hT
    have hle := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (anc_tree_of_anc hp hz hTC hCr)
    have hn := nohigher z hz r ell C hr ht hTC
    refine ⟨r, ell, C, hr, ht, hTC, ?_⟩
    rw [← hσ]
    omega
  · exact False.elim (nohigher z hz r ell C hr ht hTC hh)

/-- Exact C1.2 from the shared actual-report supplier. The public service statement is
unchanged; this module does not import the operational implementation of the supplier. -/
theorem outcome_service_of_reports
    (supply : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a : Time),
      ReadyProposalReportSupply tr H proposer dg g ΔF a) : Compose.OutcomeService := by
  intro sp ro proposer dg H tr g ΔF a cF kF hrun hs hc hcf hto hreset
    p k i T u hP hentry hR hhigh hhj hretained
  classical
  have hp : ResetPremises tr H proposer dg g ΔF a := ⟨hrun, hs.healthy, hs.noColl, hreset⟩
  have hslot := hP.2.2.2.2.1
  subst u
  rw [← drainTime_eq] at hR
  have hpost := tr.state_succ_of_call hentry.2.1
  have hT : T ∈ (tr.state p (i + 1)).fg.tree := by
    rw [hpost, (Store.tree_grows _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hentry.1 i)).1
      T _ (hrun.toLocalRun.cutLaw p hentry.1 _ _ hentry.2.1).2.1]
    exact Set.mem_insert _ _
  have he : ((tr.state p (i + 1)).fg.σ T.root).Th = T.root := by
    rw [hpost]; exact hentry.2.2
  have hhT : HZ tr H g + 1 ≤ ((tr.state p (i + 1)).fg.σ T.root).h := by
    rwa [hpost]
  have hhJ : ((tr.state p (i + 1)).fg.σ T.root).previousHeightJustified →
      HZ tr H g + 1 ≤ ((tr.state p (i + 1)).fg.σ T.root).hj := by
    rw [hpost]
    exact fun h => hhj h.1 h.2
  obtain ⟨hu, _, hgu⟩ := drain_margins hp hR
  have hΔ := sp.toParams.hΔ
  rcases rows_or_early_outcome (supply sp ro tr H proposer dg g ΔF a) hp hs hc hP hR
      hentry.1 hT he hhT hhJ hcf (kF := kF) with ⟨ids, hq, hrows⟩ | hearly
  swap
  · rw [hpost] at hearly
    refine ⟨Or.inr hearly, fun _ => ?_⟩
    obtain ⟨y, hy, j, X, hacc, ht, hj, _, _⟩ := hearly
    exact ⟨y, hy, j, X, hacc, ht, hj⟩
  obtain ⟨w, kw, W, hW, hlo, hhi, Pr, hpar, hTPr⟩ := hretained
  obtain ⟨R, hwin⟩ := good_window_of_rows hp hs hentry.1 hW.1 hT he hW.2.2.2.1
    hpar hTPr hlo hhi (by linarith) hcf hto ids hq hrows
  have hWtime : tr.time kw = sp.ts W.slot := by
    rw [hW.2.2.2.1.2.2, sp.slotTime_eq]; rfl
  have hbefore : sp.ts W.slot < sp.ts (T.slot + cF + kF + 1 : Nat) :=
    (SA.ts_lt_iff sp).2 (by exact_mod_cast (show W.slot < T.slot + cF + kF + 1 by omega))
  have hTW : sp.ts T.slot ≤ sp.ts W.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast
    (show T.slot ≤ W.slot by omega))
  have hcarrier := ready_proposal_accepted_everywhere hp hs hc hW (hR.trans hTW)
    (by omega) (hgu.trans hTW)
  refine ⟨Or.inl ⟨w, kw, W, Pr, R, hWtime.trans_lt hbefore, hwin, ?_⟩, fun _ => ?_⟩
  · intro z hz
    obtain ⟨j, hj, ht⟩ := hcarrier z hz
    exact ⟨j, hj, by linarith⟩
  · have hfg : FGLocalRun (goldilocksNode sp ro).genesisPayload H
        (tr.HonestBlocks H) tr.projFG :=
      Compose.fg_projection _ _ dg H _ tr proposer
        ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
          (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
          SA.proposal_payload_valid sp _ ro⟩ hs.genesisRoot hrun.toLocalRun hs.noColl
    obtain ⟨X, hj, _, _, _, _, _⟩ := Store.window_justifies hfg hwin
    have hng : X ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
      intro heq
      have ht := hj.2.1.slot_le (hfg.coherent.mono (hfg.tree_subset w hW.1 (kw + 1)))
      have hz : X.slot = 0 := by rw [heq]; rfl
      omega
    obtain ⟨j, hjkw, hjX⟩ := (Store.tree_accepted hfg hW.1 hj.1).resolve_left hng
    have hacc := Compose.projFG_callAt.1 hjX
    have hXp : X ∈ (tr.projFG.store w (j + 1)).tree := by
      rw [(Store.tree_grows _ _ _ _ (Store.store_reachable hfg hW.1 j)).1 X _
        (Store.accept_onBlock hfg hW.1 hjX)]
      exact Set.mem_insert _ _
    have hmono : ∀ {B}, B ∈ (tr.projFG.store w (j + 1)).tree →
        B ∈ (tr.projFG.store w (kw + 1)).tree ∧
        (tr.projFG.store w (j + 1)).σ B.root = (tr.projFG.store w (kw + 1)).σ B.root := by
      intro B hB
      obtain ⟨hm, he⟩ := Store.held_mono hfg hW.1 (by omega : j + 1 ≤ kw + 1) hB
      exact ⟨hm, he.symm⟩
    have hjust : Store.JustifiesEntry sp.toParams (Payload sp.n)
        (tr.projFG.store w (j + 1)) T ((tr.projFG.store w kw).σ T.root).h X := by
      refine ⟨hXp, Store.anc_of_U hfg hW.1
        (hj.2.1.mono (hfg.tree_subset w hW.1 (kw + 1))) hXp, ?_, ?_, ?_⟩
      · rw [(hmono hXp).2]; exact hj.2.2.1
      · rw [(hmono hXp).2]; exact hj.2.2.2.1
      · intro Y hY hTY hYX hne
        have hsub : (tr.projFG.store w (j + 1)).tree ⊆
            (tr.projFG.store w (kw + 1)).tree := fun _ h => (hmono h).1
        rw [(hmono hY).2]
        exact hj.2.2.2.2 Y (hmono hY).1 (hTY.mono hsub) (hYX.mono hsub) hne
    have hstore : ∀ q, tr.projFG.store w q = (tr.state w q).fg := fun q =>
      congrArg Prod.fst (Compose.projFG_state hrun.toLocalRun hW.1 q)
    have hTw : T ∈ (tr.state w kw).fg.tree := by
      rw [← hstore]; exact hwin.entry.1
    have hσ := σ_eq_run hp hW.1 hentry.1 hTw hT
    simp only [hstore, tr.state_succ_of_call hacc, hσ, hpost] at hjust
    refine ⟨w, hW.1, j, X, hacc, ?_, hjust⟩
    exact lt_of_le_of_lt ((hrun.time_mono (Nat.lt_succ_iff.mp hjkw)).trans hWtime.le) hbefore

end Consensus.Goldilocks.Healing.Recovery

end
