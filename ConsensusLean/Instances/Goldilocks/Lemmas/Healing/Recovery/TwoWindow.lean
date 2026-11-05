module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Outcome
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: two-window finalization (C1.3)

`two_window_finalization`: a high post-drain ready proposal `U` of the stretch that is an actual
run entry (`σ[U].h ≥ H_z + 2`) is finalized by an honest acceptance before `t_{v+M}`.

* C1.2 (`Compose.OutcomeService`, taken as a hypothesis) at `U`, with the stretch's retained
  inclusion, gives a good window (`Store.window_justifies` names the justifying block) or an
  accepted early justification. Either way some honest store holds a block `V` that justifies `U`
  with `σ[V].J = U`, `σ[V].h_j = σ[U].h` and every block strictly between kept `U`'s height; so
  `V` is the first crossing above `U`, the actual successor entry, of a slot in
  `(U.slot, U.slot + c_F + k_F]`.
* `V` is then the stretch's ready proposal of its slot (one honest block per honest proposal
  slot), accepted by its proposer, and an entry whose previous height is justified. C1.2 at `V`
  gives a good window, whose justifying block finalizes `σ[V].J = U` (`window_justifies`), or an
  early justification that does (the gate). That block is accepted by an honest node before
  `t_{V.slot + c_F + k_F + 1} ≤ t_{v+M}`, and after `t_{U.slot} ≥ R_z ≥ g`.

Replay states are transported between honest stores explicitly (`σ_eq_honest`). -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- The first crossing above `A` on a held `A ⪯ B` (as `Store.first_crossing_of_anc` in
`Obligations/WindowAnchors`, structural part, local to avoid a Healing-to-Obligations edge). -/
theorem first_crossing {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A B : NodeBlock P ACP}
    (hAB : st.Anc A B) (hh : (st.σ A.root).h < (st.σ B.root).h) :
    ∃ X ∈ st.tree, st.Anc A X ∧ st.Anc X B ∧ (st.σ X.root).h = (st.σ A.root).h + 1 ∧
      (st.σ X.root).Th = X.root := by
  suffices key : (st.σ A.root).h ≤ (st.σ B.root).h ∧ ((st.σ A.root).h < (st.σ B.root).h →
      ∃ X ∈ st.tree, st.Anc A X ∧ st.Anc X B ∧ (st.σ X.root).h = (st.σ A.root).h + 1 ∧
        (st.σ X.root).Th = X.root) from key.2 hh
  clear hh
  induction hAB with
  | refl => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  | @tail W W' hAW hWW' ih =>
    obtain ⟨hle, ih⟩ := ih
    obtain ⟨hW, hW', hp⟩ := hWW'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hW' hp
    have hst : st.Anc W W' := .single ⟨hW, hW', hp⟩
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, -, -⟩ | ⟨e, -, eT⟩
    · refine ⟨e ▸ hle, fun hlt => ?_⟩
      obtain ⟨X, hX, hAX, hXW, h1, h2⟩ := ih (e ▸ hlt)
      exact ⟨X, hX, hAX, hXW.trans hst, h1, h2⟩
    · refine ⟨by omega, fun hlt => ?_⟩
      rcases Nat.lt_or_ge (st.σ A.root).h (st.σ W.root).h with hl | hl
      · obtain ⟨X, hX, hAX, hXW, h1, h2⟩ := ih hl
        exact ⟨X, hX, hAX, hXW.trans hst, h1, h2⟩
      · exact ⟨W', hW', hAW.trans hst, Relation.ReflTransGen.refl, by omega, eT⟩

/-- **A block that justifies an entry is the next entry**: one height higher and its own
entry (it is the first crossing above the entry block, since every block strictly between keeps
the entry's height). -/
private theorem justifier_entry {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {T X : NodeBlock P ACP}
    (hJ : Store.JustifiesEntry P ACP st T (st.σ T.root).h X) :
    (st.σ X.root).h = (st.σ T.root).h + 1 ∧ (st.σ X.root).Th = X.root := by
  obtain ⟨hX, hTX, hhj, -, hmid⟩ := hJ
  have hlt : (st.σ T.root).h < (st.σ X.root).h := hhj ▸ Healing.Store.hj_lt_h hr hX
  obtain ⟨V, hV, hTV, hVX, hVh, hVTh⟩ := first_crossing hr hTX hlt
  by_cases hVX' : V = X
  · subst hVX'
    exact ⟨hVh, hVTh⟩
  · have := (hmid V hV hTV hVX hVX').1
    omega

/-- **Two-window finalization.** -/
theorem two_window_finalization {Gp : Time} {W M cF kF v : Nat} {q : Fin sp.n} {kU iU : Nat}
    {U : SA.Blk sp.n (List (FG.Att sp.n))}
    (houtcome : Compose.OutcomeService)
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (hpat : PatternPremises tr H proposer dg g ΔF Gp W M cF kF)
    (hwindow : ∀ u, v ≤ u → u < v + M →
      ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer (proposer u) k u B ∧
        ∀ y i, Compose.RunEntry tr H y i B →
          ∃ (w : Fin sp.n) (kw : Nat) (Q : SA.Blk sp.n (List (FG.Att sp.n))),
            ReadyProposal tr H proposer w kw Q.slot Q ∧
            u + cF ≤ Q.slot ∧ Q.slot ≤ u + cF + kF ∧
            ∃ Pr, Q.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) B Pr)
    (hU : ReadyProposal tr H proposer q kU U.slot U)
    (hentry : Compose.RunEntry tr H q iU U)
    (hhigh : HZ tr H g + 2 ≤ ((tr.post iU).fg.σ U.root).h)
    (hvU : v ≤ U.slot) (hR : drainTime sp a ≤ sp.ts U.slot)
    (hroom : U.slot + 2 * (cF + kF) + 1 ≤ v + M) :
    ∃ x ∈ H, ∃ kX X, tr.AcceptAt x kX X ∧ g ≤ tr.time kX ∧
      tr.time kX < sp.ts (v + M : Nat) ∧
      ∃ Fx ∈ (tr.post kX).fg.tree,
        Fx.root = ((tr.post kX).fg.σ X.root).F ∧ Anc (tr.HonestBlocks H) U Fx := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hcoh := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hfg := (fg_run_of_hs hrun hpat.shared).1
  have hreach (y : Fin sp.n) (hy : y ∈ H) (c : Nat) :=
    Compose.fg_reachable hrun.toLocalRun hy c
  have hsub (y : Fin sp.n) (hy : y ∈ H) (c : Nat) :
      (tr.state y c).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, c, hX⟩
  have hts {m n : Nat} (h : m ≤ n) : sp.ts m ≤ sp.ts n :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  -- a cut before `t_{n+1}` has slot `≤ n`; a block accepted at it has slot `≤ n`
  have hslot_lt {k n : Nat} (hk : tr.time k < sp.ts (n + 1 : Nat)) : sp.slot (tr.time k) ≤ n := by
    by_contra hc
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) ((n + 1 : Nat) : Int)).2
      (by push_cast; omega)
    linarith
  -- `g ≤ R_z ≤ t_{U.slot}`
  have hgU : g ≤ sp.ts U.slot := by
    have h1 := cutZ_lt_reset hrun hp.healthy hp.reset
    have h2 := lt_cutZ sp g
    have h0 := le_gbar g
    have hΔ := sp.toParams.hΔ
    have h3 : a < sp.ts (sp.slot a + 1 : Nat) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp (by linarith [gbar_nonneg g]) _).1 h
      push_cast at this
      omega
    have h4 := hts (show sp.slot a + 1 ≤ sp.slot a + 2 * sp.k + 5 by omega)
    rw [drainTime_eq] at hR
    linarith
  -- `U` at its acceptance
  obtain ⟨hqH, hUacc, hUTh⟩ := id hentry
  have hpostU : tr.post iU = tr.state q (iU + 1) := (tr.state_succ_of_call hUacc).symm
  have hUm : U ∈ (tr.state q (iU + 1)).fg.tree := Healing.accept_mem' hrun hqH hUacc
  rw [hpostU] at hhigh
  set h := ((tr.state q (iU + 1)).fg.σ U.root).h with hh
  have hUσ : ∀ {y} (_ : y ∈ H) {c}, U ∈ (tr.state y c).fg.tree →
      (tr.state y c).fg.σ U.root = (tr.state q (iU + 1)).fg.σ U.root :=
    fun hy _ hUy => σ_eq_honest hrun hnc hy hqH hUy hUm
  -- the stretch's retained inclusion at `U`
  obtain ⟨kB, B, hBr, hBret⟩ := hwindow U.slot hvU (by omega)
  obtain ⟨hpbH, -, -, hBprop, hBs, -⟩ := id hBr
  obtain rfl : U = B := Compose.eq_of_slot hrun hpbH hBprop (hsub q hqH _ hUm) hBs.symm
  have hdrainU : sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) ≤ sp.ts U.slot := by
    rw [← drainTime_eq]; exact hR
  -- **first outcome, at `U`**: an honest store holds the block `V` justifying `U`
  have o1 := (houtcome sp ro proposer dg H tr g ΔF a cF kF hrun hpat.shared
    hpat.catchPremise hpat.cF_upper hpat.timeout hp.reset q kU iU U
    U.slot hU hentry hdrainU (by rw [hpostU]; omega) (fun _ h1 => by rw [hpostU] at h1 ⊢; omega)
    (hBret q iU hentry)).1
  have hA : ∃ y ∈ H, ∃ c V,
      Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.state y c).fg U h V ∧
      V.slot ≤ U.slot + cF + kF := by
    rcases o1 with ⟨q', j, Bs, Pr, R, -, hgw, -⟩ | ⟨y, hy, k, V, hacc, hkt, hJ, -, -⟩
    · have hq' := hgw.proposal.1
      obtain ⟨V, hJ, hVBs, -⟩ := Store.window_justifies hfg hgw
      have hUq' := hgw.entry.1
      simp only [projFG_store_eq hrun hq'] at hJ hVBs hUq'
      rw [hUσ hq' hUq'] at hJ
      refine ⟨q', hq', j + 1, V, hJ, ?_⟩
      have := (Anc.slot_le hcoh (hVBs.mono (hsub q' hq' _))).1
      have := hgw.window.2
      omega
    · rw [hpostU, ← tr.state_succ_of_call hacc] at hJ
      exact ⟨y, hy, k + 1, V, hJ, ((hrun.cutLaw y hy k _ hacc).1).trans (hslot_lt hkt)⟩
  -- `V` is the actual successor entry: one height higher, its own entry, justifying `U`
  obtain ⟨y, hy, c, V, hJV, hVs⟩ := hA
  obtain ⟨hVm, hUV, hVhj, hVJ, -⟩ := id hJV
  have hUy : U ∈ (tr.state y c).fg.tree :=
    mem_of_honest_anc hrun hnc hy (hUV.mono (hsub y hy c)) hVm
  have hJV' : Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.state y c).fg U
      ((tr.state y c).fg.σ U.root).h V := by
    rw [hUσ hy hUy]; exact hJV
  obtain ⟨hVh, hVTh⟩ := justifier_entry (hreach y hy c) hJV'
  have hUVs : U.slot < V.slot :=
    (Anc.slot_le hcoh (hUV.mono (hsub y hy c))).2 fun e => by rw [e] at hVh; omega
  rw [hUσ hy hUy] at hVh
  -- `V` is the stretch's ready proposal of its slot, accepted by its proposer
  obtain ⟨kV, B', hB'r, hB'ret⟩ := hwindow V.slot (by omega) (by omega)
  obtain ⟨hpvH, -, -, hB'prop, hB's, -⟩ := id hB'r
  obtain rfl : V = B' := Compose.eq_of_slot hrun hpvH hB'prop (hsub y hy c hVm) hB's.symm
  obtain ⟨hVacc, hVm', hpostV⟩ := accept_of_proposesAt hrun hnc hpvH hB'prop
  have hVσ := σ_eq_honest hrun hnc hpvH hy hVm' hVm
  have hVent : Compose.RunEntry tr H (proposer V.slot) kV V :=
    ⟨hpvH, hVacc, by rw [hpostV, hVσ]; exact hVTh⟩
  have hpjy : ((tr.state y c).fg.σ V.root).previousHeightJustified :=
    ⟨by rw [hVhj]; omega, by rw [hVhj, hVh]⟩
  have hpj : ((tr.post kV).fg.σ V.root).previousHeightJustified := by
    rw [hpostV, hVσ]; exact hpjy
  have hJr : ((tr.post kV).fg.σ V.root).J = U.root := by rw [hpostV, hVσ]; exact hVJ
  -- **second outcome, at `V`**: a block finalizing `U`, accepted before `t_{v+M}`
  have o2 := (houtcome sp ro proposer dg H tr g ΔF a cF kF hrun hpat.shared
    hpat.catchPremise hpat.cF_upper hpat.timeout hp.reset
    (proposer V.slot) kV kV V V.slot hB'r hVent (hdrainU.trans (hts hUVs.le))
    (by rw [hpostV, hVσ, hVh]; omega) (fun _ _ => by rw [hpostV, hVσ, hVhj]; omega)
    (hB'ret _ _ hVent)).1
  have hT1 : sp.ts (V.slot + cF + kF + 1 : Nat) ≤ sp.ts (v + M : Nat) := hts (by omega)
  have finish : ∀ x ∈ H, ∀ k Z, tr.AcceptAt x k Z →
      tr.time k < sp.ts (V.slot + cF + kF + 1 : Nat) → Anc (tr.HonestBlocks H) V Z →
      ((tr.state x (k + 1)).fg.σ Z.root).F = U.root →
      ∃ x ∈ H, ∃ kX X, tr.AcceptAt x kX X ∧ g ≤ tr.time kX ∧
        tr.time kX < sp.ts (v + M : Nat) ∧
        ∃ Fx ∈ (tr.post kX).fg.tree,
          Fx.root = ((tr.post kX).fg.σ X.root).F ∧ Anc (tr.HonestBlocks H) U Fx := by
    intro x hx k Z hacc hkt hVZ hF
    have hUZ : Anc (tr.HonestBlocks H) U Z := (hUV.mono (hsub y hy c)).trans hVZ
    refine ⟨x, hx, k, Z, hacc, ?_, hkt.trans_le hT1, U, ?_, ?_, .refl⟩
    · have hZs : Z.slot ≤ sp.slot (tr.time k) := (hrun.cutLaw x hx k _ hacc).1
      have hVZs := (Anc.slot_le hcoh hVZ).1
      have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) (U.slot : Int)).2
        (by exact_mod_cast (show U.slot ≤ sp.slot (tr.time k) by omega))
      linarith
    · rw [← tr.state_succ_of_call hacc]
      exact mem_of_honest_anc hrun hnc hx hUZ (Healing.accept_mem' hrun hx hacc)
    · rw [← tr.state_succ_of_call hacc, hF]
  rcases o2 with ⟨q', j, Bs, Pr, R, hjt, hgw, -⟩ | ⟨x, hx, k, Z, hacc, hkt, hJZ, hfin, -⟩
  · -- good window at `V`: its justifying block finalizes `σ[V].J = U`
    have hq' := hgw.proposal.1
    obtain ⟨Z, hJZ, -, -, -, -, hfin⟩ := Store.window_justifies hfg hgw
    have hVq' := hgw.entry.1
    simp only [projFG_store_eq hrun hq'] at hJZ hfin hVq'
    rw [σ_eq_honest hrun hnc hq' hy hVq' hVm] at hfin
    have hFZ := (hfin hpjy).1
    rw [hVJ] at hFZ
    have hZm := hJZ.1
    have hVZ := hJZ.2.1.mono (hsub q' hq' _)
    rcases Compose.tree_cases hrun.toLocalRun hq' hZm with hgen | ⟨k', hk', hacc⟩
    · have := (Anc.slot_le hcoh hVZ).1
      rw [hgen] at this
      simp [Params.genesisBlock] at this
      omega
    · refine finish q' hq' k' Z hacc
        (lt_of_le_of_lt (hrun.time_mono (Nat.lt_succ_iff.mp hk')) hjt) hVZ ?_
      rw [σ_eq_honest hrun hnc hq' hq' (Healing.accept_mem' hrun hq' hacc) hZm]
      exact hFZ
  · -- early justification of `V`: the gate has finalized `σ[V].J = U`
    have hFZ := (hfin (decide_eq_true hpj)).2
    rw [hJr] at hFZ
    rw [← tr.state_succ_of_call hacc] at hFZ hJZ
    exact finish x hx k Z hacc hkt (hJZ.2.1.mono (hsub x hx _)) hFZ

end Consensus.Goldilocks.Healing.Recovery

end
