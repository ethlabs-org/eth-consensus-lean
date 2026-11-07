module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainRows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise

public section

/-! # Row crossing with independently honest observations

The proposal's store is read at its own cut. Historical source states are transported by
replay agreement, and the quorum is counted at consumption, not at signing.
-/

namespace Consensus.Goldilocks.Healing.Growing

namespace KernelProof

open SA (SAParams ReplayOrder Payload gbar)

private theorem ThSlot_eq_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) :
    (st.σ W.root).ThSlot = (st.σ A.root).ThSlot := by
  induction h with
  | refl => rfl
  | @tail Y Y' hAY hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hY' hp
    have h₁ := h_le_of_store_anc hr hAY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, e', -⟩ | ⟨e, -, -⟩
    · rw [e']; exact ih (by rw [← e]; exact hh)
    · omega

private theorem ThSlot_le_slot {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree) :
    (st.σ Z.root).ThSlot ≤ Z.slot := by
  obtain ⟨hcoh, -, hg⟩ := (Store.accepted_tree P ACP acp₀ st hr).2
  induction hg Z hZ with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    exact Nat.zero_le _
  | @tail Y Y' hGY hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hY' hp
    have hsl : Y.slot < Y'.slot := hcoh.2 Y hY Y' hY' hp
    have := ih hY
    rcases P.fg.stateTransition_ThSlot ht with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · rw [e]; omega
    · rw [e]; rfl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Delivered historical rows cross one height; honesty is read separately at every cut. -/
theorem round_cross_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    {P D X : SA.Blk sp.n (List (FG.Att sp.n))} (hPH : P ∈ tr.HonestBlocksAt H)
    (hPD : Anc (tr.HonestBlocksAt H) P D) (hpar : X.parent = some D.root)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ sp.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : P.slot + sp.toParams.fg.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ P ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ P.root).h ∧
          att.T = ((tr.state w c).fg.σ P.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        P ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ R.root).h) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  classical
  have hd := hrun.time_nonneg kX
  have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq =>
    hrun.time_mono (by omega)
  have hs := Trace.upTo_state tr p hle
  have hs1 := Trace.upTo_state tr p hle1
  -- Restrict only the proposer's local execution; historical witnesses remain in the full trace.
  have hr := hrun.upTo hd
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  have hcoh := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨Pr, hpar', hPr⟩ := Healing.proposal_parent_held hr (hnc.upTo _) hp hX'
  rw [hs] at hPr
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hr (hnc.upTo _) hp hX'
  rw [hs1] at hXm he
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨p, kX, _, hd, hle, hp, hPr⟩
  have hDH : D ∈ tr.HonestBlocksAt H := by
    rcases Relation.ReflTransGen.cases_tail hPD with rfl | ⟨Z, -, hZ⟩
    · exact hPH
    · exact hZ.2.1
  obtain rfl : D = Pr := hcoh.1 hDH hPrH (Option.some_injective _ (hpar.symm.trans hpar'))
  have hR := fg_reachable_at hrun hd hle hp
  have hR1 := fg_reachable_at hrun hd hle1 hp
  have hPst := mem_of_honest_anc_at hrun hnc hd hle hp hPD hPr
  have hPDs := store_anc_of_honest_anc_at hrun hnc hd hle hp hPD hPr
  have hPDh := h_le_of_store_anc hR hPDs
  have hmono : (tr.state p kX).fg.tree ⊆ (tr.state p (kX + 1)).fg.tree := by
    simpa only [hs, hs1] using Compose.tree_mono hr.toLocalRun hp (Nat.le_succ kX)
  have hDm := hmono hPr
  have hPm := hmono hPst
  have hσP := σ_eq_honest_at hrun hnc hd hle hp hd hle1 hp hPst hPm
  have hσD := σ_eq_honest_at hrun hnc hd hle hp hd hle1 hp hPr hDm
  have hle' := h_le_of_store_anc hR1 (.single ⟨hDm, hXm, hpar⟩)
  refine ⟨hPm, hXm, ?_⟩
  rw [← hσP]
  rw [← hσD] at hle'
  by_cases hlt : ((tr.state p kX).fg.σ P.root).h < ((tr.state p kX).fg.σ D.root).h
  · omega
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ P.root).h := by omega
  have hDTh := Th_eq_of_anc hR hPDs hDh
  have hThS : ((tr.state p kX).fg.σ D.root).ThSlot ≤ P.slot := by
    rw [ThSlot_eq_of_anc hR hPDs hDh]
    exact ThSlot_le_slot hR hPst
  let S := Finset.univ.filter (· ∈ H (tr.time kX))
  have hScard : sp.toParams.fg.q ≤ S.card := by
    have hcard : S.card = (H (tr.time kX)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : (H (tr.time kX)).ncard + (H (tr.time kX))ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  obtain ⟨hfg, hXt, hDt, hσX, hσD', hplace⟩ :=
    Healing.proposal_rows_placed hr (hnc.upTo _) hp hX' hpar (by rwa [hs])
  have hcross := Healing.cross_step hfg hp hXt hDt hpar S hScard ?_ ?_
  · have h1 := hcross.1
    rw [← hσX, he, ← hσD', hs] at h1
    omega
  · intro y hyS
    have hy : y ∈ H (tr.time kX) := (Finset.mem_filter.1 hyS).2
    rcases hrow y hy with ⟨w, c, hw, hPw, k, att, hyk, hsig, hk, hah, haT⟩ |
      ⟨R, hRD, w, c, hw, hPw, hRw, hhR⟩
    · have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
        (fun q hq => hrun.time_mono hq.le) hw hd hle hp hPw hPst
      rw [hσ] at hah haT
      have hproc := rows_delivered_service_at hsvc hnr hrun hv hp hX hvx hkb hyk hsig hk
      have hval := Healing.signAt_val (hrun.upTo (hrun.time_nonneg k)) hyk
        ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hsig⟩)
      rw [← hσD', hs]
      refine ⟨att, hval, hah.trans hDh.symm, haT.trans hDTh.symm, ?_⟩
      exact hplace att (by
        obtain ⟨j, hj, hproc⟩ := hproc
        exact ⟨j, hj, (RunTrace.upTo_processAttAt _).mpr ⟨hrun.time_mono hj.le, hproc⟩⟩)
        (by rw [hs]; exact hah.trans hDh.symm)
        (by rw [hs]; exact haT.trans hDTh.symm)
    · exfalso
      have hRst := mem_of_honest_anc_at hrun hnc hd hle hp hRD hPr
      have hRDh := h_le_of_store_anc hR (store_anc_of_honest_anc_at hrun hnc hd hle hp hRD hPr)
      rw [σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hPw hPst,
        σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hRw hRst] at hhR
      omega
  · rw [← hσD', hs]
    omega

end KernelProof

end Consensus.Goldilocks.Healing.Growing

end
