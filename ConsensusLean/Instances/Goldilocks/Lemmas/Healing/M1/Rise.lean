module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The rise (ROUND at one proposal)

* `rows_delivered_service` (ROW-deliver): an attestation signed by `v ≥ ḡ` is processed by the
  honest proposer before its proposal cut when `v + Δ_F ≤ t_x ≤ b`. Only `ResetService.signedRow`
  and `NoRestartAfter ḡ` are used (no `HSShared`).
* `round_cross` (ROUND at one proposal): `P ⪯ D = parent(X)`, `P.slot + δ_t ≤ X.slot`, and every
  honest node has an attestation for `P`'s height and entry by `v`, or a block in `(P, D]` above
  `P`'s height: `σ[X].h ≥ σ[P].h + 1`. ROW-include is the landed `proposal_rows_placed` (the payload
  is the pool filtered by validity at the parent and "not on the chain"; no cap).

`Δ_F` stays a parameter: the timing premise is `6Δ + Δ_F ≤ 4Δ·δ_t`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- Entry-slot constancy while the height stays along ancestry (as in `WindowSeed`). -/
private theorem ThSlot_eq_of_anc' {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
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

/-- The entry slot is at most the slot (as `Store.ThSlot_le_slot` in Obligations). -/
private theorem ThSlot_le_slot' {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree) :
    (st.σ Z.root).ThSlot ≤ Z.slot := by
  obtain ⟨hcoh, -, hg⟩ := (Goldilocks.Store.accepted_tree P ACP acp₀ st hr).2
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
    · rw [e]; (clear * - hsl this; omega)
    · rw [e]; rfl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **ROW-deliver** from the finite service: an attestation signed by an honest validator by `v ≥ ḡ`
is processed by the honest proposer before its proposal cut when `v + Δ_F ≤ t_{kX} ≤ b`. -/
theorem rows_delivered_service {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hv : gbar g ≤ v) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j, ∀ τ : Time, tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := fun j τ => by
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k' _ hr => hnr p hp k' (Compose.projAC_restartAt.1 hr)) τ
    simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
    linarith
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j, tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := fun j => by
    have := hdl0 j (max (tr.time k) g)
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hsvc.signedRow y hy k att hsig p hp kX ⟨_, hcall⟩ hkb
    (by linarith [hdl kX])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith only [hdl k', hlt, hvx]

/-- **ROUND at one honest proposal.** `X` is an honest proposal on the parent `D ⪰ P`, at a slot
`≥ P.slot + δ_t`, with `v ≥ ḡ` and `v + Δ_F ≤ t_X ≤ b`. Every honest `y` either signed an
attestation for `P`'s height and entry by `v`, or some block `R ⪯ D` is above `P`'s height. Then `X`
is at least one height above `P`. -/
theorem round_cross (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {g ΔF b v : Time} (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {P D X : SA.Blk sp.n (List (FG.Att sp.n))} (hPH : P ∈ tr.HonestBlocks H)
    (hPD : Anc (tr.HonestBlocks H) P D) (hpar : X.parent = some D.root)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} (hX : tr.ProposesAt p kX X)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : P.slot + sp.toParams.fg.δt ≤ X.slot)
    (hrow : ∀ y ∈ H,
      (∃ w ∈ H, ∃ c, P ∈ (tr.state w c).fg.tree ∧ ∃ k att, tr.SignAt y k att ∧
        tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ P.root).h ∧
        att.T = ((tr.state w c).fg.σ P.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocks H) R D ∧ ∃ w ∈ H, ∃ c, P ∈ (tr.state w c).fg.tree ∧
        R ∈ (tr.state w c).fg.tree ∧
        ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ R.root).h) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  classical
  have hcoh := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨Pr, hpar', hPr⟩ := proposal_parent_held hrun hnc hp hX
  obtain ⟨-, hXm, he⟩ := accept_of_proposesAt hrun hnc hp hX
  have hPrH : Pr ∈ tr.HonestBlocks H := ⟨_, hp, kX, hPr⟩
  have hDH : D ∈ tr.HonestBlocks H := by
    rcases Relation.ReflTransGen.cases_tail hPD with rfl | ⟨Z, -, hZ⟩
    · exact hPH
    · exact hZ.2.1
  obtain rfl : D = Pr := hcoh.1 hDH hPrH (Option.some_injective _ (hpar.symm.trans hpar'))
  have hr := Compose.fg_reachable hrun.toLocalRun hp kX
  have hr1 := Compose.fg_reachable hrun.toLocalRun hp (kX + 1)
  have hPst := mem_of_honest_anc hrun hnc hp hPD hPr
  have hPDs := store_anc_of_honest_anc hrun hnc hp hPD hPr
  have hPDh := h_le_of_store_anc hr hPDs
  have hmono := Compose.tree_mono hrun.toLocalRun hp (Nat.le_succ kX)
  have hDm : D ∈ (tr.state p (kX + 1)).fg.tree := hmono hPr
  have hPm := hmono hPst
  have hσP := σ_eq_honest hrun hnc hp hp hPst hPm
  have hσD := σ_eq_honest hrun hnc hp hp hPr hDm
  have hle' := h_le_of_store_anc hr1 (.single ⟨hDm, hXm, hpar⟩)
  refine ⟨hPm, hXm, ?_⟩
  rw [← hσP]
  rw [← hσD] at hle'
  by_cases hlt : ((tr.state p kX).fg.σ P.root).h < ((tr.state p kX).fg.σ D.root).h
  · (clear * - hle' hlt; omega)
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ P.root).h := by
    clear * - hPDh hlt; omega
  have hDTh := Th_eq_of_anc hr hPDs hDh
  have hThS : ((tr.state p kX).fg.σ D.root).ThSlot ≤ P.slot := by
    rw [ThSlot_eq_of_anc' hr hPDs hDh]
    exact ThSlot_le_slot' hr hPst
  let S : Finset (Fin sp.n) := Finset.univ.filter (· ∈ H)
  have hScard : sp.toParams.fg.q ≤ S.card := by
    have hcard : S.card = H.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    change (2 * sp.n + 2) / 3 ≤ _
    clear * - hf hn; omega
  have hcross := cross_of_rows hrun hnc hp hX hpar hPr S
    (fun z hz => (Finset.mem_filter.1 hz).2) hScard ?_ (by omega)
  · have h1 := hcross.1
    rw [he] at h1
    clear * - hPDh h1; omega
  intro y hyS
  have hy : y ∈ H := (Finset.mem_filter.1 hyS).2
  rcases hrow y hy with ⟨w, hw, c, hPw, k, att, hsig, hk, hah, haT⟩ |
    ⟨R, hRD, w, hw, c, hPw, hRw, hhR⟩
  · have hσ := σ_eq_honest hrun hnc hw hp hPw hPst
    rw [hσ] at hah haT
    exact ⟨k, att, hsig, hah.trans hDh.symm, haT.trans hDTh.symm,
      rows_delivered_service hsvc hnr hv hp hX hvx hkb hy hsig hk⟩
  · exfalso
    have hRst := mem_of_honest_anc hrun hnc hp hRD hPr
    have hRDh := h_le_of_store_anc hr (store_anc_of_honest_anc hrun hnc hp hRD hPr)
    rw [σ_eq_honest hrun hnc hw hp hPw hPst, σ_eq_honest hrun hnc hw hp hRw hRst] at hhR
    clear * - hlt hhR hRDh; omega

end Consensus.Goldilocks.Healing

end
