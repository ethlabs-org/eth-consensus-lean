module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # M1′ E1–E3: the rise (ROUND, two rounds, the high source)

pre_advance_finality §24.4, §26 Step E/F, §27 and §30 G1; healing_parallel_plan §2 P6.

* `rows_delivered_service` (ROW-deliver): a row signed by `v ≥ ḡ` is processed by the honest
  proposer before its proposal cut when `v + Δ_F ≤ t_x ≤ b`. Only `ResetService.signedRow` and
  `NoRestartAfter ḡ` are used (no `HSShared`).
* `round_cross` (ROUND at one proposal): `P ⪯ D = parent(X)`, `P.slot + δ_t ≤ X.slot`, and every
  honest node has a row for `P`'s height and entry by `v`, or a block in `(P, D]` above `P`'s
  height: `σ[X].h ≥ σ[P].h + 1`. ROW-include is the landed `proposal_rows_placed` (the payload is
  the pool filtered by validity at the parent and "not on the chain"; no cap).
* `row_or_high_of_report` (ROW-sign at the actual report, G1): an honest report `R ⪰ P` gives a
  row for `(σ[P].h, σ[P].T_h)` signed by the report time, or `σ[R].h > σ[P].h`.
* `FrameWindow.round_of_warm` (ROUND at a warm proposal): the drain's actual reports
  (`proposal_report_follow`) feed `round_cross` at the next honest proposal of slot
  `x ∈ [u + δ_t, N]`.
* The rise reset itself (Step F) is `FrameWindow.rise_reset_rounds` in `M1/RiseRounds`.

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

/-- The entry slot is at most the slot (as `Store.ThSlot_le_slot` in Refinement). -/
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
    · rw [e]; omega
    · rw [e]; rfl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **ROW-deliver** from the finite service: a row signed by an honest validator by `v ≥ ḡ` is
processed by the honest proposer before its proposal cut when `v + Δ_F ≤ t_{kX} ≤ b`. -/
theorem rows_delivered_service {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hv : gbar g ≤ v) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j, ∀ τ : Time, tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := fun j τ => by
    have h := deadline_le_restarts (T := tr.projAC) (c := j)
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
  linarith [hdl k']

/-- **ROUND at one honest proposal** (§24.4, §26 Step E). `X` is an honest proposal on the parent
`D ⪰ P`, at a slot `≥ P.slot + δ_t`, with `v ≥ ḡ` and `v + Δ_F ≤ t_X ≤ b`. Every honest `y`
either signed a row for `P`'s height and entry by `v`, or some block `R ⪯ D` is above `P`'s
height. Then `X` is at least one height above `P`. -/
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
  · omega
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ P.root).h := by omega
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
    omega
  have hcross := cross_of_rows hrun hnc hp hX hpar hPr S
    (fun z hz => (Finset.mem_filter.1 hz).2) hScard ?_ (by omega)
  · have h1 := hcross.1
    rw [he] at h1
    omega
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
    omega

/-- **ROW-sign at the actual report** (§30 G1, §24.3–§24.4). An honest report `R ⪰ P` at cut `i`
before `T`: `y` signed a row for `(σ[P].h, σ[P].T_h)` by `t_i`, or `σ[R].h > σ[P].h`. At equal
heights the lock premise is the height `HZ` (F3-lock, from NoAdvance) or the O1-L kind clause. -/
theorem row_or_high_of_report (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) {g T : Time}
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {R P : SA.Blk sp.n (List (FG.Att sp.n))} (hR : SA.ToFGAt tr.projAC y i ell R)
    (hiT : tr.time i < T) (hPR : Anc (tr.HonestBlocks H) P R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h →
      ((tr.state y i).fg.σ P.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    P ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧ att.T = ((tr.state y i).fg.σ P.root).Th) ∨
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have hRm := toFG_mem_tree hrun hy hR
  have hPm := mem_of_honest_anc hrun hnc hy hPR hRm
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  have hPRs := store_anc_of_honest_anc hrun hnc hy hPR hRm
  have hle := h_le_of_store_anc hr hPRs
  refine ⟨hPm, hRm, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  left
  have hf' : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨hc, hto, hres⟩ := hR
  rw [Compose.projAC_state hrun.toLocalRun hy] at hres
  obtain ⟨sg, hatt, ht, hfg⟩ :=
    toFG_attest hrun.toLocalRun hy (Compose.projAC_callAt.mp hc) hto hres
  obtain ⟨⟨E, hE, hEr, hER, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hr R hRm
  have hEnt : EntryOf (tr.state y (i + 1)).fg R E ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]
    exact ⟨⟨hE, hETh.trans hEr.symm⟩, hEh.trans heq.symm, hER⟩
  have hCh : ((tr.state y (i + 1)).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]; exact heq.symm
  have hTh : E.root = ((tr.state y i).fg.σ P.root).Th :=
    hEr.trans (Th_eq_of_anc hr hPRs heq.symm)
  have hrow : (∃ att, sg = some att ∧ att.h = ((tr.state y i).fg.σ P.root).h ∧
      att.T = E.root) ∨ ∃ k' < i + 1, ∃ att, tr.SignAt y k' att ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧ att.T = E.root := by
    rcases hkind heq.symm with hHZ | hk
    · rw [hHZ] at hEnt hCh ⊢
      exact client_signs_HZ_of_noAdvance hrun hna hy (by rw [ht]; exact hiT) hatt hEnt hCh
    · refine client_signs_of_frame hrun hnc hf' hy hatt hEnt hCh ?_
      rw [hfg]; exact hk
  rcases hrow with ⟨att, rfl, hah, haT⟩ | ⟨k', hk', att, hs, hah, haT⟩
  · exact ⟨i + 1, att, ⟨R, hatt⟩, ht.le, hah, haT.trans hTh⟩
  · exact ⟨k', att, hs, hrun.time_mono (Nat.lt_succ_iff.mp hk'), hah, haT.trans hTh⟩

/-- **ROUND at a warm proposal** (§26 Step E with §30 G1). `P` is the actual warm proposal of
slot `u` (FrameWindow drain), `X` an actual honest proposal of slot `x ∈ [u + δ_t, N]`. The rows
come from the actual reports of `proposal_report_follow`; at each report of the same height as
`P`, `report_kind_of_warm` derives O1-L from the frame floor. This strengthens the interface
by removing the redundant lock premise, without changing the conclusion. -/
theorem FrameWindow.round_of_warm
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (hz : z ∈ H) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} (hp : p ∈ H) (hdx : p = proposer x)
    {kX : Nat} (hX : tr.ProposesAt p kX X) (hXs : X.slot = x) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  have hk := sp.two_le_k
  have hΔ := sp.toParams.hΔ
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  obtain ⟨-, k, ℓ, d, pay, hc, hcall, hd, htc, hpar, -⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hp hdx hX hXs
  have hpx : proposer x ∈ H := hdx ▸ hp
  have hrep := fun y (hy : y ∈ H) => hframe.proposal_report_follow hrun hnc hsvc hawake hf
    hcatch hnr hm hwarm (by omega) hmb hz hdes hP hPs hy
  have hfol : ∀ y ∈ H, ∃ i ell R, SA.ToFGAt tr.projAC y i ell R ∧
      tr.time i ≤ sp.ts (s + 2 : Nat) + 2 * sp.Δ ∧ Anc (tr.HonestBlocks H) P R ∧
      Anc (tr.HonestBlocks H) R d.head := by
    intro y hy
    obtain ⟨i, ell, R, hR, hti, hPR, hf⟩ := hrep y hy
    exact ⟨i, ell, R, hR, hti, hPR,
      hf x (by omega) hxN (proposer x) hpx k ℓ hc hcall htc d pay hd⟩
  obtain ⟨-, hPm, -⟩ := accept_of_proposesAt hrun hnc hz hP
  obtain ⟨i₀, -, R₀, -, -, hPR₀, hR₀d⟩ := hfol z hz
  have htX : tr.time kX = sp.ts x := by
    have : tr.time kX = sp.ts X.slot := by rw [hX.2.2, sp.slotTime_eq]; rfl
    rw [this, hXs]
  have hv : gbar g ≤ sp.ts (s + 2 : Nat) + 2 * sp.Δ := by
    have := hts (show s₀ ≤ s + 2 by omega); linarith
  have hvx : sp.ts (s + 2 : Nat) + 2 * sp.Δ + ΔF ≤ tr.time kX := by
    rw [htX]
    have h1 := hts (show s + 1 + sp.toParams.fg.δt ≤ x by omega)
    have h2 : sp.ts (s + 1 + sp.toParams.fg.δt : Nat) =
        sp.ts (s + 2 : Nat) + 4 * sp.Δ * (sp.toParams.fg.δt : Time) - 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  refine round_cross hrun hnc hsvc hnr hf ⟨z, hz, kP + 1, hPm⟩ (hPR₀.trans hR₀d) hpar hp hX
    hv hvx (by rw [htX]; linarith [hts hxN]) (by omega) ?_
  intro y hy
  obtain ⟨i, ell, R, hR, hti, hPR, hRd⟩ := hfol y hy
  have hiT : tr.time i < T := lt_of_le_of_lt hti hT
  obtain ⟨hPy, hRy, hor⟩ := row_or_high_of_report hrun hnc hf hna hy hR hiT hPR
    (fun heq => Or.inr (hframe.report_kind_of_warm hrun hnc hsvc hawake hf hcatch hnr
      hm hwarm (by omega) hmb hz hdes hP hPs y hy i ell R hR hPR hti heq))
  rcases hor with ⟨k', att, hs, hk', hah, haT⟩ | hlt
  · exact Or.inl ⟨y, hy, i, hPy, k', att, hs, hk'.trans hti, hah, haT⟩
  · exact Or.inr ⟨R, hRd, y, hy, i, hPy, hRy, hlt⟩

end Consensus.Goldilocks.Healing

end
