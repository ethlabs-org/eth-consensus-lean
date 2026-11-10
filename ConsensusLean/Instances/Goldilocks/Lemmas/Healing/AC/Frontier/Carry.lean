module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ReceiptCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The pre-`b` frontier over AC traces: what an origin carries to the next voters

The unlock-given copies of `Compose/Sleepy/Transport`'s node facts and of the writer-pool
condition, at a write mode, under the deadline-cut service `SyncUntilAC`:

* a block stamp is not earlier than the block's acceptance (`blockStamp_ge_of_acceptU`, after
  `Compose.blockStamp_ge_of_accept`);
* what a result's or an optimistic selection's writer did with its counted votes
  (`result_writerU`, `optimistic_writer_votesU`, after `Compose.result_writer` and
  `Compose.optimistic_writer_votes`);
* **`Carry_y` from a writer** (`carryAt_of_writerAC`, after `Compose.carryAt_of_writer_before`):
  the counted votes, sent or admitted by an honest writer before `t_s + 2Δ`, and their heads,
  accepted by it before `t_s + 2Δ`, reach an honest slot-`(s+1)` voter at a time `≤ b` before the
  freeze `t_s + 3Δ`. The receiver's deadline is at most `t_s + 3Δ`, below its vote time, so within
  the cut of `SyncUntilAC`; the processing is since the voter's latest restart, so kept;
* **the writer-pool condition** (A1.8 (d), `writer_mergedAC`, after
  `SA.writer_merged_window_before`): every slot-`s` vote of a slot-`(s+1)` voter's merged view is
  in the pool of an honest update of slot `s` within `b`, or makes its validator an equivocator
  there. -/

namespace Consensus.Goldilocks.SA


variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-! ### Stamps and the writers' counted votes -/

/-- `Compose.blockStamp_ge_of_accept` with the unlock given: after an honest node accepts a block
other than genesis at cut `k`, its stamp is at least the time of `k`. -/
theorem blockStamp_ge_of_acceptU (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : Blk sp.n FGP} (hk : tr.AcceptAt y k B) (hB : B.root ≠ sp.genesisRoot) :
    ∀ c, k + 1 ≤ c → ETime.of (tr.time k) ≤ (tr.state y c).blockStamp B.root := by
  have hpost : ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      (ℓ.call = .block B ∨ ETime.of (tr.time k) ≤ (tr.state y c).blockStamp B.root) →
      ETime.of (tr.time k) ≤ (tr.post c).blockStamp B.root := by
    intro c ℓ hc hkc hpre
    have hΦ : FrameOK ℓ.frame := (frameIn_of_callAtU hr hy hc).1
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp : tr.post c =
        (stepWithM sp ro wm y (u c) (tr.state y c) ℓ.frame (tr.time c) ℓ.call).1 := by
      rw [he]
    have htk : ETime.of (tr.time k) ≤ ETime.of (tr.time c) :=
      etime_of_le_of.2 (hr.time_mono hkc)
    obtain ⟨hblk, -, hoth⟩ :=
      stepWith_blockStamp_eq (wm := wm) ro y (u c) (tr.state y c) hΦ (hr.time_nonneg c) ℓ.call
    rw [hp]
    generalize ℓ.call = cl at hpre hblk hoth ⊢
    cases cl with
    | block B' =>
      rw [hblk B' rfl, Function.update_apply]
      split_ifs with h
      · exact htk
      · rcases hpre with hpre | hpre
        · cases hpre
          exact absurd rfl h
        · exact hpre
    | restart =>
      change _ ≤ (acRestart sp ro y (tr.state y c) ℓ.frame (tr.time c)).1.blockStamp B.root
      rcases ((restart_state sp) FGP ro y (tr.state y c) ℓ.frame (tr.time c) hΦ
        (hr.time_nonneg c)).2.2.2.2.2.2.2.2.2.2 B.root with h | ⟨h, -⟩
      · rw [h]; simp [SAState.initial, hB]
      · rw [h]; exact htk
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    obtain ⟨ℓ, hcl, hcall⟩ := hk
    rw [state_succ_of_call hcl]
    exact hpost k ℓ hcl le_rfl (Or.inl hcall)
  | succ c hkc ih =>
    by_cases hn : ∃ ℓ, tr.CallAt y c ℓ
    · obtain ⟨ℓ, hcl⟩ := hn
      rw [state_succ_of_call hcl]
      exact hpost c ℓ hcl (by omega) (Or.inr ih)
    · rw [Trace.state_succ_of_not tr fun ℓ hcl => hn ⟨ℓ, hcl⟩]
      exact ih

/-- An honest vote is cast by `t_s + Δ` of its slot `s`. -/
theorem cast_time_leAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    tr.time i ≤ sp.ts e.msg.slot + sp.Δ := by
  have h := vote_time_leU hr hy ⟨ℓ, hc⟩
  rw [← (castAt_specU hr hy hc).2.1] at h
  exact h

/-- `Compose.result_writer` with the unlock given: each counted vote of an honest result was
admitted (or sent) by the writer at a time in `[t_s, t_s + 2Δ)`, and its head extends the result
and is genesis or was accepted by the writer before `t_s + 2Δ`. -/
theorem result_writerU (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, tr.AcceptAt X k Hv ∧ tr.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓX, ⟨hcX, htick, -, -⟩, -, rfl⟩ := hR
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΦXU : ℓX.frame.tree ⊆ U := (frameIn_of_callAtU hr hX hcX).2
  rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
  have hvs : v.slot = s := state_pool_slotU sp hr hX i₀ s v hvp
  obtain ⟨hvst, hbst⟩ : (tr.state X i₀).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (tr.state X i₀).blockStamp v.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
    unfold resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [ETime.of])
    · split_ifs at hvres
      · exact absurd hvres (by simp [ETime.of])
      · exact max_lt_iff.1 hvres
  refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
  · rcases pool_originU hr hX i₀ v (by rw [hvs]; exact hvp) with
      ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
    · rw [hst, etime_of_lt_of] at hvst
      exact ⟨k, hsend, (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
    · exfalso
      rw [hst, etime_of_lt_of] at hvst
      have hBv := (frame_validPayloadU sp hr hX hck B hB).1 v hvB
      have hBs := frame_slot_leU sp hr hX hck B hB
      have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time k) := fun h => by
        have := (ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
        rw [ts_succ] at this; linarith only [this, hvst, hΔ]
      omega
  · rcases Compose.frame_anc_acceptedU hr hX i₀ ℓX hcX R hR R Relation.ReflTransGen.refl with
      hg | ⟨k, hk, hacc⟩
    · exact Or.inl hg
    · refine Or.inr ⟨k, hacc, not_le.1 fun hge => ?_⟩
      have hki : k < i₀ := by
        refine lt_of_le_of_ne hk ?_
        rintro rfl
        obtain ⟨ℓ', hc', hcall⟩ := hacc
        rw [Option.some.inj (hc'.2.symm.trans hcX.2), htick] at hcall
        cases hcall
      rw [← hRr] at hbst
      have h := (blockStamp_ge_of_acceptU hr hX hacc (accept_ne_genesisU sp hr hX hacc) i₀
        hki).trans_lt hbst
      rw [etime_of_lt_of] at h
      linarith only [h, hge]

/-- `Compose.optimistic_writer_votes` with the unlock given. -/
theorem optimistic_writer_votesU (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hO : OptimisticLockAt tr x i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, tr.SendOrAdmit x k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, tr.AcceptAt x k Hv ∧ tr.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓx, A, hp, hsl, hsel, rfl⟩ := hO
  have hc := hp.1
  have hti : tr.time i₀ < sp.ts (sp.slot (tr.time i₀)) + 2 * sp.Δ := by
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with h
    all_goals first
      | cases hsel
      | exact not_le.1 fun h' => h (Or.inr (Or.inr h'))
  rw [hsl] at hti
  have hΦU : ℓx.frame.tree ⊆ U := (frameIn_of_callAtU hr hx hc).2
  rintro v ⟨hvA, R, hR, hRr, hCR⟩
  have hv1 := optimisticPoint_pool_postU hr hx hp s hvA
  have hvs : v.slot = s := state_pool_slotU sp hr hx (i₀ + 1) s v hv1
  refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
  · rcases pool_originU hr hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
      ⟨k, hk, hsend, -, hsl'⟩ | ⟨k, hk, ℓk, hck, -, -, B, hB, hvB⟩
    · exact ⟨k, hsend, (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl'), lt_of_le_of_lt (hr.time_mono (by omega)) hti⟩
    · exfalso
      have hBv := (frame_validPayloadU sp hr hx hck B hB).1 v hvB
      have hBs := frame_slot_leU sp hr hx hck B hB
      have := slot_mono sp (hr.time_nonneg k) (hr.time_mono (show k ≤ i₀ by omega))
      omega
  · rcases Compose.frame_anc_acceptedU hr hx i₀ ℓx hc R hR R Relation.ReflTransGen.refl with
      hg | ⟨k, hk, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk) hti⟩

/-! ### `Carry_y` from a writer -/

/-- **`Carry_y` from a writer under the deadline-cut service** (`Compose.carryAt_of_writer_before`
with the unlock given): for an honest `y` casting its slot-`(s+1)` vote at a time `≤ b`, if each
counted vote is of slot `s`, was sent or admitted by an honest writer `w` at a time in
`[t_s, t_s + 2Δ)`, and has a head above `y`'s `Φ.F` that is genesis or was accepted by `w` before
`t_s + 2Δ`, then `Carry_y(s, ·, ·)` holds for the counted votes. Every delivery read has the
voter's deadline at most `t_s + 3Δ ≤ τ ≤ b`. -/
theorem carryAt_of_writerAC (hr : ACLocalRunU wm u H U tr)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    {s : Nat} {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, tr.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, tr.AcceptAt w k Hv ∧ tr.time k < sp.ts s + 2 * sp.Δ)) :
    CarryAt tr U y i e s CV := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := castAt_specU hr hy hc
  obtain ⟨hrsy, hti⟩ := vote_restartsAC hr hy hc hs
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ → tr.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ from
      lt_add_of_pos_right _ (mul_pos two_pos hΔ))
    change tr.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith only [h₁, h₂]
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨-, -, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    have hyacc : AcceptedBefore tr y Hv (sp.ts s + 3 * sp.Δ) := by
      rcases hacc with hg | ⟨kw, hkw, hkwt⟩
      · exact Or.inl hg
      · have hdi : tr.deadline y i (tr.time kw) ≤ tr.time i := by
          linarith only [hdl i le_rfl _ hkwt, hti, hΔ]
        obtain ⟨ky, hky, hacc', hkyt⟩ :=
          hsy.relay w hw kw Hv hkw y hy i ℓ hc.1 hdi (by linarith) hFHv
        exact Or.inr ⟨ky, hacc', hkyt.trans (hdl ky hky _ hkwt)⟩
    rcases hyacc with hg | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt'⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    rcases Compose.frame_anc_acceptedU hr hy ky ℓk hck Hv
      ((accept_newU sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) X hX with hg | ⟨k, hk, hkX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt'⟩
  · obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, -⟩ := hW v hv
    have hdi : tr.deadline y i (tr.time k) ≤ tr.time i := by
      linarith only [hdl i le_rfl _ hk2, hti, hΔ]
    obtain ⟨k', hk'i, hkk', hp, hk'dl, hnr'⟩ :=
      hsy.message w hw k v hsend y hy i ℓ hc.1 hdi (by linarith)
    have hk'lt : tr.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hk2)
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ tr.RestartAt y r :=
      fun r h₁ h₂ => hnr' r (by omega) (by omega)
    have hsk' : sp.slot (tr.time k') = s :=
      slot_of_mem sp s (hk1.trans hkk') (by rw [ts_succ]; linarith only [hk'lt, hΔ])
    have hheld : ∀ u' ∈ (tr.state y (k' + 1)).pool s,
        HeldBefore e.readPoint u' (sp.ts s + 3 * sp.Δ) := by
      intro u' hu
      have hus : u'.slot = s := state_pool_slotU sp hr hy (k' + 1) s u' hu
      have hu' := pool_monoU hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine heldBefore_readPointU hr hy hc (by omega) ⟨by rw [hus]; exact hu', ?_⟩
      rcases pool_originU hr hy (i + 1) u' (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, etime_of_lt_of]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · have h := cast_time_leAC hr hy ⟨hc₁, he₁⟩
            rw [hus] at h
            linarith only [h, hΔ]
          · exact absurd (pool_monoU hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, etime_of_lt_of]
        have := hrsy k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith only [this, hΔ]
    by_cases hv' : v ∈ (tr.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases held_of_processAtU hr hy hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (tr.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (tr.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, state_pool_slotU sp hr hy _ s a ha',
          state_pool_slotU sp hr hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

/-- **A result's counted votes reach a next-slot voter** at a time `≤ b` whose `Φ.F` is at or
below the result. -/
theorem result_carryAC (hr : ACLocalRunU wm u H U tr)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hR : ResultAt tr X i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) (hF : Anc U ℓ.frame.F C) :
    CarryAt tr U y i e s CV := by
  refine carryAt_of_writerAC hr hsy hX hy hc hs hib fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := result_writerU hr hX hR v hv
  exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩

/-- **An optimistic selection's counted votes reach a next-slot voter** at a time `≤ b` whose
`Φ.F` is at or below the selection. -/
theorem optimistic_carryAC (hr : ACLocalRunU wm u H U tr)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hO : OptimisticLockAt tr x i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) (hF : Anc U ℓ.frame.F C) :
    CarryAt tr U y i e s CV := by
  refine carryAt_of_writerAC hr hsy hx hy hc hs hib fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := optimistic_writer_votesU hr hx hO v hv
  exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩

/-! ### The writer-pool condition -/

/-- The writer's pool covers the voter's pool (`SA.writer_pool_window_before` with the unlock
given): every slot-`s` vote that an honest slot-`(s+1)` voter holds at a cut up to its vote is in
the pool of an honest update of slot `s` within `b`, or makes its validator an equivocator
there. -/
theorem writer_poolAC (hr : ACLocalRunU wm u H U tr) (hsv : ServiceWindowBefore H U 0 b tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ s ℓX) (hi₀ : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) {k : Nat} (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hrsy, -⟩ := vote_restartsAC hr hy hc hs
  have hrsX := update_restartsAC hr hX hupd
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have := cast_time_leAC hr hy hc
    rw [hs, ts_succ] at this; linarith only [this]
  intro v hv
  have hvs : v.slot = s := state_pool_slotU sp hr hy (k + 1) s v hv
  rcases pool_originU hr hy (k + 1) v (hvs ▸ hv) with
    ⟨k', hk', hsend, -, hsl⟩ | ⟨k', hk', ℓk, hck, hrk, -, B, hB, hvB⟩
  · have hsk : sp.ts s ≤ tr.time k' :=
      (ts_le_iff_le_slot sp (hr.time_nonneg k') s).2 (by rw [← hvs]; exact_mod_cast hsl)
    have hki : tr.time k' ≤ tr.time i := hr.time_mono ((Nat.le_of_lt_succ hk').trans hk)
    have hdl : tr.time k' + sp.Δ ≤ tr.time i₀ := by
      rw [hupd.2.2.1]; linarith only [hki, hti]
    have hslot : ∀ t, tr.time k' ≤ t → t < tr.time k' + sp.Δ →
        (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t := by
      rw [hvs]; exact slot_window_of_forward (hr.time_nonneg k') hsk hki hti
    have hheld := sync_window_before_forwardU hr hsv hy hsend (hr.time_nonneg k')
      (hdl.trans hi₀) hX hupd.1 (fun k'' hk'' hr'' => (hrsX k'' hk'' hr'').trans hsk) hdl hslot
    rwa [hvs] at hheld
  · have hBv := (frame_validPayloadU sp hr hy hck B hB).1 v hvB
    have hBs := frame_slot_leU sp hr hy hck B hB
    have htk := hrsy k' ((Nat.le_of_lt_succ hk').trans hk) ⟨ℓk, hck, hrk⟩
    have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time k') := fun h => by
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k') _).2 h
      rw [ts_succ] at this; linarith only [this, htk, hΔ]
    clear * - this hBv hBs hvs
    omega

/-- **The writer-pool condition** (A1.8 (d), `SA.writer_merged_window_before` with the unlock
given): every slot-`s` vote of an honest slot-`(s+1)` voter's merged view is in the pool of an
honest update of slot `s` within `b`, or makes its validator an equivocator there. -/
theorem writer_mergedAC (hr : ACLocalRunU wm u H U tr) (hsv : ServiceWindowBefore H U 0 b tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ s ℓX) (hi₀ : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  rintro v (hv | ⟨B, hB, hBs, hvB⟩) hvs
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    exact writer_poolAC hr hsv hX hupd hi₀ hy hc hs le_rfl v
      (readPoint_poolU hr hy hc (by simpa using hv)).1
  obtain ⟨-, hys, -, -⟩ := castAt_specU hr hy hc
  rcases frame_genesis_or_acceptedU sp hr hy hc.1 B hB with h0 | ⟨k, hki, ℓk, hck, hcall⟩
  · omega
  have hBk : B.slot ≤ sp.slot (tr.time k) := by
    rcases hr.frameLaw y hy k ℓk hck with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩ <;>
    · rw [hcall] at hok
      obtain ⟨-, -, -, h⟩ := hok
      exact h
  have hki' := slot_mono sp (hr.time_nonneg k) (hr.time_mono hki)
  have he := hr.exec k ℓk hck.2 (hck.1 ▸ hy)
  rw [hck.1, hcall] at he
  have hpost : tr.post k = (tryVoteWithM sp wm y (u k) (optimisticConfirmationM sp wm
      (blockReceipt sp (tr.state y k) (tr.time k) B) ℓk.frame (tr.time k)) ℓk.frame
      (tr.time k)).1 := (congrArg Prod.fst he).symm
  exact receipt_vote_covered (L := u k) (t := tr.time k) y (tr.state y k) ℓk.frame hvB hvs
    (by omega) (by omega) fun w hw => writer_poolAC hr hsv hX hupd hi₀ hy hc hs hki w
      (by rw [state_succ_of_call hck, hpost]; exact hw)

end Consensus.Goldilocks.SA

end
