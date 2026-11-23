module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: what an origin carries to the next voters

Transport and the non-root case of S3 (`SleepyInvariantUpTo`): for an origin `C` of label `s` and an
honest slot-`(s+1)` vote whose `Σ.F` is at or below `C`, the counted votes and heads reach the voter
in time (`AC.CarryAt`), and, for a result, every slot-`s` vote of the voter's merged view reaches
the writer (A1.8 (d)). Under `Sync[0, ∞)`: each counted vote was admitted by the writer (so
forwarded) and each counted head accepted by it (so relayed) before `t_s + 2Δ`; the voter is joined
at its vote, so awake since `t_s` with its pool kept, and processes them before `t_s + 3Δ`; the
relay applies since the voter's `Σ.F` is below `C`, below each head. -/

namespace Consensus.Goldilocks.Compose

variable {wm : AC.WriteMode}

open AC (ACParams ReplayOrder Vote Payload)


/-! ### One honest node over an AC trace -/

section Node

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {T : AC.GTrace sp FGP ro}

/-- `frame_anc_accepted` with the unlock given. -/
theorem frame_anc_acceptedU
    {u : Nat → Set AC.Lock} {ini} (hr : AC.ACLocalRunU wm u H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (AC.goldilocksAC sp FGP ro)), T.CallAt y i ℓ → ∀ B ∈ ℓ.frame.tree, ∀ X,
      Anc U X B → X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    have step : ∀ Φ : AC.Frm sp.n FGP, Φ.tree ⊆ U →
        (AC.goldilocksAC sp FGP ro).CallOK U Φ (T.time i) ℓ.call ℓ.frame →
        (∀ B ∈ Φ.tree, ∀ X, Anc U X B → X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X) →
        ∀ B ∈ ℓ.frame.tree, ∀ X, Anc U X B →
          X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X := by
      intro Φ hΦU hok hv B hB X hX
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm
      cases c with
      | block B₀ =>
        rw [hm.1.tree_eq] at hB
        rcases hB.1 with rfl | hB'
        · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, hXQ, hQ⟩
          · exact Or.inr ⟨i, le_rfl, ℓ, hc, hcall⟩
          · obtain ⟨P, hP, hPr⟩ := hm.1.parent_mem
            have hQP : Q = P :=
              hr.coherent.1 hQ.1 (hΦU hP) (Option.some.inj (hQ.2.2.symm.trans hPr))
            exact hv P hP X (hQP ▸ hXQ)
        · exact hv B hB' X hX
      | message m => exact hv B (hm.1 ▸ hB) X hX
      | tick => exact hv B (hm ▸ hB) X hX
      | proposal => exact hv B (hm ▸ hB) X hX
      | toFG => exact hv B (hm ▸ hB) X hX
      | restart => exact hv B (hm ▸ hB) X hX
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -, hpar, -⟩, hin, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ hin.2 hok fun B hB X hX => Or.inl ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hroot
      · exact absurd (hQ.2.2.symm.trans hpar) (Option.some_ne_none _)
    · have hin' : ℓ'.frame.tree ⊆ U := by
        rcases hr.frameLaw y hy j ℓ' hc' with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
          exact h.1.2
      exact step _ hin' hok fun B hB X hX =>
        (ih j hj ℓ' hc' B hB X hX).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩

/-- **Frames are closed under acceptance**: every ancestor (inside `U`) of a block of an honest
node's frame at a call is genesis or was accepted by the node at that call or an earlier one. -/
theorem frame_anc_accepted {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (AC.goldilocksAC sp FGP ro)), T.CallAt y i ℓ → ∀ B ∈ ℓ.frame.tree, ∀ X,
      Anc U X B → X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X :=
  frame_anc_acceptedU (hr := hr.toU) (y := y) (hy := hy)

/-- **`Carry_y` from a writer, per head.** For an honest `y` casting its slot-`(s+1)` vote,
under `Sync` from `a ≤ t_s` to at least `t_s + 2Δ`: if each counted vote is of slot `s`, was sent
or admitted by an honest writer `w` at a time in `[t_s, t_s + 2Δ)`, and has a head above `y`'s
`Σ.F` that `w` accepted in `[a, t_s + 2Δ)` (so relayed) or that `y` accepted before the freeze
`t_s + 3Δ` by other means (genesis included), then `Carry_y(s, ·, ·)` holds for the counted
votes. -/
theorem carryAt_of_writer_heads
    {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {a b : Time}
    {s : Nat} (ha : a ≤ sp.ts s)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} {e : AC.Em sp FGP}
    (hc : AC.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hsync : SyncAC (AC.goldilocksAC sp FGP ro) H U a b T ∨
      AC.ServiceWindowBefore H U a (T.time i) T)
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        ((∃ k, T.AcceptAt w k Hv ∧ a ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∨
          AC.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ))) :
    AC.CarryAt T U y i e s CV := by
  refine carryAt_of_served hr
    hini (frame_anc_accepted hr hy) hy hc hs fun v hv => ?_
  obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, Hv, -, hHvr, hFHv, hacc⟩ := hW v hv
  -- the vote: forwarded by `w` from `t_k ∈ [t_s, t_s + 2Δ)`
  refine ⟨hvs, ⟨T.time k, hk1, hk2, fun hdi => hsync.elim
    (fun h => (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl
      (h.1 w hw k v hsend (ha.trans hk1) (by linarith only [hk2, hb]) y hy i ℓ hc.1 hdi)))
    (fun h => h.message w hw k v hsend (ha.trans hk1) y hy i ℓ hc.1 hdi hdi)⟩, Hv, hHvr, ?_⟩
  -- the head: relayed by `w` from its acceptance, or accepted by `y` by other means
  refine hacc.imp (fun ⟨kw, hkw, hakw, hkwt⟩ => ⟨T.time kw, hkwt, fun hdi => hsync.elim
    (fun h => h.2 w hw kw Hv hkw hakw (by linarith only [hkwt, hb]) y hy i ℓ hc.1 hdi hFHv)
    (fun h => h.relay w hw kw Hv hkw hakw y hy i ℓ hc.1 hdi hdi hFHv)⟩) id

/-- **`Carry_y` from a writer, on a window**: `carryAt_of_writer_heads`, with every head that
`w` accepted before `a` (outside the relay window) reaching `y` before the freeze (`hold`). -/
private theorem carryAt_of_writer_service
    {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {a b : Time}
    {s : Nat} (ha : a ≤ sp.ts s)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} {e : AC.Em sp FGP}
    (hc : AC.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hsync : SyncAC (AC.goldilocksAC sp FGP ro) H U a b T ∨
      AC.ServiceWindowBefore H U a (T.time i) T)
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ))
    (hold : ∀ k Hv, T.AcceptAt w k Hv → T.time k < a → Anc U ℓ.frame.F Hv →
      AC.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ)) :
    AC.CarryAt T U y i e s CV := by
  refine carryAt_of_writer_heads hr hini ha hb hw hy hc hs hsync fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact Or.inr (Or.inl hg)
  by_cases hakw : a ≤ T.time kw
  · exact Or.inl ⟨kw, hkw, hakw, hkwt⟩
  · exact Or.inr (hold kw Hv hkw (not_le.1 hakw) hFHv)

/-- Windowed writer transport combines new-source service with old-head catch-up. -/
theorem carryAt_of_writer_window_before {ini}
    (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {a κ b : Time} (hsync : AC.ServiceWindowBefore H U a b T) {s : Nat} (ha : a ≤ sp.ts s)
    (hcatch : CatchACWindowBefore T H U a κ b) (hcatchTime : a + κ ≤ sp.ts s + 3 * sp.Δ)
    {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} {e : AC.Em sp FGP}
    (hc : AC.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) (hi : T.time i ≤ b)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ)) :
    AC.CarryAt T U y i e s CV := by
  have restricted : AC.ServiceWindowBefore H U a (T.time i) T := {
    message := fun x hx k m hm h0 z hz j ℓ hc hd ht =>
      hsync.message x hx k m hm h0 z hz j ℓ hc (hd.trans hi) ht
    relay := fun x hx k B hB h0 z hz j ℓ hc hd ht hanc =>
      hsync.relay x hx k B hB h0 z hz j ℓ hc (hd.trans hi) ht hanc }
  refine carryAt_of_writer_service hr hini (b := sp.ts s + 2 * sp.Δ) ha le_rfl
    hw hy hc hs (Or.inr restricted) hW ?_
  intro k B hk hka hanc
  have hslot := (AC.castAt_spec hr hy hc).2.1
  have hstart : sp.ts (s + 1 : Nat) ≤ T.time i :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨j, -, hj, hjt⟩ := hcatch.relay w hw k B hk hka y hy i ℓ hc.1
    (by rw [hts] at hstart; linarith only [hstart, hcatchTime, sp.toParams.hΔ]) hi hanc
  exact Or.inr ⟨j, hj, hjt.trans_le hcatchTime⟩

/-- **What a result's writer did with its counted votes**: each was admitted (or sent) by the
writer at a time in `[t_s, t_s + 2Δ)` (its stamp, below the resolution time), and its head extends
the result and is genesis or was accepted by the writer before `t_s + 2Δ` (the head's stamp). -/
theorem result_writer {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : AC.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hR : AC.ResultAt T X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit X k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt X k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓX, ⟨hcX, htick, -, -⟩, -, rfl⟩ := hR
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hΦXU : ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw X hX i₀ ℓX hcX with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
  have hvs : v.slot = s := AC.state_pool_slot sp hr hini hX i₀ s v hvp
  -- the stamps of the vote and of its head are before `t_s + 2Δ`
  obtain ⟨hvst, hbst⟩ : (T.state X i₀).voteStamp v < AC.ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (T.state X i₀).blockStamp v.head < AC.ETime.of (sp.ts s + 2 * sp.Δ) := by
    unfold AC.resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [AC.ETime.of])
    · split_ifs at hvres
      · exact absurd hvres (by simp [AC.ETime.of])
      · exact max_lt_iff.1 hvres
  refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
  · rcases AC.pool_origin hr hini hX i₀ v (by rw [hvs]; exact hvp) with
      ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
    · rw [hst, AC.etime_of_lt_of] at hvst
      exact ⟨k, hsend, (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
    · -- a restart's vote is of a block of slot at most `slot(t_k) ≤ s`, so of slot below `s`
      exfalso
      rw [hst, AC.etime_of_lt_of] at hvst
      have hBv := (AC.frame_validPayload sp hr hX hck B hB).1 v hvB
      have hBs := AC.frame_slot_le sp hr hX hck B hB
      have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (T.time k) := fun h => by
        have := (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
        rw [hts] at this; linarith only [this, hvst, hΔ]
      omega
  · rcases frame_anc_accepted hr hX i₀ ℓX hcX R hR R Relation.ReflTransGen.refl with
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
      have h := (blockStamp_ge_of_accept hr hX hacc (AC.accept_ne_genesis sp hr hX hacc) i₀
        hki).trans_lt
        hbst
      rw [AC.etime_of_lt_of] at h
      linarith only [h, hge]

/-- **What an optimistic selection's writer did with its counted votes**: each was admitted (or
sent) by the writer at a time in `[t_s, t_s + 2Δ)` (at or before the selection), and its head
extends the selection and is genesis or was accepted by the writer before `t_s + 2Δ` (it is in
the writer's frame at the selection). -/
theorem optimistic_writer_votes {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U T ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {C : AC.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hO : AC.OptimisticLockAt T x i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit x k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt x k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓx, A, hp, hsl, hsel, rfl⟩ := hO
  have hc := hp.1
  have hti : T.time i₀ < sp.ts (sp.slot (T.time i₀)) + 2 * sp.Δ := by
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with h
    all_goals first
      | cases hsel
      | exact not_le.1 fun h' => h (Or.inr (Or.inr h'))
  rw [hsl] at hti
  have hΦU : ℓx.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx i₀ ℓx hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  rintro v ⟨hvA, R, hR, hRr, hCR⟩
  have hv1 := AC.optimisticPoint_pool_post hr hx hp s hvA
  have hvs : v.slot = s := AC.state_pool_slot sp hr hini hx (i₀ + 1) s v hv1
  refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
  · rcases AC.pool_origin hr hini hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
      ⟨k, hk, hsend, -, hsl'⟩ | ⟨k, hk, ℓk, hck, -, -, B, hB, hvB⟩
    · exact ⟨k, hsend, (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl'), lt_of_le_of_lt (hr.time_mono (by omega)) hti⟩
    · -- a restart's vote is of a block of slot at most `slot(t_k) ≤ s`, so of slot below `s`
      exfalso
      have hBv := (AC.frame_validPayload sp hr hx hck B hB).1 v hvB
      have hBs := AC.frame_slot_le sp hr hx hck B hB
      have := AC.slot_mono sp (hr.time_nonneg k) (hr.time_mono (show k ≤ i₀ by omega))
      omega
  · rcases frame_anc_accepted hr hx i₀ ℓx hc R hR R Relation.ReflTransGen.refl with
      hg | ⟨k, hk, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk) hti⟩

end Node

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

variable {s₀ : Nat}

end Consensus.Goldilocks.Compose

end
