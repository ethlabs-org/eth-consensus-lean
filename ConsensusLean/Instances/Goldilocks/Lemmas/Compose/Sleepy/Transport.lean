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

Transport and the non-root case of S3 (`SleepyInvariant`): for an origin `C` of label `s` and an
honest slot-`(s+1)` vote whose `Σ.F` is at or below `C`, the counted votes and heads reach the voter
in time (`SA.CarryAt`), and, for a result, every slot-`s` vote of the voter's merged view reaches
the writer (A1.8 (d)). Under `Sync[0, ∞)`: each counted vote was admitted by the writer (so
forwarded) and each counted head accepted by it (so relayed) before `t_s + 2Δ`; the voter is joined
at its vote, so awake since `t_s` with its pool kept, and processes them before `t_s + 3Δ`; the
relay applies since the voter's `Σ.F` is below `C`, below each head. -/

namespace Consensus.Goldilocks.Compose

variable {wm : SA.WriteMode}

open SA (SAParams ReplayOrder Vote Payload)


/-! ### One honest node over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- `frame_anc_accepted` with the unlock given. -/
theorem frame_anc_acceptedU
    {u : Nat → Set SA.Lock} {ini} (hr : SA.ACLocalRunU wm u H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), T.CallAt y i ℓ → ∀ B ∈ ℓ.frame.tree, ∀ X,
      Anc U X B → X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    have step : ∀ Φ : SA.Frm sp.n FGP, Φ.tree ⊆ U →
        (SA.goldilocksSA sp FGP ro).CallOK U Φ (T.time i) ℓ.call ℓ.frame →
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
theorem frame_anc_accepted {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), T.CallAt y i ℓ → ∀ B ∈ ℓ.frame.tree, ∀ X,
      Anc U X B → X.root = sp.genesisRoot ∨ ∃ k ≤ i, T.AcceptAt y k X :=
  frame_anc_acceptedU (hr := hr.toU) (y := y) (hy := hy)

/-- **`Carry_y` from a writer, per head.** For an honest `y` casting its slot-`(s+1)` vote,
under `Sync` from `a ≤ t_s` to at least `t_s + 2Δ`: if each counted vote is of slot `s`, was sent
or admitted by an honest writer `w` at a time in `[t_s, t_s + 2Δ)`, and has a head above `y`'s
`Σ.F` that `w` accepted in `[a, t_s + 2Δ)` (so relayed) or that `y` accepted before the freeze
`t_s + 3Δ` by other means (genesis included), then `Carry_y(s, ·, ·)` holds for the counted
votes. -/
theorem carryAt_of_writer_heads
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b : Time}
    {s : Nat} (ha : a ≤ sp.ts s)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a b T ∨
      SA.ServiceWindowBefore H U a (T.time i) T)
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        ((∃ k, T.AcceptAt w k Hv ∧ a ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∨
          SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ))) :
    SA.CarryAt T U y i e s CV := by
  refine carryAt_of_served hr
    (fun _ => SA.voteStart_initial _) (frame_anc_accepted hr hy) hy hc hs fun v hv => ?_
  obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, Hv, -, hHvr, hFHv, hacc⟩ := hW v hv
  -- the vote: forwarded by `w` from `t_k ∈ [t_s, t_s + 2Δ)`
  refine ⟨hvs, ⟨T.time k, hk1, hk2, fun hdi => hsync.elim
    (fun h => (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
      (h.1 w hw k v hsend (ha.trans hk1) (by linarith only [hk2, hb]) y hy i ℓ hc.1 hdi)))
    (fun h => h.message w hw k v hsend (ha.trans hk1) y hy i ℓ hc.1 hdi hdi)⟩, Hv, hHvr, ?_⟩
  -- the head: relayed by `w` from its acceptance, or accepted by `y` by other means
  refine hacc.imp (fun ⟨kw, hkw, hakw, hkwt⟩ => ⟨T.time kw, hkwt, fun hdi => hsync.elim
    (fun h => h.2 w hw kw Hv hkw hakw (by linarith only [hkwt, hb]) y hy i ℓ hc.1 hdi hFHv)
    (fun h => h.relay w hw kw Hv hkw hakw y hy i ℓ hc.1 hdi hdi hFHv)⟩) id

/-- **`Carry_y` from a writer, on a window**: `carryAt_of_writer_heads`, with every head that
`w` accepted before `a` (outside the relay window) reaching `y` before the freeze (`hold`). -/
private theorem carryAt_of_writer_service
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b : Time}
    {s : Nat} (ha : a ≤ sp.ts s)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a b T ∨
      SA.ServiceWindowBefore H U a (T.time i) T)
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ))
    (hold : ∀ k Hv, T.AcceptAt w k Hv → T.time k < a → Anc U ℓ.frame.F Hv →
      SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  refine carryAt_of_writer_heads hr ha hb hw hy hc hs hsync fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact Or.inr (Or.inl hg)
  by_cases hakw : a ≤ T.time kw
  · exact Or.inl ⟨kw, hkw, hakw, hkwt⟩
  · exact Or.inr (hold kw Hv hkw (not_le.1 hakw) hFHv)

/-- Writer transport with a sender window, including pre-window accepted heads. -/
theorem carryAt_of_writer_win (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b : Time}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a b T) {s : Nat} (ha : a ≤ sp.ts s)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ))
    (hold : ∀ k Hv, T.AcceptAt w k Hv → T.time k < a → Anc U ℓ.frame.F Hv →
      SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ)) :
    SA.CarryAt T U y i e s CV :=
  carryAt_of_writer_service hr ha hb hw hy hc hs (Or.inl hsync) hW hold

/-- Windowed writer transport combines new-source service with old-head catch-up. -/
theorem carryAt_of_writer_window_before (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {a κ b : Time} (hsync : SA.ServiceWindowBefore H U a b T) {s : Nat} (ha : a ≤ sp.ts s)
    (hcatch : CatchACWindowBefore T H U a κ b) (hcatchTime : a + κ ≤ sp.ts s + 3 * sp.Δ)
    {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) (hi : T.time i ≤ b)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  have restricted : SA.ServiceWindowBefore H U a (T.time i) T := {
    message := fun x hx k m hm h0 z hz j ℓ hc hd ht =>
      hsync.message x hx k m hm h0 z hz j ℓ hc (hd.trans hi) ht
    relay := fun x hx k B hB h0 z hz j ℓ hc hd ht hanc =>
      hsync.relay x hx k B hB h0 z hz j ℓ hc (hd.trans hi) ht hanc }
  refine carryAt_of_writer_service hr (b := sp.ts s + 2 * sp.Δ) ha le_rfl
    hw hy hc hs (Or.inr restricted) hW ?_
  intro k B hk hka hanc
  have hslot := (SA.castAt_spec hr hy hc).2.1
  have hstart : sp.ts (s + 1 : Nat) ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨j, -, hj, hjt⟩ := hcatch.relay w hw k B hk hka y hy i ℓ hc.1
    (by rw [hts] at hstart; linarith only [hstart, hcatchTime, sp.toParams.hΔ]) hi hanc
  exact Or.inr ⟨j, hj, hjt.trans_le hcatchTime⟩

/-- Writer transport needs recipient service only up to the receiving vote's time. -/
theorem carryAt_of_writer_before (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {b : Time} (hsync : SA.ServiceBefore H U b T) {s : Nat}
    {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) (hi : T.time i ≤ b)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt w k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  have hs0 : 0 ≤ sp.ts s := by
    have := sp.toParams.hΔ
    simp only [SAParams.ts]
    positivity
  exact carryAt_of_writer_window_before hr hsync hs0
    (κ := 0) ⟨fun _ _ k _ _ hk => absurd hk (not_lt.2 (hr.time_nonneg k))⟩
    (by linarith only [hs0, sp.toParams.hΔ]) hw hy hc hs hi hW

/-- **What a result's writer did with its counted votes**: each was admitted (or sent) by the
writer at a time in `[t_s, t_s + 2Δ)` (its stamp, below the resolution time), and its head extends
the result and is genesis or was accepted by the writer before `t_s + 2Δ` (the head's stamp). -/
theorem result_writer {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
    (hini : ∀ y, SA.VoteStart sp.genesisRoot (ini y))
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt T X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit X k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt X k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓX, ⟨hcX, htick, -, -⟩, -, rfl⟩ := hR
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hΦXU : ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw X hX i₀ ℓX hcX with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
  have hvs : v.slot = s := SA.state_pool_slot_from sp hr hini hX i₀ s v hvp
  -- the stamps of the vote and of its head are before `t_s + 2Δ`
  obtain ⟨hvst, hbst⟩ : (T.state X i₀).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (T.state X i₀).blockStamp v.head < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    unfold SA.resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [SA.ETime.of])
    · split_ifs at hvres
      · exact absurd hvres (by simp [SA.ETime.of])
      · exact max_lt_iff.1 hvres
  refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
  · rcases SA.pool_origin_from hr hini hX i₀ v (by rw [hvs]; exact hvp) with
      ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
    · rw [hst, SA.etime_of_lt_of] at hvst
      exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
    · -- a restart's vote is of a block of slot at most `slot(t_k) ≤ s`, so of slot below `s`
      exfalso
      rw [hst, SA.etime_of_lt_of] at hvst
      have hBv := (SA.frame_validPayload sp hr hX hck B hB).1 v hvB
      have hBs := SA.frame_slot_le sp hr hX hck B hB
      have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (T.time k) := fun h => by
        have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
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
      have h := (blockStamp_ge_of_accept hr hX hacc (SA.accept_ne_genesis sp hr hX hacc) i₀
        hki).trans_lt
        hbst
      rw [SA.etime_of_lt_of] at h
      linarith only [h, hge]

/-- **What an optimistic selection's writer did with its counted votes**: each was admitted (or
sent) by the writer at a time in `[t_s, t_s + 2Δ)` (at or before the selection), and its head
extends the selection and is genesis or was accepted by the writer before `t_s + 2Δ` (it is in
the writer's frame at the selection). -/
theorem optimistic_writer_votes {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
    (hini : ∀ y, SA.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt T x i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit x k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt x k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓx, A, hp, hsl, hsel, rfl⟩ := hO
  have hc := hp.1
  have hti : T.time i₀ < sp.ts (sp.slot (T.time i₀)) + 2 * sp.Δ := by
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with h
    all_goals first
      | cases hsel
      | exact not_le.1 fun h' => h (Or.inr (Or.inr h'))
  rw [hsl] at hti
  have hΦU : ℓx.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx i₀ ℓx hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  rintro v ⟨hvA, R, hR, hRr, hCR⟩
  have hv1 := SA.optimisticPoint_pool_post hr hx hp s hvA
  have hvs : v.slot = s := SA.state_pool_slot_from sp hr hini hx (i₀ + 1) s v hv1
  refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
  · rcases SA.pool_origin_from hr hini hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
      ⟨k, hk, hsend, -, hsl'⟩ | ⟨k, hk, ℓk, hck, -, -, B, hB, hvB⟩
    · exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl'), lt_of_le_of_lt (hr.time_mono (by omega)) hti⟩
    · -- a restart's vote is of a block of slot at most `slot(t_k) ≤ s`, so of slot below `s`
      exfalso
      have hBv := (SA.frame_validPayload sp hr hx hck B hB).1 v hvB
      have hBs := SA.frame_slot_le sp hr hx hck B hB
      have := SA.slot_mono sp (hr.time_nonneg k) (hr.time_mono (show k ≤ i₀ by omega))
      omega
  · rcases frame_anc_accepted hr hx i₀ ℓx hc R hR R Relation.ReflTransGen.refl with
      hg | ⟨k, hk, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk) hti⟩

end Node

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The window premises' `Sync[t_{s₀}, b − Δ]` on the AC projection, on any `[a, b']` inside. -/
private theorem window_sync {b : Time} {s₀ : Nat} (hrun : GoldilocksRun proposer dg H tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {a b' : Time} (ha : sp.ts s₀ ≤ a) (hb : b' ≤ b - sp.Δ) :
    SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) H (tr.HonestBlocks H) a b' tr.projAC :=
  have hs := (sleepyWindow_iff.1 hwin).2.1
  sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer ΔF a b'
    hrun.toLocalRun
    { deltaF := hs.deltaF
      delta_le := hs.delta_le
      message := fun x hx i m h hw => hs.message x hx i m h ⟨ha.trans hw.1, hw.2.trans hb⟩
      block := fun x hx i B h hw => hs.block x hx i B h ⟨ha.trans hw.1, hw.2.trans hb⟩
      relay := fun x hx i B h hw => hs.relay x hx i B h ⟨ha.trans hw.1, hw.2.trans hb⟩
      attestation := fun x hx i a h hw => hs.attestation x hx i a h ⟨ha.trans hw.1, hw.2.trans hb⟩ }

/-- **A block that an honest writer accepted before `t_{s₀}` reaches `y` before `T`**, at the AC
level, from the run-level form of `SleepyBase.old_blocks`. -/
theorem acceptedBefore_of_old (hrun : GoldilocksRun proposer dg H tr) {s₀ : Nat} {y : Fin sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {T : Time}
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) Φ.F B → SA.AcceptedBefore tr.projAC y B T)
    {w : Fin sp.n} (hw : w ∈ H) :
    ∀ k B, tr.projAC.AcceptAt w k B → tr.projAC.time k < sp.ts s₀ →
      Anc (tr.HonestBlocks H) Φ.F B → SA.AcceptedBefore tr.projAC y B T := by
  rintro k B ⟨ℓk, hck, hb⟩ hk hF
  obtain ⟨k', rfl, hc', ht⟩ := acBlock_prev hrun.toLocalRun hw (projAC_callAt.1 hck) hb
  exact hold w hw k' B hc' (lt_of_eq_of_lt ht hk) hF

/-- An honest slot-`(s+1)` vote is cast from `t_{s+1} = t_s + 4Δ` on. -/
private theorem vote_time_ge (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hc
  have hsi : sp.slot (tr.projAC.time i) = s + 1 := by omega
  have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s + 1 : Nat) : Int)).2 (by rw [hsi])
  rw [hts] at this
  exact this

variable {s₀ : Nat}

/-- **A result's counted votes reach the next voters, on a window** (`Carry_y`): under the
window premises from slot `s₀ ≤ s` to `b`, at a vote at a time `≤ b`, with the heads accepted
before `t_{s₀}` caught up (`hold`, `SleepyBase.old_blocks`), when the voter's `Σ.F` is at or below
the result. -/
theorem result_carry_win {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat} (hs₀ : s₀ ≤ s) {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hW := result_writer hr (fun _ => SA.voteStart_initial _) hX hR
  have := vote_time_ge hrun hnc hy hc hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  exact carryAt_of_writer_win hr
    (window_sync hrun hwin (b' := sp.ts s + 2 * sp.Δ) le_rfl (by linarith only [this, hib, hΔ]))
    (ts_le_ts hs₀) le_rfl
    hX hy hc hs (fun v hv => by
      obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := hW v hv
      exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩)
    (acceptedBefore_of_old hrun hold hX)

/-- A result's counted votes reach a next-slot voter using only deadlines within `b`. -/
theorem result_carry_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsync : SleepyServiceBefore tr H ΔF b) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  refine carryAt_of_writer_before hr hsync.ac
    hX hy hc hs hib ?_
  intro v hv
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := result_writer hr
    (fun _ => SA.voteStart_initial _) hX hR v hv
  exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩

/-- **An optimistic selection's counted votes reach the next voters, on a window** (`Carry_y`), as
`result_carry_win`. -/
theorem optimistic_carry_win {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} (hs₀ : s₀ ≤ s) {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC x i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hW := optimistic_writer_votes hr (fun _ => SA.voteStart_initial _) hx hO
  have := vote_time_ge hrun hnc hy hc hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  exact carryAt_of_writer_win hr
    (window_sync hrun hwin (b' := sp.ts s + 2 * sp.Δ) le_rfl (by linarith only [this, hib, hΔ]))
    (ts_le_ts hs₀) le_rfl
    hx hy hc hs (fun v hv => by
      obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := hW v hv
      exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩)
    (acceptedBefore_of_old hrun hold hx)

/-- An optimistic writer's votes reach a next-slot voter within the recipient horizon. -/
theorem optimistic_carry_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsync : SleepyServiceBefore tr H ΔF b) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC x i₀ s C CV) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  refine carryAt_of_writer_before hr hsync.ac
    hx hy hc hs hib ?_
  intro v hv
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := optimistic_writer_votes hr
    (fun _ => SA.voteStart_initial _) hx hO v hv
  exact ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans hCHv, h₃⟩

/-- A result's writer pool needs only sources since the result slot's start. -/
theorem result_writer_pool_window_before {a b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsync : SA.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} (ha : a ≤ sp.ts s)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) (hi₀ : tr.time i₀ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
  obtain ⟨ℓX, hupd, -, -⟩ := hR
  exact SA.writer_merged_window_before (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc)
    hsync hX ha hupd hi₀ hy hc hs

/-- A1.8 (d) uses AC recipient service only through the result's writer update. -/
theorem result_writer_pool_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) (hi₀ : tr.time i₀ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} :=
  result_writer_pool_window_before hrun hnc hsync
    hX (by have := sp.toParams.hΔ; simp only [SAParams.ts]; positivity) hR hi₀ hy hc hs

/-- **A1.8 (d) on the window from slot `s₀ ≤ s` to `b`**, for a result within `b`. -/
theorem result_writer_pool_win {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat} (hs₀ : s₀ ≤ s) {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) (hi₀ : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨ℓX, hupd, -, -⟩ := hR
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hupd.2.2.1
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ :=
      (cast_head_fcRoot hrun'.localRun hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  exact SA.writer_merged hrun' hX hupd hy hc hs
    (window_sync hrun hwin (b' := tr.time i) (ts_le_ts hs₀) (by linarith only [hti, ht₀, hi₀]))

end Consensus.Goldilocks.Compose

end
