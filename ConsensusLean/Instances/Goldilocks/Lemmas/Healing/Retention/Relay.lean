module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: relay after the GST and the writers of fast locks

The relay of a counted vote and its head to a next
voter under `Sync` on a window `[a₀, b]` instead of `Sync[0, b]` (`carryAt_of_writer_window`,
the Sleepy `carryAt_of_writer_before` with the extra premise that the head was accepted at or after
`a₀`), and what a writer of a fast lock did with its counted votes before `t_s + 2Δ`
(`fastLock_writer`, main's Sleepy `result_writer` / `optimistic_writer` for both origins of a fast
lock, the fast test's selected block instead of the result), with the counted votes nonempty
(`fastLock_counted_nonempty`). The timing and writer-carry steps are the shared ones of
`Compose/Sleepy/Timing` and `Compose.carryAt_of_writer_heads`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Vote Payload)
open Compose

/-- Reset service projects to AC synchrony on any source window after GST. Only
message and relay service are used; signed-attestation processing times play no role. -/
theorem ResetService.syncAC {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF b lo hi : Time}
    (hs : ResetService tr H g ΔF b) (hrun : GoldilocksRun proposer dg H tr)
    (hg : g ≤ lo) : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) lo hi tr.projAC := by
  have h := hrun.toLocalRun
  constructor
  · intro x hx i m hsa hai _ y hy j ℓ hc hdl
    obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, projAC_callAt.1 hc₀, by
      rw [projAC_state h hx] at hm
      exact hm⟩
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x hx i m hsa' y hy j
      ⟨_, projAC_callAt.1 hc⟩ (by rw [he, ← projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, ?_⟩
    · rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
      exacts [⟨ℓ', projAC_callAt.2 hc', Or.inl hm'⟩, ⟨ℓ', projAC_callAt.2 hc', Or.inr hm'⟩]
    · rw [projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using hlt
  · intro x hx i B hacc hai _ y hy j ℓ hc hdl hanc
    obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := projAC_callAt.1 hc
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev h hx (projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y hy j _ hc).1]
      rfl
    have hgi : g ≤ tr.time i' := hti ▸ hg.trans hai
    have he : max (tr.time i') g = tr.time i' := max_eq_left hgi
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x hx i' B hi' hgi y hy j ⟨_, hc⟩
      (by rw [he, hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := accept_next h hy hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.2 hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
    rw [projAC_deadline, htk, ← hti]
    rw [he] at hlt
    simpa only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] using hlt

/-! ### One honest node over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- At an honest vote, the pool of a slot other than the vote's, and the stamps of its votes,
are those of the state after the vote's call (main's Sleepy `readPoint_slot`). -/
theorem readPoint_pool_of_ne (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) {σ : Nat} (hσ : e.msg.slot ≠ σ) :
    (T.state y (i + 1)).pool σ = e.readPoint.pool σ ∧
      ∀ u : Vote sp.n, u.slot = σ → (T.state y (i + 1)).voteStamp u = e.readPoint.voteStamp u := by
  rw [Trace.state_succ_of_call T hc.1, SA.post_of_castAt hr hy hc]
  have hopt : ∀ A : SA.SAState sp.n,
      (SA.optimisticConfirmation sp A ℓ.frame (T.time i)).pool = A.pool ∧
        (SA.optimisticConfirmation sp A ℓ.frame (T.time i)).voteStamp = A.voteStamp := by
    intro A
    unfold SA.optimisticConfirmation SA.updateLatestConfirmed
    split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  rw [(hopt _).1, (hopt _).2]
  unfold SA.admitVote
  split_ifs
  · exact ⟨rfl, fun _ _ => rfl⟩
  · exact ⟨rfl, fun _ _ => rfl⟩
  · exact ⟨Function.update_of_ne (Ne.symm hσ) _ _,
      fun u hu => Function.update_of_ne (by rintro rfl; exact hσ hu) _ _⟩

/-- **`Carry_y` from a writer, after the GST** (the Sleepy
`carryAt_of_writer_before` with `Sync[a₀, b]` instead of `Sync[0, b]`). For an honest `y` casting
its slot-`(s+1)` vote, with `a₀ ≤ t_s` and `t_s + 2Δ ≤ b`: if each counted vote is of slot `s`, was
sent or admitted by an honest writer `w` at a time in `[t_s, t_s + 2Δ)`, and has a head above `y`'s
`Σ.F` that is genesis or that `w` accepted in `[a₀, t_s + 2Δ)`, then `Carry_y(s, ·, ·)` holds for
the counted votes. -/
theorem carryAt_of_writer_window (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ b T) {s : Nat}
    (ha₀ : a₀ ≤ sp.ts s) (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨
          ∃ k, T.AcceptAt w k Hv ∧ a₀ ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  refine carryAt_of_writer_heads hr ha₀ hb hw hy hc hs (Or.inl hsync) fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases hacc with hg | hw'
  · exact Or.inr (Or.inl hg)
  · exact Or.inl hw'

/-- **Head-only relay to a voter, after the GST**: a block `W`
above the voter's `Σ.F` that an honest writer accepted in `[a₀, t_s + 2Δ)`, under `Sync[a₀, b]`
with `t_s + 2Δ ≤ b`, is in the voter block tree of every honest vote of a slot `> s` (relayed to
the voter, joined at its vote, before `t_{s} + 3Δ`, at or before its vote freeze). -/
theorem relay_mem_voterBlockTree (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ b T) {w : Fin sp.n}
    (hw : w ∈ H) {kw : Nat} {W : SA.Blk sp.n FGP} (hkw : T.AcceptAt w kw W)
    (ha₀ : a₀ ≤ T.time kw) {s : Nat} (hkwt : T.time kw < sp.ts s + 2 * sp.Δ)
    (hb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e)
    (hs : s + 1 ≤ e.msg.slot) (hF : Anc U ℓ.frame.F W) :
    W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hm : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).2 (by omega)
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [← hys] at this
  have hdl : ∀ k ≤ i, T.deadline y k (T.time kw) < sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro k hk
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') (T.time kw)
    have h₂ := max_lt (show T.time kw < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hkwt, hsm])
      (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hΔ])
    change T.deadline y k (T.time kw) ≤ max (T.time kw) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ
      at h₁
    linarith only [h₂, h₁]
  obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.2 w hw kw W hkw ha₀ (by linarith only [hkwt, hb]) y hy i
    ℓ hc.1 (by linarith only [hΔ, hm, hti, hdl i le_rfl]) hF
  have hkyt' : T.time ky < SA.freeze sp e.msg.slot := by
    have := hdl ky hky
    unfold SA.freeze
    linarith only [hkyt, this]
  have hfz : SA.freeze sp e.msg.slot ≤ T.time i := by unfold SA.freeze; linarith only [hΔ, hm, hti]
  have hWt := SA.mem_tree_of_acceptAt sp hr hy hacc hky hc.1 hF
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hWt (Or.inr ⟨ky, hacc, hkyt'⟩)
    (fun k hk hrk => lt_of_le_of_lt (hrsy k hk hrk) (by unfold SA.freeze; linarith only [hΔ]))
    (Or.inl hfz)
  have hne : ∀ B, ℓ.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (SA.accept_new sp hr hy ⟨ℓ, hc.1, hcall⟩).1 ℓ hc.1
    obtain rfl : B₀ = W := hU.1 ((SA.frameIn_of_callAt hr hy hc.1).2 hB₀)
      ((SA.frameIn_of_callAt hr hy hc.1).2 hWt) hB.symm
    have heq := SA.accept_unique sp hr hy hacc ⟨ℓ, hc.1, hcall⟩
    rw [heq] at hkyt'
    linarith only [hkyt', hfz]
  rw [← SA.readPoint_blockStamp hr hy hc hne] at hbs
  exact ⟨hWt, Or.inl hbs⟩

/-- A counted head reaches the actual voter freeze through either window service or
catch-up of an old acceptance. Only recipient observations through `b` are used. -/
private theorem relay_mem_voterBlockTree_window_aux
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b : Time}
    (hsync : SyncACWindowBefore H U a b T)
    {w y : Fin sp.n} (hw : w ∈ H) (hy : y ∈ H) {kw i s : Nat} {W : SA.Blk sp.n FGP}
    (hkw : T.AcceptAt w kw W) (ht : T.time kw < sp.ts s + 2 * sp.Δ)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hcatch : T.time kw < a → ∃ ky ≤ i, T.AcceptAt y ky W ∧ T.time ky < SA.freeze sp e.msg.slot)
    (hF : Anc U ℓ.frame.F W) :
    W ∈ ℓ.frame.tree ∧ e.readPoint.blockStamp W.root < SA.ETime.of (SA.freeze sp e.msg.slot) := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hm : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).2 (by omega)
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [← hys] at this
  have hdl : ∀ k ≤ i, T.deadline y k (T.time kw) < sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro k hk
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') (T.time kw)
    have h₂ := max_lt (show T.time kw < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [ht, hsm])
      (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hΔ])
    change T.deadline y k (T.time kw) ≤ max (T.time kw) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ
      at h₁
    linarith only [h₂, h₁]
  have haccepted : ∃ ky ≤ i, T.AcceptAt y ky W ∧ T.time ky < SA.freeze sp e.msg.slot := by
    by_cases ha : a ≤ T.time kw
    · obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.relay w hw kw W hkw ha y hy i ℓ hc.1
        (by linarith only [hi, hΔ, hm, hti, hdl i le_rfl])
        (by linarith only [hΔ, hm, hti, hdl i le_rfl]) hF
      refine ⟨ky, hky, hacc, ?_⟩
      have := hdl ky hky
      unfold SA.freeze
      linarith only [hkyt, this]
    · exact hcatch (lt_of_not_ge ha)
  obtain ⟨ky, hky, hacc, hkyt⟩ := haccepted
  have hfz : SA.freeze sp e.msg.slot ≤ T.time i := by unfold SA.freeze; linarith only [hΔ, hm, hti]
  have hWt := SA.mem_tree_of_acceptAt sp hr hy hacc hky hc.1 hF
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hWt (Or.inr ⟨ky, hacc, hkyt⟩)
    (fun k hk hrk => lt_of_le_of_lt (hrsy k hk hrk) (by unfold SA.freeze; linarith only [hΔ]))
    (Or.inl hfz)
  have hne : ∀ B, ℓ.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (SA.accept_new sp hr hy ⟨ℓ, hc.1, hcall⟩).1 ℓ hc.1
    obtain rfl : B₀ = W := hU.1 ((SA.frameIn_of_callAt hr hy hc.1).2 hB₀)
      ((SA.frameIn_of_callAt hr hy hc.1).2 hWt) hB.symm
    have heq := SA.accept_unique sp hr hy hacc ⟨ℓ, hc.1, hcall⟩
    rw [heq] at hkyt
    linarith only [hkyt, hfz]
  rw [← SA.readPoint_blockStamp hr hy hc hne] at hbs
  exact ⟨hWt, hbs⟩

/-- Post-start acceptance relay needs no catch-up premise. -/
theorem relay_mem_voterBlockTree_window_after
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b : Time}
    (hsync : SyncACWindowBefore H U a b T)
    {w y : Fin sp.n} (hw : w ∈ H) (hy : y ∈ H) {kw i s : Nat} {W : SA.Blk sp.n FGP}
    (hkw : T.AcceptAt w kw W) (ha : a ≤ T.time kw) (ht : T.time kw < sp.ts s + 2 * sp.Δ)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hF : Anc U ℓ.frame.F W) : W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  obtain ⟨hW, hstamp⟩ := relay_mem_voterBlockTree_window_aux hr hsync hw hy hkw ht hc hs hi
    (fun h => False.elim (not_lt_of_ge ha h)) hF
  exact ⟨hW, Or.inl hstamp⟩

/-- Old acceptances use catch-up; post-start acceptances use window relay.
The strict stamp is at the actual emission read point, suitable for iterating the unanimity
propagation (`unanimous_next_votes_of_witness`). -/
theorem relay_readPoint_stamp_window_before
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b κ : Time}
    (hsync : SyncACWindowBefore H U a b T) (hcatch : CatchACWindowBefore T H U a κ b)
    {w y : Fin sp.n} (hw : w ∈ H) (hy : y ∈ H) {kw i s : Nat} {W : SA.Blk sp.n FGP}
    (hkw : T.AcceptAt w kw W) (ht : T.time kw < sp.ts s + 2 * sp.Δ)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F W) :
    W ∈ ℓ.frame.tree ∧ e.readPoint.blockStamp W.root < SA.ETime.of (SA.freeze sp e.msg.slot) := by
  apply relay_mem_voterBlockTree_window_aux hr hsync hw hy hkw ht hc hs hi ?_ hF
  intro ha
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti : sp.ts e.msg.slot ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hm : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  obtain ⟨ky, hky, hacc, hkyt⟩ := hcatch.relay w hw kw W hkw ha y hy i ℓ hc.1
    (by linarith only [hcatchTime, hΔ, hti, hm]) hi hF
  refine ⟨ky, hky, hacc, ?_⟩
  unfold SA.freeze
  linarith only [hcatchTime, hkyt]

/-- Relay and catch-up place an accepted block in the later frozen voter domain. -/
theorem relay_mem_voterBlockTree_window_before
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b κ : Time}
    (hsync : SyncACWindowBefore H U a b T) (hcatch : CatchACWindowBefore T H U a κ b)
    {w y : Fin sp.n} (hw : w ∈ H) (hy : y ∈ H) {kw i s : Nat} {W : SA.Blk sp.n FGP}
    (hkw : T.AcceptAt w kw W) (ht : T.time kw < sp.ts s + 2 * sp.Δ)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F W) : W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  obtain ⟨hW, hstamp⟩ := relay_readPoint_stamp_window_before hr hsync hcatch hw hy
    hkw ht hc hs hi hcatchTime hF
  exact ⟨hW, Or.inl hstamp⟩

/-- **What the writer of a fast lock did with its counted votes** (main's Sleepy
`result_writer` and `optimistic_writer`, for the selected block): each was admitted (or sent) by
the writer at a time in `[t_s, t_s + 2Δ)`, and its head extends the selected block and is genesis
or was accepted by the writer before `t_s + 2Δ`. -/
theorem fastLock_writer (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {D : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt T x i₀ s D CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit x k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U D Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt x k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rcases hfl with ⟨ℓX, C, ⟨hcX, htick, -, -⟩, -, -, -, rfl⟩ | ⟨ℓx, A, hp, hsl, hsel, rfl⟩
  · have hΦXU : ℓX.frame.tree ⊆ U := (SA.frameIn_of_callAt hr hx hcX).2
    rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
    have hvs : v.slot = s := SA.state_pool_slot sp hr hx i₀ s v hvp
    obtain ⟨hvst, hbst⟩ : (T.state x i₀).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) ∧
        (T.state x i₀).blockStamp v.head < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
      unfold SA.resolutionTime at hvres
      split at hvres
      · exact absurd hvres (by simp [SA.ETime.of])
      · split_ifs at hvres
        · exact absurd hvres (by simp [SA.ETime.of])
        · exact max_lt_iff.1 hvres
    refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
    · rcases SA.pool_origin hr hx i₀ v (by rw [hvs]; exact hvp) with
        ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
      · rw [hst, SA.etime_of_lt_of] at hvst
        exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
          (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
      · exfalso
        rw [hst, SA.etime_of_lt_of] at hvst
        have hBv := (SA.frame_validPayload sp hr hx hck B hB).1 v hvB
        have hBs := SA.frame_slot_le sp hr hx hck B hB
        have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (T.time k) := fun h => by
          have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
          rw [hts] at this; linarith only [hΔ, hvst, this]
        omega
    · rcases frame_anc_accepted hr hx i₀ ℓX hcX R hR R Relation.ReflTransGen.refl with
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
        have h := (blockStamp_ge_of_accept hr hx hacc (SA.accept_ne_genesis sp hr hx hacc) i₀
          hki).trans_lt hbst
        rw [SA.etime_of_lt_of] at h
        linarith only [hge, h]
  · have hc := hp.1
    have hti : T.time i₀ < sp.ts (sp.slot (T.time i₀)) + 2 * sp.Δ := by
      unfold SA.optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel with h
      all_goals first
        | cases hsel
        | exact not_le.1 fun h' => h (Or.inr (Or.inr h'))
    rw [hsl] at hti
    have hΦU : ℓx.frame.tree ⊆ U := (SA.frameIn_of_callAt hr hx hc).2
    rintro v ⟨hvA, R, hR, hRr, hCR⟩
    have hv1 := SA.optimisticPoint_pool_post hr hx hp s hvA
    have hvs : v.slot = s := SA.state_pool_slot sp hr hx (i₀ + 1) s v hv1
    refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
    · rcases SA.pool_origin hr hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
        ⟨k, hk, hsend, -, hsl'⟩ | ⟨k, hk, ℓk, hck, -, -, B, hB, hvB⟩
      · exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
          (by rw [← hvs]; exact_mod_cast hsl'), lt_of_le_of_lt (hr.time_mono (by omega)) hti⟩
      · exfalso
        have hBv := (SA.frame_validPayload sp hr hx hck B hB).1 v hvB
        have hBs := SA.frame_slot_le sp hr hx hck B hB
        have := SA.slot_mono sp (hr.time_nonneg k) (hr.time_mono (show k ≤ i₀ by omega))
        omega
    · rcases frame_anc_accepted hr hx i₀ ℓx hc R hR R Relation.ReflTransGen.refl with
        hg | ⟨k, hk, hacc⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk) hti⟩

/-- **A fast lock counts a vote**: the fast test passes with half of the committee (`n ≥ 1`), the
optimistic test with three quarters, and each counted validator has a counted vote. -/
theorem fastLock_counted_nonempty (hcommittee : 0 < sp.committeeSize)
    {x : Fin sp.n} {i₀ s : Nat} {D : SA.Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt T x i₀ s D CV) : CV.Nonempty := by
  rcases hfl with ⟨ℓX, C, -, -, hsel, rfl⟩ | ⟨ℓx, A, -, hsl, hsel, rfl⟩
  · obtain ⟨⟨-, -, hfast⟩, -⟩ := SA.deepest_mem hsel
    unfold SA.FastTest SA.confirmationScore at hfast
    dsimp only at hfast
    generalize hS : SA.supporters _ _ _ _ = S at hfast
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    rw [← hS] at hi
    obtain ⟨hi, v, ⟨hvp, hvres⟩, rfl, -, hv⟩ := hi
    exact ⟨v, hvp, hi, hvres, hv⟩
  · unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    obtain ⟨⟨-, hq, -⟩, -⟩ := SA.deepest_mem hsel
    generalize hS : SA.optimisticVoters _ _ _ _ _ = S at hq
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    rw [← hS] at hi
    obtain ⟨v, hv, -, hvD⟩ := hi
    exact ⟨v, hsl ▸ hv, hvD⟩

/-- A raw writer supplies a counted head above the target, accepted before the slot freeze. -/
theorem raw_writer_relay_source
    (hcommittee : 0 < sp.committeeSize)
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat}
    {B C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : SA.ResultAt T x i s C CV ∨ SA.FastLockAt T x i s C CV)
    (hBC : Anc U B C) :
    ∃ v ∈ CV, ∃ D ∈ U, D.root = v.head ∧ Anc U B D ∧
      (D.root = sp.genesisRoot ∨
        ∃ q, T.AcceptAt x q D ∧ T.time q < sp.ts s + 2 * sp.Δ) := by
  have hne : CV.Nonempty := by
    rcases hwriter with hR | hF
    · have hm := SA.result_majority hR
      obtain ⟨w, v, hv, _⟩ := Set.nonempty_of_ncard_ne_zero
        (s := {w | ∃ v ∈ CV, v.val = w}) (by omega)
      exact ⟨v, hv⟩
    · exact fastLock_counted_nonempty hcommittee hF
  obtain ⟨v, hv⟩ := hne
  have hw := hwriter.elim (fun hR => result_writer hr hx hR v hv)
    (fun hF => fastLock_writer hr hx hF v hv)
  obtain ⟨D, hD, hDr, hCD, hacc⟩ := hw.2.2
  exact ⟨v, hv, D, hD, hDr, hBC.trans hCD, hacc⟩

/-- An ancestor of an early source is available in a later voter's frozen block tree.
The source may be genesis or an actual acceptance; old acceptances use Catch. -/
theorem voterBlockTree_of_relay_source
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b κ : Time}
    (hsync : SyncACWindowBefore H U a b T) (hcatch : CatchACWindowBefore T H U a κ b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {i s : Nat}
    {B D : SA.Blk sp.n FGP} (hDU : D ∈ U) (hBD : Anc U B D)
    (hsource : D.root = sp.genesisRoot ∨
      ∃ q, T.AcceptAt x q D ∧ T.time q < sp.ts s + 2 * sp.Δ)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F B) : B ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  rcases hsource with hgen | ⟨q, hq, hqt⟩
  all_goals obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  · have hFD := hF.trans hBD
    obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy _ _ hc.1
    have hDG : D = G := hr.coherent.1 hDU hGU (hgen.trans hGr.symm)
    subst D
    have hDt : G ∈ ℓ.frame.tree := by
      obtain heq | ⟨c, _, hp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFD
      · exact heq ▸ hΦ.rooted.1
      · exact absurd (hp.2.2.symm.trans hGp) (Option.some_ne_none _)
    have hΔ := sp.toParams.hΔ
    obtain ⟨_, hys, hyj, _⟩ := SA.castAt_spec hr hy hc
    have hti : sp.ts e.msg.slot ≤ T.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hys])
    have hfz : SA.freeze sp e.msg.slot < T.time i := by
      unfold SA.freeze SAParams.ts at hti ⊢
      linarith only [hΔ, hti]
    have hrs : ∀ k ≤ i, T.RestartAt y k → T.time k < SA.freeze sp e.msg.slot := by
      have hj' : SA.joined sp (T.post i) (T.time i) := by
        unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
      intro k hk hrk
      have ht := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
      rw [← hys] at ht
      unfold SA.freeze
      linarith only [hΔ, ht]
    have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hDt (Or.inl hGr)
      hrs (Or.inl hfz.le)
    have hne : ∀ X, ℓ.call = .block X → G.root ≠ X.root := by
      intro X hcall heq
      exact SA.accept_ne_genesis sp hr hy ⟨ℓ, hc.1, hcall⟩ (heq.symm.trans hGr)
    rw [← SA.readPoint_blockStamp hr hy hc hne] at hbs
    have hBt := SA.frame_mem_of_between sp hr.coherent hΦ hΦU hDt hBD hF
    exact SA.voterBlockTree_anc hr hy hc G ⟨hDt, Or.inl hbs⟩ B
      (SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hBt hBD hDt)
  · have hDt := relay_mem_voterBlockTree_window_before hr hsync hcatch hx hy hq hqt
      hc hs hi hcatchTime (hF.trans hBD)
    have hBt := SA.frame_mem_of_between sp hr.coherent hΦ hΦU hDt.1 hBD hF
    exact SA.voterBlockTree_anc hr hy hc D hDt B
      (SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hBt hBD hDt.1)

/-- A raw writer's ancestor is available in a later voter's frozen block tree. -/
theorem raw_writer_voterBlockTree_window_before
    (hcommittee : 0 < sp.committeeSize)
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {a b κ : Time}
    (hsync : SyncACWindowBefore H U a b T) (hcatch : CatchACWindowBefore T H U a κ b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {j i s : Nat}
    {B C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : SA.ResultAt T x j s C CV ∨ SA.FastLockAt T x j s C CV)
    (hBC : Anc U B C) {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : T.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F B) : B ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  obtain ⟨v, _, D, hDU, _, hBD, hsource⟩ := raw_writer_relay_source hcommittee hr hx hwriter hBC
  exact voterBlockTree_of_relay_source hr hsync hcatch hx hy hDU hBD hsource
    hc hs hi hcatchTime hF

end Node

end Consensus.Goldilocks.Healing

end
