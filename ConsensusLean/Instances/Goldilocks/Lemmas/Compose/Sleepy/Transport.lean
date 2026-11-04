module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: what an origin carries to the next voters

workbench#11 §2.3 (transport) and S3's non-root case: for an origin `C` of label `s` and an honest
slot-`(s+1)` vote whose `Σ.F` is at or below `C`, the counted votes and heads reach the voter in
time (`SA.CarryAt`), and, for a result, every slot-`s` vote of the voter's merged view reaches the
writer (A1.8 (d)). Under `Sync[0, ∞)`: each counted vote was admitted by the writer (so forwarded)
and each counted head accepted by it (so relayed) before `t_s + 2Δ`; the voter is joined at its
vote, so awake since `t_s` with its pool kept, and processes them before `t_s + 3Δ`; the relay
applies since the voter's `Σ.F` is below `C`, below each head. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)


/-! ### One honest node over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- **Frames are closed under acceptance**: every ancestor (inside `U`) of a block of an honest
node's frame at a call is genesis or was accepted by the node at that call or an earlier one. -/
theorem frame_anc_accepted (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
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

/-- At an honest vote, the pool of a slot other than the vote's, and the stamps of its votes,
are those of the state after the vote's call. -/
private theorem readPoint_slot (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
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
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hsi : sp.slot (T.time i) = s + 1 := by omega
  have hti : sp.ts s + 4 * sp.Δ ≤ T.time i := by
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s + 1 : Nat) : Int)).2 (by rw [hsi])
    rwa [hts] at this
  -- the voter's restarts up to its vote are at or before `t_s`
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k ≤ sp.ts s := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [hsi, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by push_cast; ring] at this
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ → T.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := ac_deadline_le_of_restarts (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith)
    change T.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · -- the head: relayed to `y` before `t_s + 3Δ`, with its ancestors
    obtain ⟨-, -, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    -- `y` accepted the head before the freeze: relayed, or by other means
    have hyacc : SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ) := by
      rcases hacc with ⟨kw, hkw, hakw, hkwt⟩ | hacc
      · have hdi : T.deadline y i (T.time kw) ≤ T.time i := by
          linarith [hdl i le_rfl _ hkwt]
        have delivered := hsync.elim
          (fun h => h.2 w hw kw Hv hkw hakw (by linarith) y hy i ℓ hc.1 hdi hFHv)
          (fun h => h.relay w hw kw Hv hkw hakw y hy i ℓ hc.1 hdi hdi hFHv)
        obtain ⟨ky, hky, hacc', hkyt⟩ := delivered
        exact Or.inr ⟨ky, hacc', hkyt.trans (hdl ky hky _ hkwt)⟩
      · exact hacc
    rcases hyacc with hg | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt'⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    rcases frame_anc_accepted hr hy ky ℓk hck Hv
      ((SA.accept_new sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) X hX with hg | ⟨k, hk, hkX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt'⟩
  · -- the vote: forwarded by `w`, processed by `y` before `t_s + 3Δ` and kept
    obtain ⟨hvs, ⟨k, hsend, hk1, hk2⟩, -⟩ := hW v hv
    have hdi : T.deadline y i (T.time k) ≤ T.time i := by
      linarith [hdl i le_rfl _ hk2]
    have delivered := hsync.elim
      (fun h => (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
        (h.1 w hw k v hsend (ha.trans hk1) (by linarith) y hy i ℓ hc.1 hdi)))
      (fun h => h.message w hw k v hsend (ha.trans hk1) y hy i ℓ hc.1 hdi hdi)
    rcases (SA.messageServedBefore_iff _ _ _ _).mp delivered with delivered | retained
    swap
    · have evidence := (retained.evidence hr hy).weaken (hdl i le_rfl _ hk2).le
      have hheld (u : Vote sp.n) (hus : u.slot = s)
          (hu : SA.HeldBefore (T.state y i) u (sp.ts s + 3 * sp.Δ)) :
          SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
        have hp := SA.heldBefore_mono hr hy (Nat.le_succ i)
          (fun r hr₁ hr₂ hrr => by
            have heq : r = i := by omega
            subst r
            have := hrsy i le_rfl hrr
            linarith) hu
        obtain ⟨hpool, hstamp⟩ := readPoint_slot hr hy hc (σ := s) (by omega)
        exact ⟨by rw [hus, ← hpool]; simpa only [hus] using hp.1,
          by rw [← hstamp u hus]; exact hp.2⟩
      rcases (SA.poolEvidenceBefore_iff _ _ _).mp evidence with hv' |
        ⟨u, w, huw, huv, hwv, hus, hws, hu, hw⟩
      · exact Or.inl (hheld v hvs hv')
      · by_cases huv' : u = v
        · subst u; exact Or.inl (hheld v hvs hu)
        by_cases hwv' : w = v
        · subst w; exact Or.inl (hheld v hvs hw)
        exact Or.inr ⟨u, w, huw, huv', hwv', huv, hwv, hus.trans hvs, hws.trans hvs,
          hheld u (hus.trans hvs) hu, hheld w (hws.trans hvs) hw⟩
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := delivered
    have hk'lt : T.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hk2)
    obtain ⟨ℓ', hc', -⟩ := id hp
    -- no restart of `y` after `k'` up to its vote
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ T.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
      linarith
    have hsk' : sp.slot (T.time k') = s :=
      SA.slot_of_mem sp s (hk1.trans hkk') (by rw [hts]; linarith)
    -- every slot-`s` vote that `y` holds after `k'` is held at the vote, received before the freeze
    have hheld : ∀ u ∈ (T.state y (k' + 1)).pool s,
        SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
      intro u hu
      have hus : u.slot = s := SA.state_pool_slot sp hr hy (k' + 1) s u hu
      obtain ⟨hpool, hstamp⟩ := readPoint_slot hr hy hc (σ := s) (by omega)
      have hu' := SA.pool_mono hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine ⟨by rw [hus, ← hpool]; exact hu', ?_⟩
      rw [← hstamp u hus]
      rcases SA.pool_origin hr hy (i + 1) u (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, SA.etime_of_lt_of]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · -- `y`'s own slot-`s` vote, cast at most `Δ` after `t_s`
            have h := (cast_head_fcRoot hr hy ⟨hc₁, he₁⟩).2
            rw [hus] at h
            linarith
          · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, SA.etime_of_lt_of]
        have := hrsy k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith
    by_cases hv' : v ∈ (T.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases SA.held_of_processAt hr hy hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, SA.state_pool_slot sp hr hy _ s a ha',
          SA.state_pool_slot sp hr hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

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
    (by rw [hts] at hstart; linarith [sp.toParams.hΔ]) hi hanc
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
    (by linarith [sp.toParams.hΔ]) hw hy hc hs hi hW

/-- **What a result's writer did with its counted votes**: each was admitted (or sent) by the
writer at a time in `[t_s, t_s + 2Δ)` (its stamp, below the resolution time), and its head extends
the result and is genesis or was accepted by the writer before `t_s + 2Δ` (the head's stamp). -/
theorem result_writer (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
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
  have hvs : v.slot = s := SA.state_pool_slot sp hr hX i₀ s v hvp
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
  · rcases SA.pool_origin hr hX i₀ v (by rw [hvs]; exact hvp) with
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
        rw [hts] at this; linarith
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
      linarith

/-- **What an optimistic selection's writer did with its counted votes**: each was admitted (or
sent) by the writer at a time in `[t_s, t_s + 2Δ)` (at or before the selection), and its head
extends the selection and is genesis or was accepted by the writer before `t_s + 2Δ` (it is in
the writer's frame at the selection). -/
theorem optimistic_writer_votes (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
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
  have hvs : v.slot = s := SA.state_pool_slot sp hr hx (i₀ + 1) s v hv1
  refine ⟨hvs, ?_, R, hΦU hR, hRr, Anc.mono hΦU hCR, ?_⟩
  · rcases SA.pool_origin hr hx (i₀ + 1) v (by rw [hvs]; exact hv1) with
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
  have hW := result_writer hr hX hR
  have := vote_time_ge hrun hnc hy hc hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  exact carryAt_of_writer_win hr
    (window_sync hrun hwin (b' := sp.ts s + 2 * sp.Δ) le_rfl (by linarith)) (ts_le_ts hs₀) le_rfl
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
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := result_writer hr hX hR v hv
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
  have hW := optimistic_writer_votes hr hx hO
  have := vote_time_ge hrun hnc hy hc hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  exact carryAt_of_writer_win hr
    (window_sync hrun hwin (b' := sp.ts s + 2 * sp.Δ) le_rfl (by linarith)) (ts_le_ts hs₀) le_rfl
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
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := optimistic_writer_votes hr hx hO v hv
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
    linarith
  exact SA.writer_merged hrun' hX hupd hy hc hs
    (window_sync hrun hwin (b' := tr.time i) (ts_le_ts hs₀) (by linarith))

end Consensus.Goldilocks.Compose

end
