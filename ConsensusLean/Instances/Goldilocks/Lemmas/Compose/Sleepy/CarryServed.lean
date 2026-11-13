module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: what a voter keeps of the votes and heads served to it

The voter's side of the transport to a slot-`(s+1)` vote (`SA.CarryAt`), with the deliveries as
premises: each counted vote is served to the voter from a release time in `[t_s, t_s + 2Δ)`, and
each head is relayed from a time before `t_s + 2Δ` or accepted before the freeze `t_s + 3Δ` by
other means. The argument reads one honest node's run over an SA trace; the sender and the
service that delivers are its users' (`carryAt_of_writer_heads` under `Sync[0, ∞)` or a service
window, and the growing-fault transports). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote)

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- At an honest vote, the pool of a slot other than the vote's, and the stamps of its votes,
are those of the state after the vote's call. -/
private theorem readPoint_slot {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
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

/-- **`Carry_y` from what is served.** For an honest `y` casting its slot-`(s+1)` vote whose
frames are closed under its acceptances (`hframe`, `frame_anc_accepted`): if each counted vote is
of slot `s`, has a release time `τ ∈ [t_s, t_s + 2Δ)` at which it is served to `y` (once `y`'s
deadline for `τ` is at or before the vote), and has a head that is relayed to `y` from a time
before `t_s + 2Δ` (likewise) or that `y` accepted before the freeze `t_s + 3Δ` (genesis
included), then `Carry_y(s, ·, ·)` holds for the counted votes. -/
theorem carryAt_of_served {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T ini)
    (hini : ∀ y, SA.VoteStart sp.genesisRoot (ini y))
    {y : Fin sp.n} -- supplier: `frame_anc_accepted`
    (hframe : ∀ k (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), T.CallAt y k ℓ →
      ∀ B ∈ ℓ.frame.tree, ∀ X, Anc U X B →
        X.root = sp.genesisRoot ∨ ∃ k' ≤ k, T.AcceptAt y k' X)
    (hy : y ∈ H) {s i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ τ, sp.ts s ≤ τ ∧ τ < sp.ts s + 2 * sp.Δ ∧
        (T.deadline y i τ ≤ T.time i → SA.MessageServedBefore T y i τ v)) ∧
      ∃ Hv : SA.Blk sp.n FGP, Hv.root = v.head ∧
        ((∃ τ, τ < sp.ts s + 2 * sp.Δ ∧ (T.deadline y i τ ≤ T.time i →
            ∃ k ≤ i, T.AcceptAt y k Hv ∧ T.time k < T.deadline y k τ)) ∨
          SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ))) :
    SA.CarryAt T U y i e s CV := by
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
    have := (SA.joined_awakeU sp FGP ro H U T hr.toU y hy i ℓ hc.1 hj').2 k hk hrk
    rwa [hsi, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by push_cast; ring] at this
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ → T.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := ac_deadline_le_of_restarts (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ from
      lt_add_of_pos_right _ (mul_pos two_pos hΔ))
    change T.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith only [h₁, h₂]
  have hdi : ∀ τ, τ < sp.ts s + 2 * sp.Δ → T.deadline y i τ ≤ T.time i := fun τ hτ => by
    linarith only [hdl i le_rfl τ hτ, hti, hΔ]
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · -- the head: relayed to `y` before `t_s + 3Δ`, with its ancestors
    obtain ⟨-, -, Hv, hHvr, hacc⟩ := hW v hv
    -- `y` accepted the head before the freeze: relayed, or by other means
    have hyacc : SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ) := by
      rcases hacc with ⟨τ, hτ, hdel⟩ | hacc
      · obtain ⟨ky, hky, hacc', hkyt⟩ := hdel (hdi τ hτ)
        exact Or.inr ⟨ky, hacc', hkyt.trans (hdl ky hky _ hτ)⟩
      · exact hacc
    rcases hyacc with hg | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt'⟩
    · -- genesis: the head is the genesis block of `y`'s frame
      refine ⟨G, hGU, hGr.trans (hg.symm.trans hHvr), fun X hX => Or.inl ?_⟩
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    have hHvk : Hv ∈ ℓk.frame.tree := (SA.accept_new sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck
    refine ⟨Hv, (SA.frameIn_of_callAt hr hy hck).2 hHvk, hHvr, fun X hX => ?_⟩
    rcases hframe ky ℓk hck Hv hHvk X hX with hg | ⟨k, hk, hkX⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt'⟩
  · -- the vote: served to `y` before `t_s + 3Δ` and kept
    obtain ⟨hvs, ⟨τ, hk1, hk2, hdel⟩, -⟩ := hW v hv
    have delivered := hdel (hdi τ hk2)
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
            linarith only [this, hti, hΔ]) hu
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
      linarith only [h₁, h₂, hu, hk1, hkk']
    have hsk' : sp.slot (T.time k') = s :=
      SA.slot_of_mem sp s (hk1.trans hkk') (by rw [hts]; linarith only [hk'lt, hΔ])
    -- every slot-`s` vote that `y` holds after `k'` is held at the vote, received before the freeze
    have hheld : ∀ u ∈ (T.state y (k' + 1)).pool s,
        SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
      intro u hu
      have hus : u.slot = s := SA.state_pool_slot_from sp hr hini hy (k' + 1) s u hu
      obtain ⟨hpool, hstamp⟩ := readPoint_slot hr hy hc (σ := s) (by omega)
      have hu' := SA.pool_mono hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine ⟨by rw [hus, ← hpool]; exact hu', ?_⟩
      rw [← hstamp u hus]
      rcases SA.pool_origin_from hr hini hy (i + 1) u (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, SA.etime_of_lt_of]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · -- `y`'s own slot-`s` vote, cast at most `Δ` after `t_s`
            have h := (cast_head_fcRoot_from hr hini hy ⟨hc₁, he₁⟩).2
            rw [hus] at h
            linarith only [h, hΔ]
          · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, SA.etime_of_lt_of]
        have := hrsy k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith only [this, hΔ]
    by_cases hv' : v ∈ (T.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases SA.held_of_processAt hr hy hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, SA.state_pool_slot_from sp hr hini hy _ s a ha',
          SA.state_pool_slot_from sp hr hini hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

end Consensus.Goldilocks.Compose

end
