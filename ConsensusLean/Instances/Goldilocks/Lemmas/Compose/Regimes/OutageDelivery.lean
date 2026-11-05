module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks: the delivery halves of `vote_held_before_early` under receiver service

Under `ReceiverServiceAfter` from `g ≤ t_q + Δ`, at a receiver call from `t_q + 2Δ` with no restart
after `t_q`:
* D1: a held block (genesis, or accepted by an honest node by `t_q + Δ`) above `Σ.F` is in the
  frame, stamped before `t_q + 2Δ`;
* D2: an honest slot-`q` vote is pooled, stamped before `t_q + 2Δ`;
* D3: with its head's facts as premises, the vote is resolved before `t_q + 2Δ`.

The proofs restate `honest_vote_at_update_of_sync` (`Compose/Service/Batch.lean`) without head
facts. No voter tree, vote domain or vote head is read: the late-cast arm uses
`SA.vote_signer_slot` and `SA.one_vote_per_slot` in place of `cast_head_fcRoot`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-! ### Deadlines -/

section Deadline

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} {T : ACTrace A}

/-- The deadline from `g ≤ t + Δ` of an object of time at most `t + Δ`, with every restart at or
before `t`, is at most `t + 2Δ`. -/
private theorem deadline_le_two {y : Fin P.n} {c : Nat} {t g : Time}
    (h : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ t) (hg : g ≤ t + P.Δ) {τ : Time}
    (hτ : τ ≤ t + P.Δ) : T.deadline y c (max τ g) ≤ t + 2 * P.Δ := by
  have h₁ := ac_deadline_le_of_restarts h (max τ g)
  have hΔ : 0 < P.Δ := P.hΔ
  linarith [max_le (max_le hτ hg) (show t ≤ t + P.Δ by linarith)]

end Deadline

/-! ### The delivery halves over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The block of the tree with the root of one of its blocks. -/
private theorem lookup_of_mem {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {B : SA.Blk sp.n FGP}
    (hB : B ∈ Φ.tree) : SA.lookup Φ B.root = some B := by
  have hin : SA.InTree Φ B.root := ⟨B, hB, rfl⟩
  unfold SA.lookup
  rw [dite_eq_left_of_eq_true (eq_true hin)]
  obtain ⟨h₁, h₂⟩ := hin.choose_spec
  rw [hΦ.coherent.1 h₁ hB h₂]

/-- D1 (L1, relay half). A block that is genesis or that an honest node accepted by `t_q + Δ`,
and that is above the receiver's `Σ.F`, is in the receiver's frame and stamped before
`t_q + 2Δ` at every receiver call from `t_q + 2Δ` with no restart after `t_q`. -/
theorem accepted_held_before_early (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H) (hS : ReceiverServiceAfter H U g y T)
    {q c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : T.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ T.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ sp.ts q)
    {B : SA.Blk sp.n FGP} (hBU : B ∈ U)
    (hacc : B.root = sp.genesisRoot ∨
      ∃ x ∈ H, ∃ k, T.AcceptAt x k B ∧ T.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F B) :
    B ∈ ℓ.frame.tree ∧ (T.state y c).blockStamp B.root < SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hy hc
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ →
      T.deadline y k (max τ g) ≤ sp.ts q + 2 * sp.Δ := fun k hk _ hτ =>
    deadline_le_two (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hg hτ
  have hab : SA.AcceptedBefore T y B (sp.ts q + 2 * sp.Δ) ∧ B ∈ ℓ.frame.tree := by
    rcases hacc with hgen | ⟨x, hx, k, hax, hkt⟩
    · refine ⟨Or.inl hgen, ?_⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy c ℓ hc
      obtain rfl : B = G := hU.1 hBU hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF with h | ⟨Q, -, hQ⟩
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    · obtain ⟨ky, hky, hay, hkyt⟩ :=
        hS.relay x hx k B hax c ℓ hc (by linarith [hdl c le_rfl _ hkt]) hF
      exact ⟨Or.inr ⟨ky, hay, hkyt.trans_le (hdl ky hky _ hkt)⟩,
        SA.mem_tree_of_acceptAt sp hr hy hay hky hc hF⟩
  obtain ⟨hab, hBt⟩ := hab
  exact ⟨hBt, SA.blockStamp_lt_of_acceptedBefore sp hr hy hc hBt hab
    (fun k hk hrk => by linarith [hres k hk hrk]) (Or.inl hct)⟩

/-- D2 (L1, message half). An honest slot-`q` vote is in the receiver's pool, with a stamp
before `t_q + 2Δ`, at every receiver call from `t_q + 2Δ` with no restart after `t_q`. -/
theorem vote_pooled_before_early (hrun : SA.ACRun proposer T H U)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H) (hS : ReceiverServiceAfter H U g y T)
    {q c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : T.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ T.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = q) :
    e.msg ∈ (T.state y c).pool q ∧
      (T.state y c).voteStamp e.msg < SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ →
      T.deadline y k (max τ g) ≤ sp.ts q + 2 * sp.Δ := fun k hk _ hτ =>
    deadline_le_two (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hg hτ
  obtain ⟨hxv, hxs⟩ := SA.vote_signer_slot hr hx hv
  have htj : T.time j ≤ sp.ts q + sp.Δ := by
    have h := SA.vote_time_le hr hx hv
    rwa [← hxs, hes] at h
  have hsj : sp.ts q ≤ T.time j :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) q).2 (by omega)
  obtain ⟨ℓv, hcv, hev⟩ := id hv
  -- the vote is processed by the receiver before `t_q + 2Δ` (fresh processing only)
  obtain ⟨k', hk'c, hjk', hp, hk'dl⟩ := hS.message x hx j e.msg ⟨ℓv, hcv, Or.inl ⟨e, hev, rfl⟩⟩
    c ℓ hc (by linarith [hdl c le_rfl _ htj])
  have hk'lt : T.time k' < sp.ts q + 2 * sp.Δ := hk'dl.trans_le (hdl k' hk'c _ htj)
  have hk'c' : k' < c := lt_of_le_of_ne hk'c (by rintro rfl; linarith)
  have hsk' : sp.slot (T.time k') = q :=
    SA.slot_of_mem sp q (hsj.trans hjk') (by rw [hts]; linarith)
  have hnr : ∀ r, k' + 1 ≤ r → r < c + 1 → ¬ T.RestartAt y r := by
    rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hp
    have h₁ := hprev k' (by omega) ℓ' hc'
    have h₂ := hres r (by omega) ⟨ℓr, hcr, hrr⟩
    linarith
  have hpk' : e.msg ∈ (T.state y (k' + 1)).pool q := by
    rcases SA.held_of_processAt hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · rw [hes] at ha hb
      obtain ⟨ja, -, ea, hea, hea'⟩ :=
        hrun.honest.pool_vote y hy _ q a ha (by rw [hav, hxv]; exact hx)
      obtain ⟨jb, -, eb, heb, heb'⟩ :=
        hrun.honest.pool_vote y hy _ q b hb (by rw [hbv, hxv]; exact hx)
      rw [hav, hxv] at hea
      rw [hbv, hxv] at heb
      obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp FGP ro H U T hr x hx ja jb ea eb hea heb
        (by rw [hea', heb', SA.state_pool_slot sp hr hy _ q a ha,
          SA.state_pool_slot sp hr hy _ q b hb])
      exact absurd (hea'.symm.trans heb') hab
  have hpool : e.msg ∈ (T.state y c).pool q :=
    SA.pool_mono hr hy (show k' + 1 ≤ c by omega) (fun r h₁ h₂ => hnr r h₁ (by omega)) q hpk'
  refine ⟨hpool, ?_⟩
  rcases SA.pool_origin hr hy c e.msg (by rw [hes]; exact hpool) with
    ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
  · rw [hst₁, SA.etime_of_lt_of]
    by_cases hk₁k' : k₁ ≤ k'
    · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
    · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, he₁m⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
      · -- the receiver cast the vote itself: it is the voter, and the cast is the vote at `j`
        have hv₁ : SA.VoteAt T y k₁ e₁ := ⟨ℓ₁, hc₁, he₁⟩
        have hyx : y = x := by
          rw [← (SA.vote_signer_slot hr hy hv₁).1, he₁m, hxv]
        rw [hyx] at hv₁
        obtain ⟨rfl, -⟩ := SA.one_vote_per_slot sp FGP ro H U T hr x hx k₁ j e₁ e hv₁ hv
          (by rw [he₁m])
        linarith
      · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
          (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hes]; exact hpk')) hn₁
  · rw [hst₁, SA.etime_of_lt_of]
    linarith [hres k₁ hk₁.le ⟨ℓ₁, hc₁, hr₁⟩]

/-- D3 (L1 without its head facts). The vote is pooled, its head is held, and the vote is
resolved before `t_q + 2Δ`, given the head's slot bound and its acceptance by the voter by
`t_q + Δ` (or genesis). -/
theorem vote_resolved_before_early (hrun : SA.ACRun proposer T H U)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H) (hS : ReceiverServiceAfter H U g y T)
    {q c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : T.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ T.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = q) {Hd : SA.Blk sp.n FGP} (hHdU : Hd ∈ U)
    (hHdr : Hd.root = e.msg.head) (hHds : Hd.slot ≤ q)
    (hHdacc : Hd.root = sp.genesisRoot ∨
      ∃ k, T.AcceptAt x k Hd ∧ T.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F Hd) :
    e.msg ∈ (T.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      SA.resolutionTime (T.state y c) ℓ.frame e.msg < SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hpool, hvst⟩ := vote_pooled_before_early hrun hy hS hc hct hg hres hx hv hes
  obtain ⟨hHdt, hbst⟩ := accepted_held_before_early hrun.localRun hy hS hc hct hg hres hHdU
    (hHdacc.imp_right fun ⟨k, h⟩ => ⟨x, hx, k, h⟩) hF
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hrun.localRun hy hc
  have hHs : Hd.slot ≤ e.msg.slot := by rw [hes]; exact hHds
  refine ⟨hpool, hHdt, ?_⟩
  unfold SA.resolutionTime
  rw [← hHdr, lookup_of_mem hΦ hHdt]
  dsimp only
  simp only [not_lt.2 hHs, ↓reduceIte]
  exact max_lt hvst hbst

end Node

end Consensus.Goldilocks.Compose
