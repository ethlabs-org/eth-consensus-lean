module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The outage over AC traces, the restored side: delivery under service from `b₁`

The delivery rows of the outage census (`Compose/Regimes/OutageDelivery`, and `carryAt_after` of
`Obligations/OutageS5/Step`), stated over an AC trace of the SA with the unlock given at a write
mode (`ACLocalRunU wm u`, `ACRunU wm u`), with the receiver-scoped service after `g`
(`Compose.ReceiverServiceAfter H U g y tr` at every honest `y`) as hypothesis:

* `vote_signer_slotAC`: an honest vote is its caster's, of the slot of its cast time;
* D1 (`accepted_held_before_earlyAC`): a held block (genesis, or accepted by an honest node by
  `t_q + Δ`) above the call's `Φ.F` is in the call's frame, stamped before `t_q + 2Δ`;
* D2 (`vote_pooled_before_earlyAC`): an honest slot-`q` vote is pooled, stamped before
  `t_q + 2Δ`;
* D3 (`vote_resolved_before_earlyAC`): with its head's facts as premises, the vote is resolved
  before `t_q + 2Δ`;
* `honest_head_accepted_afterAC`: an honest head of a slot at most `q` above the call's `Φ.F` is
  accepted by an honest slot-`(q+1)` voter before the freeze `t_q + 3Δ`;
* `carryAt_afterAC`: `Carry_y(s, ·, ·)` for honest slot-`s` votes whose heads extend the call's
  `Φ.F`, at an honest slot-`(s+1)` vote.

D1–D3 are read at a receiver call from `t_q + 2Δ` with no restart of the receiver after `t_q`
(an explicit hypothesis, as in the originals); `carryAt_afterAC` derives that from the voter's
joined vote. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {g : Time}

/-! ### Deadlines and votes -/

/-- The deadline from `g ≤ t + Δ` of an object of time at most `t + Δ`, with every restart at or
before `t`, is at most `t + 2Δ`. -/
private theorem deadline_le_two {y : Fin sp.n} {c : Nat} {t : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ t) (hg : g ≤ t + sp.Δ) {τ : Time}
    (hτ : τ ≤ t + sp.Δ) : tr.deadline y c (max τ g) ≤ t + 2 * sp.Δ := by
  have h₁ := Compose.ac_deadline_le_of_restarts h (max τ g)
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  linarith [max_le (max_le hτ hg) (show t ≤ t + sp.Δ by linarith)]

/-- `SA.vote_signer_slot` with the unlock given: an honest vote is its caster's, of the slot of
its cast time. -/
theorem vote_signer_slotAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {e : Em sp FGP} (hv : VoteAt tr x j e) :
    e.msg.val = x ∧ e.msg.slot = sp.slot (tr.time j) := by
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨h₁, h₂, -⟩ := castAt_specU hr hx ⟨hc, he⟩
  exact ⟨h₁, h₂⟩

/-! ### D1–D3 -/

/-- **D1** (L1, relay half; `Compose.accepted_held_before_early` with the unlock given). A block
that is genesis or that an honest node accepted by `t_q + Δ`, and that is above the call's `Φ.F`,
is in the call's frame and stamped before `t_q + 2Δ`, at every honest call from `t_q + 2Δ` with
no restart after `t_q`, under the service from `g ≤ t_q + Δ`. -/
theorem accepted_held_before_earlyAC (hr : ACLocalRunU wm u H U tr)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr)
    {y : Fin sp.n} (hy : y ∈ H) {q c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {B : Blk sp.n FGP} (hBU : B ∈ U)
    (hacc : B.root = sp.genesisRoot ∨
      ∃ x ∈ H, ∃ k, tr.AcceptAt x k B ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F B) :
    B ∈ ℓ.frame.tree ∧ (tr.state y c).blockStamp B.root < ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hS' := hS y hy
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hy hc
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ →
      tr.deadline y k (max τ g) ≤ sp.ts q + 2 * sp.Δ := fun k hk _ hτ =>
    deadline_le_two (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hg hτ
  have hab : AcceptedBefore tr y B (sp.ts q + 2 * sp.Δ) ∧ B ∈ ℓ.frame.tree := by
    rcases hacc with hgen | ⟨x, hx, k, hax, hkt⟩
    · refine ⟨Or.inl hgen, ?_⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy c ℓ hc
      obtain rfl : B = G := hU.1 hBU hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF with h | ⟨Q, -, hQ⟩
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    · obtain ⟨ky, hky, hay, hkyt⟩ :=
        hS'.relay x hx k B hax c ℓ hc (by linarith [hdl c le_rfl _ hkt]) hF
      exact ⟨Or.inr ⟨ky, hay, hkyt.trans_le (hdl ky hky _ hkt)⟩,
        mem_tree_of_acceptAtU sp hr hy hay hky hc hF⟩
  obtain ⟨hab, hBt⟩ := hab
  exact ⟨hBt, blockStamp_lt_of_acceptedBeforeU sp hr hy hc hBt hab
    (fun k hk hrk => by linarith [hres k hk hrk]) (Or.inl hct)⟩

/-- **D2** (L1, message half; `Compose.vote_pooled_before_early` with the unlock given). An honest
slot-`q` vote is in the receiver's pool, with a stamp before `t_q + 2Δ`, at every honest call from
`t_q + 2Δ` with no restart after `t_q`, under the service from `g ≤ t_q + Δ`. -/
theorem vote_pooled_before_earlyAC (hrun : ACRunU wm u proposer tr H U)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr) {y : Fin sp.n} (hy : y ∈ H) {q c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e)
    (hes : e.msg.slot = q) :
    e.msg ∈ (tr.state y c).pool q ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hr := hrun.localRun
  have hS' := hS y hy
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ →
      tr.deadline y k (max τ g) ≤ sp.ts q + 2 * sp.Δ := fun k hk _ hτ =>
    deadline_le_two (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hg hτ
  obtain ⟨hxv, hxs⟩ := vote_signer_slotAC hr hx hv
  have htj : tr.time j ≤ sp.ts q + sp.Δ := by
    have h := vote_time_leU hr hx hv
    rwa [← hxs, hes] at h
  have hsj : sp.ts q ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) q).2 (by omega)
  obtain ⟨ℓv, hcv, hev⟩ := id hv
  -- the vote is processed by the receiver before `t_q + 2Δ` (fresh processing only)
  obtain ⟨k', hk'c, hjk', hp, hk'dl⟩ := hS'.message x hx j e.msg ⟨ℓv, hcv, Or.inl ⟨e, hev, rfl⟩⟩
    c ℓ hc ((hdl c le_rfl _ htj).trans hct)
  have hk'lt : tr.time k' < sp.ts q + 2 * sp.Δ := hk'dl.trans_le (hdl k' hk'c _ htj)
  have hk'c' : k' < c := lt_of_le_of_ne hk'c (by rintro rfl; exact hk'lt.not_ge hct)
  have hsk' : sp.slot (tr.time k') = q :=
    slot_of_mem sp q (hsj.trans hjk') (by rw [ts_succ]; linarith only [hk'lt, hΔ])
  have hnr : ∀ r, k' + 1 ≤ r → r < c + 1 → ¬ tr.RestartAt y r := by
    rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hp
    have h₁ := hprev k' (by omega) ℓ' hc'
    have h₂ := hres r (by omega) ⟨ℓr, hcr, hrr⟩
    exact (hsj.trans hjk').not_gt (h₁.trans (hu.trans_le h₂))
  have hpk' : e.msg ∈ (tr.state y (k' + 1)).pool q := by
    rcases held_of_processAtU hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · rw [hes] at ha hb
      obtain ⟨ja, -, ea, hea, hea'⟩ :=
        hrun.honest.pool_vote y hy _ q a ha (by rw [hav, hxv]; exact hx)
      obtain ⟨jb, -, eb, heb, heb'⟩ :=
        hrun.honest.pool_vote y hy _ q b hb (by rw [hbv, hxv]; exact hx)
      rw [hav, hxv] at hea
      rw [hbv, hxv] at heb
      obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr x hx ja jb ea eb hea heb
        (by rw [hea', heb', state_pool_slotU sp hr hy _ q a ha,
          state_pool_slotU sp hr hy _ q b hb])
      exact absurd (hea'.symm.trans heb') hab
  have hpool : e.msg ∈ (tr.state y c).pool q :=
    pool_monoU hr hy (show k' + 1 ≤ c by omega) (fun r h₁ h₂ => hnr r h₁ (by omega)) q hpk'
  refine ⟨hpool, ?_⟩
  rcases pool_originU hr hy c e.msg (by rw [hes]; exact hpool) with
    ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
  · rw [hst₁, etime_of_lt_of]
    by_cases hk₁k' : k₁ ≤ k'
    · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
    · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, he₁m⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
      · -- the receiver cast the vote itself: it is the voter, and the cast is the vote at `j`
        have hv₁ : VoteAt tr y k₁ e₁ := ⟨ℓ₁, hc₁, he₁⟩
        have hyx : y = x := by
          rw [← (vote_signer_slotAC hr hy hv₁).1, he₁m, hxv]
        rw [hyx] at hv₁
        obtain ⟨rfl, -⟩ := one_vote_per_slotU sp FGP ro H U tr hr x hx k₁ j e₁ e hv₁ hv
          (by rw [he₁m])
        linarith only [htj, hΔ]
      · exact absurd (pool_monoU hr hy (show k' + 1 ≤ k₁ by omega)
          (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hes]; exact hpk')) hn₁
  · rw [hst₁, etime_of_lt_of]
    exact (hres k₁ hk₁.le ⟨ℓ₁, hc₁, hr₁⟩).trans_lt
      (lt_add_of_pos_right _ (mul_pos two_pos hΔ))

/-- **D3** (L1 without its head facts; `Compose.vote_resolved_before_early` with the unlock
given). The vote is pooled, its head is in the call's frame, and the vote is resolved before
`t_q + 2Δ`, given the head's slot bound and its acceptance by the voter by `t_q + Δ` (or
genesis). -/
theorem vote_resolved_before_earlyAC (hrun : ACRunU wm u proposer tr H U)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr) {y : Fin sp.n} (hy : y ∈ H) {q c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e)
    (hes : e.msg.slot = q) {Hd : Blk sp.n FGP} (hHdU : Hd ∈ U)
    (hHdr : Hd.root = e.msg.head) (hHds : Hd.slot ≤ q)
    (hHdacc : Hd.root = sp.genesisRoot ∨
      ∃ k, tr.AcceptAt x k Hd ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F Hd) :
    e.msg ∈ (tr.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      resolutionTime (tr.state y c) ℓ.frame e.msg < ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hpool, hvst⟩ := vote_pooled_before_earlyAC hrun hS hy hc hct hg hres hx hv hes
  obtain ⟨hHdt, hbst⟩ := accepted_held_before_earlyAC hrun.localRun hS hy hc hct hg hres hHdU
    (hHdacc.imp_right fun ⟨k, h⟩ => ⟨x, hx, k, h⟩) hF
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hrun.localRun hy hc
  have hHs : Hd.slot ≤ e.msg.slot := by rw [hes]; exact hHds
  refine ⟨hpool, hHdt, ?_⟩
  unfold resolutionTime
  rw [← hHdr, lookup_of_mem hΦ hHdt]
  dsimp only
  simp only [not_lt.2 hHs, ↓reduceIte]
  exact max_lt hvst hbst

/-! ### `Carry_y` after the outage -/

/-- **An honest head of a slot at most `q` is accepted by `y` before the freeze `t_q + 3Δ`**
(`Compose.honest_head_accepted_after` with the unlock given), under the service from
`g ≤ t_q + Δ`, at an honest slot-`(q+1)` vote of `y` whose call's `Φ.F` it extends: its voter
accepted it by `t_q + Δ` (or it is genesis), and `y`, joined (so with no restart after `t_q`),
receives it by `max(τ, g) + Δ ≤ t_q + 2Δ`. -/
theorem honest_head_accepted_afterAC (hr : ACLocalRunU wm u H U tr)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr)
    {y : Fin sp.n} (hy : y ∈ H) {q : Nat} (hg : g ≤ sp.ts q + sp.Δ) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = q + 1) {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {e' : Em sp FGP}
    (hv : VoteAt tr x k e') (hs' : e'.msg.slot ≤ q) {Hd : Blk sp.n FGP} (hHd : Hd ∈ U)
    (hHdr : Hd.root = e'.msg.head) (hFHd : Anc U ℓ.frame.F Hd) :
    AcceptedBefore tr y Hd (sp.ts q + 3 * sp.Δ) := by
  have hS' := hS y hy
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓ', hcx, hex⟩ := hv
  -- the head is in its voter's frame, and the vote is cast by `t_{slot} + Δ ≤ t_q + Δ`
  obtain ⟨Hd₀, hHd₀t, hHd₀r, -⟩ := honest_head_frameU hr hx ⟨hcx, hex⟩
  obtain ⟨-, hΦx⟩ := frameIn_of_callAtU hr hx hcx
  obtain rfl : Hd₀ = Hd := hr.coherent.1 (hΦx hHd₀t) hHd (hHd₀r.trans hHdr.symm)
  have hkt : tr.time k ≤ sp.ts q + sp.Δ := by
    have h1 := cast_time_leAC hr hx ⟨hcx, hex⟩
    have h2 : sp.ts e'.msg.slot ≤ sp.ts q := (ts_le_iff sp).2 (by exact_mod_cast hs')
    linarith only [h1, h2]
  obtain ⟨hrs, hti⟩ := vote_restartsAC hr hy hc hs
  -- its voter accepted it (or it is genesis)
  rcases Compose.frame_anc_acceptedU hr hx k ℓ' hcx Hd₀ hHd₀t Hd₀ .refl with
    hgen | ⟨m, hm, hacc⟩
  · exact Or.inl hgen
  have hmt : tr.time m ≤ sp.ts q + sp.Δ := (hr.time_mono hm).trans hkt
  have hdl : ∀ c ≤ i, tr.deadline y c (max (tr.time m) g) ≤ sp.ts q + 2 * sp.Δ :=
    fun c hc' => deadline_le_two (fun k hk hr' => hrs k (hk.trans hc') hr') hg hmt
  obtain ⟨k', hk'i, hAy, hk't⟩ := hS'.relay x hx m Hd₀ hacc i ℓ hc.1
    (by have := hdl i le_rfl; linarith only [this, hti, hΔ]) hFHd
  exact Or.inr ⟨k', hAy, by have := hdl k' hk'i; linarith only [this, hk't, hΔ]⟩

/-- **`Carry_y` after the outage's GST** (`Compose.carryAt_after` with the unlock given): at an
honest slot-`(s+1)` vote of `y`, under the service from `g ≤ t_s + Δ`, `Carry_y(s, ·, ·)` holds
for honest slot-`s` votes whose heads extend the call's `Φ.F`: each is sent by its voter by
`t_s + Δ` and its head accepted by then, so `y` (joined, no restart after `t_s`) holds the vote
and accepts the head and its ancestors before `t_s + 3Δ`. -/
theorem carryAt_afterAC (hr : ACLocalRunU wm u H U tr)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hg : g ≤ sp.ts s + sp.Δ) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hCV : ∀ v ∈ CV, ∃ x ∈ H, ∃ k e', VoteAt tr x k e' ∧ e'.msg = v ∧ v.slot = s ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv) :
    CarryAt tr U y i e s CV := by
  have hS' := hS y hy
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, -, hyj, -⟩ := castAt_specU hr hy hc
  obtain ⟨hrsy, hti⟩ := vote_restartsAC hr hy hc hs
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ → tr.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith only [hΔ])
    change tr.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith only [h₁, h₂]
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · -- the head and its ancestors are accepted before the freeze
    obtain ⟨x, hx, k, e', hv', rfl, hvs, Hv, hHv, hHvr, hFHv⟩ := hCV _ hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    rcases honest_head_accepted_afterAC hr hS hy hg hc hs hx hv' hvs.le hHv hHvr hFHv with
      hgen | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    rcases Compose.frame_anc_acceptedU hr hy ky ℓk hck Hv
      ((accept_newU sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) X hX with hgen | ⟨k, hk, hkX⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt⟩
  · -- the vote is held before the freeze
    obtain ⟨x, hx, k, ev, hvk, hev, hvs, -⟩ := hCV v hv
    obtain ⟨ℓv, hcv, hevv⟩ := id hvk
    have hsend : tr.SendOrAdmit x k v := ⟨ℓv, hcv, Or.inl ⟨ev, hevv, hev⟩⟩
    have hk1 : sp.ts s ≤ tr.time k := by
      have h := (vote_signer_slotAC hr hx hvk).2
      rw [hev, hvs] at h
      exact (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
    have hk2 : tr.time k ≤ sp.ts s + sp.Δ := by
      have h := cast_time_leAC hr hx ⟨hcv, hevv⟩
      rw [hev, hvs] at h
      exact h
    have hmx : max (tr.time k) g < sp.ts s + 2 * sp.Δ :=
      max_lt (by linarith only [hk2, hΔ]) (by linarith only [hg, hΔ])
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hS'.message x hx k v hsend i ℓ hc.1
      (by have := hdl i le_rfl _ hmx; linarith only [this, hti, hΔ])
    have hk'lt : tr.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hmx)
    obtain ⟨ℓ', hc', -⟩ := id hp
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ tr.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ : tr.time r ≤ sp.ts s := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
      linarith only [h₁, h₂, hu, hk1, hkk']
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

end Consensus.Goldilocks.SA

end
