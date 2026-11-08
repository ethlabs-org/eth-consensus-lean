module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Agree
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The proposal walk after a hand-over

The setting of the seeded service lemmas and the family of blocks the proposal walk of a slot
`s ≥ σ + 1` passes after a hand-over.

* `rowsAbove_height_mono`: the high rows above a height are high rows above every greater one;
* `SeededRun`: a run through `b ≥ T` with the hand-over seed, the reset service, the slot counts
  from `r`, the seeded invariant from `t₁ ≥ t_{r+k}` and conviction below a third;
* `SeededOld`: the members of the healed family of labels at most `s − 2`, and the optimistic
  origins of label `s − 1`;
* `seeded_proposer_holds`: the proposer of slot `s`, at `t_s ≥ t₁`, holds every member of
  `SeededOld`, or it is below its `Σ.F`: a member of label `≤ s − 2` is extended by every honest
  slot-`(s−1)` vote (S2), whose head reaches the proposer; an optimistic origin of label `s − 1`
  by `proposal_holds_old_from`;
* `seeded_walk_passes`: the proposal walk passes every member of `SeededOld`
  (`proposal_walk_passes_from`): held, viable or below `fc_root` (`SeededInvariant.viable`),
  supported at slot `s − 1`, and compatible with the proposer's lock writes of its live locks,
  which are members after the drain. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- `RowsAbove` at a height passes to every greater height. -/
theorem rowsAbove_height_mono {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {Hs : Set (Fin sp.n)}
    {tr₀ : GoldilocksTrace sp ro} {y : Fin sp.n} {i h₀ h₁ : Nat}
    (h : Compose.RowsAbove tr₀ Hs G y i h₀) (hle : h₀ ≤ h₁) : Compose.RowsAbove tr₀ Hs G y i h₁ :=
  Compose.rowsAbove_iff.2 fun X hX a ha hav hE hh =>
    Compose.rowsAbove_iff.1 h X hX a ha hav hE (hle.trans hh)

/-- **The seeded setting through `b`**: a run with the hand-over seed at `T ≤ b`, the reset
service, the slot counts from `r`, the seeded invariant from `t₁ ≥ t_{r+k}` and conviction below
a third. -/
structure SeededRun (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF T : Time) (r σ : Nat) (t₁ b : Time) : Prop where
  run : Growing.GoldilocksRun proposer dg H tr
  noColl : NoCollRun dg tr
  seed : HandoverSeed tr H proposer dg g ΔF T r σ
  service : Healing.Growing.ResetService tr H g ΔF b
  bounds : SleepyBoundsFrom tr H r b
  inv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b
  conv : ChainConvictedBelow tr H
  horizon : T ≤ b
  drain : sp.ts (r + sp.k : Nat) ≤ t₁

variable {T : Time} {r σ : Nat} {t₁ b : Time}

/-- The reset service with its catch-up is the sleepy service from `ḡ`, with catch-up `2Δ`. -/
theorem SeededRun.sync (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) :
    SleepyServiceFrom tr H ΔF (SA.gbar g) (2 * sp.Δ) b :=
  sleepyServiceFrom_of_reset hS.run hS.service hS.seed.catchRun (by linarith [sp.toParams.hΔ])

/-- `ḡ + 20Δ ≤ t_l` for every label `l ≥ r`. -/
theorem SeededRun.gbar_le (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {l : Nat}
    (hl : r ≤ l) : SA.gbar g + 20 * sp.Δ ≤ sp.ts l :=
  hS.seed.timing.2.2.trans (ts_le_ts hl)

/-- A node honest at a time `t ≥ t_{r+k}`, read at or before cut `i` with `t ≤ time i`, has an AC
call before `i` from `t_{r−k−3}` on. -/
theorem SeededRun.called (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {y : Fin sp.n}
    {i : Nat} {t : Time} (hy : y ∈ H t) (ht : sp.ts (r + sp.k : Nat) ≤ t)
    (hti : t ≤ tr.time i) :
    ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c :=
  seeded_reader_called_at hS.run hS.seed hy ht hti

/-- **A live lock of a node honest at a cut at a time `≥ t_{r+k}` has label at least `r`**: its
expiry is at most `k` slots after its label (`LocksWF`). -/
theorem SeededRun.live_label (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) (hdt : sp.ts (r + sp.k : Nat) ≤ tr.time i)
    {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks) (hlive : l.LiveAt sp (tr.time i)) :
    r ≤ l.slot := by
  have hd := hS.run.time_nonneg i
  have hwf : SA.LocksWF sp (tr.state y i).ac.locks := by
    have h := Compose.locksWF_state (hS.run.upTo hd) (hS.noColl.upTo _) hy i
    rwa [RunTrace.upTo_state_of_le hS.run.time_mono le_rfl] at h
  have hcap := hwf.cap hl
  have hsl := (SA.ts_le_iff_le_slot sp hd _).1 hdt
  change sp.slot (tr.time i) ≤ l.expiry at hlive
  push_cast at hsl
  omega

/-- **The old family of slot `s` after a hand-over**: the members of the healed family of labels
at most `s − 2`, and the optimistic origins of label `s − 1`. -/
def SeededOld (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g : Time) (r : Nat)
    (b : Time) (s : Nat) (C : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  (∃ l, HealedOrigin tr H g r (r + sp.k - 1) C l b ∧ l + 2 ≤ s) ∨
    ∃ x k CV, x ∈ H (tr.time k) ∧ SA.OptimisticLockAt tr.projAC x k (s - 1) C CV

theorem seededOld_iff {s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} :
    SeededOld tr H g r b s C ↔ (∃ l, HealedOrigin tr H g r (r + sp.k - 1) C l b ∧ l + 2 ≤ s) ∨
      ∃ x k CV, x ∈ H (tr.time k) ∧ SA.OptimisticLockAt tr.projAC x k (s - 1) C CV :=
  Iff.rfl

/-- An optimistic origin of a label `m` has its event before `t_{m+1}`. -/
theorem optimistic_time_lt (hrun : Growing.GoldilocksRun proposer dg H tr) {x : Fin sp.n}
    {k m : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.OptimisticLockAt tr.projAC x k m C CV) : tr.time k < sp.ts (m + 1 : Nat) := by
  obtain ⟨ℓ, A, _, hs, _⟩ := h
  change sp.slot (tr.time k) = m at hs
  by_contra ht
  have hle := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) ((m + 1 : Nat) : Int)).1
    (le_of_not_gt ht)
  rw [hs] at hle
  omega

/-- **Every member of the old family is a member of the healed family**, of a label below `s`,
given `t_s ≤ b` and `r + k ≤ s` (an optimistic origin of label `s − 1 ≥ r + k − 1`). -/
theorem SeededOld.member (hrun : Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : SeededOld tr H g r b s C) (hsb : sp.ts s ≤ b)
    (hrs : r + sp.k ≤ s) : ∃ l < s, HealedOrigin tr H g r (r + sp.k - 1) C l b := by
  have hk := sp.two_le_k
  rcases h with ⟨l, hC, hl⟩ | ⟨x, k, CV, hx, hO⟩
  · exact ⟨l, by omega, hC⟩
  refine ⟨s - 1, by omega, .of_origin (by omega) (originWithin_iff.2 ⟨x, k, CV, hx, ?_, Or.inr hO⟩)⟩
  have := optimistic_time_lt hrun hO
  rw [show s - 1 + 1 = s by omega] at this
  exact this.le.trans hsb

/-! ### The proposer of a slot after the split slot -/

/-- `t_{s−1}` in its natural form, for `s > 0`. -/
theorem ts_pred {s : Nat} (hs : 0 < s) : sp.ts ((s : Int) - 1) = sp.ts (s - 1 : Nat) := by
  congr 1
  push_cast [Nat.cast_sub (show 1 ≤ s by omega)]
  ring

/-- The timing of the slot `s` of a proposal after the split slot: the catch-up from `ḡ` is over
by `t_{s−1}`. -/
theorem SeededRun.slot_timing (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {s : Nat}
    (hs : σ + 1 ≤ s) :
    0 < s ∧ r + sp.k ≤ s ∧ SA.gbar g + 2 * sp.Δ ≤ sp.ts ((s : Int) - 1) ∧
      SA.gbar g + 2 * sp.Δ ≤ max (sp.ts ((s : Int) - 1) + 3 * sp.Δ) 0 := by
  have hΔ := sp.toParams.hΔ
  have hrσ := hS.seed.timing.2.1
  have hk := sp.two_le_k
  have h0 : 0 < s := by omega
  have h1 := hS.gbar_le (show r ≤ s - 1 by omega)
  rw [← ts_pred h0] at h1
  refine ⟨h0, by omega, by linarith, le_max_of_le_left (by linarith)⟩

variable {p : Fin sp.n} {s i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-- **The proposer's `Σ.F` is on the healed chain**, at a proposal at `t_s ∈ [t₁, b]`. -/
theorem SeededRun.proposer_F (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hp : p ∈ H (tr.time i)) (hc : tr.projAC.CallAt p i ℓp) (ht₁ : t₁ ≤ tr.time i)
    (hb : tr.time i ≤ b) :
    OnHealedChain tr H g r (r + sp.k - 1) ℓp.frame.F b := by
  have hi : ∀ k < i, tr.time k ≤ tr.time i := fun _ h => hS.run.time_mono h.le
  have hF := (hS.inv.caches p i (tr.time i) ht₁ hi hb hp
    (hS.called hp (hS.drain.trans ht₁) le_rfl)).1
  rw [frame_of_projAC_at hS.run hp hc]
  exact hF

/-- **The proposer of slot `s ≥ σ + 1` holds every member of the old family, or it is below its
`Σ.F`**, at a proposal at `t_s ∈ [t₁, b]`: `Σ.F` is on the healed chain, so compatible with the
member; a member of label `≤ s − 2` is extended by every honest slot-`(s−1)` vote (S2), whose head
reaches the proposer (`proposer_accepts_head_from`); an optimistic origin of label `s − 1` by
`proposal_holds_old_from` at the floor `r + k − 1`. -/
theorem seeded_proposer_holds (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) (hp : p ∈ H (tr.time i)) (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (ht₁ : t₁ ≤ tr.time i) (hb : tr.time i ≤ b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : SeededOld tr H g r b s C) :
    C ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocksAt H) C ℓp.frame.F := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hU := honestBlocksAt_coherent hS.run hS.noColl
  obtain ⟨hs0, hrs, -, hκ⟩ := hS.slot_timing hs
  have hF := hS.proposer_F hp hc ht₁ hb
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hS.run hS.noColl hp hc
  rcases hC with ⟨l, hC, hl⟩ | ⟨x, k, CV, hx, hO⟩
  · rcases OnHealedChain.compatible hS.run hS.noColl hS.inv.origins_compatible hF hC with hFC | hCF
    swap
    · exact Or.inr hCF
    left
    -- an honest slot-`(s−1)` voter, honest at `t_{s−1} + Δ`
    have hsb : sp.ts (s - 1 : Nat) + sp.Δ ≤ b := by
      have : sp.ts (s - 1 : Nat) + 4 * sp.Δ = sp.ts s := by
        simp only [SAParams.ts]; push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
      linarith
    have hcount := hS.bounds.slot (s - 1) (sp.ts (s - 1 : Nat) + sp.Δ) (by omega) le_rfl hsb
      (by linarith)
    obtain ⟨z, hz, hw, hjz⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨j, e, hv, hes, hjt⟩ := vote_of_awake_joined_at hS.run hS.noColl hz hw hjz
    obtain ⟨Hd, hHd, hHdr, hCHd⟩ :=
      hS.inv.vote_extends C l hC z j e hv (hjt.trans hsb) (by omega)
    have hHdt := (proposer_accepts_head_from hS.run hS.noColl hS.sync hp hc hcall hd hti hb hκ hv
      (by omega) hHd hHdr (hFC.trans hCHd)).1
    exact mem_between hU hΦ hΦU hΦ.rooted.1 hHdt hFC hCHd
  · obtain ⟨-, -, hga, -⟩ := hS.slot_timing hs
    have hρ : SA.gbar g ≤ sp.ts (r + sp.k - 1 : Nat) := by
      have := hS.gbar_le (show r ≤ r + sp.k - 1 by omega)
      linarith
    refine proposal_holds_old_from hS.run hS.noColl hS.sync hS.bounds (ρ := r + sp.k - 1)
      (by omega) hρ hp hc hcall hd hti hb hκ (fun O m hOm hm _ => OnHealedChain.compatible
        hS.run hS.noColl hS.inv.origins_compatible hF (.of_origin hm hOm)) C
      (oldOriginAbove_iff.2 ⟨x, k, s - 1, CV, hx, by omega, Or.inr ⟨hO, by omega⟩⟩)

/-- **The proposal walk of slot `s ≥ σ + 1` passes every member of the old family**, at a proposal
at `t_s ∈ [t₁, b]` (`proposal_walk_passes_from`): the member is held or below `Σ.F`
(`seeded_proposer_holds`), viable or below `fc_root` when held (`SeededInvariant.viable`, the
proposer having called from `t_{r−k−3}`), supported at slot `s − 1` (S2, or the optimistic
origin), and compatible with every lock write of the slot of a live stored lock (a member after
the drain, `SeededRun.live_label`). -/
theorem seeded_walk_passes (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) (hp : p ∈ H (tr.time i)) (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (ht₁ : t₁ ≤ tr.time i) (hb : tr.time i ≤ b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : SeededOld tr H g r b s C) :
    Anc (tr.HonestBlocksAt H) C d.head := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  obtain ⟨hs0, hrs, hga, hκ⟩ := hS.slot_timing hs
  have hi : ∀ k < i, tr.time k ≤ tr.time i := fun _ h => hS.run.time_mono h.le
  have hdt : sp.ts (r + sp.k : Nat) ≤ tr.time i := hS.drain.trans ht₁
  obtain ⟨lC, -, hCm⟩ := hC.member hS.run (hti ▸ hb) hrs
  have hfr := frame_of_projAC_at hS.run hp hc
  refine proposal_walk_passes_from hS.run hS.noColl hS.sync hS.bounds hp hc hcall hd hti hb hs0
    (by omega) (by linarith) hκ (seeded_proposer_holds hS hs hp hc hcall hd hti ht₁ hb hC)
    (fun hCt => ?_) ?_ fun l hl hlive D hD => hS.inv.origins_compatible D l.slot C lC
      (.of_lock (hS.live_label hp hdt hl hlive) (hD.mono hb)) hCm
  · rw [hfr] at hCt ⊢
    exact hS.inv.viable p i (tr.time i) ht₁ hi hb hp (hS.called hp hdt le_rfl) C
      (onHealedChain_iff.2 ⟨C, lC, hCm, .refl⟩) hCt
  · rcases hC with ⟨l, hC, hl⟩ | ⟨x, k, CV, hx, hO⟩
    · exact Or.inl fun z j e hv hes hjb => hS.inv.vote_extends C l hC z j e hv hjb (by omega)
    · exact Or.inr ⟨x, k, CV, hx, hO⟩

end Consensus.Goldilocks.Compose.Growing

end
