module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAdvanceUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Healed
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Refinement: the per-height groups of `height_advance_upTo` (#137)

consensus-lean#137. `height_advance_upTo` takes, at each height, a live fast lock of an honest
call (`hl hf hB hBl`) and a unanimous slot `u` (`hP hslot hu hPg hun hgu hR htu huv`). Here:

* `lock_kept_run`: a lock stays in an honest node's lock set over `[i, N]` when, at each cut,
  it does not expire, its block `P` is in the frame and its own viable ancestor, and `unlock`
  does not move `P` (`SA.mem_step_locks_of_keep_view`; FG steps do not change the locks).
* `fast_lock_of_unanimous_update`: the slot-`p` update at `t_p + 6Δ` of a unanimous slot writes
  the fast lock `⟨P.root, p, true⟩` (the lock step of `floor_of_unanimous_update`).
* `live_fast_lock_of_healed_upTo`: the two together give, at a later honest call, the live fast
  lock in the shape of `hl hf hB hBl`, with block `P`.
* `unanimous_slot_of_within`: `UnanimousWithin T Bw` at a time `t` gives the unanimous-slot group.
* `height_advance_healed_upTo`: `height_advance_upTo` with both groups supplied.
* `hXP_of_c3_upTo`: the lock entry is below every honest proposal of a slot `u` with
  `time k + Δ ≤ t_u ≤ b` (lock entry ⪯ lock block, then C3).
* `height_advance_healed_c3_upTo`: `height_advance_upTo` with any live fast lock and `hXP`
  from C3; the scheduling premise is `time k + Δ ≤ t`.
* `live_fast_lock_at_tick_upTo`, `height_advance_healed_tick_upTo`: the same at the cut right
  after the unanimous tick (no keep interval). -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A kept lock stays.** If `l` (on block `P`) is held at cut `i` and keeps at every cut of
`[i, N)`, it is held at `N`. -/
theorem lock_kept_run (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {l : SA.Lock} {P : SA.Blk sp.n (List (FG.Att sp.n))} {i N : Nat} (hiN : i ≤ N)
    (hl : l ∈ (tr.state y i).ac.locks) (hPr : P.root = l.block)
    (hcut : ∀ j, i ≤ j → j < N → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      P ∈ (Node.frame (tr.state y j)).tree ∧ (Node.frame (tr.state y j)).viableAncestor P = P ∧
      ∀ ℓ, tr.CallAt y j (.ac ℓ) → (sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨
        SA.unlockTarget sp (Node.frame (tr.state y j))
          (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j)
            ℓ.call) ((sp.slot (tr.time j) : Int) - 1) P = P) :
    l ∈ (tr.state y N).ac.locks := by
  induction N, hiN using Nat.le_induction with
  | base => exact hl
  | succ N hiN ih =>
    have hlN := ih fun j h1 h2 => hcut j h1 (by omega)
    obtain ⟨hk, hP, hva, hu⟩ := hcut N hiN (by omega)
    by_cases hc : ∃ c, tr.CallAt y N c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy N c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := hlaw
        rw [hfr] at hstep
        have := SA.mem_step_locks_of_keep_view (ro := ro) y ℓ.call
          (Compose.frameOK_state hrun.toLocalRun hy N) (hrun.time_nonneg N) hlN hk hP hPr hva
          (hu ℓ hc)
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [hlaw.2.2.1]; exact hlN
          | false => rw [hlaw.2]; exact hlN
        | attestation a => rw [hlaw.2.1]; exact hlN
        | attest C s =>
          cases s with
          | none => rw [hlaw.2]; exact hlN
          | some a => rw [hlaw.2.2]; exact hlN
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hlN

/-- **A unanimous update writes the fast lock** `⟨P.root, p, true⟩`: the premises of
`Healing.floor_of_unanimous_update` without `B₀`. -/
theorem fast_lock_of_unanimous_update (hrun : GoldilocksRun proposer dg H tr) {g : Time}
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g) {p : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hun : Healing.Unanimous tr H p P) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ)
    (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) (hPt : P ∈ ℓ.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot) (hva : ℓ.frame.viableAncestor P = P)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k),
      Compatible (tr.HonestBlocks H) L P) :
    (⟨P.root, p, true⟩ : SA.Lock) ∈ (tr.state y (k + 1)).ac.locks := by
  have hΦ : FrameOK ℓ.frame := (SA.frameIn_of_callAt hS.run.localRun hy hc).1
  obtain ⟨hconf, hnv, hf, hpost⟩ := SA.first_update_post hS hp4 hun hy hc hcall htk hPt hlocks
  have hfast := SA.fastSelect_eq_result hΦ hPt hPg hf
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (p + 1 : Nat) = sp.ts p + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts2 : sp.ts (p + 1 + 1 : Nat) = sp.ts (p + 1 : Nat) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.time k) = p + 1 :=
    SA.slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith)
      (by rw [htk, hts2, hts1]; linarith)
  have hk2 := sp.two_le_k
  have hmem := SA.fastLock_mem_updateConfirmation hPt hva hconf hnv hfast
    (by change sp.slot (tr.time k) ≤ _; rw [hslot]; omega)
  rw [← hpost] at hmem
  have hst : (tr.state y (k + 1)).ac = tr.projAC.post k := by
    rw [← Compose.projAC_state hrun.toLocalRun hy (k + 1)]
    simp [Trace.state, hc.1, hc.2]
  rw [hst]
  exact hmem

/-- **The live fast lock of a later call** (group `hl hf hB hBl` of `height_advance_upTo`).
The fast lock `⟨P.root, p, true⟩` written by the unanimous update at the tick `k₀`
(`t_p + 6Δ`), kept over `[k₀ + 1, k)` (`hkeep`), is a live fast lock of the honest call at `k`
with block `P` when it does not expire there and `P` is in the frame and its own viable
ancestor. -/
theorem live_fast_lock_of_healed_upTo (hrun : GoldilocksRun proposer dg H tr) {g : Time}
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g) {p : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hun : Healing.Unanimous tr H p P) (hPg : P.root ≠ sp.genesisRoot)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ : Nat} {ℓ₀ : ACLabel (goldilocksNode sp ro)}
    (hc₀ : tr.projAC.CallAt y k₀ ℓ₀) (hcall : ℓ₀.call = .tick)
    (htk : tr.time k₀ = sp.ts p + 6 * sp.Δ) (hPt : P ∈ ℓ₀.frame.tree)
    (hva₀ : ℓ₀.frame.viableAncestor P = P)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k₀).locks ℓ₀.frame (tr.time k₀),
      Compatible (tr.HonestBlocks H) L P)
    {k : Nat} (hk₀k : k₀ < k)
    (hkeep : ∀ j, k₀ + 1 ≤ j → j < k → sp.slot (tr.time j) ≤ p + sp.k ∧
      P ∈ (Node.frame (tr.state y j)).tree ∧ (Node.frame (tr.state y j)).viableAncestor P = P ∧
      ∀ ℓ, tr.CallAt y j (.ac ℓ) → (sp.slot (tr.time j) : Int) - 1 ≤ p ∨
        SA.unlockTarget sp (Node.frame (tr.state y j))
          (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j)
            ℓ.call) ((sp.slot (tr.time j) : Int) - 1) P = P)
    {ℓ : ACLabel (goldilocksNode sp ro)} (hk : sp.slot (tr.time k) ≤ p + sp.k)
    (hP : P ∈ ℓ.frame.tree)
    (hva : ℓ.frame.viableAncestor P = P) :
    ∃ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k),
      l.fast = true ∧ P.root = l.block := by
  have h₀ :=
    fast_lock_of_unanimous_update hrun hS hp4 hun hy hc₀ hcall htk hPt hPg hva₀ hlocks
  have hl := lock_kept_run hrun hy (by omega : k₀ + 1 ≤ k) h₀ rfl hkeep
  rw [Compose.projAC_state hrun.toLocalRun hy]
  exact ⟨_, SA.mem_liveLocks_of_keep hl hk hP rfl hva, rfl, rfl⟩

/-- **The unanimous slot from `UnanimousWithin`** (group `hP hslot hu hPg hun hgu hR htu huv` of
`height_advance_upTo`). For `T ≤ t` with `ḡ + 4Δ`, the drain time and `tH` at most `t`, and
`t + Bw + 6Δ ≤ v`: a unanimous honest proposal `P` of a slot `u` with all these premises. -/
theorem unanimous_slot_of_within (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {T Bw : Time} (hU : Regimes.UnanimousWithin tr H proposer T Bw)
    {t : Time} (hTt : T ≤ t) {gR a tH v b : Time} (hgt : SA.gbar gR + 4 * sp.Δ ≤ t)
    (hRt : Healing.drainTime sp a ≤ t) (htHt : tH ≤ t) (htv : t + Bw + 6 * sp.Δ ≤ v) :
    ∃ u P, Healing.HonestProposalRun tr H proposer u P ∧ P ∈ tr.HonestBlocks H ∧
      P.slot = u ∧ 0 < u ∧ P.root ≠ sp.genesisRoot ∧
      (∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
        e.msg.slot = u → e.msg.head = P.root) ∧
      SA.gbar gR + 4 * sp.Δ ≤ sp.ts u ∧ Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) ∧
      tH ≤ sp.ts u ∧ sp.ts u + 6 * sp.Δ ≤ v := by
  obtain ⟨u, P, htu, hub, hPr, hun⟩ := hU t hTt
  have hΔ := sp.toParams.hΔ
  have hg0 : 0 ≤ SA.gbar gR := le_max_right gR 0
  have hu : 0 < u := by
    by_contra h0
    have : u = 0 := by omega
    subst this
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at htu
    linarith
  obtain ⟨kp, hkp⟩ := proposesAt_of_honestProposalRun hrun hPr
  obtain ⟨-, hPm, -⟩ := Healing.accept_of_proposesAt hrun hnc hPr.1 hkp
  have hPH : P ∈ tr.HonestBlocks H := ⟨_, hPr.1, kp + 1, hPm⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hslot, -⟩ := hPr.2
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPg : P.root ≠ sp.genesisRoot := by
    intro he
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hPr.1 kp)
    have heq := hr.coherent.1 hPH ⟨_, hPr.1, kp, hG⟩ he
    have hz : P.slot = 0 := by rw [heq]; rfl
    omega
  have hlt : sp.ts u < sp.ts (u + 1 : Nat) := (SA.ts_lt_iff sp).2 (by push_cast; omega)
  exact ⟨u, P, hPr, hPH, hslot, hu, hPg, fun y hy j e hv _ hs => hun y hy j e hv hs,
    by linarith, by linarith, by linarith, by linarith⟩

/-- **One height of advance from the healed state.** `height_advance_upTo` with the live fast
lock supplied by `live_fast_lock_of_healed_upTo` (block `Pl`, the unanimous slot-`pl` proposal
locked at the tick `k₀`, kept to the call `k`) and the unanimous slot `u` by
`unanimous_slot_of_within` at time `t`. Open: the shared group, `hS`, the tick and keep
premises, `hh₀`, `hks`, the entry bound `hXP` (for every honest proposal of the window), the
`v`/window group, `hAX` and the arithmetic `hδ`. -/
theorem height_advance_healed_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {ΔR a : Time} (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    -- the live fast lock
    {gl : Time} (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer gl) {pl : Nat}
    {Pl : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar gl + 4 * sp.Δ ≤ sp.ts pl)
    (hunl : Healing.Unanimous tr H pl Pl) (hPgl : Pl.root ≠ sp.genesisRoot)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ : Nat} {ℓ₀ : ACLabel (goldilocksNode sp ro)}
    (hc₀ : tr.projAC.CallAt y k₀ ℓ₀) (hcall : ℓ₀.call = .tick)
    (htk : tr.time k₀ = sp.ts pl + 6 * sp.Δ) (hPt : Pl ∈ ℓ₀.frame.tree)
    (hva₀ : ℓ₀.frame.viableAncestor Pl = Pl)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k₀).locks ℓ₀.frame (tr.time k₀),
      Compatible (tr.HonestBlocks H) L Pl)
    {k : Nat} (hk₀k : k₀ < k)
    (hkeep : ∀ j, k₀ + 1 ≤ j → j < k → sp.slot (tr.time j) ≤ pl + sp.k ∧
      Pl ∈ (Node.frame (tr.state y j)).tree ∧ (Node.frame (tr.state y j)).viableAncestor Pl = Pl ∧
      ∀ ℓ, tr.CallAt y j (.ac ℓ) → (sp.slot (tr.time j) : Int) - 1 ≤ pl ∨
        SA.unlockTarget sp (Node.frame (tr.state y j))
          (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j)
            ℓ.call) ((sp.slot (tr.time j) : Int) - 1) Pl = Pl)
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k)
    (hkl : sp.slot (tr.time k) ≤ pl + sp.k) (hPl : Pl ∈ ℓ.frame.tree)
    (hval : ℓ.frame.viableAncestor Pl = Pl) (hks : tr.time k + sp.Δ ≤ sp.ts s₁)
    (hh₀ : h₀ + 1 ≤ ((tr.state y k).fg.σ Pl.root).h)
    -- the unanimous slot
    {T Bw : Time} (hU : Regimes.UnanimousWithin tr H proposer T Bw) {t : Time} (hTt : T ≤ t)
    (hgt : SA.gbar gR + 4 * sp.Δ ≤ t) (hRt : Healing.drainTime sp a ≤ t) (htHt : tH ≤ t)
    (htv : t + Bw + 6 * sp.Δ ≤ v)
    (hXP : ∀ u P, Healing.HonestProposalRun tr H proposer u P → tH ≤ sp.ts u →
      sp.ts u + 6 * sp.Δ ≤ v → ∀ X ∈ (tr.state y k).fg.tree,
        X.root = ((tr.state y k).fg.σ Pl.root).Th → Anc (tr.HonestBlocks H) X P)
    -- v, the windows, the link and the slot condition
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hAX : ∀ X ∈ (tr.state y k).fg.tree, X.root = ((tr.state y k).fg.σ Pl.root).Th →
      Anc (tr.HonestBlocks H) A X)
    (hδ : ∀ X ∈ (tr.state y k).fg.tree, X.root = ((tr.state y k).fg.σ Pl.root).Th →
      s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1) :
    ∃ s, min s₁ s₂ ≤ s ∧ s < max s₁ s₂ + gM ∧ ∃ P',
      Healing.HonestProposalRun tr H proposer s P' ∧ ∃ kp, tr.ProposesAt (proposer s) kp P' ∧
        P' ∈ (tr.post kp).fg.tree ∧ Anc (tr.HonestBlocks H) A P' ∧
        ∀ w ∈ H, ∀ j, P' ∈ (tr.state w j).fg.tree →
          ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ P'.root).h := by
  obtain ⟨l, hl, hf, hBl⟩ := live_fast_lock_of_healed_upTo hrun hS hp4 hunl hPgl hy hc₀ hcall
    htk hPt hva₀ hlocks hk₀k hkeep (ℓ := ℓ) hkl hPl hval
  obtain ⟨u, P, hPr, hP, hslot, hu, hPg, hun, hgu, hR, htu, huv⟩ :=
    unanimous_slot_of_within (b := b) hrun hp.noColl hU hTt hgt hRt htHt htv
  exact height_advance_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf hPl hBl hks
    rfl rfl hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv (hXP u P hPr htu huv) hs₂ hvs₂
    hwb₂ hAX hδ

/-- `unanimous_slot_of_within` that also keeps the lower bound `t ≤ t_u` of the witness. -/
theorem unanimous_slot_of_within_ge (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {T Bw : Time} (hU : Regimes.UnanimousWithin tr H proposer T Bw)
    {t : Time} (hTt : T ≤ t) {gR a tH v b : Time} (hgt : SA.gbar gR + 4 * sp.Δ ≤ t)
    (hRt : Healing.drainTime sp a ≤ t) (htHt : tH ≤ t) (htv : t + Bw + 6 * sp.Δ ≤ v) :
    ∃ (u : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts u ∧
      Healing.HonestProposalRun tr H proposer u P ∧ P ∈ tr.HonestBlocks H ∧
      P.slot = u ∧ 0 < u ∧ P.root ≠ sp.genesisRoot ∧
      (∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
        e.msg.slot = u → e.msg.head = P.root) ∧
      SA.gbar gR + 4 * sp.Δ ≤ sp.ts u ∧ Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) ∧
      tH ≤ sp.ts u ∧ sp.ts u + 6 * sp.Δ ≤ v := by
  obtain ⟨u, P, htu, hub, hPr, hun⟩ := hU t hTt
  have hΔ := sp.toParams.hΔ
  have hg0 : 0 ≤ SA.gbar gR := le_max_right gR 0
  have hu : 0 < u := by
    by_contra h0
    have : u = 0 := by omega
    subst this
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at htu
    linarith
  obtain ⟨kp, hkp⟩ := proposesAt_of_honestProposalRun hrun hPr
  obtain ⟨-, hPm, -⟩ := Healing.accept_of_proposesAt hrun hnc hPr.1 hkp
  have hPH : P ∈ tr.HonestBlocks H := ⟨_, hPr.1, kp + 1, hPm⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hslot, -⟩ := hPr.2
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPg : P.root ≠ sp.genesisRoot := by
    intro he
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hPr.1 kp)
    have heq := hr.coherent.1 hPH ⟨_, hPr.1, kp, hG⟩ he
    have hz : P.slot = 0 := by rw [heq]; rfl
    omega
  have hlt : sp.ts u < sp.ts (u + 1 : Nat) := (SA.ts_lt_iff sp).2 (by push_cast; omega)
  exact ⟨u, P, htu, hPr, hPH, hslot, hu, hPg, fun y hy j e hv _ hs => hun y hy j e hv hs,
    by linarith, by linarith, by linarith, by linarith⟩

/-- **The lock entry is below a later honest proposal** (the `hXP` of `height_advance_upTo`,
L5.4 via C3). For a live fast lock `l` on `B` of the honest call at `k` (`tH ≤ time k`), the
entry block `X` of `σ[B]` (`X.root = σ[B].Th`) is ⪯ every honest proposal `P` of a slot `u`
with `time k + Δ ≤ t_u ≤ b`: `X ⪯ B` (entry of the state of `B`) and C3 gives `B ⪯ parent(P)`. -/
theorem hXP_of_c3_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer u P) (hku : tr.time k + sp.Δ ≤ sp.ts u)
    (hub : sp.ts u ≤ b) :
    ∀ X ∈ (tr.state y k).fg.tree, X.root = ((tr.state y k).fg.σ B.root).Th →
      Anc (tr.HonestBlocks H) X P := by
  intro X hX hXr
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨T, hT, hTr, hTB, -, -⟩ := lock_entry_block hrun hy hBy
  have hXT : X = T :=
    (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy k)).2.1.1 hX hT
      (hXr.trans hTr.symm)
  subst hXT
  obtain ⟨Pr, hPrH, hpar, hBPr⟩ := hH.c3 y hy k ℓ hc htH l hl hf B hB hBl u P hP hku hub
  obtain ⟨kp, hkp⟩ := proposesAt_of_honestProposalRun hrun hP
  obtain ⟨-, hPm, -⟩ := Healing.accept_of_proposesAt hrun hnc hP.1 hkp
  have hPH : P ∈ tr.HonestBlocks H := ⟨_, hP.1, kp + 1, hPm⟩
  exact (Healing.honest_anc_of_store_anc hy hTB).trans
    (hBPr.tail ⟨hPrH, hPH, hpar⟩)

/-- **One height of advance from the healed state, C3 form.** `height_advance_upTo` with an
honest live fast lock `l` on `B` at the call `k` (any fast lock: the consumer does not need the
lock of a fixed unanimous slot) and the unanimous slot `u` from `unanimous_slot_of_within` at a
time `t` with `time k + Δ ≤ t`. The entry bound `hXP` is discharged by `hXP_of_c3_upTo`
(`t ≤ t_u`, `t_u + 6Δ ≤ v ≤ b`). -/
theorem height_advance_healed_c3_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {ΔR a : Time} (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    -- the live fast lock
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁)
    (hh₀ : h₀ + 1 ≤ ((tr.state y k).fg.σ B.root).h)
    -- the unanimous slot
    {T Bw : Time} (hU : Regimes.UnanimousWithin tr H proposer T Bw) {t : Time} (hTt : T ≤ t)
    (hgt : SA.gbar gR + 4 * sp.Δ ≤ t) (hRt : Healing.drainTime sp a ≤ t) (htHt : tH ≤ t)
    (htv : t + Bw + 6 * sp.Δ ≤ v) (hkt : tr.time k + sp.Δ ≤ t)
    -- v, the windows, the link and the slot condition
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hAX : ∀ X ∈ (tr.state y k).fg.tree, X.root = ((tr.state y k).fg.σ B.root).Th →
      Anc (tr.HonestBlocks H) A X)
    (hδ : ∀ X ∈ (tr.state y k).fg.tree, X.root = ((tr.state y k).fg.σ B.root).Th →
      s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1) :
    ∃ s, min s₁ s₂ ≤ s ∧ s < max s₁ s₂ + gM ∧ ∃ P',
      Healing.HonestProposalRun tr H proposer s P' ∧ ∃ kp, tr.ProposesAt (proposer s) kp P' ∧
        P' ∈ (tr.post kp).fg.tree ∧ Anc (tr.HonestBlocks H) A P' ∧
        ∀ w ∈ H, ∀ j, P' ∈ (tr.state w j).fg.tree →
          ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ P'.root).h := by
  obtain ⟨u, P, htu', hPr, hP, hslot, hu, hPg, hun, hgu, hR, htu, huv⟩ :=
    unanimous_slot_of_within_ge (b := b) hrun hp.noColl hU hTt hgt hRt htHt htv
  have hΔ := sp.toParams.hΔ
  have hXP := hXP_of_c3_upTo hrun hp.noColl hH hy hc htH hl hf hB hBl hPr
    (by linarith) (by linarith)
  exact height_advance_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf hB hBl hks
    rfl rfl hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP hs₂ hvs₂ hwb₂ hAX hδ

/-- **The live fast lock right after the unanimous tick** (group `hl hf hB hBl` of
`height_advance_upTo`, no keep interval). The fast lock `⟨P.root, p, true⟩` written by the
unanimous update at the tick `k₀` (`t_p + 6Δ`) is a live fast lock at the next cut `k₀ + 1`,
for any label `ℓ` whose frame holds `P` as its own viable ancestor, when it does not expire. -/
theorem live_fast_lock_at_tick_upTo (hrun : GoldilocksRun proposer dg H tr) {g : Time}
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g) {p : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hun : Healing.Unanimous tr H p P) (hPg : P.root ≠ sp.genesisRoot)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ : Nat} {ℓ₀ : ACLabel (goldilocksNode sp ro)}
    (hc₀ : tr.projAC.CallAt y k₀ ℓ₀) (hcall : ℓ₀.call = .tick)
    (htk : tr.time k₀ = sp.ts p + 6 * sp.Δ) (hPt : P ∈ ℓ₀.frame.tree)
    (hva₀ : ℓ₀.frame.viableAncestor P = P)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k₀).locks ℓ₀.frame (tr.time k₀),
      Compatible (tr.HonestBlocks H) L P)
    {ℓ : ACLabel (goldilocksNode sp ro)} (hk : sp.slot (tr.time (k₀ + 1)) ≤ p + sp.k)
    (hP : P ∈ ℓ.frame.tree) (hva : ℓ.frame.viableAncestor P = P) :
    ∃ l ∈ SA.liveLocks sp (tr.projAC.state y (k₀ + 1)).locks ℓ.frame (tr.time (k₀ + 1)),
      l.fast = true ∧ P.root = l.block :=
  live_fast_lock_of_healed_upTo hrun hS hp4 hun hPg hy hc₀ hcall htk hPt hva₀ hlocks
    (Nat.lt_succ_self k₀) (fun j h1 h2 => absurd h2 (by omega)) hk hP hva

/-- **One height of advance from the unanimous tick.** `height_advance_healed_c3_upTo` at the
call `k₀ + 1` right after the unanimous slot-`pl` tick `k₀`, with the live fast lock on `Pl`
from `live_fast_lock_at_tick_upTo`. Open frame facts at `k₀ + 1`: the call `hc`, `Pl` in its
frame and its own viable ancestor (`hPl hval`), no expiry (`hkl`). The scheduling premises are
`hks : time (k₀+1) + Δ ≤ t_{s₁}` and `hkt : time (k₀+1) + Δ ≤ t`. -/
theorem height_advance_healed_tick_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {ΔR a : Time} (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    -- the unanimous tick
    {gl : Time} (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer gl) {pl : Nat}
    {Pl : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar gl + 4 * sp.Δ ≤ sp.ts pl)
    (hunl : Healing.Unanimous tr H pl Pl) (hPgl : Pl.root ≠ sp.genesisRoot)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ : Nat} {ℓ₀ : ACLabel (goldilocksNode sp ro)}
    (hc₀ : tr.projAC.CallAt y k₀ ℓ₀) (hcall : ℓ₀.call = .tick)
    (htk : tr.time k₀ = sp.ts pl + 6 * sp.Δ) (hPt : Pl ∈ ℓ₀.frame.tree)
    (hva₀ : ℓ₀.frame.viableAncestor Pl = Pl)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k₀).locks ℓ₀.frame (tr.time k₀),
      Compatible (tr.HonestBlocks H) L Pl)
    -- the call right after the tick
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y (k₀ + 1) ℓ)
    (htH : tH ≤ tr.time (k₀ + 1)) (hkl : sp.slot (tr.time (k₀ + 1)) ≤ pl + sp.k)
    (hPl : Pl ∈ ℓ.frame.tree) (hval : ℓ.frame.viableAncestor Pl = Pl)
    (hks : tr.time (k₀ + 1) + sp.Δ ≤ sp.ts s₁)
    (hh₀ : h₀ + 1 ≤ ((tr.state y (k₀ + 1)).fg.σ Pl.root).h)
    -- the unanimous slot
    {T Bw : Time} (hU : Regimes.UnanimousWithin tr H proposer T Bw) {t : Time} (hTt : T ≤ t)
    (hgt : SA.gbar gR + 4 * sp.Δ ≤ t) (hRt : Healing.drainTime sp a ≤ t) (htHt : tH ≤ t)
    (htv : t + Bw + 6 * sp.Δ ≤ v) (hkt : tr.time (k₀ + 1) + sp.Δ ≤ t)
    -- v, the windows, the link and the slot condition
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hAX : ∀ X ∈ (tr.state y (k₀ + 1)).fg.tree,
      X.root = ((tr.state y (k₀ + 1)).fg.σ Pl.root).Th → Anc (tr.HonestBlocks H) A X)
    (hδ : ∀ X ∈ (tr.state y (k₀ + 1)).fg.tree,
      X.root = ((tr.state y (k₀ + 1)).fg.σ Pl.root).Th →
        s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1) :
    ∃ s, min s₁ s₂ ≤ s ∧ s < max s₁ s₂ + gM ∧ ∃ P',
      Healing.HonestProposalRun tr H proposer s P' ∧ ∃ kp, tr.ProposesAt (proposer s) kp P' ∧
        P' ∈ (tr.post kp).fg.tree ∧ Anc (tr.HonestBlocks H) A P' ∧
        ∀ w ∈ H, ∀ j, P' ∈ (tr.state w j).fg.tree →
          ((tr.state w j).fg.σ A.root).h + 1 ≤ ((tr.state w j).fg.σ P'.root).h := by
  obtain ⟨l, hl, hf, hBl⟩ := live_fast_lock_at_tick_upTo hrun hS hp4 hunl hPgl hy hc₀ hcall
    htk hPt hva₀ hlocks (ℓ := ℓ) hkl hPl hval
  exact height_advance_healed_c3_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hp hvb hcatch hy hc htH
    hl hf hPl hBl hks hh₀ hU hTt hgt hRt htHt htv hkt hs₂ hvs₂ hwb₂ hAX hδ

end Consensus.Goldilocks.Refinement

end
