module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Generic healing rounds

The healing leaves over any healing supplier: for any node AC `A`, run predicate
`runs : ACRun A sg` and supplier `O : ACHealing A sg runs`, each theorem's type is the generic leaf
Prop over `O` (Milestones/Statements/Generic/Healing.lean). The proofs read the node run through
`ACRun.run_local` and apply the run-level leaves of `HealingLeaves`.

Leaves 8 and 9 (`rounds_le_warm_proposal_at_of_healing`, `report_kind_of_warm_at_of_healing`)
are proved over any `ACHealing`: its `proposal_height` puts a warm honest proposal at or
above `h_max − 1` and above `h_j` of its proposer. At a constant merged key `v ≥ 2HZ` the
proposer's store has `HZ + 1 ≤ floor + r(v)` (`pred_add_riseRounds_of_key`); a report at
the proposal's height above it is at or above the reader's floor, so above `h_j`, or at it
with `J` below the report (`ACHealing.report_in_frame`).

Leaf 10 (`reset_of_high_proposal_at_of_healing`), over any `ACHealing`: the leaf's premises are
`Premises`, so `ACHealing.report_follow` gives a node honest at the horizon a report above a warm
high proposal by the next slot's report deadline. The reader is honest at `c_z` and at the report,
the report is at least as high as the proposal in its store, and leaf 6 gives the reset.

Leaf 11 (`round_of_warm_at_of_healing`), over any `ACHealing`: an honest proposal comes from the
proposal call just before its block cut, and its parent is that call's duty head
(`proposalHead_of_proposesAt`). `ACHealing.report_follow` puts a report above the warm proposal
and below that head for every node honest at the later proposal; leaf 4, with leaf 9 for the
report kind, makes each report a row of the warm proposal or strictly higher, and leaf 5 crosses
one height. The report-delivery spacing `t_{s+1} + 2Δ + ΔF ≤ t_{s+δt}` gives the row deadline and
`δt ≥ 2`, so the later proposal is at or after `c_z`.
-/

namespace Consensus.Goldilocks.Generic

/-! ## Leaves 8 and 9, warm proposals in a frame window -/

section WarmProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing.Growing (HZ)

/-- An honest proposal below a block held at an honest reader is in the reader's tree, below that
block in the reader's store, with the proposer's replay state after its proposal. -/
private theorem proposal_below_held_at {cm proposer dg H tr}
    (hrun : runs.Run cm proposer dg H tr) (hnc : Compose.NoCollRun dg tr) {z : Fin P.n}
    {kB : Nat} {B : A.Blk} (hz : z ∈ H (tr.time kB)) (hB : tr.ProposesAt z kB B) {y : Fin P.n}
    {i : Nat} {R : A.Blk} (hy : y ∈ H (tr.time i)) (hBR : Anc (tr.HonestBlocksAt H) B R)
    (hR : R ∈ (tr.state y i).fg.tree) :
    B ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc B R ∧
      (tr.state z (kB + 1)).fg.σ B.root = (tr.state y i).fg.σ B.root := by
  have hrl := runs.run_local hrun
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrl.time_mono hq.le
  have hi0 := hrl.time_nonneg i
  have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc hz hB
  have hBy := mem_of_honest_anc_at_from hrl hnc hi0 hle hy hBR hR
  exact ⟨hBy, hrl.held_anc_at hnc hi0 hle hy hBR hR,
    σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB) (fun q hq => hrl.time_mono (by omega)) hz
      hi0 hle hy hBm hBy⟩

/-- Leaf 8: the four-key deficit bound and the supplier's proposal-height bound put a warm
proposal at most `r(v)` rounds below `HZ + 1`. -/
theorem rounds_le_warm_proposal_at_of_healing {hold : Time} (O : ACHealing A sg runs hold) :
    rounds_le_warm_proposal_at A sg O := by
  intro cm proposer dg H tr g af len u floor v kindJ J B z kB hrun hnc hwin hK hv hlo hhi hz
    hdes hB hBs hf
  have hfl := (O.proposal_height hrun hnc hwin hz hdes hB hBs hlo hhi hf).1
  have hrl := runs.run_local hrun
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  have hkey := hK z kB hzk (ht ▸ hlo) (ht ▸ hhi)
  have h := pred_add_riseRounds_of_key
    (HZ := HZ tr H g) (M := (tr.state z kB).fg.hmax) (j := (tr.state z kB).fg.hj)
    (by rw [← hkey, frameKey_eq]) hv
  exact h.trans (Nat.add_le_add_right hfl _)

/-- Leaf 9: an equal-height report above a warm proposal is strictly above the reader's `h_j`.
The supplier's proposal bounds transfer through report membership (`report_in_frame`); constant
maximum height and top status compare the reader's justified height with the proposer's.
Neither the report's `fcRoot` ancestry nor the conditional window root is needed. -/
theorem report_kind_of_warm_at_of_healing {hold : Time} (O : ACHealing A sg runs hold) :
    report_kind_of_warm_at A sg O := by
  intro cm proposer dg H tr lo hi floor u kindJ J B R z kB y i hrun hnc hframe hz hdes hB hBs
    hlo hhi hf hy hR hBR hil hih heq
  have hrl := runs.run_local hrun
  obtain ⟨hfl, hstrict⟩ := O.proposal_height hrun hnc hframe hz hdes hB hBs hlo hhi hf
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  have hzlo : lo ≤ tr.time kB := ht ▸ hlo
  have hzhi : tr.time kB ≤ hi := ht ▸ hhi
  have hzM := hframe.M_eq z kB hzk hzlo hzhi
  have hyM := hframe.M_eq y i hy hil hih
  have hztop := hframe.top_iff z kB hzk hzlo hzhi
  have hytop := hframe.top_iff y i hy hil hih
  have hRm := (O.report_in_frame hrun hy hR).1
  obtain ⟨-, -, hσ⟩ := proposal_below_held_at hrun hnc (ht ▸ hz) hB hy hBR hRm
  rw [hσ] at hfl hstrict
  have hzj := Healing.Store.hj_lt_hmax_of_reachable
    (hrl.reachable_at (hrl.time_nonneg kB) (fun q hq => hrl.time_mono hq.le) hzk)
  have hj := Healing.Store.hj_lt_hmax_of_reachable
    (hrl.reachable_at (hrl.time_nonneg i) (fun q hq => hrl.time_mono hq.le) hy)
  left
  by_cases htop : kindJ
  · have hzt := hztop.mpr htop
    have hyt := hytop.mpr htop
    omega
  · have hynt : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 :=
      fun he => htop (hytop.mp he)
    omega

end WarmProposal

/-! ## Leaf 10 -/

section HighProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open AC (gbar)
open Healing (cutZ)
open Healing.Growing (HZ IsReset)

/-- The fault bound up to the horizon gives fewer than `q` faulty nodes there. -/
theorem faults_lt_q {H : Time → Set (Fin P.n)} {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) {t : Time} (ht : 0 ≤ t)
    (htb : t ≤ b) : (H t)ᶜ.ncard < P.fg.q := by
  have h3 := hf t ht htb
  have hn := P.hn
  change _ < (2 * P.n + 2) / 3
  omega

/-- Arithmetic form of the report-time shift, including its zero case. -/
theorem shiftDelay_eq_add (P : Params) (d : Nat) (t : Time) :
    shiftDelay P d t = t + (d : Time) * P.Δ := by
  cases d with
  | zero => simp [shiftDelay]
  | succ d => rfl

/-- Shifting both deadline endpoints preserves their order. -/
theorem shiftDelay_le {P : Params} (d : Nat) {t t' : Time} (h : t ≤ t') :
    shiftDelay P d t ≤ shiftDelay P d t' := by
  simp only [shiftDelay_eq_add, add_le_add_iff_right, h]

/-- **Leaf 10 under vote latency `D`**: a warm high honest proposal forces a reset by `D` after
the next slot's report deadline. `ACHealing.report_follow` gives a report above the proposal by
an observer honest at the horizon, which is honest at `c_z` and `D` after the report, and the
report is at least as high as the proposal in the reader's store; leaf 6 under latency
(`reset_of_high_report_within_from`) gives the reset. -/
theorem reset_of_high_proposal_within_of_healing {hold : Time} (O : ACHealing A sg runs hold)
    {cm proposer dg H tr} {βK : ℚ} {g ΔF b D : Time} {s₀ u N M : Nat} {isTop : Prop}
    {J B : A.Blk} {z : Fin P.n} {kB : Nat}
    (hβ : βK ≤ 1 / 2) (hframe : SlotWindowWithin tr H O.reportDelay s₀ N M isTop J)
    (hrun : runs.Run cm proposer dg H tr) (hP : Premises tr H cm βK proposer dg sg g ΔF b hold)
    (hlat : VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hm : gbar g + 4 * P.Δ ≤ P.slotTime s₀) (hwarm : s₀ + O.warmup ≤ u) (hN : u + 1 ≤ N)
    (hmb : shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b)
    (hDb : shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + D ≤ b)
    (hz : z ∈ H (P.slotTime u + P.Δ)) (hdes : z = proposer u) (hB : tr.ProposesAt z kB B)
    (hBs : B.slot = u) (hh : HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h) :
    ∃ a, IsReset tr H g a ∧
      a ≤ shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) + D := by
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  obtain ⟨y, hy⟩ := hP.nonempty
  have hu1N : P.slotTime (u + 1) ≤ P.slotTime N := P.slotTime_strictMono.monotone hN
  have hdeadline := shiftDelay_le (P := P) O.reportDelay (add_le_add_left hu1N (2 * P.Δ))
  obtain ⟨i, R, hyi, hR, -, hti, hBR, -⟩ := O.report_follow hβ hrun hP hframe hm hwarm hN hmb
    ⟨hz, hdes, hB, hBs⟩ y (hrl.antitone (hdeadline.trans hmb) hy)
  have hzk : z ∈ H (tr.time kB) := hrl.antitone (by rw [hB.2.2, hBs]; linarith) hz
  obtain ⟨-, hBRs, hσ⟩ :=
    proposal_below_held_at hrun hP.noColl hzk hB hyi hBR (O.report_in_frame hrun hyi hR).1
  have hBR' := Healing.h_le_of_store_anc
    (hrl.reachable_at (hrl.time_nonneg i) (fun q hq => hrl.time_mono hq.le) hyi) hBRs
  rw [← hσ] at hBR'
  obtain ⟨k, hk, hkb⟩ := hP.snapshot
  have hmaxb : max (cutZ P g) (tr.time i + D) ≤ b :=
    max_le (hk.2.le.trans hkb) (by linarith)
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_within_from hrl hlat (hrl.antitone hmaxb hy)
    (faults_lt_q hP.faults ((add_nonneg (hrl.time_nonneg i) hD).trans (le_max_right _ _)) hmaxb)
    hR (hh.trans hBR')
  exact ⟨a, ha, by linarith⟩

/-- Leaf 10 is the latency-`0` case of `reset_of_high_proposal_within_of_healing`: every node
run meets latency `0` (`voteLatency_zero_from`). -/
theorem reset_of_high_proposal_at_of_healing {hold : Time} (O : ACHealing A sg runs hold) :
    reset_of_high_proposal_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b s₀ u N floor kindJ J B z kB hβ hcom hframe hrun hnc hsvc
    hawake hf hcatch hnr hsl htd hsnap hm hs₀ hwarm hN hmb hH hz hdes hB hBs hh
  have hu1N : P.slotTime (u + 1) ≤ P.slotTime N := P.slotTime_strictMono.monotone hN
  have hdeadline := shiftDelay_le (P := P) O.reportDelay (add_le_add_left hu1N (2 * P.Δ))
  simpa only [add_zero] using reset_of_high_proposal_within_of_healing O hβ hframe hrun
    ⟨hcom, hnc, hsvc, hawake, hf, hcatch, hnr, htd, hsl, hsnap, hH⟩
    (voteLatency_zero_from (runs.run_local hrun)) le_rfl hm hwarm hN hmb
    (by rw [add_zero]; exact hdeadline.trans hmb) hz hdes hB hBs hh

end HighProposal

/-! ## Leaf 11 -/

section WarmRound

open Node in
/-- An honest proposal comes from the proposal call just before its block cut, at the same time:
the block's parent is the head of the duty that call returned. For any node run from any starts
`ini`. -/
private theorem proposalHead_of_proposesAt {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State} (h : Node.LocalRun proposer dg H sg tr ini)
    {p : Fin P.n} (hp : p ∈ H) {kX : Nat} {X : A.Blk} (hX : tr.ProposesAt p kX X) :
    ∃ c < kX, ∃ d, ProposalHeadAt tr p c d ∧ tr.time c = tr.time kX ∧
      X.parent = some d.head.root := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hX
  rcases Compose.blockCall_cases h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hcs : (exec proposer dg p (tr.state p j) (tr.time (j + 2)) (.tick x fgDue)).2 =
      [(acCall p (tr.state p j) (tr.time (j + 2)) .tick).2] ++
        ((acProposal (tickStep proposer dg p (tr.state p j) (tr.time (j + 2)) x .acTick).1
          (tr.time (j + 2))).2.1 ::
          (proposeBlock dg p (acProposal (tickStep proposer dg p (tr.state p j)
            (tr.time (j + 2)) x .acTick).1 (tr.time (j + 2))).1 (tr.time (j + 2)) x d.head p').2) ++
        (if fgDue then (tickStep proposer dg p (proposeBlock dg p
          (acProposal (tickStep proposer dg p
          (tr.state p j) (tr.time (j + 2)) x .acTick).1 (tr.time (j + 2))).1 (tr.time (j + 2)) x
          d.head p').1 (tr.time (j + 2)) x .fgUpdate).2 else []) := by
    cases fgDue <;>
    simp only [exec, onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil,
      Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil]
    all_goals
      have hdp' := hdp
      simp only [tickStep] at hdp'
      simp only [tickStep, ite_eq_left hpr, hdp']
  have hl1 : 1 < (exec proposer dg p (tr.state p j)
      (tr.time (j + 2)) (.tick x fgDue)).2.length := by
    rw [hcs]; simp
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hg.2.1 0 (by omega)
  obtain ⟨hn1, ht1, -, -, hl1'⟩ := hg.2.1 1 hl1
  simp only [hcs, List.cons_append, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.add_zero] at hl0 hl1' hn0 ht0
  have hc0 : tr.CallAt p j (acCall p (tr.state p j) (tr.time (j + 2)) .tick).2 := ⟨hn0, hl0⟩
  have hs1 : tr.state p (j + 1) =
      (tickStep proposer dg p (tr.state p j) (tr.time (j + 2)) x .acTick).1 := by
    rw [tr.state_succ_of_call hc0]
    obtain ⟨hfr, hst, hfg, hrec⟩ := h.cutLaw p hp j _ hc0
    simp only at hfr hst
    rw [ht0] at hst
    simp only [tickStep, acCall]
    cases hpj : tr.post j
    rw [hpj] at hst hfg hrec
    simp only at hst hfg hrec
    rw [← hfg, ← hrec, hst]
  refine ⟨j + 1, by omega, d, ⟨⟨.proposal, frame (tickStep proposer dg p (tr.state p j)
    (tr.time (j + 2)) x .acTick).1, []⟩, p', ⟨hn1, hl1'⟩, rfl, ?_⟩, ht1, rfl⟩
  rw [hs1, ht1]
  simpa [acProposal] using hdp

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open AC (gbar)
open Healing (cutZ)

/-- Leaf 11: a later honest proposal `δt` slots after a warm one, before any height advance, is
one height above it in its proposer's store. `ACHealing.report_follow` gives every node honest at
the later proposal a report above the earlier proposal and below the later proposal's parent
(`proposalHead_of_proposesAt`); leaf 4, with leaf 9 for the report kind, makes the report a row of
the earlier proposal or strictly higher, and leaf 5 crosses one height. The report-delivery
spacing `t_{s+1} + 2Δ + ΔF ≤ t_{s+δt}` gives the row deadline and `δt ≥ 2`, so the later proposal
is at or after `c_z`. -/
theorem round_of_warm_at_of_healing {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm proposer dg H} {tr : RunTrace A} {βK : ℚ} {g ΔF b T : Time} {s₀ u x N M : Nat}
      {isTop : Prop} {J B X : A.Blk} {z : Fin P.n} {kB : Nat} {p : Fin P.n} {kX : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N M isTop J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b hold → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    Healing.Growing.CatchRun tr H g (2 * P.Δ) →
    Healing.Growing.NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, Healing.FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → s₀ + O.warmup ≤ u → O.follow ≤ P.δt →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    u + P.δt ≤ x → x ≤ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b →
    NoAdvance tr H g T → shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) < T →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    p ∈ H (tr.time kX) → p = proposer x → tr.ProposesAt p kX X → X.slot = x →
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤ ((tr.state p (kX + 1)).fg.σ X.root).h := by
  intro cm proposer dg H tr βK g ΔF b T s₀ u x N floor kindJ J B X z kB p kX hβ hcom hframe
    hrun hnc hsvc hawake hf hcatch hnr hsl hrd hsnap hm hs₀u hwarm hfol htd hux hxN hmb hHb hTb hna
    hT hz hdes hB hBs hp hdx hX hXs
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  have hdF := hsvc.deltaF
  have hmono := P.slotTime_strictMono.monotone
  have hbudget : 0 ≤ (O.reportDelay : Time) * P.Δ := by positivity
  have hδ2 : 2 ≤ P.δt := by
    by_contra h1
    have h := hrd 0
    have := hmono (show 0 + P.δt ≤ 0 + 1 by omega)
    rw [shiftDelay_eq_add] at h
    linarith
  have hu1N : u + 1 ≤ N := by omega
  have hvx := (hrd u).trans (hmono hux)
  have hdeadline := shiftDelay_le (P := P) O.reportDelay
    (add_le_add_left (hmono hu1N) (2 * P.Δ))
  have hbase : P.slotTime N + 2 * P.Δ ≤ b := by
    rw [shiftDelay_eq_add] at hmb
    linarith
  have hczx : cutZ P g ≤ P.slotTime x := by
    have hg := ((slotOfSpec_iff.mp slotOf_spec) P (gbar g) (le_max_right g 0)).1
    have hs₀ : P.slotOf (gbar g) + 1 ≤ s₀ := by
      by_contra h
      have := hmono (show s₀ ≤ P.slotOf (gbar g) by omega)
      linarith
    exact hmono (show P.slotOf (gbar g) + 3 ≤ x by omega)
  have hP : Premises tr H cm βK proposer dg sg g ΔF b hold :=
    ⟨hcom, hnc, hsvc, hawake, hf, hcatch, hnr, htd, hsl, hsnap, hHb⟩
  have htX : tr.time kX = P.slotTime x := by rw [hX.2.2, hXs]
  have htB : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hvle : shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) ≤ tr.time kX := by
    rw [htX]; linarith
  have hxb : tr.time kX ≤ b := by rw [htX]; linarith [hmono hxN]
  have hfol' := fun y (hy : y ∈ H (tr.time kX)) =>
    O.report_follow hβ hrun hP hframe hm hwarm hu1N hmb ⟨hz, hdes, hB, hBs⟩ y
      (hrl.antitone hvle hy)
  -- The later proposal's parent is the head of its proposal call.
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨c, hckX, d, ⟨ℓ, pay, hcℓ, hcall, hd⟩, htc, hpar⟩ :=
    proposalHead_of_proposesAt (hrl.upTo (hrl.time_nonneg kX)) hp hX'
  have hcs := Trace.upTo_state tr p (i := c) (d := tr.time kX)
    (fun q hq => hrl.time_mono (by omega))
  have htc' : tr.time c = tr.time kX := htc
  have hhead : ProposalHeadAt tr p c d :=
    ⟨ℓ, pay, ((Trace.upTo_callAt tr).mp hcℓ).2, hcall, by rw [← hcs]; exact hd⟩
  have hhx := fun (R : A.Blk) (hRd : ∀ x', u + O.follow ≤ x' → x' ≤ N → ∀ w c d,
      w ∈ H (tr.time c) → ProposalHeadAt tr w c d → tr.time c = P.slotTime x' →
        Anc (tr.HonestBlocksAt H) R d.head) =>
    hRd x (by omega) hxN p c d (htc' ▸ hp) hhead (htc'.trans htX)
  obtain ⟨-, Rp, -, -, -, -, hBRp, hRpd⟩ := hfol' p hp
  -- The earlier proposal is held while its proposer is honest.
  have hzk : z ∈ H (tr.time kB) := hrl.antitone (by rw [htB]; linarith) hz
  have hBH : B ∈ tr.HonestBlocksAt H :=
    ⟨z, kB + 1, tr.time kB, hrl.time_nonneg kB, fun q hq => hrl.time_mono (by omega), hzk,
      proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc hzk hB⟩
  refine round_cross_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc
    hsvc.signedRow hsvc.hold_le hnr hBH (hBRp.trans (hhx Rp hRpd)) hpar hp hX
    (hf _ (hrl.time_nonneg kX) hxb)
    (v := shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ))
    (by rw [shiftDelay_eq_add]; linarith [hmono (show s₀ ≤ u + 1 by omega)])
    (by rw [htX]; exact hvx) hxb
    (by rw [hBs, hXs]; exact hux) ?_
  intro y hy
  obtain ⟨i, R, hyi, hR, htil, hti, hBR, hRd⟩ := hfol' y hy
  have hyz : y ∈ H (max (cutZ P g) (tr.time i)) :=
    hrl.antitone (max_le (htX ▸ hczx) (hti.trans hvle)) hy
  have hlo : P.slotTime s₀ ≤ P.slotTime u := hmono hs₀u
  have hhi : P.slotTime u ≤ shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) := by
    rw [shiftDelay_eq_add]; linarith [hmono (show u ≤ N by omega)]
  obtain ⟨hBy, hRy, hor⟩ := row_or_high_of_report_at_from hrl hnc
    (fun t ht htT => hf t ht (htT.le.trans hTb)) hna hyz hR (hti.trans_lt hT)
    (O.report_in_frame hrun hyi hR).1 hBR
    (fun heq => Or.inr
      (report_kind_of_warm_at_of_healing O hrun hnc hframe (hrl.antitone (by linarith) hz) hdes
        hB hBs hlo hhi
        (P.fg.faults_lt_quorum_margin
          (hf _ (by linarith [hmono (Nat.zero_le u), P.slotTime_zero]) (by linarith)))
        hyi hR hBR (hlo.trans htil) (hti.trans hdeadline) heq))
  rcases hor with ⟨k, att, hyk, hs, hk, hah, haT⟩ | hh
  · exact Or.inl ⟨y, i, hyi, hBy, k, att, hyk, hs, hk.trans hti, hah, haT⟩
  · exact Or.inr ⟨R, hhx R hRd, y, i, hyi, hBy, hRy, hh⟩

end WarmRound

end Consensus.Goldilocks.Generic
