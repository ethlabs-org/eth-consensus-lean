module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Suppliers of the finite latest-result induction under growing faults

The reset-form facts that `Kernel/ResultPrefix` consumes, read with each node honest at its own
cut.

* `fault_bound_late_at`: from the reset's cut on, the fault bound at `t ≤ b` on the AC
  projection, charged at `t`. It is the run's late fault bound (`fault_bound_late_before_at`,
  stated here with the seed layer's statement until that module is on this branch) read through
  the joined projection on the prefix through `t`;
* `ResetPremisesUpTo.half_committee_at`: after the reset's cut, the validators honest at
  `t ≥ t_m + Δ` that voted in slot `m` while honest are at least half of the committee: each is
  awake from `ḡ` and joined at `t_m + Δ` (its restarts are by the slot after `ḡ`,
  `restart_le_before_at`, stated here with the seed layer's statement), so it votes in slot `m`
  on the prefix through `t_m + Δ`; the count is `3 f_t ≤ n − 1` at `t`;
* `reset_syncACAt`: from the GST on, the reset service is AC synchrony on the projection, with each
  sender honest at its send or acceptance and each recipient at its call (the growing form of
  `Healing.ResetService.syncAC`);
* `result_carry_reset_at`, `honest_votes_carry_reset_at`: after the reset's cut, the counted
  votes of a result (its writer honest at its update), and the label-`m` votes of nodes honest at
  them, reach a next-label voter honest at its vote (`Carry_y`). The deliveries come from the
  reset service, a head accepted before the GST from the catch-up `Catch(2Δ)`; the voter's side
  is read on the prefix through its vote;
* `writer_merged_reset_at`: the writer-pool merge under that synchrony from `t_s`;
* `live_locks_of_stored_at`: the live locks at a first-successor vote from the stored-lock
  comparisons, the fault bound at the voter's cut and the earlier votes (the static argument on
  the prefix through the vote).

The results of other layers that are not yet on this branch are stated here under their names
with the suffix `_stub`, with their owners' statements: `carryAt_of_delivered` and
`result_writer_at` (the sleepy node layer) and the seed layer's two facts above. Each is an
open `sorry`. The per-cut node facts (`projAC_state_at`, `run_F_mono_at`, `acBlock_prev_at`,
`accept_next_at`) are the static ones on the prefix through the cut. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- The run's late fault bound (`Healing.Growing.fault_bound_late_before_at` of the seed layer,
same statement); stand-in until that module is on this branch. -/
theorem fault_bound_late_before_at_stub {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  sorry

/-- **The late fault bound on the AC projection**: from the reset's cut on, at `t ≤ b`, the
faults at `t` are fewer than the validators honest at `t` that are awake and joined at `t` in
the AC projection (the run's joined test is the projection's, `Compose.joined_projection` on the
prefix through `t`). -/
theorem fault_bound_late_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t : Time} (ht : cutZ sp.toParams g ≤ t) (htb : t ≤ b) :
    SA.FaultBoundAt tr.projAC H t t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := by
    have := lt_cutZ sp g
    have := gbar_nonneg g
    linarith
  have h := fault_bound_late_before_at_stub hp ht le_rfl htb
  unfold RunTrace.FaultBoundAt at h
  unfold SA.FaultBoundAt
  refine h.trans_le (Set.ncard_le_ncard (fun z hz => ⟨hz.1, hz.2.1, ?_⟩) (Set.toFinite _))
  obtain ⟨hzt, -, hj⟩ := hz
  have hjp := (Compose.joined_projection sp ro dg (H t) (tr.upTo t) proposer
    (hp.run.upTo ht0) z hzt t).1
  have hjpre : (tr.upTo t).JoinedAt z t := fun k hk hkt =>
    hj k ((RunTrace.upTo_restartAt tr).mp hk).2 hkt
  intro k hk hkt
  obtain ⟨ℓ, hc, hr⟩ := hk
  refine hjp.mp hjpre k ?_ hkt
  rw [RunTrace.upTo_projAC]
  exact ⟨ℓ, (Trace.upTo_callAt _).mpr ⟨hkt, hc⟩, hr⟩

/-- A restart of a node honest at it, by the horizon, is by the slot after `ḡ`
(`Healing.Growing.restart_le_before_at` of the seed layer, same statement); stand-in until that
module is on this branch. -/
theorem restart_le_before_at_stub {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  sorry

end Consensus.Goldilocks.Healing.Growing.KernelProof

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **Half of the committee votes** after the reset's cut, counted at `t ≥ t_m + Δ`. -/
theorem ResetPremisesUpTo.half_committee_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {m : Nat} (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b) :
    sp.n ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = m}.ncard := by
  have hΔ := sp.toParams.hΔ
  have hgt : gbar g ≤ sp.ts m + sp.Δ := by have := lt_cutZ sp g; linarith
  have hd0 : 0 ≤ sp.ts m + sp.Δ := (gbar_nonneg g).trans hgt
  have hdb : sp.ts m + sp.Δ ≤ b := hmt.trans htb
  have hsl : sp.slot (sp.ts m + sp.Δ) = m :=
    SA.slot_of_mem sp m (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hm3 : sp.slot (gbar g) + 3 ≤ m := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hm)
    exact_mod_cast h
  have hsub : H t ⊆ {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = m} := by
    intro z hz
    have hzd : z ∈ H (sp.ts m + sp.Δ) := hp.run.antitone hmt hz
    have hj : (tr.upTo (sp.ts m + sp.Δ)).JoinedAt z (sp.ts m + sp.Δ) := fun k hk hkt => by
      obtain ⟨hkd, hk⟩ := (RunTrace.upTo_restartAt tr).mp hk
      change 0 < sp.slot (sp.ts m + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
      rw [hsl, sp.slotTime_eq]
      exact ⟨by omega, (KernelProof.restart_le_before_at_stub hp
        (hp.run.antitone (hkd.trans hmt) hz) hk (hkd.trans hdb)).trans
        ((SA.ts_le_iff sp).mpr (by exact_mod_cast (show sp.slot (gbar g) + 1 ≤ m - 1 by
          clear * - hm3; omega)))⟩
    obtain ⟨q, e, hv, he, -⟩ := Compose.vote_of_awake_joined (hp.run.upTo hd0)
      (hp.noColl.upTo _) hzd ⟨hp.awake z _ hzd hgt hdb, le_rfl⟩ hj
    rw [RunTrace.upTo_projAC] at hv
    obtain ⟨ℓ, hc, he'⟩ := hv
    obtain ⟨hq, hc⟩ := (Trace.upTo_callAt _).mp hc
    exact ⟨hz, q, e, hp.run.antitone hq hzd, ⟨ℓ, hc, he'⟩, he⟩
  have hle := Set.ncard_le_ncard hsub
  have hn : (H t).ncard + (H t)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hf := hp.faults t (hd0.trans hmt) htb
  have hn' : sp.n = sp.toParams.n := rfl
  omega

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote gbar)

/-! ### Stand-ins for the node layer -/

/-- `Carry_y` from deliveries, for one honest voter over an SA trace
(`Compose.Growing.carryAt_of_delivered` of the node layer, same statement); stand-in until that
module is on this branch. -/
theorem carryAt_of_delivered_stub {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}
    (hr : Consensus.Goldilocks.ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
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
  sorry

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- What a result's writer did with its counted votes, the writer honest at its update
(`Compose.Growing.result_writer_at` of the node layer, same statement); stand-in until that
module is on this branch. -/
theorem result_writer_at_stub (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, X ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, X ∈ H (tr.time k) ∧ tr.projAC.AcceptAt X k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ) := by
  sorry

/-! ### Node-local facts at a cut, on the prefix through its time -/

/-- The AC projection holds the AC state of a node honest at the cut. -/
private theorem projAC_state_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    tr.projAC.state y i = (tr.state y i).ac := by
  have h := Compose.projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => hrun.time_mono hk.le),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- `Σ.F` of a node honest at cut `i'` moves only to descendants up to `i'`. -/
private theorem run_F_mono_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i i' : Nat} (hy : y ∈ H (tr.time i')) (hii : i ≤ i') :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y i').fg.F := by
  have hr := (hrun.upTo (hrun.time_nonneg i')).toLocalRun
  have h := Healing.run_F_mono hr hy hii
  rw [RunTrace.upTo_state_of_le hrun.time_mono (hrun.time_mono hii),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  exact h.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg i'))

/-- An AC block call of a node honest at it follows the FG acceptance at the same time. -/
private theorem acBlock_prev_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {B : (goldilocksNode sp ro).Blk} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  have hr := (hrun.upTo (hrun.time_nonneg i)).toLocalRun
  obtain ⟨i', rfl, hc', ht⟩ := Compose.acBlock_prev hr hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hb
  exact ⟨i', rfl, ((Trace.upTo_callAt _).mp hc').2, ht⟩

/-- An FG acceptance of a node honest at it is followed at once by the AC block call. -/
private theorem accept_next_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {B : (goldilocksNode sp ro).Blk}
    (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  have hr := (hrun.upTo (hrun.time_nonneg i)).toLocalRun
  obtain ⟨ℓ, hc', hb, ht⟩ := Compose.accept_next hr hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨ℓ, ((Trace.upTo_callAt _).mp hc').2, hb, ht⟩

/-- An AC call at a time `≤ d` is a call of the AC projection of the prefix through `d`. -/
private theorem projAC_callAt_upTo {d : Time} {y : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hk : tr.time k ≤ d) (hc : tr.projAC.CallAt y k ℓ) :
    (tr.upTo d).projAC.CallAt y k ℓ := by
  rw [RunTrace.upTo_projAC]
  exact (Trace.upTo_callAt _).mpr ⟨hk, hc⟩

/-- An AC call of the prefix's AC projection is one of the run's. -/
private theorem projAC_callAt_of_upTo {d : Time} {y : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : (tr.upTo d).projAC.CallAt y k ℓ) :
    tr.time k ≤ d ∧ tr.projAC.CallAt y k ℓ := by
  rw [RunTrace.upTo_projAC] at hc
  exact (Trace.upTo_callAt _).mp hc

/-- The prefix's AC deadlines at a cut through `d` are the run's. -/
private theorem projAC_deadline_upTo
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {d : Time} {y : Fin sp.n} {k : Nat} (hk : tr.time k ≤ d) (τ : Time) :
    (tr.upTo d).projAC.deadline y k τ = tr.projAC.deadline y k τ := by
  rw [Compose.projAC_deadline, Compose.projAC_deadline, RunTrace.upTo_deadline hrun.time_mono hk]

/-- A cast of a node honest at its cut, read on the prefix through its time: its frame is held
while honest, its head is in the frame above `fc_root` by the slot's `Δ`, and its slot is the
cut's. -/
theorem castAt_facts_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ℓ e) :
    (FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H) ∧
      ((∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
        tr.time i ≤ sp.ts e.msg.slot + sp.Δ) ∧
      e.msg.slot = sp.slot (tr.time i) := by
  have hd := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo hd) (hnc.upTo _)).localRun
  have hcT : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e :=
    ⟨projAC_callAt_upTo le_rfl hcast.1, hcast.2⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcT.1
  exact ⟨⟨hΦ, hΦU.trans (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)⟩,
    Compose.cast_head_fcRoot hr hy hcT, (SA.castAt_spec hr hy hcT).2.1⟩

/-! ### The reset service on the AC projection -/

/-- **The reset service gives AC synchrony** on every source window from the GST on, with each
sender honest at its send or acceptance and each recipient at its call (the growing form of
`Healing.ResetService.syncAC`). -/
theorem reset_syncACAt (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {lo hi : Time}
    (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp ro) H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  have hrun := hp.run
  refine ⟨?_, ?_⟩
  · intro x i m hx hsa hai _ y j ℓ hy hcj hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
      refine ⟨ℓ₀, Compose.projAC_callAt.1 hc₀, ?_⟩
      rwa [projAC_state_at hrun hx] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hp.sync.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', e, he', hem⟩
      · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x i B hx hacc hai _ y j ℓ hy hcj hdl hanc
    obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := Compose.projAC_callAt.mp hcj
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev_at hrun hx (Compose.projAC_callAt.mp hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(hrun.cutLaw y j _ hc hy).1]
      rfl
    have hgi : g ≤ tr.time i' := hti ▸ hg.trans hai
    have he : max (tr.time i') g = tr.time i' := max_eq_left hgi
    obtain ⟨k, hkj, hk, hlt⟩ := hp.sync.relay x i' B (hti ▸ hx) hi' hgi y j hy ⟨_, hc⟩
      (by rw [he, hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := accept_next_at hrun
      (hrun.antitone (hrun.time_mono hkj) hy) hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hrestart⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hrestart
      cases hrestart
    refine ⟨k + 1, hkj', ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
    rw [Compose.projAC_deadline]
    change tr.time (k + 1) < tr.deadline y (k + 1) (tr.time (i' + 1)) sp.Δ
    rw [htk, ← hti]
    rw [he] at hlt
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

/-- **The pre-GST catch-up on the AC projection**: a block that a node accepted while honest
before `ḡ` is accepted before `ḡ + 2Δ` by a node honest at a later call whose `Σ.F` it extends. -/
private theorem reset_catch_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ℓ) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ := by
  classical
  obtain ⟨ℓ₀, hc₀, hb⟩ := ha
  obtain ⟨kw', rfl, hkw', hti⟩ := acBlock_prev_at hrun hw (Compose.projAC_callAt.mp hc₀) hb
  have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, hi⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀i : Nat.find hex ≤ i := Nat.find_min' hex hi
  have hc := Compose.projAC_callAt.mp hcy
  have hfr : ℓ.frame.F = (tr.state y i).fg.F := by
    rw [(hrun.cutLaw y i _ hc hy).1]
    rfl
  obtain ⟨k, hk, hak⟩ := hcatch w kw' B (hti ▸ hw) hkw' (by rw [hti]; exact hkw) y
    _ (hrun.antitone hi hy) hj₀ ((run_F_mono_at hrun hy hj₀i).trans (hfr ▸ hanc))
  obtain ⟨ℓ', hc', hb', htk⟩ := accept_next_at hrun
    (hrun.antitone (hrun.time_mono (show k ≤ i by omega)) hy) hak
  exact ⟨k + 1, by omega, ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, by
    rw [htk]; exact hj₀.2 k hk⟩

/-! ### Carries after the reset -/

/-- **`Carry_y` from senders honest at their sends, after the reset's cut**: for a node honest at
its slot-`(s+1)` vote, the slot-`s` votes each sent or admitted at a time in `[t_s, t_s + 2Δ)` by
a node honest then, with heads above the voter's `Σ.F` that are genesis or accepted while honest
before `t_s + 2Δ`. Each delivery comes from the reset service, a pre-GST acceptance from the
catch-up; the voter's side is read on the prefix through its vote. -/
theorem carry_of_senders (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : cutZ sp.toParams g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : SA.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hΔ : (0 : Time) < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo hd) (hp.noColl.upTo _)).localRun
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e :=
    ⟨projAC_callAt_upTo le_rfl hcast.1, hcast.2⟩
  have hsync := reset_syncACAt hp (lo := g) (hi := sp.ts s + 2 * sp.Δ) le_rfl
  have hgs : gbar g + 8 * sp.Δ < sp.ts s := (lt_cutZ sp g).trans_le hts
  have hgg := le_gbar g
  have hti : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    have hsl := (castAt_facts_at hrun hp.noColl hy hcast).2.2
    have h := (SA.ts_le_iff_le_slot sp hd ((s + 1 : Nat) : Int)).2 (by rw [← hsl, hs])
    have hts1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith only [h, hts1]
  have hcarry := carryAt_of_delivered_stub hr hy hc' hs (CV := CV) fun v hv => by
    obtain ⟨hvs, ⟨w, k, hwk, hsend, hk1, hk2⟩, Hv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr, ?_⟩
    · rw [projAC_deadline_upTo hrun le_rfl] at hdl
      obtain ⟨k', hk'i, hk'1, ⟨ℓp, hcp, hpm⟩, hk'2⟩ := hsync.1 w k v hwk hsend
        (show g ≤ tr.time k by linarith only [hk1, hgs, hgg, hΔ]) hk2.le y i ℓ hy hcast.1 hdl
      have hk'd : tr.time k' ≤ tr.time i := hm hk'i
      exact (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k', hk'i, hk'1,
        ⟨ℓp, projAC_callAt_upTo hk'd hcp, hpm⟩, by rw [projAC_deadline_upTo hrun hk'd]; exact hk'2⟩)
    rcases hacc with hg | ⟨w', kw, hwkw, hkw, hkwt⟩
    · exact Or.inr (Or.inl hg)
    by_cases hgk : g ≤ tr.time kw
    · refine Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩
      rw [projAC_deadline_upTo hrun le_rfl] at hdl
      obtain ⟨ky, hky, ⟨ℓa, hca, hcall⟩, hkyt⟩ := hsync.2 w' kw Hv hwkw hkw hgk hkwt.le y i ℓ
        hy hcast.1 hdl hFHv
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, ⟨ℓa, projAC_callAt_upTo hkyd hca, hcall⟩,
        by rw [projAC_deadline_upTo hrun hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, ⟨ℓa, hca, hcall⟩, hkyt⟩ := reset_catch_at hrun hcatch hwkw hkw
        (lt_of_lt_of_le (not_le.mp hgk) hgg) hy hcast.1
        (by linarith only [hti, hgs, hΔ]) hFHv
      exact Or.inr (Or.inr ⟨ky, ⟨ℓa, projAC_callAt_upTo (hm hky) hca, hcall⟩,
        show tr.time ky < sp.ts s + 3 * sp.Δ by linarith only [hkyt, hgs, hΔ]⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  rcases hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hp.noColl hd hHv hX) with
    hg | ⟨k, ⟨ℓa, hca, hcall⟩, hkt⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, ⟨ℓa, (projAC_callAt_of_upTo hca).2, hcall⟩, hkt⟩

/-- **A result's counted votes reach the next voters after the reset's cut** (`Carry_y`): the
writer honest at its update, the voter at its slot-`(s+1)` vote, with the voter's `Σ.F` at or
below the result. -/
theorem result_carry_reset_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hres : SA.ResultAt tr.projAC x r s C CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV :=
  carry_of_senders hp hc hts hy hcast hs fun v hv => by
    obtain ⟨h₁, ⟨k, hk⟩, Hv, -, hHvr, hCHv, h₃⟩ :=
      result_writer_at_stub hp.run hp.noColl hx hres v hv
    exact ⟨h₁, ⟨x, k, hk⟩, Hv, hHvr, hFC.trans hCHv, h₃.imp_right fun ⟨k, hk⟩ => ⟨x, k, hk⟩⟩

/-- **The label-`m` votes of nodes honest at them, all extending `B`, reach a label-`(m+1)` vote
above `B`** after the reset's cut (`Carry_y`): each vote is its own voter's, sent at its cast
within `Δ` of `t_m`, with its head in its frame, accepted by its voter while honest. -/
theorem honest_votes_carry_reset_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {y : Fin sp.n} {i m : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hcast : SA.CastAt tr.projAC y i ℓ e) (hm : e.msg.slot = m + 1)
    (hts : cutZ sp.toParams g ≤ sp.ts m) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ z q e', z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e' → e'.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e m
      {v | ∃ z q e', z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e' ∧ e'.msg = v ∧
        v.slot = m} := by
  have hrun := hp.run
  have hΔ : (0 : Time) < sp.Δ := sp.toParams.hΔ
  refine carry_of_senders hp hc hts hy hcast hm ?_
  rintro v ⟨z, q, e', hz, ⟨ell', hc'⟩, rfl, hslot⟩
  obtain ⟨⟨-, hΦU⟩, ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩, hsl⟩ := castAt_facts_at hrun hp.noColl hz hc'
  obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall z q e' hz ⟨ell', hc'⟩ hslot
  obtain rfl : Hd = Hv :=
    (Compose.Growing.honest_blocks_coherent hrun hp.noColl).1 (hΦU hHd) hHv (hHdr.trans hHvr.symm)
  have hq0 := hrun.time_nonneg q
  have htq : sp.ts m ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp hq0 m).mpr (by rw [← hsl, hslot])
  have hqt' : tr.time q < sp.ts m + 2 * sp.Δ := by
    rw [hslot] at hqt
    linarith only [hqt, hΔ]
  refine ⟨hslot, ⟨z, q, hz, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩, htq, hqt'⟩, Hd, hHdr,
    hFB.trans hBHv, ?_⟩
  have hrq := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time q)) (tr.upTo (tr.time q))
    proposer (hrun.upTo hq0) (hp.noColl.upTo _)).localRun
  rcases Compose.frame_anc_accepted hrq hz q ell' (projAC_callAt_upTo le_rfl hc'.1) Hd hHd Hd
      .refl with hg | ⟨k, hk, ℓa, hca, hcall⟩
  · exact Or.inl hg
  · obtain ⟨hkd, hca⟩ := projAC_callAt_of_upTo hca
    exact Or.inr ⟨z, k, hrun.antitone hkd hz, ⟨ℓa, hca, hcall⟩,
      (hrun.time_mono hk).trans_lt hqt'⟩

/-- **The next-label voter's merged view of label `s` is in the writer's pool** or names an
equivocator of it, after the reset's cut: the writer-pool merge under the AC synchrony from
`t_s` that the reset service gives. -/
theorem writer_merged_reset_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hx : x ∈ H (tr.time r)) (hres : SA.ResultAt tr.projAC x r s C CV)
    (hts : cutZ sp.toParams g ≤ sp.ts s) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hcast : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state x r).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state x r).pool s} := by
  have hΔ : (0 : Time) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ellX, hupd, -⟩ := hres
  have hg : g ≤ sp.ts s := by
    have := lt_cutZ sp g
    have := le_gbar g
    linarith
  exact SA.Growing.writer_merged
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl) hx hupd
    hy hcast hs (reset_syncACAt hp hg)

/-- **The live locks at a first-successor vote are compatible with `B`**, from the stored-lock
comparisons at the cut, the fault bound at the voter's cut and the earlier votes of nodes honest
at them: the static argument on the prefix through the vote (the growing form of
`SA.live_locks_of_stored_before`). -/
theorem live_locks_of_stored_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hy : y ∈ H (tr.time i)) (hcast : SA.CastAt tr.projAC y i ℓ e)
    (hes : e.msg.slot = s + 1) (hB : B ∈ ℓ.frame.tree)
    (hstored : ∀ l ∈ (tr.projAC.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k →
      l.slot ≤ s → ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block →
        Compatible (tr.HonestBlocksAt H) Y B)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B := by
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hR := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo hd) (hnc.upTo _)
  have hr := hR.localRun
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e :=
    ⟨projAC_callAt_upTo le_rfl hcast.1, hcast.2⟩
  have hBU := (SA.frameIn_of_callAt hr hy hc'.1).2 hB
  have hanc : ∀ {X C}, C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) →
      Anc (tr.HonestBlocksAt H) X C →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) X C :=
    fun hC h => RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hC h
  have hstate : (tr.upTo (tr.time i)).projAC.state y i = tr.projAC.state y i := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC y fun k hk => hm hk.le
  have h := SA.live_locks_of_stored_before hR hf hy hc' hes
    (fun l hl hl1 hl2 Y hY hYr => (hstored l (hstate ▸ hl) hl1 hl2 Y (hsub hY) hYr).imp
      (hanc hBU) (hanc hY))
    (fun x hx j hj e' hv hslot => by
      obtain ⟨ℓ', hc''⟩ := hv
      obtain ⟨hjd, hcj⟩ := projAC_callAt_of_upTo hc''.1
      obtain ⟨Hv, hHv, hHvr, hBHv⟩ :=
        hE x j hj (hrun.antitone hjd hx) e' ⟨ℓ', hcj, hc''.2⟩ hslot
      obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hx hc''
      have hHdU := (SA.frameIn_of_callAt hr hx hc''.1).2 hHd
      obtain rfl : Hd = Hv :=
        (Compose.Growing.honest_blocks_coherent hrun hnc).1 (hsub hHdU) hHv (hHdr.trans hHvr.symm)
      exact ⟨Hd, hHdU, hHdr, hanc hHdU hBHv⟩)
  intro L hL
  exact (h L hL).imp (Anc.mono hsub) (Anc.mono hsub)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
