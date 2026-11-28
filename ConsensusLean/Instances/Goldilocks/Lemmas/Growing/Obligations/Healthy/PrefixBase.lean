module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The static healthy AC base on a read prefix under growing faults

The finite reset service, read on the prefix through a read time `d`, gives the static AC service
of the validators honest at `d` (`ResetService.upTo_ac_at`: every sender and recipient of the
prefix is honest at its own cut). From it, the static AC synchrony window on that prefix
(`sync_window_at_reset_at`), the catch-up window from `ḡ` (`catch_window_at_gbar_at`), and the
static healthy AC base of the validators honest at `d` at the slot committees of a committee
half bound (`CommitteeHalfUpTo`, `CommitteeHalfUpTo.healthy_base_before_at`) and from finite
reset premises (`healthy_base_of_reset_catch_before_at`). No reset is used. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
variable {hold : Time}

section Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- Finite AC service projects to AC synchrony using only the run core. -/
theorem ACResetService.syncACAt_core
    (hs : ACResetService tr H g ΔF)
    (core : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {lo hi : Time} (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp) H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  refine ⟨?_, ?_⟩
  · intro x i m hx hsa hai _ y j ell hy hcj hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ell₀, hc₀, hm⟩ := hsa
      refine ⟨ell₀, Compose.projAC_callAt.1 hc₀, ?_⟩
      rwa [core.projAC_state_at hx] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hs.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ell', hc', hm'⟩ | ⟨ell', hc', e, he', hem⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x i B hx hacc hai _ y j ell hy hcj hdl hanc
    apply core.acRelayAt (σ := tr.time i) hx hacc hy hcj hanc
    intro k hki hx' hk hj hF
    have hgi : g ≤ tr.time k := hki ▸ hg.trans hai
    have he : max (tr.time k) g = tr.time i := (max_eq_left hgi).trans hki
    simpa only [he] using hs.relay x k B hx' hk hgi y j hy hj
      (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- The synchrony window on a read prefix, independent of the finality update. -/
theorem sync_window_at_reset_at_core
    (core : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hs : ACResetService tr H g ΔF) {t : Time} (hga : g ≤ a) (ht0 : 0 ≤ t) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) := by
  have hm := core.time_mono
  have hsy := hs.syncACAt_core core (lo := a) (hi := t) hga
  constructor
  · intro x hx i m hsend hi y hy j ell hj ht hd
    obtain ⟨hid, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
    obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
    rw [ACTrace.upTo_deadline hm hjd] at ht hd
    obtain ⟨k, hkj, hik, hproc, hkt⟩ := hsy.1 x i m (core.antitone hid hx) hsend
      hi hid y j ell (core.antitone hjd hy) hj hd
    have hkd : tr.time k ≤ t := (hm hkj).trans hjd
    exact ⟨k, hkj, hik, ACTrace.upTo_processAt.mpr ⟨hkd, hproc⟩,
      by rwa [ACTrace.upTo_deadline hm hkd]⟩
  · intro x hx i B hacc hi y hy j ell hj ht hd hF
    obtain ⟨hid, hacc⟩ := ACTrace.upTo_acceptAt.mp hacc
    obtain ⟨hjd, hj⟩ := (Trace.upTo_callAt _).mp hj
    rw [ACTrace.upTo_deadline hm hjd] at ht hd
    obtain ⟨k, hkj, hak, hkt⟩ := hsy.2 x i B (core.antitone hid hx) hacc hi hid y j ell
      (core.antitone hjd hy) hj hd (hF.mono (RunTrace.honestBlocks_upTo_subset hm ht0))
    have hkd : tr.time k ≤ t := (hm hkj).trans hjd
    exact ⟨k, hkj, ACTrace.upTo_acceptAt.mpr ⟨hkd, hak⟩,
      by rwa [ACTrace.upTo_deadline hm hkd]⟩

/-- Prefix catch-up uses only the core's AC catch-up field. -/
theorem catch_window_at_gbar_at_core
    (core : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) :
    CatchACWindowBefore (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) (gbar g)
      (2 * sp.Δ) d := by
  have hm := core.time_mono
  rw [← RunTrace.upTo_projAC]
  constructor
  intro x hx i B ha hi y hy j ell hj ht hjd hF
  change gbar g + 2 * sp.Δ ≤ tr.time j at ht
  change tr.time j ≤ d at hjd
  rw [RunTrace.upTo_projAC] at ha hj ⊢
  obtain ⟨hid, ha'⟩ := ACTrace.upTo_acceptAt.mp ha
  obtain ⟨_, hj'⟩ := (Trace.upTo_callAt _).mp hj
  obtain ⟨k, hkj, hak, hkt⟩ := core.acCatchAt hc (core.antitone hid hx) ha' hi
    (core.antitone hjd hy) hj' ht (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
  exact ⟨k, hkj, ACTrace.upTo_acceptAt.mpr ⟨(hm hkj).trans hjd, hak⟩, hkt⟩

end Core

/-- **The AC service on a prefix**: the finite reset service, at any release hold, read on the
prefix through `d`, gives the static AC service (message, block and relay delivery) of the
validators honest at `d`. The signed-row clause is not carried: a signing shortly before `d`
may need its signer honest after `d`. -/
theorem ACResetService.upTo_ac_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hs : ACResetService tr H g ΔF) {d : Time} :
    Healing.ACService (tr.upTo d) (H d) g := by
  have hm := hrun.time_mono
  refine ⟨?_, ?_, ?_⟩
  · intro x hx i m hsa y hy j hj hdl
    obtain ⟨hid, hsa⟩ := (RunTrace.upTo_sendOrAdmitAt hm).mp hsa
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.message x i m (hrun.antitone hid hx) hsa y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_processMsgAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB y hy j hj hdl
    have hB' : (tr.time i ≤ d) ∧ (tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B) := by
      rcases hB with hB | hB
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
        exact ⟨h, Or.inl hB⟩
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_ownBlockAt (tr := tr)).mp hB
        exact ⟨h, Or.inr hB⟩
    obtain ⟨hid, hB⟩ := hB'
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.block x i B (hrun.antitone hid hx) hB y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_blockCallAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB hgi y hy j hj hdl hF
    obtain ⟨hid, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    have hd0 : 0 ≤ d := (hrun.time_nonneg j).trans hjd
    rw [RunTrace.upTo_state_of_le hm hjd] at hF
    obtain ⟨k, hkj, hak, hkd⟩ := hs.relay x i B (hrun.antitone hid hx) hB hgi y j
      (hrun.antitone hjd hy) hj hdl (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hk, hak⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
/-- `ACResetService.upTo_ac_at` for the finite reset service, at any release hold. -/
theorem ResetService.upTo_ac_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {b hold : Time} (hs : ResetService tr H g ΔF b hold) {d : Time} :
    Healing.ACService (tr.upTo d) (H d) g :=
  hs.toAC.upTo_ac_at hrun

/-- **AC synchrony from the reset on the prefix through `t`**: for the validators honest at `t`,
over the blocks they hold on that prefix, from any source time `a ≥ g` through `t`. -/
theorem sync_window_at_reset_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hs : ACResetService tr H g ΔF) {t : Time} (hga : g ≤ a) (ht0 : 0 ≤ t) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) :=
  sync_window_at_reset_at_core hrun.toCore hs hga ht0

/-- **Catch from `ḡ` on the prefix through `d`**: an acceptance before `ḡ` by a validator honest
at `d` is accepted before `ḡ + 2Δ` by every validator honest at `d` whose finalized block it
extends, as observed at a call in `[ḡ + 2Δ, d]` (the run's catch-up at the first cut from
`ḡ + 2Δ ≤ d`, with each node honest at its own cut by antitonicity). -/
theorem catch_window_at_gbar_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) :
    CatchACWindowBefore (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) (gbar g)
      (2 * sp.Δ) d :=
  catch_window_at_gbar_at_core hrun.toCore hc hd0

/-- **The committee half bound through `b`** for the slot dictionary `K`: the run's committee
facts at `K`, and fewer than half of each slot committee from `ḡ` by `b` faulty at every read time
`d ∈ [0, b]`. Finite reset premises give their slot committees
(`ResetPremisesUpTo.committeeHalf`). -/
structure CommitteeHalfUpTo (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (K : AC.CommitteeDict sp.n) (g b : Time) : Prop where
  facts : Compose.Growing.CommitteeFacts tr H K
  cs2 : ∀ s : Nat, gbar g ≤ sp.ts s → sp.ts s ≤ b → ∀ d, 0 ≤ d → d ≤ b →
    2 * (K.committee s ∩ (H d)ᶜ).ncard < sp.committeeSize

/-- **The committee half bound of finite reset premises**, at their slot committees
(`committee_cs2_at`). -/
theorem ResetPremisesUpTo.committeeHalf {b : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) :
    CommitteeHalfUpTo tr H (Generic.dictOfTime sp cm) g b :=
  ⟨hp.committeeFacts, fun _ hgs hsb _ hd0 hdb => hp.committee_cs2_at hgs hsb hd0 hdb⟩

/-- **The healthy AC premises on a read prefix, from the service and the committee half bound**:
the finite reset service, awake honest nodes from `ḡ`, the per-time fault bound and catch-up give
the static healthy AC base of the validators honest at a read time `d ∈ [0, b]`, on the prefix
through `d`, over the blocks they hold there, at the slot committees `K` of a run from `K`'s
committee start. Their facts restrict to the prefix, and the committee half bound gives CS2 from
`ḡ` through `d`. No reset is used. -/
theorem CommitteeHalfUpTo.healthy_base_before_at_core
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {K : AC.CommitteeDict sp.n} {b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  have hpre := hrun.upTo hd0
  have hncp := hnc.upTo d
  have hr := hpre.acRun hncp
  have hdr := hpre.driven hncp
  rw [RunTrace.upTo_projAC] at hr hdr
  refine ⟨hr, hdr, sync_window_at_reset_at_core hrun hs.toAC (AC.le_gbar g) hd0,
    catch_window_at_gbar_at_core hrun hc hd0, ?_, hfaults d hd0 hdb, hK.facts.hsize,
    AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP d,
    AC.CommitteeTAt.upTo hrun.antitone (hrun.committeeTAt hK.facts hnc) d,
    fun s hgs hsd => hK.cs2 s hgs (hsd.trans hdb) d hd0 hdb⟩
  intro y hy t hgt htd
  exact (Trace.upTo_awake _ y t).mpr
    ⟨hawake y t (hrun.antitone htd hy) hgt (htd.trans hdb), htd⟩

/-- The stock run is the stock-finality instance of the core healthy-base supplier. -/
theorem CommitteeHalfUpTo.healthy_base_before_at {K : AC.CommitteeDict sp.n} {b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d :=
  hK.healthy_base_before_at_core hrun.toCore hnc hs hawake hfaults hc hd0 hdb

/-- **The healthy AC premises on a read prefix**: finite reset health and catch-up give the
static healthy AC base of the validators honest at a read time `d ∈ [0, b]`, on the prefix
through `d`, over the blocks they hold there, at the run's slot committees
(`CommitteeHalfUpTo.healthy_base_before_at` at `ResetPremisesUpTo.committeeHalf`). -/
theorem healthy_base_of_reset_catch_before_at {b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo (Generic.dictOfTime sp cm) (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d :=
  hp.committeeHalf.healthy_base_before_at hp.run hp.noColl hp.sync hp.awake hp.faults hp.catchUp
    hd0 hdb

end Consensus.Goldilocks.Healing.Growing

end
