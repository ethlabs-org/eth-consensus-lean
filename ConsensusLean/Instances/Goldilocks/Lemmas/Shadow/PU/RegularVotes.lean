module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupporter
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OptimisticWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularClassification
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.WriterCompatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Restarts
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Regular next-slot votes over the shadow P-U execution

These interfaces preserve the stock fast and slow next-vote conclusions. The proof ports
reuse the supporter classification and the shared early-witness family.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (ACParams Payload gbar)
open Consensus.Goldilocks.Healing.Growing

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {hold : Time}

/-- Stored slow-window locks compare with the slow origin. -/
private theorem slow_live_locks_service_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    {x : Fin sp.n} {c s : Nat} (hx : x ∈ H (tr.time c))
    {D : AC.Blk sp.n (List (FG.Att sp.n))} (hsl : AC.SlowLockAt tr.projAC x c s D)
    (hm : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b)
    (hE : ∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
      ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg D)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ L ∈ AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L D := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := hac.upTo (hrun.time_nonneg i)
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : sp.slot (tr.time i) = s + 1 :=
    ((AC.castAt_specU hr.localRun.toU hy hc').2.1).symm.trans hs
  have hgs : gbar g ≤ sp.ts (s + 1 : Nat) := hm.trans ((AC.ts_le_iff sp).mpr (by omega))
  have hsb : sp.ts (s + 1 : Nat) ≤ b :=
    ((AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hslot])).trans hib
  have hservice (d : Time) :
      AC.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) g d tr.projAC := by
    constructor
    · intro x k v hx hv hk y j ell hy hj _ hdl
      exact (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl
        ((Healing.Growing.KernelProof.service_syncACAt hrun hsvc (lo := g) le_rfl).1
          x k v hx hv hk le_rfl y j ell hy hj hdl))
    · intro x k B hx hB hk y j ell hy hj _ hdl hanc
      exact (Healing.Growing.KernelProof.service_syncACAt hrun hsvc (lo := g) le_rfl).2
        x k B hx hB hk le_rfl y j ell hy hj hdl hanc
  apply AC.live_locks_of_stored_before hr K
    (AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _)
    (hK.cs2 (s + 1) hgs hsb _ (hrun.time_nonneg i) hib) hy hc' hs ?_ ?_
  · intro l hl hlive hle Y hY hYr
    change sp.slot (tr.time i) ≤ l.slot + sp.k at hlive
    rw [hslot] at hlive
    rw [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] at hl
    have hri := (hac.upTo (hrun.time_nonneg i)).localRun
    obtain ⟨L, hL, hLr, O, hLO, k, hki, CV, ho⟩ :=
      AC.lock_below_origin hri hac.vstart hy i l
        (by rwa [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)])
    obtain rfl : Y = L := hac.localRun.coherent.1 hY hL (hYr.trans hLr.symm)
    have hrx := (hac.upTo (hrun.time_nonneg c)).localRun
    have hsl' : AC.SlowLockAt (tr.projAC.upTo (tr.time c)) x c s D := by
      obtain ⟨ellx, C, hu, hconf, hdeep⟩ := hsl
      refine ⟨ellx, C, (AC.upTo_updateAt hrun.time_mono).mpr ⟨le_rfl, hu⟩, ?_, ?_⟩
      · rwa [Trace.upTo_state tr.projAC x (fun _ hk => hrun.time_mono hk.le)]
      · simpa only [Trace.upTo_state tr.projAC x (fun _ hk => hrun.time_mono hk.le),
          Trace.upTo_time] using hdeep
    obtain ⟨kx, R, CVx, hR, hDR⟩ := AC.slow_window_results hrx hac.vstart hx
      hsl' l.slot (by omega) hle
    obtain ⟨hkxc, hR⟩ := (AC.upTo_resultAt hrun.time_mono).mp hR
    have hxk := hrun.antitone hkxc hx
    have hj : g ≤ sp.ts l.slot := (AC.le_gbar g).trans
      (hm.trans ((AC.ts_le_iff sp).mpr (by omega)))
    have hreset : ∀ {z q j CV B}, z ∈ H (tr.time q) →
        AC.ResultAt tr.projAC z q j B CV →
        ∀ r ≤ q, tr.projAC.RestartAt z r → tr.time r ≤ sp.ts j := by
      rintro z q j CV B hz ⟨ell, hu, -, -⟩ r hr hrst
      exact Compose.update_restarts (hac.upTo (hrun.time_nonneg q)).localRun hz
        ((AC.upTo_updateAt hrun.time_mono).mpr ⟨le_rfl, hu⟩) r hr
        (ACTrace.upTo_restartAt.mpr ⟨hrun.time_mono hr, hrst⟩)
    have hcomp : Compatible (tr.HonestBlocksAt H) O R := by
      rcases ho with ho | ho
      · obtain ⟨hkt, ho⟩ := (AC.upTo_resultAt hrun.time_mono).mp ho
        have hto : tr.time k = sp.ts l.slot + 6 * sp.Δ := by
          obtain ⟨ell, hu, -, -⟩ := ho
          exact hu.2.2.1
        have htr : tr.time kx = sp.ts l.slot + 6 * sp.Δ := by
          obtain ⟨ell, hu, -, -⟩ := hR
          exact hu.2.2.1
        exact AC.Growing.result_result_compatible_window_before_at hac
          (hservice (sp.ts l.slot + 6 * sp.Δ)) hj
          (hrun.antitone hkt hy) hxk ho hR hto.le
          htr.le (hreset (hrun.antitone hkt hy) ho) (hreset hxk hR)
      · obtain ⟨hkt, ho⟩ := (AC.upTo_optimisticLockAt hrun.time_mono).mp ho
        obtain ⟨ellR, huR, hcR, hCVR⟩ := hR
        have hR : AC.ResultAt tr.projAC x kx l.slot R CVx := ⟨ellR, huR, hcR, hCVR⟩
        exact (AC.Growing.result_optimistic_compatible_window_before_at hac
          (b := max (tr.time kx) (tr.time k))
          (hservice _) hj hxk (hrun.antitone hkt hy) hR ho
          (le_max_left _ _) (le_max_right _ _) (hreset hxk hR)
          (fun v hv => hK.facts.hP.1 _ x hxk kx
            (fun _ hk => hrun.time_mono hk.le) l.slot v hv) (hK.facts.hsize l.slot)).symm
    rcases hcomp with hcomp | hcomp
    · exact AC.anc_total hac.localRun.coherent (hLO.trans hcomp) hDR
    · exact AC.anc_total hac.localRun.coherent hLO (hDR.trans hcomp)
  · intro z hz k hki ev he hes
    obtain ⟨hkt, he⟩ := AC.upTo_voteAt.mp he
    exact hE z k ev hki (hrun.antitone hkt hz) he hes

/-- A viable supporter supplies the window witness; an optimistic one supplies its own lock. -/
private theorem regular_next_votes_of_supporter_at {s₀ s M : Nat}
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {z : Fin sp.n} {q : Nat} (hz : z ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocksAt H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ sp.ts s + 6 * sp.Δ →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
  have hΔ := sp.toParams.hΔ
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg q)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have htq := AC.vote_time_leU hr.toU hz ⟨ell, hc'.1, hc'.2⟩
  have hslot := (AC.castAt_specU hr.toU hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, AC.ts_sub_one]
  have hts := AC.ts_succ s (sp := sp)
  have hqhi : tr.time q ≤ sp.ts s + 6 * sp.Δ := by
    change tr.time q ≤ sp.ts s + sp.Δ at htq
    linarith
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := vote_head_classification_of_service_at hframe
    hrun hnc hsvc hawake hf hcatch hnr hz hc hqhi (hqhi.trans hmb)
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by simpa only [hes] using hm) (by
      rw [hes]; simp only [AC.freeze]
      have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      rw [← hcast]
      linarith only [hΔ, hm]) hK
  refine KernelProof.next_votes_of_supporter_at hrun hnc hz hc hes hQU hQr hXQ
    ⟨Hd, hHd, hHdr, hclass.imp (fun hv => hv.2) id⟩ ?_ ?_
  · intro hQ hvQ
    have hframe := hframe.mono ((AC.ts_le_iff sp).mpr (by omega : (s₀ : Int) ≤ s)) le_rfl
    have halo : sp.ts s ≤ tr.time q :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).2 (by rw [hslot])
    have hwit := Shadow.PU.Growing.early_witness_viable hrun hframe hz halo hqhi hc.1 hvQ
    have hQ' := hQ
    rw [Compose.Growing.frame_of_projAC_at hrun hz hc.1, Node.frame_eq, Store.toFrame_tree] at hQ'
    exact Shadow.PU.Growing.next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch
      (by linarith) (by linarith) hmb hz (by linarith) hc.1 hQ
      (Healing.windowWitness_of_frameWindow hrun hnc hframe hz hQ'.1 hwit)
      (fun y i hy hlo hhi => hframe.finalized_below_descendant_at hrun hnc hy hz hz
        (sp.toParams.fg.faults_lt_quorum_margin
          (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
            (hqhi.trans hmb)))) hlo hhi hQ'.1 hwit hQ'.1 .refl) hXQ htransfer
  · intro hA a D CV hza hop hQD
    exact (Shadow.PU.Growing.optimistic_supporter_later_heads_at
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza hc hes hA hop hQD hK (s + 1) le_rfl le_rfl).1

/-- A regular fast selection constrains next-slot votes. -/
theorem regular_fast_next_votes_at {s₀ s M : Nat}
    {isTop : Prop} {J X D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hfast : AC.FastUpdateAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨ellx, C, hu, hconf, hsel, hCV⟩ := hfast
  have hfast : AC.FastUpdateAt tr.projAC x c s D CV :=
    ⟨ellx, C, hu, hconf, hsel, hCV⟩
  have hres : AC.ResultAt tr.projAC x c s C
      (AC.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, AC.ts_sub_one]
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    Healing.Growing.KernelProof.result_honest_supporter_before_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith)
      hx hres (hu.2.2.1.trans_le hmb) hK
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hrx := (hac.upTo (hrun.time_nonneg c)).localRun
  have hcx := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono (AC.frameIn_of_callU hrx.toU hx hcx).2
  apply regular_next_votes_of_supporter_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr (hXD.trans (hDC.trans hCQ)) ?_ hK
  intro y i ell' ev hy hv hs hhigh hFX hviab ih
  exact KernelProof.first_transfer_service_at hrun hnc hsvc hawake hcatch hnr (by linarith)
    hx hy (Or.inl hfast) hXD hv hs (hhigh.trans hmb)
    (by rwa [Compose.Growing.frame_of_projAC_at hrun hy hv.1]) hviab
    (fun z k hki hz ev hv hes => ih z k ev hki hz hv hes) hK

/-- A regular slow selection constrains next-slot votes. -/
theorem regular_slow_next_votes_at {s₀ s M : Nat}
    {isTop : Prop} {J D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : AC.SlowLockAt tr.projAC x c s D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  have hΔ := sp.toParams.hΔ
  have hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1) := by
    have hts : sp.ts s₀ ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (AC.ts_le_iff sp).mpr (by omega)
    linarith
  have hm' : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int) :=
    hm.trans ((AC.ts_le_iff sp).mpr (by exact_mod_cast hs₀))
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, AC.ts_sub_one]
  obtain ⟨ellx, C, hu, hconf, hsel⟩ := hsl
  have hsl : AC.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hres : AC.ResultAt tr.projAC x c s C
      (AC.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    Healing.Growing.KernelProof.result_honest_supporter_before_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith)
      hx hres (hu.2.2.1.trans_le hmb) hK
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hrx := (hac.upTo (hrun.time_nonneg c)).localRun
  have hcx := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono (AC.frameIn_of_callU hrx.toU hx hcx).2
  apply regular_next_votes_of_supporter_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm' hmb hz ⟨hc, he⟩ hes hQU hQr (hDC.trans hCQ) ?_ hK
  intro y i ell' ev hy hv hs hhigh hFD hviab ih
  have hts : gbar g ≤ sp.ts s := by linarith
  have hFC : Anc (tr.HonestBlocksAt H) ell'.frame.F C := by
    rw [Compose.Growing.frame_of_projAC_at hrun hy hv.1]
    exact hFD.trans hDC
  exact AC.Growing.result_transfer_anc hac hx hres hDC hy hv hs
    (KernelProof.result_carry_service_at hrun hnc hsvc hcatch hts hx hy hres hv hs hFC) hviab
    (slow_live_locks_service_at hrun hnc hsvc hx hsl hslow hy hv hs (hhigh.trans hmb) ih hK)
    (KernelProof.writer_merged_service_at hrun hnc hsvc hts hx hy hu hv hs)

end Consensus.Goldilocks.Healing.PU

end
