module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupporter
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OptimisticWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularClassification
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
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

/-- The shared service proof carries counted result votes to the next reader. -/
private theorem result_carry_service_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hts : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x c s C CV)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  exact KernelProof.Core.result_carry_service_at hrun.toCore hnc hsvc hcatch hts
    hx hy hres hc hes hFC

/-- The shared service proof compares merged votes with the result writer. -/
private theorem writer_merged_service_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode sp)}
    (hu : AC.UpdateAt tr.projAC x c s ellx) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state x c).pool s ∨
        v.val ∈ AC.equivocators {w | w ∈ (tr.projAC.state x c).pool s} := by
  exact KernelProof.Core.writer_merged_service_at hrun.toCore hnc hsvc hm hx hy hu hc hs

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

/-- The stock fast transfer applied to the shared shadow early-witness induction. -/
theorem regular_fast_next_votes_of_early_witness_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {s M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {isTop : Prop} {J X Q D C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hfast : AC.FastUpdateAt tr.projAC x c s D CV)
    {RV : Set (AC.Vote sp.n)} (hres : AC.ResultAt tr.projAC x c s C RV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  obtain ⟨ellx, C', hu, hconf, hsel, hCV⟩ := hfast
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hPhiU := (AC.frameIn_of_callU hr.toU hx hc').2
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono hPhiU
  apply Shadow.PU.Growing.next_votes_of_frameWindow_at hrun hnc hsvc hawake hf hcatch hm
    (by rw [AC.ts_succ]; linarith only [sp.toParams.hΔ]) hmb hframe hw halo hat hcw hQw hvQ
      (hXD.trans (hDC.trans hCQ))
  intro y i ell e hy hc hs hhigh hFX hviab ih
  exact KernelProof.first_transfer_service_at hrun hnc hsvc hawake hcatch hnr hm hx hy
    (Or.inl ⟨ellx, C, hu, hconf, hsel, hCV⟩) hXD hc hs (hhigh.trans hmb)
    (by rwa [Compose.Growing.frame_of_projAC_at hrun hy hc.1]) hviab
    (fun z k hki hz ev hv hes => ih z k ev hki hz hv hes) hK

/-- The stock slow transfer applied to the shared shadow early-witness induction. -/
theorem regular_slow_next_votes_of_early_witness_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} (hm : gbar g ≤ sp.ts s)
    (hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b) {isTop : Prop}
    {J Q D C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : AC.SlowLockAt tr.projAC x c s D)
    {CV : Set (AC.Vote sp.n)} (hres : AC.ResultAt tr.projAC x c s C CV)
    (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  obtain ⟨ellx, C', hu, hconf, hsel⟩ := hsl
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hsl : AC.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hPhiU := (AC.frameIn_of_callU hr.toU hx hc').2
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono hPhiU
  apply Shadow.PU.Growing.next_votes_of_frameWindow_at hrun hnc hsvc hawake hf hcatch hm
    (by rw [AC.ts_succ]; linarith only [sp.toParams.hΔ]) hmb hframe hw halo hat hcw hQw hvQ
      (hDC.trans hCQ)
  intro y i ell e hy hc hs hhigh hFD hviab ih
  have hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C := by
    rw [Compose.Growing.frame_of_projAC_at hrun hy hc.1]
    exact hFD.trans hDC
  exact AC.Growing.result_transfer_anc hac hx hres hDC hy hc hs
    (result_carry_service_at hrun hnc hsvc hcatch hm hx hy hres hc hs hFC) hviab
    (slow_live_locks_service_at hrun hnc hsvc hx hsl hslow hy hc hs (hhigh.trans hmb) ih hK)
    (writer_merged_service_at hrun hnc hsvc hm hx hy hu hc hs)

/-- The shared supporter proof consumes the shadow two-case classification. -/
theorem next_votes_of_supporter_at {s₀ s M : Nat}
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
    (hbase : Q ∈ ell.frame.tree → Q ∈ ell.frame.viableHeads →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hoptimistic : Q = AC.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, z ∈ H (tr.time a) → AC.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocksAt H) Q D →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg Q) (hK : CommitteeHalfUpTo tr H K g b) :
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
  apply KernelProof.Core.next_votes_of_supporter_at (kindJ := False) (J := J)
    hrun.toCore hnc hz hc hes hQU hQr hXQ ?_ hbase (fun h => h.elim) hoptimistic
  refine ⟨Hd, hHd, hHdr, ?_⟩
  exact hclass.elim (fun hv => Or.inl hv.2) (fun ho => Or.inr (Or.inr ho))

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
  have hr := (hac.upTo (hrun.time_nonneg q)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := AC.vote_time_leU hr.toU hz ⟨ell, hc'.1, he⟩
  have hslot := (AC.castAt_specU hr.toU hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have halo : sp.ts s ≤ tr.time q :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).2 (by rw [hslot])
  apply next_votes_of_supporter_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr (hXD.trans (hDC.trans hCQ)) ?_ ?_ hK
  · intro hQ hvQ
    exact regular_fast_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) hmb (hframe.mono ((AC.ts_le_iff sp).mpr (by omega)) le_rfl)
      hx hfast hres hXD hCQ hz halo (by linarith) hc hQ hvQ hK
  · intro hA a D' CV' hza hop hQD
    have hts := AC.ts_succ s (sp := sp)
    exact (Shadow.PU.Growing.optimistic_supporter_later_heads_at
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD hK (s + 1) le_rfl le_rfl).1

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
  have hr := (hac.upTo (hrun.time_nonneg q)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := AC.vote_time_leU hr.toU hz ⟨ell, hc'.1, he⟩
  have hslot := (AC.castAt_specU hr.toU hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have halo : sp.ts s ≤ tr.time q :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).2 (by rw [hslot])
  apply next_votes_of_supporter_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm' hmb hz ⟨hc, he⟩ hes hQU hQr (hDC.trans hCQ) ?_ ?_ hK
  · intro hQ hvQ
    exact regular_slow_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch
      (by linarith) hslow hmb (hframe.mono ((AC.ts_le_iff sp).mpr (by omega)) le_rfl)
      hx hsl hres hCQ hz halo (by linarith) hc hQ hvQ hK
  · intro hA a D' CV' hza hop hQD
    have hts := AC.ts_succ s (sp := sp)
    exact (Shadow.PU.Growing.optimistic_supporter_later_heads_at
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD hK (s + 1) le_rfl le_rfl).1

end Consensus.Goldilocks.Healing.PU

end
