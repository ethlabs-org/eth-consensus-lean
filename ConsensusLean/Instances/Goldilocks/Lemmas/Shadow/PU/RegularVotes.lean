module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularClassification
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Regular next-slot votes over the shadow P-U execution

These interfaces preserve the stock fast and slow next-vote conclusions. The proof ports
reuse the supporter classification and the shared early-witness family.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- The shadow FG catch-up bridge supplies the stock AC acceptance witness. -/
theorem service_catch_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini)
    {g : Time} (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {w : Fin sp.n} {kw : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ell : ACLabel (goldilocksNode' sp ro)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ell) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ :=
  Growing.LocalRun'.acCatchAt' hrun.toLocalRun' hcatch hw ha hkw hy hcy hi hanc

/-- The stock committee count uses only honesty, awake service and restart bounds. -/
theorem faultBoundK_of_service_at' {K : AC.CommitteeDict sp.n} {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g)) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b)
    {t : Time} (ht0 : 0 ≤ t) (hprev : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) (htb : t ≤ b) :
    AC.FaultBoundK K s tr.projAC (H t) t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (AC.ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : K.committee s ∩ H t ⊆ K.committee s ∩
      {y | y ∈ H t ∧ tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t} := by
    rintro y ⟨hyK, hy⟩
    refine ⟨hyK, hy, hawake y t hy (hprev.trans hts) htb, ?_⟩
    intro k hk hkt
    exact (hnr y k (hrun.antitone hkt hy) (Compose.projAC_restartAt.mp hk)).trans hprev
  have hf := hK.cs2 s hgs hsb t ht0 htb
  have hsplit : (K.committee s ∩ H t).ncard + (K.committee s ∩ (H t)ᶜ).ncard =
      sp.committeeSize := by
    rw [← hK.facts.hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  unfold AC.FaultBoundK
  exact lt_of_lt_of_le (by omega) (Set.ncard_le_ncard hsub)

/-- Historical messages and accepted heads are carried by the next-slot voter. -/
private theorem carry_of_service_senders'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hts : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode' sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    {CV : Set (AC.Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : AC.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ell.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hm := hrun.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hsync := service_syncACAt' hrun hsvc (lo := g) (hi := sp.ts s + 2 * sp.Δ) le_rfl
  have hgg := AC.le_gbar g
  have hti : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    have hsl := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at hsl
    have h := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) ((s + 1 : Nat) : Int)).2
      (by rw [← hsl, hs])
    rw [AC.ts_succ] at h
    exact h
  have hcarry := Compose.Growing.carryAt_of_delivered hr hac.vstart hy hc' hs (CV := CV)
      fun v hv => by
    obtain ⟨hvs, ⟨w, k, hwk, hsend, hk1, hk2⟩, Hv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr, ?_⟩
    · rw [ACTrace.upTo_deadline (tr := tr.projAC) (d := tr.time i) (i := i) hm le_rfl]
        at hdl
      exact Compose.Growing.ac_messageServedBefore_upTo hm le_rfl
        ((AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          (hsync.1 w k v hwk hsend (hgg.trans (hts.trans hk1)) hk2.le
            y i ell hy hcast.1 hdl)))
    rcases hacc with hg | ⟨w', kw, hwkw, hkw, hkwt⟩
    · exact Or.inr (Or.inl hg)
    by_cases hgk : g ≤ tr.time kw
    · refine Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (tr := tr.projAC) (d := tr.time i) (i := i) hm le_rfl]
        at hdl
      obtain ⟨ky, hky, hacc', hkyt⟩ := hsync.2 w' kw Hv hwkw hkw hgk hkwt.le
        y i ell hy hcast.1 hdl hFHv
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt).mpr ⟨hm hky, hacc'⟩,
        by rw [ACTrace.upTo_deadline (tr := tr.projAC) hm (hm hky)]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc', hkyt⟩ := service_catch_at' hrun hcatch hwkw hkw
        (lt_of_lt_of_le (not_le.mp hgk) hgg) hy hcast.1 (by linarith [sp.toParams.hΔ]) hFHv
      exact Or.inr (Or.inr ⟨ky, ACTrace.upTo_acceptAt.mpr ⟨hm hky, hacc'⟩,
        show tr.time ky < sp.ts s + 3 * sp.Δ by linarith [sp.toParams.hΔ]⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  exact ⟨Hv, hHv, hHvr, fun X hX => (hacc X hX).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, (ACTrace.upTo_acceptAt.mp hk).2, hkt⟩⟩

/-- Unresolved AC service input: a fast lock transfers at the next cast. -/
private theorem first_transfer_service_at'
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {B D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfl : AC.FastLockAt tr.projAC x c s D CV) (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hviab : AC.ViableAtVote ell e (s + 1) B)
    (hearlier : AC.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

/-- Unresolved AC service input: counted result votes reach the next reader. -/
private theorem result_carry_service_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hts : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x c s C CV)
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  apply carry_of_service_senders' hrun hnc hsvc hcatch hts hy hc hes
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hlo, hhi⟩, Hv, -, hroot, hanc, hacc⟩ :=
    Compose.result_writer hr hac.vstart hx
      ((AC.upTo_resultAt hrun.time_mono).mpr ⟨le_rfl, hres⟩) v hv
  obtain ⟨hkt, hk⟩ := (ACTrace.upTo_sendOrAdmit hrun.time_mono).mp hk
  refine ⟨hvs, ⟨x, k, hrun.antitone hkt hx, hk, hlo, hhi⟩, Hv, hroot,
    hFC.trans hanc, ?_⟩
  exact hacc.imp_right fun ⟨k', hk', htime⟩ => by
    obtain ⟨hkt', hk'⟩ := ACTrace.upTo_acceptAt.mp hk'
    exact ⟨x, k', hrun.antitone hkt' hx, hk', htime⟩

/-- Unresolved AC service input: a receiver's merged votes reach the result writer. -/
private theorem writer_merged_service_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode' sp ro)}
    (hu : AC.UpdateAt tr.projAC x c s ellx) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state x c).pool s ∨
        v.val ∈ AC.equivocators {w | w ∈ (tr.projAC.state x c).pool s} := by
  exact AC.Growing.writer_merged
    (Compose.Growing.goldilocks_ac_projection_from' hrun hnc)
    hx hu hy hc hs (service_syncACAt' hrun hsvc ((AC.le_gbar g).trans hm))

/-- Unresolved AC service input: stored slow-window locks compare with the slow origin. -/
private theorem slow_live_locks_service_at'
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    {x : Fin sp.n} {c s : Nat} (hx : x ∈ H (tr.time c))
    {D : AC.Blk sp.n (List (FG.Att sp.n))} (hsl : AC.SlowLockAt tr.projAC x c s D)
    (hm : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b)
    (hE : ∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
      ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg D)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ L ∈ AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L D := by
  sorry

/-- The stock fast transfer applied to the shared shadow early-witness induction. -/
theorem regular_fast_next_votes_of_early_witness_at'
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {s M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {isTop : Prop} {J X Q D C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hfast : AC.FastUpdateAt tr.projAC x c s D CV)
    {RV : Set (AC.Vote sp.n)} (hres : AC.ResultAt tr.projAC x c s C RV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
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
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hPhiU := (AC.frameIn_of_callU hr.toU hx hc').2
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono hPhiU
  apply Shadow.PU.Growing.next_votes_of_early_witness_at' hrun hnc hsvc hawake hf hcatch hm
    (by rw [AC.ts_succ]; linarith only [sp.toParams.hΔ]) hmb hframe hw halo hat hcw hQw hvQ
      (hXD.trans (hDC.trans hCQ))
  intro y i ell e hy hc hs hhigh hFX hviab ih
  exact first_transfer_service_at' hrun hnc hsvc hawake hcatch hnr hm hx hy
    (Or.inl ⟨ellx, C, hu, hconf, hsel, hCV⟩) hXD hc hs (hhigh.trans hmb)
    (by rwa [Shadow.PU.Growing.frame_of_projAC_at' hrun hy hc.1]) hviab
    (fun z k hki hz ev hv hes => ih z k ev hki hz hv hes) hK

/-- The stock slow transfer applied to the shared shadow early-witness induction. -/
theorem regular_slow_next_votes_of_early_witness_at'
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} (hm : gbar g ≤ sp.ts s)
    (hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b) {isTop : Prop}
    {J Q D C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : AC.SlowLockAt tr.projAC x c s D)
    {CV : Set (AC.Vote sp.n)} (hres : AC.ResultAt tr.projAC x c s C CV)
    (hCQ : Anc (tr.HonestBlocksAt H) C Q)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
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
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩
  have hPhiU := (AC.frameIn_of_callU hr.toU hx hc').2
  have hDC := ((AC.deepest_mem hsel).1.1.2.2).mono hPhiU
  apply Shadow.PU.Growing.next_votes_of_early_witness_at' hrun hnc hsvc hawake hf hcatch hm
    (by rw [AC.ts_succ]; linarith only [sp.toParams.hΔ]) hmb hframe hw halo hat hcw hQw hvQ
      (hDC.trans hCQ)
  intro y i ell e hy hc hs hhigh hFD hviab ih
  have hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C := by
    rw [Shadow.PU.Growing.frame_of_projAC_at' hrun hy hc.1]
    exact hFD.trans hDC
  exact AC.Growing.result_transfer_anc hac hx hres hDC hy hc hs
    (result_carry_service_at' hrun hnc hsvc hcatch hm hx hy hres hc hs hFC) hviab
    (slow_live_locks_service_at' hrun hnc hsvc hx hsl hslow hy hc hs (hhigh.trans hmb) ih hK)
    (writer_merged_service_at' hrun hnc hsvc hm hx hy hu hc hs)

/-- Interface-only shadow port of the regular fast next-vote base. -/
theorem next_votes_of_supporter_at' {s₀ s M : Nat}
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
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
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
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
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
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
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := vote_head_classification_of_service_at' hframe
    hrun hnc hsvc hawake hf hcatch hnr hz hc hqhi (hqhi.trans hmb)
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by simpa only [hes] using hm) (by
      rw [hes]; simp only [AC.freeze]
      have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      rw [← hcast]
      linarith only [hΔ, hm]) hK
  have hPhiU := (AC.frameIn_of_callU hr.toU hz hc'.1).2
  have hEQ : Hd = Q := (Coherence.honestBlocksAt_coherent' hrun hnc).1
    (hPhiU hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | ho
  · exact hbase hHd hv.2
  · obtain ⟨hA, l, hl, hls, a, hai, D, CV, hza, hop, -, -, -, hQD⟩ := ho
    have hheads := hoptimistic hA a D CV hza (hes ▸ hop) (hQD.mono hPhiU)
    intro y i ev hy hv hesv
    obtain ⟨W, hW, hWr, hQW⟩ := hheads y i ev hy hv hesv
    exact ⟨W, hW, hWr, hXQ.trans hQW⟩

/-- Interface-only shadow port of the regular fast next-vote base. -/
theorem regular_fast_next_votes_at' {s₀ s M : Nat}
    {isTop : Prop} {J X D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
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
    result_honest_supporter_before_at' hrun hnc hsvc hawake hf hcatch hnr (by linarith)
      hx hres (hu.2.2.1.trans_le hmb) hK
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
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
  apply next_votes_of_supporter_at' hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr (hXD.trans (hDC.trans hCQ)) ?_ ?_ hK
  · intro hQ hvQ
    exact regular_fast_next_votes_of_early_witness_at' hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) hmb (hframe.mono ((AC.ts_le_iff sp).mpr (by omega)) le_rfl)
      hx hfast hres hXD hCQ hz halo (by linarith) hc hQ hvQ hK
  · intro hA a D' CV' hza hop hQD
    have hts := AC.ts_succ s (sp := sp)
    exact (Shadow.PU.Growing.optimistic_supporter_later_heads_at'
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD hK (s + 1) le_rfl le_rfl).1

/-- Interface-only shadow port of the regular slow next-vote base. -/
theorem regular_slow_next_votes_at' {s₀ s M : Nat}
    {isTop : Prop} {J D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
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
    result_honest_supporter_before_at' hrun hnc hsvc hawake hf hcatch hnr (by linarith)
      hx hres (hu.2.2.1.trans_le hmb) hK
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
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
  apply next_votes_of_supporter_at' hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm' hmb hz ⟨hc, he⟩ hes hQU hQr (hDC.trans hCQ) ?_ ?_ hK
  · intro hQ hvQ
    exact regular_slow_next_votes_of_early_witness_at' hrun hnc hsvc hawake hf hcatch
      (by linarith) hslow hmb (hframe.mono ((AC.ts_le_iff sp).mpr (by omega)) le_rfl)
      hx hsl hres hCQ hz halo (by linarith) hc hQ hvQ hK
  · intro hA a D' CV' hza hop hQD
    have hts := AC.ts_succ s (sp := sp)
    exact (Shadow.PU.Growing.optimistic_supporter_later_heads_at'
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD hK (s + 1) le_rfl le_rfl).1

end Consensus.Goldilocks.Healing.PU

end
