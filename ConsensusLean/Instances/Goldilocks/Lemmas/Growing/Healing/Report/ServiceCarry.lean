module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite healing service carries historical votes

The receiver is read on its own honest prefix. A sender need only be honest
at its send or acceptance, not when the receiver later casts.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload Vote gbar)
open Compose.Growing

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

namespace Core

variable {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n →
    Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- The post-GST portion of finite service, projected to AC. -/
theorem service_syncACAt
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {g ΔF b lo hi : Time} (hsvc : ResetService tr H g ΔF b hold) (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp) H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  refine ⟨?_, ?_⟩
  · intro x i m hx hsa hai _ y j ell hy hcj hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ell₀, hc₀, hm⟩ := hsa
      refine ⟨ell₀, Compose.projAC_callAt.1 hc₀, ?_⟩
      have hp := (hrun.upTo (hrun.time_nonneg i)).projAC_state x hx i
      rw [RunTrace.upTo_projAC,
        Trace.upTo_state tr.projAC x (fun _ hk => hrun.time_mono hk.le),
        Trace.upTo_state tr x (fun _ hk => hrun.time_mono hk.le)] at hp
      rwa [hp] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hsvc.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ell', hc', hm'⟩ | ⟨ell', hc', e, he', hem⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ell', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x i B hx hacc hai _ y j ell hy hcj hdl hanc
    apply hrun.acRelayAt (σ := tr.time i) hx hacc hy hcj hanc
    intro k hki hx' hk hj hF
    have hgi : g ≤ tr.time k := hki ▸ hg.trans hai
    have he : max (tr.time k) g = tr.time i := (max_eq_left hgi).trans hki
    simpa only [he] using hsvc.relay x k B hx' hk hgi y j hy hj
      (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- Catch transfers a historically honest acceptance to an independently honest reader. -/
theorem service_catch_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {g : Time} (hcatch : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ell) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ := by
  exact hrun.acCatchAt hcatch hw ha hkw hy hcy hi hanc

/-- Historical sends after `ḡ` and historical accepted heads reach the next-slot cast. -/
theorem carry_of_service_senders
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : AC.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ell.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hac := hrun.acRun hnc
  have hr := (hac.upTo hd).localRun
  have hc' := ac_castAt_upTo.mpr ⟨le_rfl, hcast⟩
  have hsync := service_syncACAt hrun hsvc (lo := g) (hi := sp.ts s + 2 * sp.Δ) le_rfl
  have hgg := le_gbar g
  have hti : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    have hsl := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at hsl
    have h := (AC.ts_le_iff_le_slot sp hd ((s + 1 : Nat) : Int)).2 (by rw [← hsl, hs])
    simp only [ACParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hcarry := carryAt_of_delivered hr hrun.vstart hy hc' hs (CV := CV)
      fun v hv => by
    obtain ⟨hvs, ⟨w, k, hwk, hsend, hk1, hk2⟩, Hv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr, ?_⟩
    · rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := i) hm le_rfl] at hdl
      exact ac_messageServedBefore_upTo hm le_rfl
        ((AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          (hsync.1 w k v hwk hsend (hgg.trans (hts.trans hk1)) hk2.le y i ell hy hcast.1 hdl)))
    rcases hacc with hg | ⟨w', kw, hwkw, hkw, hkwt⟩
    · exact Or.inr (Or.inl hg)
    by_cases hgk : g ≤ tr.time kw
    · refine Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩
      rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := i) hm le_rfl] at hdl
      obtain ⟨ky, hky, hacc', hkyt⟩ := hsync.2 w' kw Hv hwkw hkw hgk hkwt.le y i ell
        hy hcast.1 hdl hFHv
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ac_acceptAt_upTo _).mpr ⟨hkyd, hacc'⟩,
        by rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) (k := ky) hm hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc', hkyt⟩ := service_catch_at hrun hcatch hwkw hkw
        (lt_of_lt_of_le (not_le.mp hgk) hgg) hy hcast.1 (by linarith) hFHv
      exact Or.inr (Or.inr ⟨ky, (ac_acceptAt_upTo _).mpr ⟨hm hky, hacc'⟩,
        show tr.time ky < sp.ts s + 3 * sp.Δ by linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X hX).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ac_acceptAt_upTo _).mp hk).2, hkt⟩

/-- A regular result's counted votes reach the next-slot cast even after its writer's compromise. -/
theorem result_carry_service_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x c s C CV)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hac := hrun.acRun hnc
  have hr := (hac.upTo (hrun.time_nonneg c)).localRun
  apply carry_of_service_senders hrun hnc hsvc hcatch hts hy hc hes
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

end Core

/-- The stock run supplies the shared service projection. -/
theorem service_syncACAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b lo hi : Time} (hsvc : ResetService tr H g ΔF b hold) (hg : g ≤ lo) :
    SyncACAt (goldilocksNode sp) H (tr.HonestBlocksAt H) lo hi tr.projAC :=
  Core.service_syncACAt hrun.toCore hsvc hg

/-- Catch transfers a historically honest acceptance to an independently honest reader. -/
theorem service_catch_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g : Time} (hcatch : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ell) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ :=
  Core.service_catch_at hrun.toCore hcatch hw ha hkw hy hcy hi hanc

/-- Historical sends and accepted heads reach the next-slot cast. -/
theorem carry_of_service_senders
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : AC.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv : AC.Blk sp.n (List (FG.Att sp.n)), Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ell.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ w k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV :=
  Core.carry_of_service_senders hrun.toCore hnc hsvc hcatch hts hy hcast hs hW

/-- A regular result's counted votes reach the next-slot cast after writer compromise. -/
theorem result_carry_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hts : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x c s C CV)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFC : Anc (tr.HonestBlocksAt H) ell.frame.F C) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV :=
  Core.result_carry_service_at hrun.toCore hnc hsvc hcatch hts hx hy hres hc hes hFC

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
