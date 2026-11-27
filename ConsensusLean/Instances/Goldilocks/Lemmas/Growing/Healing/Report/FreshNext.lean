module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.CoreLift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next-slot extension from the warm frame

The warm frame supplies the fork-choice root and height floor at each cast.
Participation is counted at that cast, never at a fixed honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

namespace Core

variable
  {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {ini : Fin sp.n → (goldilocksNode sp).State}

private theorem relayed_of_service
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) {z : Fin sp.n} {k : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hgk : g ≤ tr.time k)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time k) ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < tr.projAC.deadline y k' (tr.time k) := by
  apply hrun.acRelayAt (σ := tr.time k) hz hacc hy hci hanc
  intro q hq hz' haq hj hF
  have hgq : g ≤ tr.time q := hq ▸ hgk
  have he : max (tr.time q) g = tr.time k := (max_eq_left hgq).trans hq
  simpa only [he] using hsvc.relay z q B hz' haq hgq y i hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

private theorem carry_votes
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg i
  have hΔ := sp.toParams.hΔ
  have hgg := AC.le_gbar g
  have hU := hrun.coherent hnc
  have hsub := hrun.upTo_subset hd
  have hac := hrun.acRun_upTo hnc hd
  have hr := hac.localRun
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time i := by
    have h := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hcarry := Compose.carryAt_of_served hr hac.vstart (Compose.frame_anc_acceptedU hr.toU hy)
    hy hc' hs (CV := Compose.Growing.honestVotes tr H u) fun v hv => by
    obtain ⟨z, q, e', hz, ⟨ell', hcz⟩, rfl, hsl⟩ := hv
    have hdq := hrun.time_nonneg q
    have haq := hrun.acRun_upTo hnc hdq
    have hrq := haq.localRun
    have hcz' : AC.CastAt (tr.projAC.upTo (tr.time q)) z q ell' e' :=
      AC.upTo_castAt.mpr ⟨le_rfl, hcz⟩
    have hslq := (AC.castAt_specU hrq.toU hz hcz').2.1
    change e'.msg.slot = sp.slot (tr.time q) at hslq
    have hqts : sp.ts u ≤ tr.time q := (AC.ts_le_iff_le_slot sp hdq _).2 (by omega)
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq haq.vstart hz hcz'
    rw [hsl] at hqt
    change tr.time q ≤ _ at hqt
    have hqi : tr.time q ≤ tr.time i := by linarith
    have hHdp := (AC.frameIn_of_callAt hrq hz hcz'.1).2 hHd
    obtain rfl : Hd = P := hU.1 (hrun.upTo_subset hdq hHdp) hP
      (hHdr.trans (hun z q e' hz ⟨ell', hcz⟩ (hqi.trans hib) hsl))
    refine ⟨hsl, ⟨tr.time q, hqts, by linarith, fun hdl => ?_⟩, Hd, hHdr, ?_⟩
    · rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      exact (AC.upTo_messageServedBefore hmA le_rfl).mpr
        (served_of_resetService hsvc hz hcz (hgg.trans (hg.trans hqts)) hy hcast.1 hdl)
    rcases Compose.frame_anc_acceptedU hrq.toU hz q ell' hcz'.1 Hd hHd Hd .refl with
      h0 | ⟨k, hk, ha⟩
    · exact Or.inr (Or.inl h0)
    obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
    change tr.time k ≤ tr.time q at hkq
    have hzk := hrun.antitone hkq hz
    by_cases hkg : gbar g ≤ tr.time k
    · refine Or.inl ⟨tr.time k, by linarith, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      obtain ⟨ky, hky, hacc, hkyt⟩ := relayed_of_service hrun hsvc hzk ha (hgg.trans hkg) hy
        hcast.1 hdl hFP
      have hkyd := hm hky
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hkyd, hacc⟩,
        by rw [ACTrace.upTo_deadline hmA hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc, hkyt⟩ := hrun.acCatchAt hc hzk ha (not_le.mp hkg) hy
        hcast.1 (by linarith) hFP
      exact Or.inr (Or.inr ⟨ky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr
        ⟨hm hky, hacc⟩, by change tr.time ky < _; linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (hrun.anc_upTo_of_right hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp hk).2, hkt⟩

private theorem head_accepted
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    (hcall : tr.projAC.CallAt y j ell) (hti : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    ∃ k' ≤ j, tr.projAC.AcceptAt y k' P ∧ tr.time k' < sp.ts u + 3 * sp.Δ := by
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hU := hrun.coherent hnc
  obtain ⟨w, q, e', hwq, ⟨ellv, hv⟩, hvs, hq⟩ := hvote
  have hqj : tr.time q ≤ tr.time j := by linarith
  have hrq := hrun.acRun_upTo hnc (hrun.time_nonneg q)
  have hvq : AC.CastAt (tr.projAC.upTo (tr.time q)) w q ellv e' :=
    AC.upTo_castAt.mpr ⟨le_rfl, hv⟩
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hrq.localRun hrq.vstart hwq hvq
  have hHdq := (AC.frameIn_of_callAt hrq.localRun hwq hvq.1).2 hHd
  obtain rfl : Hd = P := hU.1 (hrun.upTo_subset (hrun.time_nonneg q) hHdq) hP
    (he.trans (hun w q e' hwq ⟨ellv, hv⟩ (hqj.trans hjb) hvs))
  obtain hz | ⟨k, hk, ha⟩ := AC.frame_genesis_or_acceptedU sp hrq.localRun.toU hwq hvq.1 Hd hHd
  · omega
  obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
  change tr.time k ≤ tr.time q at hkq
  have hwk := hrun.antitone hkq hwq
  have hdl : ∀ c ≤ j, tr.projAC.deadline y c (tr.time k) ≤ max (tr.time k) (gbar g) + sp.Δ :=
    fun c hcj => Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
      (fun r hrc hrs => hnr r (hrc.trans hcj) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
  by_cases hkg : gbar g ≤ tr.time k
  · obtain ⟨k', hk'j, ha', hlt⟩ := relayed_of_service hrun hsvc hwk ha
      ((AC.le_gbar g).trans hkg) hy hcall
      ((hdl j le_rfl).trans (by rw [max_eq_left hkg]; linarith)) hanc
    have := hdl k' hk'j
    rw [max_eq_left hkg] at this
    exact ⟨k', hk'j, ha', by linarith⟩
  · obtain ⟨k', hk'j, ha', hlt⟩ := hrun.acCatchAt hc hwk ha (not_le.mp hkg) hy
      hcall (by linarith) hanc
    exact ⟨k', hk'j, ha', by linarith⟩

private theorem cast_bounds
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) :
    sp.ts e.msg.slot ≤ tr.time j ∧ tr.time j ≤ sp.ts e.msg.slot + sp.Δ := by
  have hr := hrun.acRun_upTo hnc (hrun.time_nonneg j)
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hs := (AC.castAt_specU hr.localRun.toU hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at hs
  exact ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega),
    (Compose.cast_head_fcRoot hr.localRun hr.vstart hy hc').2⟩

private theorem next_viable
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b)
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hroot : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P)
    (hv : P ∈ ell.frame.viableHeads) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hd := hrun.time_nonneg j
  have hr := hrun.acRun_upTo hnc hd
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr.localRun hy hc'.1
  have hsub := hrun.upTo_subset hd
  have hFP := ((hPhi.F_anc_fcRoot.mono hPhiU).mono hsub).trans hroot
  have hti := (cast_bounds hrun hnc hy hcast).1
  have hΔ := sp.toParams.hΔ
  rw [hs] at hti
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨k, hkj, ha, hkt⟩ := head_accepted hrun hnc hsvc hc hP hslot hu hun hg hy hcast.1
    (by linarith) hjb hnr hvote hFP
  have ha' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y k P :=
    (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hrun.time_mono hkj, ha⟩
  have hPu : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    obtain ⟨ella, hca, hea⟩ := ha'
    exact (AC.frameIn_of_callAt hr.localRun hy hca).2
      ((AC.accept_new sp hr.localRun hy ⟨ella, hca, hea⟩).1 ella hca)
  have hroot' := hrun.anc_upTo_of_right hnc hd hPu hroot
  have hFP' := (hPhi.F_anc_fcRoot.mono hPhiU).trans hroot'
  have hPt := AC.mem_tree_of_acceptAtU sp hr.localRun.toU hy ha' hkj hc'.1 hFP'
  have hfreeze : AC.freeze sp e.msg.slot = sp.ts u + 3 * sp.Δ := by
    simp only [AC.freeze, hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hstamp := AC.readPoint_blockStamp_lt_of_acceptedBefore hr.localRun hr.vstart hy hc' hPt
    (Or.inr ⟨k, ha', by rw [hfreeze]; exact hkt⟩)
    (fun r hrj hrs => by
      rw [hfreeze]
      change tr.time r < _
      obtain ⟨ella, hca, hea⟩ := hrs
      have := hnr r hrj (Compose.projAC_restartAt.mp
        ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩)
      linarith) (by rw [hfreeze]; change _ ≤ tr.time j; linarith)
  have hPv : P ∈ AC.voterBlockTree sp e.readPoint ell.frame (u + 1) :=
    ⟨hPt, Or.inl (by simpa only [hs] using hstamp)⟩
  have hanc := AC.anc_tree_of_anc_U hr.localRun.coherent hPhi hPhiU hPhi.fcRoot_mem hroot' hPt
  exact ⟨hFP, hPv, hanc, P, hPv, hv, .refl⟩

private theorem next_votes
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hnr : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ gbar g)
    (hwit : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hvotes : ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → x ∈ K.committee u → ∃ q e,
      AC.VoteAt tr.projAC x q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ)
    (hfault : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK K u tr.projAC (H (tr.time i)) (tr.time i))
    (hcs2 : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * (K.committee (u + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (geometry : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have all : ∀ j, tr.time j ≤ b → ∀ y e, y ∈ H (tr.time j) →
      AC.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y e hy ⟨ell, hcast⟩ hs
      have htime := (cast_bounds hrun hnc hy hcast).1
      rw [hs] at htime
      obtain ⟨hroot, hv⟩ := geometry y j ell e hy hcast hs hjb
      obtain ⟨hFP, hvi⟩ := next_viable hrun hnc hsvc hc hP hslot hu hun hg hy hcast hs hjb
        (fun r hrj hrs => hnr y r (hrun.antitone (hrun.time_mono hrj) hy) hrs
          ((hrun.time_mono hrj).trans hjb)) hwit hroot hv
      have hcarry := carry_votes hrun hnc hsvc hc hP hun hg hy hcast hs hjb hFP
      have hf := hfault j htime hjb
      have hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
          AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u}.ncard := by
        have hsub : K.committee u ∩ H (tr.time j) ⊆ {x | x ∈ H (tr.time j) ∧ ∃ q e',
            x ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u} := by
          rintro x ⟨hxK, hx⟩
          obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x (hrun.antitone htime hx) hxK
          exact ⟨hx, q, e', hrun.antitone (by linarith) hx, hv, hvs⟩
        have h₁ := Set.ncard_le_ncard hsub
        have h₂ := Set.ncard_le_ncard (s := K.committee u ∩ {y | y ∈ H (tr.time j) ∧
            tr.projAC.awake y (tr.time j) ∧ AC.JoinedAt tr.projAC y (tr.time j)})
          (t := K.committee u ∩ H (tr.time j)) (fun x hx => ⟨hx.1, hx.2.1⟩)
        have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u) (H (tr.time j))
          (Set.toFinite _)
        rw [hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time j))ᶜ] at hsplit
        unfold AC.FaultBoundK at hf
        omega
      refine AC.Growing.next_transfer_from (hrun.acRun hnc) K hPK hTK hsize hy hcast hs ?_
        hhalf hcarry hf (hcs2 j htime hjb) (Or.inl hvi) ?_
      · intro x q e' hx hv hvs
        have hq := (cast_bounds hrun hnc hx hv.choose_spec).2
        rw [hvs] at hq
        exact ⟨P, hP, (hun x q e' hx hv (by linarith) hvs).symm, .refl⟩
      · intro x q hq hx e' hv hvs
        exact ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
  exact fun y j e hy hv hjb hs => all j hjb y e hy hv hs

/-- Next-slot extension from call-local full-frame geometry, independently of the frame handler. -/
theorem unanimous_next_votes_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root) (hK : CommitteeHalfUpTo tr H K g b)
    (geometry : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have _ := hdes
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [ACParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [AC.gbar_nonneg g]
  have hshort : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) := by
    simp only [ACParams.ts]; push_cast; linarith
  have hdeadline : sp.ts u + sp.Δ ≤ b := by linarith
  have hnextb : sp.ts (u + 1 : Nat) ≤ b := by linarith
  have hS := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [AC.gbar_nonneg g]) hdeadline
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  have hPh : P ∈ tr.HonestBlocksAt H := by
    have ht : tr.time kP = sp.ts u := by
      simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
    have hzP : z ∈ H (tr.time kP) := hrun.antitone (by rw [ht]; linarith) hz
    have hp := hrun.upTo (hrun.time_nonneg kP)
    have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
    obtain ⟨ha, hta, _⟩ := hp.ac_block_after z hzP
      (hp.accept_of_proposesAt (hnc.upTo _) hzP hP').1
    have hzA : z ∈ H (tr.time (kP + 1)) := hta ▸ hzP
    rw [RunTrace.upTo_projAC] at ha
    obtain ⟨ella, hca, hea⟩ := ha
    have ha' : tr.projAC.AcceptAt z (kP + 1) P :=
      ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
    have hr := hrun.acRun_upTo hnc (hrun.time_nonneg (kP + 1))
    have ha'' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time (kP + 1))) z (kP + 1) P :=
      (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨le_rfl, ha'⟩
    obtain ⟨ellb, hcb, heb⟩ := ha''
    exact hrun.upTo_subset (hrun.time_nonneg (kP + 1))
      ((AC.frameIn_of_callAt hr.localRun hzA hcb).2
        ((AC.accept_new sp hr.localRun hzA ⟨ellb, hcb, heb⟩).1 ellb hcb))
  -- an honest member of the slot-`u` committee witnesses `P` by the slot's vote deadline
  have hnext0 : 0 ≤ sp.ts (u + 1 : Nat) := (AC.gbar_nonneg g).trans (hgu.trans (by linarith))
  obtain ⟨w, hwK, hw⟩ : (K.committee u ∩ H (sp.ts (u + 1 : Nat))).Nonempty := by
    have hcs := hK.cs2 u hgu (by linarith) _ hnext0 hnextb
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u)
      (H (sp.ts (u + 1 : Nat))) (Set.toFinite _)
    rw [hK.facts.hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H _)ᶜ] at hsplit
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  have hw' := hrun.antitone hshort hw
  obtain ⟨q, e, hv, hes, hq⟩ := hvotes w hw' hwK
  refine next_votes hrun hnc hsvc hcatch hPh hPs hu0
    (fun y j e hy hv _ hs => hun y j e hy hv hs) hgu hK.facts.hP (hrun.committeeTAt hK.facts hnc)
    hK.facts.hsize (fun y k hy hk _ => hnr y k hy hk)
    ⟨w, q, e, hrun.antitone hq hw', hv, hes, hq⟩
    (fun x hx hxK => hvotes x (hrun.antitone hshort hx) hxK) ?_ ?_ geometry
  · intro i hlo hib
    have hslot : u + 1 ≤ sp.slot (tr.time i) := by
      exact_mod_cast (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hlo
    exact KernelProof.Core.faultBoundK_of_service_at hK hrun hawake hnr hgu (by linarith)
      (hrun.time_nonneg i) (hgu.trans ((AC.ts_le_iff sp).2 (by omega))) hib
  · intro i hlo hib
    exact hK.cs2 (u + 1) (hgu.trans (by linarith)) hnextb _ (hrun.time_nonneg i) hib

end Core

end Consensus.Goldilocks.Healing.Growing

end
