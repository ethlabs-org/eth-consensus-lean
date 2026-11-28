module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The no-Catch carry steps of retained high-origin votes

The growing forms of `Healing.ResetPremisesUpTo.first_carry_of_finalized_anc` and
`later_carry_of_finalized_anc` (`Healing/Retention/Boot`), without the catch-up premise: every
counted vote is sent, and its head accepted, by a node honest at that cut, after GST
(`carry_of_post_gst_senders_at`).

An acceptance of a head above a high origin is after the snapshot cut `c_z`
(`cutZ_lt_of_anc_at`), which needs the holder honest at the later of the acceptance and `c_z`:
the first carry's writer is honest at its write and at `c_z` (`HighOrigin`); a later carry's
voter casts its vote of label `m > j` after `c_z`, so its acceptance before the vote is read
there. A genesis head is excluded by the height of a high origin (`not_genesis_above_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Vote Payload)
open ProposalImpl

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- **An acceptance of a head above a high origin is after GST**, for an acceptor honest
at the later of its acceptance and `c_z`. -/
private theorem gst_le_acceptance {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {w : Fin sp.n} {c : Nat}
    (hw : w ∈ H (max (tr.time c) (cutZ sp.toParams g)))
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hacc : tr.projAC.AcceptAt w c W)
    (hBW : Anc (tr.HonestBlocksAt H) B W) : g ≤ tr.time c := by
  have rc := hp.core
  have hwc := rc.antitone (le_max_left _ _) hw
  have hac := rc.acRun hp.noColl
  obtain ⟨ellC, hcC, heC⟩ := hacc
  have hrC := hac.localRun.upTo (rc.time_nonneg c)
  have hcC' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcC)
  have hWc : W ∈ (tr.state w c).fg.tree :=
    (rc.frame_tree_subset_at hp.noColl hwc hcC).2
      ((AC.accept_new sp hrC hwc ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have := hp.cutZ_lt_of_anc_at ho hw hWc hBW
  linarith [Healing.lt_cutZ sp g, AC.le_gbar g, sp.toParams.hΔ]

/-- A high origin's counted votes reach a next-slot honest cast without Catch. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.ResetRunCore.first_carry_of_finalized_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)}
    (ho : HighOrigin tr H g x i j B)
    (hfl : Compose.StoredFastLockAt tr x i j B CV)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV := by
  have rc := hp.core
  have hm := rc.time_mono
  have hac := rc.acRun hp.noColl
  have hx := rc.antitone (le_max_right _ _) ho.1
  have hxU : (tr.state x i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, i, tr.time i, rc.time_nonneg i, fun _ hq => hm hq.le, hx, h⟩
  obtain ⟨ellw, D, hcw, hflD, rfl⟩ := hfl
  have hBD : Anc (tr.HonestBlocksAt H) (ellw.frame.viableAncestor D) D :=
    (AC.anc_viableAncestor _ D).mono
      ((rc.frame_tree_subset_at hp.noColl hx hcw).2.trans hxU)
  have hgj : g ≤ sp.ts j := by
    have := hp.cutZ_le_ts_of_highOrigin_at ho
    linarith [Healing.lt_cutZ sp g, AC.le_gbar g, sp.toParams.hΔ]
  refine hp.carry_of_post_gst_senders_at hgj hy hc hs fun v hv => ?_
  obtain ⟨hvs, ⟨k', hxk, hsend, hk1, hk2⟩, Hv, hHvU, hHvr, hDHv, hacc⟩ :=
    fastLock_writer_at hac.localRun hac.vstart hx hflD v hv
  have hBHv := hBD.trans hDHv
  refine ⟨hvs, ⟨x, k', hxk, hsend, hk1, hk2⟩, Hv, hHvr, hF.trans hBHv, ?_⟩
  rcases hacc with hg | ⟨q, hxq, haq, hqt⟩
  · exact (hp.not_genesis_above_at ho hHvU hBHv hg).elim
  have hxmax : x ∈ H (max (tr.time q) (cutZ sp.toParams g)) := by
    rcases le_total (tr.time q) (cutZ sp.toParams g) with h | h
    · rw [max_eq_right h]; exact rc.antitone (le_max_left _ _) ho.1
    · rw [max_eq_left h]; exact hxq
  exact ⟨x, q, hxq, haq, gst_le_acceptance hp ho hxmax haq hBHv, hqt⟩

/-- A high origin's counted votes reach a next-slot honest cast without Catch. -/
theorem first_carry_of_finalized_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)}
    (ho : HighOrigin tr H g x i j B)
    (hfl : Compose.StoredFastLockAt tr x i j B CV)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV :=
  hp.toCore.first_carry_of_finalized_anc_at ho hfl hy hc _hkb hs hF

/-- Earlier honest votes extending a high origin reach a later cast without Catch. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.ResetRunCore.later_carry_of_finalized_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k m : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = m + 1) (hjm : j < m)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      e'.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e m
      {v | ∃ z q e', Compose.Growing.HVoteAt tr H z q e' ∧ e'.msg = v ∧ v.slot = m} := by
  have rc := hp.core
  have hm := rc.time_mono
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hac := rc.acRun hp.noColl
  have hU := hac.localRun.coherent
  have hZj := hp.cutZ_le_ts_of_highOrigin_at ho
  have hjm' := (AC.ts_le_iff sp).mpr (show (j : Int) ≤ m by clear * - hjm; omega)
  have hgm : g ≤ sp.ts m := by
    linarith [Healing.lt_cutZ sp g, AC.le_gbar g]
  have hrk := hac.localRun.upTo (rc.time_nonneg k)
  have hck : AC.CastAt (tr.projAC.upTo (tr.time k)) y k ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hyk := (AC.castAt_specU hrk.toU hy hck).2.1
  change e.msg.slot = sp.slot (tr.time k) at hyk
  refine hp.carry_of_post_gst_senders_at hgm hy hc hs ?_
  rintro v ⟨z, q, e', hzv, rfl, hvs⟩
  obtain ⟨hzq, ellq, hcq, he'⟩ := Compose.Growing.hVoteAt_iff.mp hzv
  have hrq := hac.localRun.upTo (rc.time_nonneg q)
  have hcq' : AC.CastAt (tr.projAC.upTo (tr.time q)) z q ellq e' :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hcq⟩, he'⟩
  have hzs := (AC.castAt_specU hrq.toU hzq hcq').2.1
  change e'.msg.slot = sp.slot (tr.time q) at hzs
  change e'.msg.slot = m at hvs
  have hqk : q < k := by
    by_contra hn
    have := AC.slot_mono sp (rc.time_nonneg k) (hm (not_lt.mp hn))
    clear * - this hyk hzs hvs hs; omega
  obtain ⟨Hv, hHvU, hHvr, hBHv⟩ := hprior z q e' hqk hzv hvs
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hrq hac.vstart hzq hcq'
  have hHdU := (AC.frameIn_of_callAt hrq hzq hcq'.1).2 hHd
  obtain rfl : Hd = Hv := hU.1 hHdU hHvU (hHdr.trans hHvr.symm)
  change tr.time q ≤ sp.ts e'.msg.slot + sp.Δ at hqt
  rw [hvs] at hqt
  have hqt' : tr.time q < sp.ts m + 2 * sp.Δ := by linarith
  have hmq : sp.ts m ≤ tr.time q :=
    (AC.ts_le_iff_le_slot sp (rc.time_nonneg q) m).mpr (by
      clear * - hzs hvs; omega)
  refine ⟨hvs, ⟨z, q, hzq, ⟨ellq, hcq, Or.inl ⟨e', he', rfl⟩⟩, hmq, hqt'⟩, Hd, hHdr,
    hF.trans hBHv, ?_⟩
  -- the voter accepted its head before its cast, which is after `c_z`
  have hZq : cutZ sp.toParams g ≤ tr.time q := hZj.trans (hjm'.trans hmq)
  have hcq'' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcq)
  rcases Compose.frame_anc_acceptedU hrq.toU hzq q ellq hcq'' Hd hHd Hd .refl with hg |
      ⟨c, hcq₀, hacc⟩
  · exact (hp.not_genesis_above_at ho hHdU hBHv hg).elim
  obtain ⟨-, hacc⟩ := (ACTrace.upTo_acceptAt).mp hacc
  have hct : tr.time c ≤ tr.time q := hm hcq₀
  have hzmax : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
    rc.antitone (max_le hct hZq) hzq
  exact ⟨z, c, rc.antitone hct hzq, hacc, gst_le_acceptance hp ho hzmax hacc hBHv,
    hct.trans_lt hqt'⟩

/-- Earlier honest votes extending a high origin reach a later cast without Catch. -/
theorem later_carry_of_finalized_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k m : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = m + 1) (hjm : j < m)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      e'.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e m
      {v | ∃ z q e', Compose.Growing.HVoteAt tr H z q e' ∧ e'.msg = v ∧ v.slot = m} :=
  hp.toCore.later_carry_of_finalized_anc_at ho hy hc _hkb hs hjm hF hprior

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
