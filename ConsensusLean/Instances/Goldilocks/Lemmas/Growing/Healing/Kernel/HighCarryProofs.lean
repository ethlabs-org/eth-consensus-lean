module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
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
the first carry's writer is honest through its write, which is after `c_z`; a later carry's
voter casts its vote of label `m > j` after `c_z`, so its acceptance before the vote is read
there. A genesis head is excluded by the height of a high origin. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Vote Payload)
open ProposalImpl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A bounded high origin's write is at or after the snapshot cut `c_z`. -/
private theorem cutZ_le_write (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b) :
    cutZ sp.toParams g ≤ tr.time i := by
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
  exact (hp.cutZ_le_ts_of_highOrigin_at ho hib).trans (ts_le_of_fastLock_at hp.run hfl)

/-- No genesis block is above a bounded high origin. -/
private theorem not_genesis_above (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    {G : SA.Blk sp.n (List (FG.Att sp.n))} (hGU : G ∈ tr.HonestBlocksAt H)
    (hBG : Anc (tr.HonestBlocksAt H) B G) (hg : G.root = sp.genesisRoot) : False := by
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hreach := fg_reachable_at hp.run hi0 hle ho.1
  have heq : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hGU
      ⟨x, i, tr.time i, hi0, hle, ho.1, (Store.accepted_tree _ _ _ _ hreach).2.2.1⟩ hg
  have hGx : G ∈ (tr.state x i).fg.tree := heq ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.1
  have hh := hp.high_of_anc_at ho hi0 hle ho.1 hGx hBG
  rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl, Store.σ_genesis hreach] at hh
  change HZ tr H g + 1 ≤ 1 at hh
  obtain ⟨kZ, hkZ, _⟩ := hp.snapshot
  have hxZ := hp.run.antitone (cutZ_le_write hp ho hib) ho.1
  have hZ0 : 0 ≤ cutZ sp.toParams g := by
    linarith [Healing.lt_cutZ sp g, SA.gbar_nonneg g, sp.toParams.hΔ]
  have hreachZ := fg_reachable_at hp.run hZ0 hkZ.1 hxZ
  have hGZ := (Store.accepted_tree _ _ _ _ hreachZ).2.2.1
  have hbnd := (Store.cache_invariants _ _ _ _ hreachZ).2.2.2.2.1 _ hGZ
  rw [show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl, Store.σ_genesis hreachZ] at hbnd
  have hmax : (tr.state x kZ).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v kZ).fg.hmax).subset ?_).bddAbove)
      ⟨x, hxZ, kZ, hkZ, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hkZ
    exact ⟨v, rfl⟩
  change 1 ≤ (tr.state x kZ).fg.hmax at hbnd
  omega

/-- **An acceptance of a head above a bounded high origin is after GST**, for an acceptor honest
at the later of its acceptance and `c_z`. -/
private theorem gst_le_acceptance (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {w : Fin sp.n} {c : Nat}
    (hw : w ∈ H (max (tr.time c) (cutZ sp.toParams g)))
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hacc : tr.projAC.AcceptAt w c W)
    (hBW : Anc (tr.HonestBlocksAt H) B W) : g ≤ tr.time c := by
  have hwc := hp.run.antitone (le_max_left _ _) hw
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨ellC, hcC, heC⟩ := hacc
  have hrC := hac.localRun.upTo (hp.run.time_nonneg c)
  have hcC' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcC)
  have hWc : W ∈ (tr.state w c).fg.tree :=
    (frame_tree_subset_at hp.run hp.noColl hwc hcC).2
      ((SA.accept_new sp hrC hwc ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have := cutZ_lt_of_anc_at hp ho hw hWc hBW
  linarith [Healing.lt_cutZ sp g, SA.le_gbar g, sp.toParams.hΔ]

/-- A high origin's counted votes reach a next-slot honest cast without Catch. -/
theorem first_carry_of_finalized_anc_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hfl : Compose.StoredFastLockAt tr x i j B CV)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hxU : (tr.state x i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hm hq.le, ho.1, h⟩
  obtain ⟨ellw, D, hcw, hflD, rfl⟩ := hfl
  have hBD : Anc (tr.HonestBlocksAt H) (ellw.frame.viableAncestor D) D :=
    (SA.anc_viableAncestor _ D).mono
      ((frame_tree_subset_at hp.run hp.noColl ho.1 hcw).2.trans hxU)
  have hZi := cutZ_le_write hp ho hib
  have hgj : g ≤ sp.ts j := by
    have := hp.cutZ_le_ts_of_highOrigin_at ho hib
    linarith [Healing.lt_cutZ sp g, SA.le_gbar g, sp.toParams.hΔ]
  refine carry_of_post_gst_senders_at hp hgj hy hc hs fun v hv => ?_
  obtain ⟨hvs, ⟨k', hxk, hsend, hk1, hk2⟩, Hv, hHvU, hHvr, hDHv, hacc⟩ :=
    fastLock_writer_at hac.localRun ho.1 hflD v hv
  have hBHv := hBD.trans hDHv
  refine ⟨hvs, ⟨x, k', hxk, hsend, hk1, hk2⟩, Hv, hHvr, hF.trans hBHv, ?_⟩
  rcases hacc with hg | ⟨q, hxq, haq, hqt⟩
  · exact (not_genesis_above hp ho hib hHvU hBHv hg).elim
  have hxmax : x ∈ H (max (tr.time q) (cutZ sp.toParams g)) := by
    rcases le_total (tr.time q) (cutZ sp.toParams g) with h | h
    · rw [max_eq_right h]; exact hp.run.antitone hZi ho.1
    · rw [max_eq_left h]; exact hxq
  exact ⟨x, q, hxq, haq, gst_le_acceptance hp ho hxmax haq hBHv, hqt⟩

/-- Earlier honest votes extending a high origin reach a later cast without Catch. -/
theorem later_carry_of_finalized_anc_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hs : e.msg.slot = m + 1) (hjm : j < m)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      e'.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e m
      {v | ∃ z q e', Compose.Growing.HVoteAt tr H z q e' ∧ e'.msg = v ∧ v.slot = m} := by
  have hm := hp.run.time_mono
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hac.localRun.coherent
  have hZj := hp.cutZ_le_ts_of_highOrigin_at ho hib
  have hjm' := (SA.ts_le_iff sp).mpr (show (j : Int) ≤ m by clear * - hjm; omega)
  have hgm : g ≤ sp.ts m := by
    linarith [Healing.lt_cutZ sp g, SA.le_gbar g]
  have hrk := hac.localRun.upTo (hp.run.time_nonneg k)
  have hck : SA.CastAt (tr.projAC.upTo (tr.time k)) y k ell e :=
    SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hyk := (SA.castAt_spec hrk hy hck).2.1
  change e.msg.slot = sp.slot (tr.time k) at hyk
  refine carry_of_post_gst_senders_at hp hgm hy hc hs ?_
  rintro v ⟨z, q, e', hzv, rfl, hvs⟩
  obtain ⟨hzq, ellq, hcq, he'⟩ := Compose.Growing.hVoteAt_iff.mp hzv
  have hrq := hac.localRun.upTo (hp.run.time_nonneg q)
  have hcq' : SA.CastAt (tr.projAC.upTo (tr.time q)) z q ellq e' :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hcq⟩, he'⟩
  have hzs := (SA.castAt_spec hrq hzq hcq').2.1
  change e'.msg.slot = sp.slot (tr.time q) at hzs
  change e'.msg.slot = m at hvs
  have hqk : q < k := by
    by_contra hn
    have := SA.slot_mono sp (hp.run.time_nonneg k) (hm (not_lt.mp hn))
    clear * - this hyk hzs hvs hs; omega
  obtain ⟨Hv, hHvU, hHvr, hBHv⟩ := hprior z q e' hqk hzv hvs
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hrq hzq hcq'
  have hHdU := (SA.frameIn_of_callAt hrq hzq hcq'.1).2 hHd
  obtain rfl : Hd = Hv := hU.1 hHdU hHvU (hHdr.trans hHvr.symm)
  change tr.time q ≤ sp.ts e'.msg.slot + sp.Δ at hqt
  rw [hvs] at hqt
  have hqt' : tr.time q < sp.ts m + 2 * sp.Δ := by linarith
  have hmq : sp.ts m ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) m).mpr (by
      clear * - hzs hvs; omega)
  refine ⟨hvs, ⟨z, q, hzq, ⟨ellq, hcq, Or.inl ⟨e', he', rfl⟩⟩, hmq, hqt'⟩, Hd, hHdr,
    hF.trans hBHv, ?_⟩
  -- the voter accepted its head before its cast, which is after `c_z`
  have hZq : cutZ sp.toParams g ≤ tr.time q := hZj.trans (hjm'.trans hmq)
  have hcq'' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcq)
  rcases Compose.frame_anc_accepted hrq hzq q ellq hcq'' Hd hHd Hd .refl with hg |
      ⟨c, hcq₀, hacc⟩
  · exact (not_genesis_above hp ho hib hHdU hBHv hg).elim
  obtain ⟨-, hacc⟩ := (ACTrace.upTo_acceptAt).mp hacc
  have hct : tr.time c ≤ tr.time q := hm hcq₀
  have hzmax : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hct hZq) hzq
  exact ⟨z, c, hp.run.antitone hct hzq, hacc, gst_le_acceptance hp ho hzmax hacc hBHv,
    hct.trans_lt hqt'⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
