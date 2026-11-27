module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Origins
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.CommitteeFaults
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow P-U: counted high-origin heads at a vote freeze

Stock receipt and relay arguments on the shadow AC projection. The origin's
snapshot cutoff is read through the finality-parametric store invariants.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

private theorem ts_le_of_fastLock
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {x : Fin sp.n} {r l : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hf : AC.FastLockAt tr.projAC x r l D CV) :
    sp.ts l ≤ tr.time r := by
  rcases hf with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hs, _⟩
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    rw [ht']
    have := sp.toParams.hΔ
    linarith
  · change sp.slot (tr.time r) = l at hs
    exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg r) l).mpr (by omega)

private theorem highOrigin_raw_head
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {r l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) :
    ∃ ell D CV, tr.projAC.CallAt x r ell ∧ AC.FastLockAt tr.projAC x r l D CV ∧
      Anc (tr.HonestBlocksAt H) O D := by
  obtain ⟨hxz, _, ⟨CV, ell, D, hc, hf, rfl⟩, _⟩ := ho
  have hx := hrun.antitone (le_max_right _ _) hxz
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hf
  obtain rfl : ell = ell' := Option.some.inj (hc.2.symm.trans hc'.2)
  obtain ⟨hok, hsub⟩ := Shadow.PU.Growing.frame_tree_subset_at hrun hnc hx hc
  refine ⟨ell, D, CV, hc, hf, (AC.viableAncestor_anc hok hD).2.mono ?_⟩
  exact fun _ hB => ⟨x, r, tr.time r, hrun.time_nonneg r,
    fun _ hq => hrun.time_mono hq.le, hx, hsub hB⟩

private theorem cutZ_lt_of_anc
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {z : Fin sp.n} {k : Nat}
    (hz : z ∈ H (max (tr.time k) (cutZ sp.toParams g)))
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z k).fg.tree)
    (hBW : Anc (tr.HonestBlocksAt H) B W) :
    cutZ sp.toParams g < tr.time k := by
  classical
  by_contra h
  have hkZ : tr.time k ≤ cutZ sp.toParams g := not_lt.mp h
  have hzZ : z ∈ H (cutZ sp.toParams g) := by rwa [max_eq_right hkZ] at hz
  have hZ0 : 0 ≤ cutZ sp.toParams g := (hp.run.time_nonneg k).trans hkZ
  have hhigh := Outcome.high_of_anc_at' hp.run hp.noColl ho hZ0
    (fun _ hq => (hp.run.time_mono hq.le).trans hkZ) hzZ hW hBW
  obtain ⟨c, hc, _⟩ := hp.snapshot
  have hkc : k ≤ c := by
    by_contra hn
    exact (not_lt_of_ge hkZ) (hc.2.trans_le (hp.run.time_mono (by omega)))
  have hr := hp.run.upTo hZ0
  have hWk : W ∈ ((tr.upTo (cutZ sp.toParams g)).state z k).fg.tree := by
    rwa [Trace.upTo_state tr z (fun _ hq => (hp.run.time_mono hq.le).trans hkZ)]
  have hWc := Coherence.tree_mono' hr.toLocalRun' hzZ hkc hWk
  rw [Trace.upTo_state tr z hc.1] at hWc
  have hs := σ_eq_honest_at' hp.run hp.noColl hZ0
    (fun _ hq => (hp.run.time_mono hq.le).trans hkZ) hzZ hZ0 hc.1 hzZ hW hWc
  have hreach := Compose.Growing.reachable_at' hp.run hZ0 hzZ hc.1
  have hbnd := (Store.cache_invariants' hreach).2.2.2.2.1 W hWc
  have hmax : (tr.state z c).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v c).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzZ, c, hc, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hc
    exact ⟨v, rfl⟩
  rw [← hs] at hbnd
  omega

private theorem not_genesis_above
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    {G : AC.Blk sp.n (List (FG.Att sp.n))} (hGU : G ∈ tr.HonestBlocksAt H)
    (hBG : Anc (tr.HonestBlocksAt H) B G) (hg : G.root = sp.genesisRoot) : False := by
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hx := hp.run.antitone (le_max_right _ _) ho.1
  have hreach := Compose.Growing.reachable_at' hp.run hi0 hx hle
  have hgen := (Store.accepted_tree_with Store.finalitySpec_updateFinality'
    hreach.reachableWith).2.2.1
  have heq : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Coherence.honestBlocksAt_coherent hp.run hp.noColl).1 hGU
      ⟨x, i, tr.time i, hi0, hle, hx, hgen⟩ hg
  have hGx : G ∈ (tr.state x i).fg.tree := heq ▸ hgen
  have hh := Outcome.high_of_anc_at' hp.run hp.noColl ho hi0 hle hx hGx hBG
  rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl,
    Store.σ_genesis_with Store.finalitySpec_updateFinality' hreach.reachableWith] at hh
  change HZ tr H g + 1 ≤ 1 at hh
  obtain ⟨kZ, hkZ, _⟩ := hp.snapshot
  have hxZ := hp.run.antitone (le_max_left _ _) ho.1
  have hZ0 : 0 ≤ cutZ sp.toParams g := by
    linarith [lt_cutZ sp g, Healing.gbar_nonneg g, sp.toParams.hΔ]
  have hreachZ := Compose.Growing.reachable_at' hp.run hZ0 hxZ hkZ.1
  have hGZ := (Store.accepted_tree_with Store.finalitySpec_updateFinality'
    hreachZ.reachableWith).2.2.1
  have hbnd := (Store.cache_invariants' hreachZ).2.2.2.2.1 _ hGZ
  rw [show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl,
    Store.σ_genesis_with Store.finalitySpec_updateFinality' hreachZ.reachableWith] at hbnd
  have hmax : (tr.state x kZ).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v kZ).fg.hmax).subset ?_).bddAbove)
      ⟨x, hxZ, kZ, hkZ, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hkZ
    exact ⟨v, rfl⟩
  change 1 ≤ (tr.state x kZ).fg.hmax at hbnd
  omega

private theorem cutZ_le_ts_of_highOrigin
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) : cutZ sp.toParams g ≤ sp.ts j := by
  have hac := Compose.Growing.goldilocks_ac_projection_from' hp.run hp.noColl
  have hx := hp.run.antitone (le_max_right _ _) ho.1
  have hxZ := hp.run.antitone (le_max_left _ _) ho.1
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨ell', hc', -⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hci.2.symm.trans hc'.2)
  obtain ⟨-, hPhiTree⟩ := Shadow.PU.Growing.frame_tree_subset_at hp.run hp.noColl hx hci
  have hBD := (AC.anc_viableAncestor ell.frame D).mono fun C hC =>
    (⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hp.run.time_mono hq.le, hx,
      hPhiTree hC⟩ : C ∈ tr.HonestBlocksAt H)
  obtain ⟨v, hv⟩ := Healing.fastLock_counted_nonempty hp.committee_pos hfl
  obtain ⟨-, -, Hv, hHvU, -, hDHv, hacc⟩ :=
    fastLock_writer_at hac.localRun hac.vstart hx hfl v hv
  have hBHv := hBD.trans hDHv
  rcases hacc with hg | ⟨q, hxq, ⟨ellq, hcq, heq⟩, hqt⟩
  · exact (not_genesis_above hp ho hHvU hBHv hg).elim
  have hrq := hac.localRun.upTo (hp.run.time_nonneg q)
  have hcq' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcq)
  have hHvq : Hv ∈ (tr.state x q).fg.tree :=
    (Shadow.PU.Growing.frame_tree_subset_at hp.run hp.noColl hxq hcq).2
      ((AC.accept_new sp hrq hxq ⟨ellq, hcq', heq⟩).1 ellq hcq')
  have hxmax : x ∈ H (max (tr.time q) (cutZ sp.toParams g)) := by
    rcases le_total (tr.time q) (cutZ sp.toParams g) with h | h
    · rw [max_eq_right h]; exact hxZ
    · rw [max_eq_left h]; exact hxq
  have hck := cutZ_lt_of_anc hp ho hxmax hHvq hBHv
  have hqt' : tr.time q < sp.ts j + 2 * sp.Δ := hqt
  rw [cutZ_eq] at hck ⊢
  refine (AC.ts_le_iff sp).2 ?_
  by_contra hlt
  have h₂ := (AC.ts_le_iff sp).2
    (show (j : Int) + 1 ≤ ((sp.slot (AC.gbar g) + 3 : Nat) : Int) by clear * - hlt; omega)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  simp only [ACParams.ts] at h₂ hck hqt'
  linarith

private theorem frame_relay
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B) (hgi : g ≤ tr.time i)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < tr.projAC.deadline y k (tr.time i) := by
  apply hp.run.toLocalRun'.acRelayAt' (σ := tr.time i) hx hacc hy hc hFB
  intro q hqt hx' hq hj hF
  have hgq : g ≤ tr.time q := hqt ▸ hgi
  have he : max (tr.time q) g = tr.time i := (max_eq_left hgq).trans hqt
  simpa only [he] using hp.sync.relay x q B hx' hq hgq y j hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- A historical acceptance before the slot deadline reaches a later honest vote's freeze. -/
theorem KernelProof.relay_mem_voterBlockTree_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {w y : Fin sp.n} {kw i s : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hw : w ∈ H (tr.time kw)) (hkw : tr.projAC.AcceptAt w kw W)
    (hg : g ≤ tr.time kw) (hkwt : tr.time kw < sp.ts s + 2 * sp.Δ)
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : s + 1 ≤ e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F W) :
    W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from' hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg i)).localRun
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := AC.castAt_specU hr.toU hy hc'
  change e.msg.slot = sp.slot (tr.time i) at hys
  have hslot : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [ACParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg i) _).2 (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (AC.ts_le_iff sp).2 (by omega)
  have hrsy : ∀ k ≤ i, tr.projAC.RestartAt y k →
      tr.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : AC.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAtU hr.toU hy hc']
      exact hyj
    intro k hk hrk
    have := ((AC.joined_awakeU sp) _ ro _ _ _ hr.toU y hy i ell hc'.1 hj').2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hm hk, hrk⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at this
    rwa [← hys] at this
  have hdl : ∀ k ≤ i, tr.projAC.deadline y k (tr.time kw) <
      sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro k hk
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') (tr.time kw)
    have h₂ := max_lt (show tr.time kw < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hkwt, hsm])
      (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hΔ])
    change tr.projAC.deadline y k (tr.time kw) ≤
      max (tr.time kw) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ at h₁
    linarith only [h₂, h₁]
  obtain ⟨ky, hky, hacc, hkyt⟩ := frame_relay hp hw hkw hg hy hc.1
    (by linarith only [hΔ, hslot, hti, hdl i le_rfl]) hF
  have hkyt' : tr.time ky < AC.freeze sp e.msg.slot := by
    have := hdl ky hky
    unfold AC.freeze
    linarith only [hkyt, this]
  have hfz : AC.freeze sp e.msg.slot ≤ tr.time i := by
    unfold AC.freeze
    linarith only [hΔ, hslot, hti]
  have hacc' := ACTrace.upTo_acceptAt.mpr (And.intro (hm hky) hacc)
  have hWt := AC.mem_tree_of_acceptAtU sp hr.toU hy hacc' hky hc'.1 hF
  have hbs := AC.blockStamp_lt_of_acceptedBeforeU sp hr.toU hp.run.vstart hy hc'.1 hWt
    (Or.inr ⟨ky, hacc', hkyt'⟩)
    (fun k hk hrk => lt_of_le_of_lt (hrsy k hk (ACTrace.upTo_restartAt.mp hrk).2)
      (by unfold AC.freeze; linarith only [hΔ])) (Or.inl hfz)
  have hne : ∀ B, ell.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (AC.accept_new sp hr hy ⟨ell, hc'.1, hcall⟩).1 ell hc'.1
    obtain rfl : B₀ = W := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hc'.1).2 hB₀)
      ((AC.frameIn_of_callAt hr hy hc'.1).2 hWt) hB.symm
    have heq := AC.accept_uniqueU sp hr.toU hy hacc' ⟨ell, hc'.1, hcall⟩
    rw [heq] at hkyt'
    linarith only [hkyt', hfz]
  refine ⟨hWt, Or.inl ?_⟩
  rw [AC.readPoint_blockStampU hr.toU hy hc' hne]
  exact hbs

/-- A counted high-origin head is held at a later honest vote's freeze. -/
theorem KernelProof.high_origin_frozen_head_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r l k : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) O D := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from' hp.run hp.noColl
  obtain ⟨ellX, D, CV, hcx, hfl, hOD⟩ := highOrigin_raw_head hp.run hp.noColl ho
  have hr := hac.upTo (hp.run.time_nonneg r)
  have hlab := cutZ_le_ts_of_highOrigin hp ho
  have hf := hp.committeeFaults.committee_cs2_at hp.beta_le hp.committee_pos
    (hp.committeeFacts.hsize l) (Healing.gbar_le_of_cutZ_le sp hlab)
    ((ts_le_of_fastLock hp.run hfl).trans hrb) (hp.run.time_nonneg r) hrb
  obtain ⟨z, hz, j, ev, hv, hes, W, hW, hWr, hDW⟩ :=
    AC.fastLock_honest_vote hr _
      (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP _)
      (hp.run.antitone (le_max_right _ _) ho.1)
      ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) hf
  obtain ⟨hjr, hv₀⟩ := AC.upTo_voteAt.mp hv
  have hzj := hp.run.antitone hjr hz
  obtain ⟨ellZ, hcz, he⟩ := hv₀
  have hrj := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcz' := Trace.upTo_callAt tr.projAC |>.mpr (And.intro le_rfl hcz)
  obtain ⟨⟨W', hW't, hW'r, _⟩, hjt⟩ :=
    Compose.cast_head_fcRoot hrj hp.run.vstart hzj ⟨hcz', he⟩
  have heq : W' = W := hac.localRun.coherent.1
    ((AC.frameIn_of_callAt hrj hzj hcz').2 hW't) hW (hW'r.trans hWr.symm)
  subst W'
  have hOW := hOD.trans hDW
  have hzZ : z ∈ H (max (tr.time j) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hjr (hlab.trans (ts_le_of_fastLock hp.run hfl))) hz
  have hWz : W ∈ (tr.state z j).fg.tree :=
    (Shadow.PU.Growing.frame_tree_subset_at hp.run hp.noColl hzj hcz).2 hW't
  have hZj := cutZ_lt_of_anc hp ho hzZ hWz hOW
  have hjt' : tr.time j ≤ sp.ts l + sp.Δ := by rw [hes] at hjt; exact hjt
  rcases Compose.frame_anc_acceptedU hrj.toU hzj j ellZ hcz' W hW't W .refl with hg |
      ⟨c, hcj, hacc⟩
  · exact (not_genesis_above hp ho
      ⟨z, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hm hq.le, hzj, hWz⟩ hOW hg).elim
  have hctj : tr.time c ≤ tr.time j := hm hcj
  have hacc₀ := ACTrace.upTo_acceptAt.mp hacc |>.2
  have hzc : z ∈ H (max (tr.time c) (cutZ sp.toParams g)) :=
    hp.run.antitone (max_le hctj hZj.le) hzj
  have hzc₀ := hp.run.antitone hctj hzj
  have hWc : W ∈ (tr.state z c).fg.tree := by
    obtain ⟨ellC, hcC, heC⟩ := hacc₀
    have hrC := (hac.upTo (hp.run.time_nonneg c)).localRun
    have hcC' := Trace.upTo_callAt tr.projAC |>.mpr (And.intro le_rfl hcC)
    exact (Shadow.PU.Growing.frame_tree_subset_at hp.run hp.noColl hzc₀ hcC).2
      ((AC.accept_new sp hrC hzc₀ ⟨ellC, hcC', heC⟩).1 ellC hcC')
  have hgc : g ≤ tr.time c := by
    have hcZ := cutZ_lt_of_anc hp ho hzc hWc hOW
    have := lt_cutZ sp g
    have := le_gbar g
    have := sp.toParams.hΔ
    linarith
  have hWT := KernelProof.relay_mem_voterBlockTree_at' (s := l) hp hzc₀ hacc₀ hgc
    (by have := sp.toParams.hΔ; linarith) hy hc (by omega) (hFO.trans hOW)
  exact ⟨W, hWT, hOW⟩

end Consensus.Goldilocks.Healing.Growing
