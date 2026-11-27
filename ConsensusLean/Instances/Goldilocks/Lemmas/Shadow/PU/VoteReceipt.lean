module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRelay
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
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
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
  have hWc := Coherence.tree_mono hr.toLocalRun hzZ hkc hWk
  rw [Trace.upTo_state tr z hc.1] at hWc
  have hs := σ_eq_honest_at hp.run hp.noColl hZ0
    (fun _ hq => (hp.run.time_mono hq.le).trans hkZ) hzZ hZ0 hc.1 hzZ hW hWc
  have hreach := Compose.Growing.reachable_at hp.run hZ0 hzZ hc.1
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
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    {G : AC.Blk sp.n (List (FG.Att sp.n))} (hGU : G ∈ tr.HonestBlocksAt H)
    (hBG : Anc (tr.HonestBlocksAt H) B G) (hg : G.root = sp.genesisRoot) : False := by
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hx := hp.run.antitone (le_max_right _ _) ho.1
  have hreach := Compose.Growing.reachable_at hp.run hi0 hx hle
  have hgen := (Store.accepted_tree_with Store.finalitySpec_updateFinality
    hreach.reachableWith).2.2.1
  have heq : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Coherence.honestBlocksAt_coherent hp.run hp.noColl).1 hGU
      ⟨x, i, tr.time i, hi0, hle, hx, hgen⟩ hg
  have hGx : G ∈ (tr.state x i).fg.tree := heq ▸ hgen
  have hh := Outcome.high_of_anc_at' hp.run hp.noColl ho hi0 hle hx hGx hBG
  rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl,
    Store.σ_genesis_with Store.finalitySpec_updateFinality hreach.reachableWith] at hh
  change HZ tr H g + 1 ≤ 1 at hh
  obtain ⟨kZ, hkZ, _⟩ := hp.snapshot
  have hxZ := hp.run.antitone (le_max_left _ _) ho.1
  have hZ0 : 0 ≤ cutZ sp.toParams g := by
    linarith [lt_cutZ sp g, Healing.gbar_nonneg g, sp.toParams.hΔ]
  have hreachZ := Compose.Growing.reachable_at hp.run hZ0 hxZ hkZ.1
  have hGZ := (Store.accepted_tree_with Store.finalitySpec_updateFinality
    hreachZ.reachableWith).2.2.1
  have hbnd := (Store.cache_invariants' hreachZ).2.2.2.2.1 _ hGZ
  rw [show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl,
    Store.σ_genesis_with Store.finalitySpec_updateFinality hreachZ.reachableWith] at hbnd
  have hmax : (tr.state x kZ).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v kZ).fg.hmax).subset ?_).bddAbove)
      ⟨x, hxZ, kZ, hkZ, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hkZ
    exact ⟨v, rfl⟩
  change 1 ≤ (tr.state x kZ).fg.hmax at hbnd
  omega

private theorem cutZ_le_ts_of_highOrigin
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
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
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B) (hgi : g ≤ tr.time i)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < tr.projAC.deadline y k (tr.time i) := by
  apply hp.run.toLocalRun.acRelayAt (σ := tr.time i) hx hacc hy hc hFB
  intro q hqt hx' hq hj hF
  have hgq : g ≤ tr.time q := hqt ▸ hgi
  have he : max (tr.time q) g = tr.time i := (max_eq_left hgq).trans hqt
  simpa only [he] using hp.sync.relay x q B hx' hq hgq y j hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

end Consensus.Goldilocks.Healing.Growing
