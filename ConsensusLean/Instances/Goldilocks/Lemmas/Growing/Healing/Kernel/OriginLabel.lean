module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # The snapshot bounds each high origin's label

The writer of a high origin is honest at its write and at `c_z` (`HighOrigin`). It accepted each
counted head, above the origin, before `t_j + 2Δ` (`fastLock_writer_at`). The head is not
genesis, which is low at the snapshot (`not_genesis_above_at`), and an acceptance of it by a
node honest at the later of the acceptance and `c_z` is after `c_z` (`cutZ_lt_of_anc_at`). So
`c_z < t_j + 2Δ`, hence `c_z ≤ t_j`, as both are slot starts. No fault count.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open ProposalImpl

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- `not_genesis_above_at` over the run-facts bundle. -/
theorem ResetRunCore.not_genesis_above_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    {G : AC.Blk sp.n (List (FG.Att sp.n))} (hGU : G ∈ tr.HonestBlocksAt H)
    (hBG : Anc (tr.HonestBlocksAt H) B G) (hg : G.root = sp.genesisRoot) : False := by
  have rc := hp.core
  have hm := rc.time_mono
  have hi0 := rc.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hx := rc.antitone (le_max_right _ _) ho.1
  have hreach := rc.reachable_at hi0 hx hle
  have hgm := Store.genesis_mem_with rc.finalitySpec hreach
  have heq : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (rc.coherent hp.noColl).1 hGU ⟨x, i, tr.time i, hi0, hle, hx, hgm⟩ hg
  have hGx : G ∈ (tr.state x i).fg.tree := heq ▸ hgm
  have hh := hp.high_of_anc_at ho hi0 hle hx hGx hBG
  rw [heq, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl, Store.σ_genesis_with rc.finalitySpec hreach] at hh
  change HZ tr H g + 1 ≤ 1 at hh
  obtain ⟨kZ, hkZ, _⟩ := hp.snapshot
  have hxZ := rc.antitone (le_max_left _ _) ho.1
  have hZ0 : 0 ≤ cutZ sp.toParams g := by
    linarith [lt_cutZ sp g, Healing.gbar_nonneg g, sp.toParams.hΔ]
  have hreachZ := rc.reachable_at hZ0 hxZ hkZ.1
  have hGZ := Store.genesis_mem_with rc.finalitySpec hreachZ
  have hbnd := (Store.cache_invariants_with rc.finalitySpec hreachZ).2.2.2.2.1 _ hGZ
  rw [show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
      sp.toParams.genesisRoot from rfl, Store.σ_genesis_with rc.finalitySpec hreachZ] at hbnd
  have hmax : (tr.state x kZ).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v kZ).fg.hmax).subset ?_).bddAbove)
      ⟨x, hxZ, kZ, hkZ, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hkZ
    exact ⟨v, rfl⟩
  change 1 ≤ (tr.state x kZ).fg.hmax at hbnd
  omega

/-- **No genesis block is above a high origin**: genesis is low at the snapshot cut, read by the
origin's writer, honest at `c_z`. The growing form of `genesis_not_high`. -/
theorem ResetPremisesUpTo.not_genesis_above_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    {G : AC.Blk sp.n (List (FG.Att sp.n))} (hGU : G ∈ tr.HonestBlocksAt H)
    (hBG : Anc (tr.HonestBlocksAt H) B G) (hg : G.root = sp.genesisRoot) : False :=
  hp.toCore.not_genesis_above_at ho hGU hBG hg

/-- `cutZ_le_ts_of_highOrigin_at` over the run-facts bundle. -/
theorem ResetRunCore.cutZ_le_ts_of_highOrigin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j := by
  have rc := hp.core
  have hac := rc.acRun hp.noColl
  have hx := rc.antitone (le_max_right _ _) ho.1
  have hxZ := rc.antitone (le_max_left _ _) ho.1
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨ell', hc', -⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hci.2.symm.trans hc'.2)
  obtain ⟨-, hPhiTree⟩ := rc.frame_tree_subset_at hp.noColl hx hci
  have hBD := (AC.anc_viableAncestor ell.frame D).mono fun C hC =>
    (⟨x, i, tr.time i, rc.time_nonneg i, fun _ hq => rc.time_mono hq.le, hx,
      hPhiTree hC⟩ : C ∈ tr.HonestBlocksAt H)
  obtain ⟨v, hv⟩ := Healing.fastLock_counted_nonempty
    hp.committee_pos hfl
  obtain ⟨-, -, Hv, hHvU, -, hDHv, hacc⟩ :=
    fastLock_writer_at hac.localRun hac.vstart hx hfl v hv
  have hBHv := hBD.trans hDHv
  rcases hacc with hg | ⟨q, hxq, ⟨ellq, hcq, heq⟩, hqt⟩
  · exact (hp.not_genesis_above_at ho hHvU hBHv hg).elim
  have hrq := hac.localRun.upTo (rc.time_nonneg q)
  have hcq' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hcq)
  have hHvq : Hv ∈ (tr.state x q).fg.tree :=
    (rc.frame_tree_subset_at hp.noColl hxq hcq).2
      ((AC.accept_new sp hrq hxq ⟨ellq, hcq', heq⟩).1 ellq hcq')
  have hxmax : x ∈ H (max (tr.time q) (cutZ sp.toParams g)) := by
    rcases le_total (tr.time q) (cutZ sp.toParams g) with h | h
    · rw [max_eq_right h]; exact hxZ
    · rw [max_eq_left h]; exact hxq
  have hck := hp.cutZ_lt_of_anc_at ho hxmax hHvq hBHv
  have hqt' : tr.time q < sp.ts j + 2 * sp.Δ := hqt
  rw [cutZ_eq] at hck ⊢
  refine (AC.ts_le_iff sp).2 ?_
  by_contra hlt
  have h₂ := (AC.ts_le_iff sp).2
    (show (j : Int) + 1 ≤ ((sp.slot (AC.gbar g) + 3 : Nat) : Int) by clear * - hlt; omega)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  simp only [ACParams.ts] at h₂ hck hqt'
  linarith

/-- **The label bound of a high origin** (`c_z ≤ t_j`). A counted head was accepted by the
writer before `t_j + 2Δ`; it is above the origin, so not genesis, and its acceptance is after
`c_z`, the writer being honest at `c_z`. -/
theorem ResetPremisesUpTo.cutZ_le_ts_of_highOrigin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j :=
  hp.toCore.cutZ_le_ts_of_highOrigin_at ho

end Consensus.Goldilocks.Healing.Growing

end
