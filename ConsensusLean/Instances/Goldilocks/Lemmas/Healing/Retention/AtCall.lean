module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: high-origin heldness and the low-`Σ.J` root at an arbitrary call

Call-time forms of `high_origin_held_at_vote` and `low_root_of_seed_before` (`Retention/Boot`),
for the H.3 invariant after the reset. The vote
forms read the voter block tree; here the counted head of a high origin of label `j` reaches an
honest node by the GST acceptance relay at any of its AC calls from `t_{j+1}` on: the head was
accepted by its honest writer at `kw` with `g ≤ t_kw < t_j + 2Δ`, no honest node restarts after
`ḡ < t_kw`, so the relay deadline is `t_kw + Δ < t_{j+1}`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **Heldness of a high origin at an honest AC call** from `t_{j+1}` on, when the call's
finalized tip is below the origin. The counted head is relayed by the GST acceptance relay with
deadline `t_kw + Δ` (no honest restart after `ḡ`). -/
theorem high_origin_held_at_call (hp : ResetPremises tr H proposer dg g ΔF a)
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ell)
    (ht : sp.ts (j + 1 : Nat) ≤ tr.time k)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ (tr.state y k).fg.tree := by
  have hpu := hp.toUpTo tr H (le_refl a)
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ellw, D, CV, hcw, hflw, -, -, -, hBD, -⟩ := hpu.highOrigin_mem ho
  obtain ⟨v, hv⟩ := fastLock_counted_nonempty hflw
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHvz⟩, -, hDHv, hacc⟩ := fastLock_writer hr ho.1 hflw v hv
  have hBHv : Anc (tr.HonestBlocks H) B Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr ho.1 hcw).2 hBD).trans hDHv
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (hpu.cutZ_lt_of_anc ho hz hHvz hBHv).2
  have hkwg : gbar g < tr.projAC.time kw := by
    have := (hpu.cutZ_lt_of_anc ho ho.1 (hpu.acceptAt_mem ho.1 hkw) hBHv).1
    have := lt_cutZ sp g
    change gbar g < tr.time kw
    linarith
  have hkwt' : tr.time kw < sp.ts j + 2 * sp.Δ := hkwt
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- the relay deadline at every cut of `y`: no restart after `ḡ < t_kw`
  have hdl : ∀ k', tr.projAC.deadline y k' (tr.projAC.time kw) ≤ tr.time kw + sp.Δ := by
    intro k'
    have h₁ := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k')
      (fun k'' _ hr' => (hnr y hy k'' (Compose.projAC_restartAt.1 hr')).trans
        (show gbar g ≤ tr.projAC.time kw from hkwg.le)) (tr.projAC.time kw)
    rw [max_eq_left le_rfl] at h₁
    exact h₁
  have hsync : SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) H (tr.HonestBlocks H) g
      (tr.time k) tr.projAC :=
    Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
      tr proposer ΔF g (tr.time k) hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)
  obtain ⟨ky, hky, hacc, -⟩ := hsync.2 x ho.1 kw Hv hkw
    (by have := le_gbar g; linarith) (by change tr.time kw ≤ tr.time k; linarith)
    y hy k ell hc (by have := hdl k; change _ ≤ tr.time k at *; linarith) (hF.trans hBHv)
  have hHvT := SA.mem_tree_of_acceptAt sp hr hy hacc hky hc (hF.trans hBHv)
  exact hpu.mem_tree_of_anc hy hBHv (hpu.frame_tree_subset hy hc hHvT)

/-- **The low-`Σ.J` root at an honest AC call** from `t_{m+1}` on: the seed `S`, a high origin of
label `m`, is below the call's finalized tip and held there (`high_origin_held_at_call`), so the
held-seed comparison applies. -/
theorem low_root_of_seed_at_call (hp : ResetPremises tr H proposer dg g ΔF a)
    (hnr : NoRestartAfter tr H (gbar g))
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x r).fg.tree) (hy : y ∈ H)
    (hS : HighOrigin tr H g v q m S) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (ht : sp.ts (m + 1 : Nat) ≤ tr.time i)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g) (hBS : Compatible (tr.HonestBlocks H) B S)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  have hFS := low_finalized_below_origin hp hy i hlow hS
  have hFF : ell.frame.F = (tr.state y i).fg.F := by
    rw [Compose.frame_of_projAC hp.run hy hc]; rfl
  have hSy := high_origin_held_at_call hp hnr hS hy hc ht (by rw [hFF]; exact hFS)
  exact low_root_of_held_seed_at_call hp hx hBx hy hS hc hSy hlow hBS hheld

end Consensus.Goldilocks.Healing

end
