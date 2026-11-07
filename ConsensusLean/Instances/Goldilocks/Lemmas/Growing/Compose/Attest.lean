module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest

public section

/-! # Signing provenance retained at the signer's honesty horizon -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {proposer : Nat → Fin sp.n}

/-- An honest signing is at a public time, using honesty only at the signing cut. -/
theorem sign_public (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    sp.toParams.IsPublic (tr.time j) := by
  exact Compose.sign_public (hrun.upTo (hrun.time_nonneg j)) hy
    ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)

/-- Signing follows the same node's source call at the preceding cut and the same time.
Both states are retained at the signing cut, even if the node is compromised later. -/
theorem attest_source (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧ tr.time j' = tr.time j ∧
      ((goldilocksNode sp ro).toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j', hj, ℓ, hc', hto, ht, hC, hs⟩ :=
    Compose.attest_source (hrun.toLocalRun.upTo (hrun.time_nonneg j)) hy
      ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩)
  change tr.time j' = tr.time j at ht
  have hstate := RunTrace.upTo_state_of_le (tr := tr) (y := y)
    hrun.time_mono (le_refl (tr.time j))
  have hstate' := RunTrace.upTo_state_of_le (tr := tr) (y := y) hrun.time_mono ht.le
  rw [hstate'] at hC
  rw [hstate, hstate'] at hs
  exact ⟨j', hj, ℓ, ((Trace.upTo_callAt _).mp hc').2, hto, ht, hC, hs⟩

/-- At a common time, honest tick signings precede an honest delivery's cuts. -/
theorem sign_before_delivery
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {v y : Fin sp.n} {j' k j₀ : Nat} (hv : v ∈ H (tr.time j'))
    (hy : y ∈ H (tr.time k)) {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hs : tr.CallAt v j' (.fg (.attest C (some a))))
    {e : Node.Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j₀ (tr.time k) e) (he : e.phase = 2) (hk : j₀ ≤ k)
    (ht : tr.time j' = tr.time k) : j' < k := by
  have hlocal := hrun.toLocalRun.upTo (hrun.time_nonneg k)
  have hv' : v ∈ H (tr.time k) := ht ▸ hv
  have hs' := (Trace.upTo_callAt _).mpr ⟨ht.le, hs⟩
  obtain ⟨j₁, e₁, i₁, hg₁, rfl, hk₁⟩ := call_in_group hlocal hv' hs'
  have hm : Cut.fg (.attest C (some a)) ∈
      (Node.exec proposer dg v ((tr.upTo (tr.time k)).state v j₁)
        (tr.time (j₁ + i₁)) e₁).2 := List.mem_of_getElem? hk₁
  obtain ⟨xt, he₁⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg v
    ((tr.upTo (tr.time k)).state v j₁) (tr.time (j₁ + i₁)) e₁ C a hm
  subst he₁
  have hg' := (RunTrace.upTo_groupAt hrun.time_mono).mpr ⟨le_rfl, hg⟩
  change (tr.upTo (tr.time k)).GroupAt proposer dg v j₁ (tr.time (j₁ + i₁)) (.tick xt) at hg₁
  rw [ht] at hg₁
  change (Node.exec proposer dg v ((tr.upTo (tr.time k)).state v j₁)
    (tr.time (j₁ + i₁)) (.tick xt)).2[i₁]? = some (.fg (.attest C (some a))) at hk₁
  rw [ht] at hk₁
  have hlen := (List.getElem?_eq_some_iff.1 hk₁).1
  by_contra hjk
  rcases lt_trichotomy j₀ j₁ with hlt | rfl | hgt
  · have h' := hlocal.phase_order y hy v hv' j₀ j₁ _ e (.tick xt) hg' hg₁ hlt
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have hn : y = v := ((hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).1).symm.trans
      (hg₁.2.1 0 (List.length_pos_iff.2 hg₁.1)).1
    subst hn
    have h' := group_phase hg' hg₁
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have := group_start hg₁ hg' (le_of_lt hgt) (by omega)
    omega

end Consensus.Goldilocks.Compose.Growing

end
