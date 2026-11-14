module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FaultBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Comparing high origins from strictly earlier honest votes

Each historical lock retains its own writer. Neither writer is required to survive the other
write: for equal labels the common fault budget is read at the finite horizon; otherwise the
later label's count is read at its own write, after `c_z` by the label bound
(`cutZ_le_ts_of_highOrigin_at`).
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Earlier vote extension compares two bounded origins, including an origin whose
write is pending but whose label's votes all precede the induction cut. -/
theorem origins_compatible_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ z c e, c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
        SA.VoteAt tr.projAC z c e → j < e.msg.slot →
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) (hrk : r < k) :
    Compatible (tr.HonestBlocksAt H) B O := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  have hU := hr.coherent
  have hf : 2 * (H b)ᶜ.ncard < sp.n := by
    have := hp.faults b ((hp.run.time_nonneg i).trans hib) le_rfl
    have := sp.toParams.hn
    change 0 < sp.n at this
    omega
  have hx := hp.run.antitone (le_max_right _ _) ho.1
  have hz := hp.run.antitone (le_max_right _ _) hO.1
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨CV', ell', D', hcr, hfl', rfl⟩ := hO.2.2.1
  obtain ⟨ellD, hcD, hDt⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ellD := Option.some.inj (hci.2.symm.trans hcD.2)
  obtain ⟨ellD', hcD', hDt'⟩ := Healing.fastLock_mem hfl'
  obtain rfl : ell' = ellD' := Option.some.inj (hcr.2.symm.trans hcD'.2)
  have htree := (frame_tree_subset_at hp.run hp.noColl hx hci).2
  have htree' := (frame_tree_subset_at hp.run hp.noColl hz hcr).2
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨x, i, tr.time i, hp.run.time_nonneg i,
      fun _ hq => hp.run.time_mono hq.le, hx, htree hC⟩
  have hPhiU' : ell'.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨z, r, tr.time r, hp.run.time_nonneg r,
      fun _ hq => hp.run.time_mono hq.le, hz, htree' hC⟩
  have hBD := (SA.anc_viableAncestor ell.frame D).mono hPhiU
  have hOD := (SA.anc_viableAncestor ell'.frame D').mono hPhiU'
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hcut := (hp.cutZ_le_ts_of_highOrigin_at ho).trans
      (ProposalImpl.ts_le_of_fastLock_at hp.run hfl)
    have hDO := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg i)) _
      SA.CommitteeP.full hx (Nat.lt_succ_self i)
      ((SA.upTo_fastLockAt hp.run.time_mono).mpr ⟨le_rfl, hfl⟩)
      (SA.Growing.cs2_full_of_faultBoundAt hp.stock (fault_bound_late_at hp hcut hib))
      (B := ell'.frame.viableAncestor D') ?_
    · by_contra hn
      exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
    · intro v hv c hci' e hve hs
      obtain ⟨hct, hve⟩ := SA.upTo_voteAt.mp hve
      have hv := hp.run.antitone hct hv
      have hck : c < k := by
        rcases hact with hi | ht
        · omega
        · apply ht c
          obtain ⟨ellv, hcast⟩ := hve
          have hslot := (castAt_facts_at hp.run hp.noColl hv hcast).2.2
          by_contra hn
          have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg c) (j + 1 : Nat)).mp
            (not_lt.mp hn)
          omega
      exact hvote z r l _ hO hrb v c e hck hv
        ((hp.run.time_mono (by omega)).trans hib) hve (by omega)
  · have hgj : g ≤ sp.ts l := by
      have := hp.cutZ_le_ts_of_highOrigin_at ho
      have := Healing.lt_cutZ sp g
      have := Healing.le_gbar g
      have := sp.toParams.hΔ
      linarith
    have hsync := reset_syncACAt hp (hi := sp.ts (l + 1 : Nat) + sp.Δ) hgj
    rcases SA.Growing.fastLock_same_slot hac _ (fun _ => SA.CommitteeP.full)
        (SA.size_binding_full hp.stock) hx hfl hz hfl' hsync
        (d := b) (fun _ => hib) hrb (SA.cs2_full hp.stock hf) with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD
    · exact SA.anc_total hU hBD (hOD.trans h)
  · have hcut := (hp.cutZ_le_ts_of_highOrigin_at hO).trans
      (ProposalImpl.ts_le_of_fastLock_at hp.run hfl')
    have hDB := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg r)) _
      SA.CommitteeP.full hz (Nat.lt_succ_self r)
      ((SA.upTo_fastLockAt hp.run.time_mono).mpr ⟨le_rfl, hfl'⟩)
      (SA.Growing.cs2_full_of_faultBoundAt hp.stock (fault_bound_late_at hp hcut hrb))
      (B := ell.frame.viableAncestor D) ?_
    · by_contra hn
      exact SA.not_compatible_of_anc hU hOD hn hDB.symm
    · intro v hv c hcr' e hve hs
      obtain ⟨hct, hve⟩ := SA.upTo_voteAt.mp hve
      have hv := hp.run.antitone hct hv
      exact hvote x i j _ ho hib v c e (by omega) hv
        ((hp.run.time_mono (by omega)).trans hrb) hve (by omega)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
