module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FaultBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Comparing high origins from strictly earlier honest votes

Each historical lock retains its own writer. The common fault budget is read at the
finite horizon, not by requiring either writer to survive the other write.
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
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨CV', ell', D', hcr, hfl', rfl⟩ := hO.2.2.1
  obtain ⟨ellD, hcD, hDt⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ellD := Option.some.inj (hci.2.symm.trans hcD.2)
  obtain ⟨ellD', hcD', hDt'⟩ := Healing.fastLock_mem hfl'
  obtain rfl : ell' = ellD' := Option.some.inj (hcr.2.symm.trans hcD'.2)
  have htree := (frame_tree_subset_at hp.run hp.noColl ho.1 hci).2
  have htree' := (frame_tree_subset_at hp.run hp.noColl hO.1 hcr).2
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨x, i, tr.time i, hp.run.time_nonneg i,
      fun _ hq => hp.run.time_mono hq.le, ho.1, htree hC⟩
  have hPhiU' : ell'.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨z, r, tr.time r, hp.run.time_nonneg r,
      fun _ hq => hp.run.time_mono hq.le, hO.1, htree' hC⟩
  have hBD := (SA.anc_viableAncestor ell.frame D).mono hPhiU
  have hOD := (SA.anc_viableAncestor ell'.frame D').mono hPhiU'
  have hfi : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
        (Set.compl_subset_compl.mpr (hp.run.antitone hib)))) hf
  have hfr : 2 * (H (tr.time r))ᶜ.ncard < sp.n := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
        (Set.compl_subset_compl.mpr (hp.run.antitone hrb)))) hf
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hDO := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg i)) ho.1
      (Nat.lt_succ_self i) ((SA.upTo_fastLockAt hp.run.time_mono).mpr ⟨le_rfl, hfl⟩)
      hfi (B := ell'.frame.viableAncestor D') ?_
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
      have := hp.cutZ_le_ts_of_highOrigin_at ho hib
      have := Healing.lt_cutZ sp g
      have := Healing.le_gbar g
      have := sp.toParams.hΔ
      linarith
    have hsync := reset_syncACAt hp (hi := sp.ts (l + 1 : Nat) + sp.Δ) hgj
    rcases SA.Growing.fastLock_same_slot hac ho.1 hfl hO.1 hfl' hsync
        (d := b) (fun _ => hib) hrb hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD
    · exact SA.anc_total hU hBD (hOD.trans h)
  · have hDB := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg r)) hO.1
      (Nat.lt_succ_self r) ((SA.upTo_fastLockAt hp.run.time_mono).mpr ⟨le_rfl, hfl'⟩)
      hfr (B := ell.frame.viableAncestor D) ?_
    · by_contra hn
      exact SA.not_compatible_of_anc hU hOD hn hDB.symm
    · intro v hv c hcr' e hve hs
      obtain ⟨hct, hve⟩ := SA.upTo_voteAt.mp hve
      have hv := hp.run.antitone hct hv
      exact hvote x i j _ ho hib v c e (by omega) hv
        ((hp.run.time_mono (by omega)).trans hrb) hve (by omega)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
