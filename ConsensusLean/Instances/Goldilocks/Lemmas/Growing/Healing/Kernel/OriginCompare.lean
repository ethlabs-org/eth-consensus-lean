module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # Comparing high origins from strictly earlier honest votes

Each historical lock retains its own writer. Neither writer is required to survive the other
write: for equal labels the common fault budget is read at the finite horizon; otherwise the
later label's count is read at its own write, after `c_z` by the label bound
(`cutZ_le_ts_of_highOrigin_at`).
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- Earlier vote extension compares two bounded origins, including an origin whose
write is pending but whose label's votes all precede the induction cut. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.ResetRunCore.origins_compatible_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold) {k : Nat}
    (hvote : ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ z c e, c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
        AC.VoteAt tr.projAC z c e → j < e.msg.slot →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) (hrk : r < k) :
    Compatible (tr.HonestBlocksAt H) B O := by
  have rc := hp.core
  have hac := rc.acRun hp.noColl
  have hr := hac.localRun
  have hU := hr.coherent
  have hPK := fun t => AC.CommitteePAt.upTo rc.time_mono rc.antitone hp.committeeFacts.hP t
  have hb0 : 0 ≤ b := (rc.time_nonneg i).trans hib
  have hx := rc.antitone (le_max_right _ _) ho.1
  have hz := rc.antitone (le_max_right _ _) hO.1
  obtain ⟨CV, ell, D, hci, hfl, rfl⟩ := ho.2.2.1
  obtain ⟨CV', ell', D', hcr, hfl', rfl⟩ := hO.2.2.1
  obtain ⟨ellD, hcD, hDt⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ellD := Option.some.inj (hci.2.symm.trans hcD.2)
  obtain ⟨ellD', hcD', hDt'⟩ := Healing.fastLock_mem hfl'
  obtain rfl : ell' = ellD' := Option.some.inj (hcr.2.symm.trans hcD'.2)
  have htree := (rc.frame_tree_subset_at hp.noColl hx hci).2
  have htree' := (rc.frame_tree_subset_at hp.noColl hz hcr).2
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨x, i, tr.time i, rc.time_nonneg i,
      fun _ hq => rc.time_mono hq.le, hx, htree hC⟩
  have hPhiU' : ell'.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro C hC
    exact ⟨z, r, tr.time r, rc.time_nonneg r,
      fun _ hq => rc.time_mono hq.le, hz, htree' hC⟩
  have hBD := (AC.anc_viableAncestor ell.frame D).mono hPhiU
  have hOD := (AC.anc_viableAncestor ell'.frame D').mono hPhiU'
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hDO := AC.fastLock_compatible_of_votes (hac.upTo (rc.time_nonneg i)) _
      (hPK _) hx (Nat.lt_succ_self i)
      ((AC.upTo_fastLockAt rc.time_mono).mpr ⟨le_rfl, hfl⟩)
      (hp.committee_cs2_at
        (Healing.gbar_le_of_cutZ_le sp (hp.cutZ_le_ts_of_highOrigin_at ho))
        ((rc.ts_le_of_fastLock_at hfl).trans hib) (rc.time_nonneg i) hib)
      (B := ell'.frame.viableAncestor D') ?_
    · by_contra hn
      exact AC.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
    · intro v hv c hci' e hve hs
      obtain ⟨hct, hve⟩ := AC.upTo_voteAt.mp hve
      have hv := rc.antitone hct hv
      have hck : c < k := by
        rcases hact with hi | ht
        · omega
        · apply ht c
          obtain ⟨ellv, hcast⟩ := hve
          have hslot := (rc.castAt_facts_at hp.noColl hv hcast).2.2
          by_contra hn
          have := (AC.ts_le_iff_le_slot sp (rc.time_nonneg c) (j + 1 : Nat)).mp
            (not_lt.mp hn)
          omega
      exact hvote z r l _ hO hrb v c e hck hv
        ((rc.time_mono (by omega)).trans hib) hve (by omega)
  · have hgj : g ≤ sp.ts l := by
      have := hp.cutZ_le_ts_of_highOrigin_at ho
      have := Healing.lt_cutZ sp g
      have := Healing.le_gbar g
      have := sp.toParams.hΔ
      linarith
    have hsync := hp.reset_syncACAt (hi := sp.ts (l + 1 : Nat) + sp.Δ) hgj
    rcases AC.Growing.fastLock_same_slot hac _ hPK hp.committeeFacts.hsize hx hfl hz hfl' hsync
        (d := b) (fun _ => hib) hrb
        (hp.committee_cs2_at (Healing.gbar_le_of_cutZ_le sp (hp.cutZ_le_ts_of_highOrigin_at ho))
          ((rc.ts_le_of_fastLock_at hfl).trans hib) hb0 le_rfl) with h | h
    · exact AC.anc_total hU (hBD.trans h) hOD
    · exact AC.anc_total hU hBD (hOD.trans h)
  · have hDB := AC.fastLock_compatible_of_votes (hac.upTo (rc.time_nonneg r)) _
      (hPK _) hz (Nat.lt_succ_self r)
      ((AC.upTo_fastLockAt rc.time_mono).mpr ⟨le_rfl, hfl'⟩)
      (hp.committee_cs2_at
        (Healing.gbar_le_of_cutZ_le sp (hp.cutZ_le_ts_of_highOrigin_at hO))
        ((rc.ts_le_of_fastLock_at hfl').trans hrb) (rc.time_nonneg r) hrb)
      (B := ell.frame.viableAncestor D) ?_
    · by_contra hn
      exact AC.not_compatible_of_anc hU hOD hn hDB.symm
    · intro v hv c hcr' e hve hs
      obtain ⟨hct, hve⟩ := AC.upTo_voteAt.mp hve
      have hv := rc.antitone hct hv
      exact hvote x i j _ ho hib v c e (by omega) hv
        ((rc.time_mono (by omega)).trans hrb) hve (by omega)

/-- Earlier vote extension compares two bounded origins, including an origin whose
write is pending but whose label's votes all precede the induction cut. -/
theorem origins_compatible_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {k : Nat}
    (hvote : ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ z c e, c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
        AC.VoteAt tr.projAC z c e → j < e.msg.slot →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) (hrk : r < k) :
    Compatible (tr.HonestBlocksAt H) B O :=
  hp.toCore.origins_compatible_before_at hvote ho hib hact hO hrb hrk

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
