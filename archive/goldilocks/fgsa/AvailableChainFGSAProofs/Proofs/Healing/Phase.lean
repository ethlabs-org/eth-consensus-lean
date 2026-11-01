module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseOrder

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1142–1171, 1193–1209; plan S20, H-PHASE/P7.
DC: INTENTIONAL actual cumulative carriers for all three phase kinds.
This internal record stays in the proof lane. It does not assume relay or service. -/
structure HealingPhaseWitness (i m : Nat) : Prop where
  frontier : ∃ x W, HeldAt p c E rho i x W ∧ (heightView p W).h = m
  top : TopEvidence p c E rho i m →
    ∃ x C, HeldAt p c E rho i x C ∧ (heightView p C).h = m ∧
      (heightView p C).h_j + 1 = m ∧
      (heightView p C).J = (storeAt p c E rho i x).fg.J
  contest : ContestEvidence p c E rho i m →
    ∃ x C W, HeldAt p c E rho i x C ∧ HeldAt p c E rho i x W ∧
      (heightView p C).h = m ∧ (heightView p W).h = m ∧
      (heightView p C).h_j + 1 = m ∧ ¬ FGBlock.Preceq (heightView p C).J W

/-- Blueprint 21:1105–1113, 1153–1171; plan S20, H-PHASE/P7.
DC: INTENTIONAL the producer extracts accepted carriers from live caches.
No phase contract, service fact, or reset witness is an input. -/
theorem healing_phaseWitness {i m : Nat} (hm : 1 ≤ m)
    (hfront : frontierAtIdx p c E rho i = m) : HealingPhaseWitness p c E rho i m := by
  have hne : rho.honest.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    change rho.honest.sup (fun x => (storeAt p c E rho i x).fg.h_max) = m at hfront
    rw [he, Finset.sup_empty] at hfront
    change 0 = m at hfront
    omega
  have top (x : V) (hx : x ∈ rho.honest)
      (ht : (storeAt p c E rho i x).fg.h_j + 1 = m) :
      ∃ C, HeldAt p c E rho i x C ∧ (heightView p C).h = m ∧
        (heightView p C).h_j + 1 = m ∧
        (heightView p C).J = (storeAt p c E rho i x).fg.J := by
    obtain ⟨C, hC, _, hj, hJ⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.pair.1
    have hlt := (fgCertificateLaws p).height.justified_below_height C
    have hle := (healing_phase_height_le p c E rho hC).trans
      (healing_phase_local_le_frontier p c E rho hx)
    have hle' : (heightView p C).h ≤ m := hle.trans_eq hfront
    change (storeAt p c E rho i x).fg.h_j = _ at hj
    exact ⟨C, ⟨hx, hC⟩, by simp only [Height] at *; omega, hj ▸ ht, hJ.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hs⟩ := Finset.exists_mem_eq_sup rho.honest hne
      (fun x => (storeAt p c E rho i x).fg.h_max)
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho i x
    exact ⟨x, W, ⟨hx, hW⟩, hh.trans (hs.symm.trans hfront)⟩
  · rintro ⟨x, hx, ht⟩
    obtain ⟨C, hC, hh, hj, hJ⟩ := top x hx ht
    exact ⟨x, C, hC, hh, hj, hJ⟩
  · rintro ⟨x, hx, hH, hc⟩
    have ht : (storeAt p c E rho i x).fg.h_max = (storeAt p c E rho i x).fg.h_j + 1 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    have hw : ∃ W ∈ (storeAt p c E rho i x).fg.TF,
        FGBlock.Preceq (storeAt p c E rho i x).fg.F W ∧
        (heightView p W).h = (storeAt p c E rho i x).fg.h_max ∧
        ¬ FGBlock.Preceq (storeAt p c E rho i x).fg.J W :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
    obtain ⟨W, hW, _hFW, hhW, hn⟩ := hw
    obtain ⟨C, hC, hh, hj, hJ⟩ := top x hx (ht.symm.trans hH)
    exact ⟨x, C, W, hC, ⟨hx, hW⟩, hh, hhW.trans hH, hj, hJ ▸ hn⟩

/-- Blueprint 21:1236–1237, 1467–1468; plan S20, H-PHASE bootstrap.
DC: SAME the initial frontier is one if an honest node exists.
This fact does not assert the first service or a first rise. -/
theorem healing_phase_initial_frontier (hne : rho.honest.Nonempty) :
    frontierAtIdx p c E rho 0 = 1 := by
  change rho.honest.sup (fun _ => 1) = 1
  exact Finset.sup_const hne 1

end AvailableChain.FGSA.Run
end
