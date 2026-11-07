module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import Mathlib.Tactic.FinCases

public section

/-! # The fields of a final window from four honest anchors, under growing faults

The growing form of `Obligations/WindowCoverageUpTo` and `Obligations/WindowFieldsUpTo`:

* `finalWindow_fields_of_honest_anchors_at`: proposal cuts, the proposers' acceptances, the
  post-store as the proposer's next state, and the anchor chain;
* `window_slots_of_honest_anchors_at`, `strictMono_cut_of_proposesAt_at`,
  `finalWindow_cuts_of_honest_anchors_at`: the slot, cut-time, order, freshness and bound fields;
* `finalWindow_data_of_honest_anchors_gap_at`: a `FinalWindowDataAt` at the slots
  `start + [0, c, 2c, 3c]`, with the readiness and carrier fields as explicit premises. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload)

section Generic

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **Window fields from four honest anchors**: proposal cuts with the proposals, the proposer's
acceptances, the post-store as the proposer's next state, and the chain. -/
theorem finalWindow_fields_of_honest_anchors_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) :
    ∃ cut : Fin 4 → Nat, (∀ i, tr.ProposesAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, tr.AcceptAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, P i ∈ (tr.post (cut i)).fg.tree) ∧
      (∀ i, tr.post (cut i) = tr.state (P i).proposer (cut i + 1)) ∧
      ∀ i j, i ≤ j → Anc (tr.HonestBlocksAt H) (P i) (P j) := by
  have hex : ∀ i, ∃ k, tr.ProposesAt (proposer (s i)) k (P i) := fun i =>
    proposesAt_of_honestProposalRun_at hp.run (hP i)
  choose cut hcut using hex
  have hmem : ∀ i, (P i).proposer ∈ H (tr.time (cut i)) := fun i =>
    (hcut i).2.1 ▸ proposer_mem_of_proposesAt_at hp.run (hP i) (hcut i)
  have hcut' : ∀ i, tr.ProposesAt (P i).proposer (cut i) (P i) := fun i => (hcut i).2.1 ▸ hcut i
  have hacc := fun i => accept_of_proposesAt_at hp.run hp.noColl (hmem i) (hcut' i)
  refine ⟨cut, hcut', fun i => (hacc i).1, fun i => ?_, fun i => (hacc i).2.2,
    window_anchors_chain_upTo_at hp hc hP hs hR hb hadj⟩
  rw [(hacc i).2.2]
  exact (hacc i).2.1

/-- **`slots`**, for any offset function `off`. -/
theorem window_slots_of_honest_anchors_at {ι : Type*} {start : Nat} {off : ι → Nat}
    {P : ι → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer (start + off i) (P i)) :
    ∀ i, (P i).slot = start + off i := fun i => honestProposalRun_slot_at (hP i)

/-- **`ordered`**: proposal cuts of blocks of strictly increasing slots strictly increase. -/
theorem strictMono_cut_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {cut : Fin 4 → Nat} {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hcut : ∀ i, tr.ProposesAt (P i).proposer (cut i) (P i))
    (hs : StrictMono fun i => (P i).slot) : StrictMono cut := by
  intro i j hij
  by_contra h
  have ht := hrun.time_mono (Nat.le_of_not_gt h)
  rw [(hcut i).2.2, (hcut j).2.2] at ht
  exact absurd (sp.toParams.slotTime_strictMono (hs hij)) (not_lt.2 ht)

/-- **Window cut fields from four honest anchors**, with the cut times, `ordered`, `fresh` (from
`hq`) and `bounded` (from `hD`). -/
theorem finalWindow_cuts_of_honest_anchors_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) {q D : Time}
    (hq : q < sp.toParams.slotTime (s 0)) (hD : sp.toParams.slotTime (s 3) ≤ D) :
    ∃ cut : Fin 4 → Nat, (∀ i, tr.ProposesAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, tr.AcceptAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, P i ∈ (tr.post (cut i)).fg.tree) ∧
      (∀ i, tr.post (cut i) = tr.state (P i).proposer (cut i + 1)) ∧
      (∀ i j, i ≤ j → Anc (tr.HonestBlocksAt H) (P i) (P j)) ∧
      (∀ i, tr.time (cut i) = sp.toParams.slotTime (s i)) ∧
      StrictMono cut ∧ q < tr.time (cut 0) ∧ ∀ i, tr.time (cut i) ≤ D := by
  obtain ⟨cut, hcut, hacc, htree, hpost, hch⟩ :=
    finalWindow_fields_of_honest_anchors_at hp hc hP hs hR hb hadj
  have hsl : ∀ i, (P i).slot = s i := fun i => honestProposalRun_slot_at (hP i)
  have ht : ∀ i, tr.time (cut i) = sp.toParams.slotTime (s i) := fun i => by
    rw [(hcut i).2.2, hsl i]
  have hord : StrictMono cut := strictMono_cut_of_proposesAt_at hp.run hcut (by
    intro i j hij
    change (P i).slot < (P j).slot
    rw [hsl i, hsl j]
    exact hs hij)
  refine ⟨cut, hcut, hacc, htree, hpost, hch, ht, hord, (ht 0).symm ▸ hq, fun i => ?_⟩
  rw [ht i]
  exact (sp.toParams.slotTime_strictMono.monotone (hs.monotone (Fin.le_last i))).trans hD

end Generic

section Final

open Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **`FinalWindowDataAt` from four honest anchors at gap `c`**, at the slots
`start + [0, c, 2c, 3c]`, with `2 ≤ c` and `3c ≤ δt`. Derived: `slots`, `proposals`, `accepted`,
`ordered`, `chain`; `fresh` from `hq`, `bounded` from `hD`. Explicit: `hready` (`ready`) and
`hcarrier` (`carrierProcessed`). -/
theorem finalWindow_data_of_honest_anchors_gap_at (Q : FinalQueryAt S A V)
    {proposer : Nat → Fin Q.params.n}
    {dg : Digest (List (FG.Att Q.params.n)) (Payload Q.params.n)} {g ΔF a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun Q.trace Q.keys g (2 * Q.params.Δ)) {c : Nat}
    (hc2 : 2 ≤ c) (h3c : 3 * c ≤ S.δt) (start : Nat)
    {P : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun Q.trace Q.keys proposer
      (start + ![0, c, 2 * c, 3 * c] i) (P i))
    (hR : Healing.drainTime Q.params a ≤ Q.params.ts start)
    (hb : Q.params.ts (start + 3 * c) ≤ b)
    (hq : Q.query < Q.params.toParams.slotTime start)
    (hD : Q.params.toParams.slotTime (start + 3 * c) ≤ Q.deadline)
    (hready : ∀ i, Regimes.Growing.ReadyAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) (P i).proposer
      (Q.params.toParams.slotTime (start + ![0, c, 2 * c, 3 * c] i)))
    (hcarrier : ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j (P 3) ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowDataAt S A V Q, W.start = start ∧ W.gap = c ∧ W.block = P := by
  have hs : StrictMono fun i : Fin 4 => start + ![0, c, 2 * c, 3 * c] i := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · change start + 0 < start + c; omega
    · change start + c < start + 2 * c; omega
    · change start + 2 * c < start + 3 * c; omega
  obtain ⟨cut, hcut, hacc, -, -, hch, ht, hord, hfr, hbd⟩ :=
    finalWindow_cuts_of_honest_anchors_at hp hc hP hs hR hb
      (fun h => by change start + 3 * c = start + 2 * c + 1 at h; omega) hq hD
  refine ⟨⟨start, c, hc2, h3c, P, cut, window_slots_of_honest_anchors_at hP, hcut, hacc,
    fun i => ?_, hfr, hord, hbd, hch, hcarrier⟩, rfl, rfl, rfl⟩
  rw [ht i]
  exact hready i

end Final

end Consensus.Goldilocks.Obligations.Growing

end
