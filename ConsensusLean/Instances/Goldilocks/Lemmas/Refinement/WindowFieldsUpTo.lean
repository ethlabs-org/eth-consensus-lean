module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowCoverageUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs

public section

/-! # Goldilocks Refinement: the remaining final-window fields (#137)

consensus-lean#137. `finalWindow_fields_of_honest_anchors` gives the proposal cuts, proposals,
acceptances and chain of `FinalWindowData`. Here, per field:
* `slots`: from the honest-anchor slots (`honestProposalRun_slot`), for any offset function;
* `ordered`: from the slots and `time_mono` (`strictMono_cut_of_proposesAt`);
* `fresh`, `bounded`: from an explicit query premise and an explicit deadline premise;
* `ready`, `carrierProcessed`: OPEN (awake schedule of the anchor proposers, and delivery of the
  last anchor before the deadline); explicit premises of `finalWindow_data_of_honest_anchors`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

section Generic

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The block of an honest anchor of slot `s` has slot `s`. -/
theorem honestProposalRun_slot {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) : P.slot = s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hP
  exact hs

/-- **`slots`**, for any offset function `off`. -/
theorem window_slots_of_honest_anchors {ι : Type*} {start : Nat} {off : ι → Nat}
    {P : ι → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (start + off i) (P i)) :
    ∀ i, (P i).slot = start + off i := fun i => honestProposalRun_slot (hP i)

/-- **`ordered`**: proposal cuts of blocks of strictly increasing slots strictly increase. -/
theorem strictMono_cut_of_proposesAt (hrun : GoldilocksRun proposer dg H tr)
    {cut : Fin 4 → Nat} {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hcut : ∀ i, tr.ProposesAt (P i).proposer (cut i) (P i))
    (hs : StrictMono fun i => (P i).slot) : StrictMono cut := by
  intro i j hij
  by_contra h
  have ht := hrun.time_mono (Nat.le_of_not_gt h)
  rw [(hcut i).2.2, (hcut j).2.2] at ht
  exact absurd (sp.toParams.slotTime_strictMono (hs hij)) (not_lt.2 ht)

/-- **Window cut fields from four honest anchors**: the fields of
`finalWindow_fields_of_honest_anchors`, with the cut times, `ordered`, `fresh` (from `hq`) and
`bounded` (from `hD`). -/
theorem finalWindow_cuts_of_honest_anchors
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) {q D : Time}
    (hq : q < sp.toParams.slotTime (s 0)) (hD : sp.toParams.slotTime (s 3) ≤ D) :
    ∃ cut : Fin 4 → Nat, (∀ i, tr.ProposesAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, tr.AcceptAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, P i ∈ (tr.post (cut i)).fg.tree) ∧
      (∀ i, tr.post (cut i) = tr.state (P i).proposer (cut i + 1)) ∧
      (∀ i j, i ≤ j → Anc (tr.HonestBlocks H) (P i) (P j)) ∧
      (∀ i, tr.time (cut i) = sp.toParams.slotTime (s i)) ∧
      StrictMono cut ∧ q < tr.time (cut 0) ∧ ∀ i, tr.time (cut i) ≤ D := by
  obtain ⟨cut, hcut, hacc, htree, hpost, hch⟩ :=
    finalWindow_fields_of_honest_anchors hp hc hP hs hR hb hadj
  have hsl : ∀ i, (P i).slot = s i := fun i => honestProposalRun_slot (hP i)
  have ht : ∀ i, tr.time (cut i) = sp.toParams.slotTime (s i) := fun i => by
    rw [(hcut i).2.2, hsl i]
  have hord : StrictMono cut := strictMono_cut_of_proposesAt hp.run hcut (by
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

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **`FinalWindowData` from four honest anchors at gap `c`**, at the slots
`start + [0, c, 2c, 3c]`, with `2 ≤ c` and `3c ≤ δt`. Derived: `slots`, `proposals`,
`accepted`, `ordered`, `chain`. Explicit run/regime premises: `hq` (`fresh`) and `hD`
(`bounded`). OPEN, explicit premises: `hready` (`ready`, the awake schedule of each anchor
proposer over its catch-up interval) and `hcarrier` (`carrierProcessed`, delivery of the last
anchor to every node ready at the deadline). -/
theorem finalWindow_data_of_honest_anchors_gap (Q : FinalQuery S A V)
    {proposer : Nat → Fin Q.params.n}
    {dg : Digest (List (FG.Att Q.params.n)) (Payload Q.params.n)} {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ)) {c : Nat}
    (hc2 : 2 ≤ c) (h3c : 3 * c ≤ S.δt) (start : Nat)
    {P : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : ∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
      (start + ![0, c, 2 * c, 3 * c] i) (P i))
    (hR : Healing.drainTime Q.params a ≤ Q.params.ts start)
    (hb : Q.params.ts (start + 3 * c) ≤ b)
    (hq : Q.query < Q.params.toParams.slotTime start)
    (hD : Q.params.toParams.slotTime (start + 3 * c) ≤ Q.deadline)
    (hready : ∀ i, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) (P i).proposer
      (Q.params.toParams.slotTime (start + ![0, c, 2 * c, 3 * c] i)))
    (hcarrier : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j (P 3) ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, W.start = start ∧ W.gap = c ∧ W.block = P := by
  have hs : StrictMono fun i : Fin 4 => start + ![0, c, 2 * c, 3 * c] i := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simp <;> omega
  obtain ⟨cut, hcut, hacc, -, -, hch, ht, hord, hfr, hbd⟩ :=
    finalWindow_cuts_of_honest_anchors hp hc hP hs (by simpa using hR) (by simpa using hb)
      (by intro h; simp at h; omega) (by simpa using hq) (by simpa using hD)
  refine ⟨⟨start, c, hc2, h3c, P, cut, window_slots_of_honest_anchors hP, hcut, hacc,
    fun i => ?_, hfr, hord, hbd, hch, hcarrier⟩, rfl, rfl, rfl⟩
  rw [ht i]
  exact hready i

/-- **`FinalWindowData` from four honest anchors** at the slots `start + off a` with the
window's offsets `off = ![0, 2, 4, 6]`: `finalWindow_data_of_honest_anchors_gap` at `c = 2`. -/
theorem finalWindow_data_of_honest_anchors (Q : FinalQuery S A V)
    {proposer : Nat → Fin Q.params.n}
    {dg : Digest (List (FG.Att Q.params.n)) (Payload Q.params.n)} {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ)) (start : Nat)
    {P : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : ∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
      (start + ![0, 2, 4, 6] i) (P i))
    (hs : StrictMono fun i => start + ![0, 2, 4, 6] i)
    (hR : Healing.drainTime Q.params a ≤ Q.params.ts (start + 0))
    (hb : Q.params.ts (start + 6) ≤ b)
    (hadj : start + 6 = start + 4 + 1 →
      Q.params.ts (start + 4) + 6 * Q.params.Δ ≤ b)
    (hq : Q.query < Q.params.toParams.slotTime (start + 0))
    (hD : Q.params.toParams.slotTime (start + 6) ≤ Q.deadline)
    (hready : ∀ i, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) (P i).proposer
      (Q.params.toParams.slotTime (start + ![0, 2, 4, 6] i)))
    (hcarrier : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j (P 3) ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, W.start = start ∧ W.block = P := by
  have hoff : (![0, 2, 2 * 2, 3 * 2] : Fin 4 → Nat) = ![0, 2, 4, 6] := by
    ext i; fin_cases i <;> rfl
  obtain ⟨cut, hcut, hacc, -, -, hch, ht, hord, hfr, hbd⟩ :=
    finalWindow_cuts_of_honest_anchors hp hc hP hs hR hb hadj hq hD
  refine ⟨⟨start, 2, le_rfl, by have := A.timeout; omega, P, cut,
    by rw [hoff]; exact window_slots_of_honest_anchors hP, hcut, hacc, fun i => ?_, hfr,
    hord, hbd, hch, hcarrier⟩, rfl, rfl⟩
  rw [ht i]
  exact hready i

end Final

end Consensus.Goldilocks.Refinement

end
