module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service

public section

/-! # Goldilocks Healing: the record half of the Healed bundle (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` §4.6–4.7
(L4.6 `healed`, L4.7 `record_premises_on_C`). The paper derives C2*⁺ (i), (ii) and R0 from the
clean-height premise CH. Under the reset they hold without CH at every height `h ≥ H_z + 1`, for
the entry `E h` of the high chain at `h` (`HighEntry`: a block below a high origin, held by an
honest node, whose state has height `h` and entry `E h` itself):

* C2*⁺ (i), rows: every honest row at `h` names `E h` (`high_row_entry`);
* C2*⁺ (ii), locks: every honest `Λ.lock[h]` is `⊥` or `E h`
  (`ResetPremisesUpTo.high_lock_entry_of_upTo`);
* R0: `permits(Λ, h, E h)` at every cut (`permits_high_entry`).

`HealedRecords` collects them from a height `h₀` on, with RH (`H_z + 1 ≤ h₀`).
`healed_records_of_reset_canonical_upTo` proves it from `ResetPremisesUpTo`, RH, and the high
entries at the heights
`≥ h₀`. RH and the high entries are explicit: in the paper they come from CH (iii) and L4.5. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- `Z` is an entry of the high chain at height `h`: it is below the block of a high origin, an
honest node holds it, and its state has height `h` and entry `Z`. -/
structure HighEntry (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (h : Nat)
    (Z : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  origin : ∃ x i j B, HighOrigin tr H g x i j B ∧ Anc (tr.HonestBlocks H) Z B
  held : ∃ z ∈ H, ∃ m, Z ∈ (tr.state z m).fg.tree ∧ ((tr.state z m).fg.σ Z.root).h = h ∧
    ((tr.state z m).fg.σ Z.root).Th = Z.root

/-- **C2*⁺ (i) under the reset (bounded form).** An honest row at a height `h ≥ H_z + 1`,
signed by the horizon `b`, names the entry of the high chain at `h`. -/
theorem ResetPremisesUpTo.high_row_entry {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {v : Fin sp.n} (hv : v ∈ H)
    {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hdb : tr.time d ≤ b)
    (hh : HZ tr H g + 1 ≤ att.h)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    (hE : E ∈ (tr.state z m).fg.tree) (hEh : ((tr.state z m).fg.σ E.root).h = att.h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : att.T = E.root := by
  obtain ⟨q, hqd, l, O, hO, X, hX, hXO, hXr, hXh, hXT⟩ := hp.high_row_source hv hs hh
  exact hXr.symm.trans (hp.high_entry_eq hO ((hp.run.time_mono hqd.le).trans hdb) ho hiob
    (hXO.mono fun D hD => ⟨v, hv, q, hD⟩) hEB hv hz hX hE (hXh.trans hEh.symm) hXT hET)

/-- **R0 under the reset (bounded form).** At a cut by the horizon `b`, an honest record permits
the entry of the high chain at every height `h ≥ H_z + 1`. -/
theorem ResetPremisesUpTo.permits_high_entry {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {i h : Nat} (hib : tr.time i ≤ b) (hh : HZ tr H g + 1 ≤ h)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    (hE : E ∈ (tr.state z m).fg.tree) (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) :
    (tr.state y i).record.permits h E.root := by
  have key := fun r hr => hp.record_entry_eq hy (r := r) hib hh hr ho hiob hEB hz hE hEh hET
  refine ⟨?_, fun r hr => Finset.mem_singleton.2 (key r (Or.inr (Or.inl hr))), ?_⟩
  · rcases ht : (tr.state y i).record.target h with _ | r
    · exact Or.inl rfl
    · exact Or.inr (by rw [key r (Or.inl ht)])
  · rcases hl : (tr.state y i).record.lock h with _ | r
    · exact Or.inl rfl
    · exact Or.inr (by rw [key r (Or.inr (Or.inr hl))])

/-- **C2*⁺ (i) under the reset.** `high_row_entry` with the horizon of the row and the origin. -/
theorem ResetPremises.high_row_entry (hp : ResetPremises tr H proposer dg g ΔF a)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) {E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : HighEntry tr H g att.h E) : att.T = E.root := by
  obtain ⟨⟨xo, io, jo, B, ho, hEB⟩, ⟨z, hz, m, hEm, hEh, hET⟩⟩ := hE
  have hup := hp.toUpTo tr H (le_max_left a (max (tr.time d) (tr.time io)))
  exact hup.high_row_entry hv hs ((le_max_left _ _).trans (le_max_right _ _)) hh ho
    ((le_max_right _ _).trans (le_max_right _ _)) hEB hz hEm hEh hET

/-- **R0 under the reset.** `permits_high_entry` with the horizon of the cut and the origin. -/
theorem ResetPremises.permits_high_entry (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {h : Nat} (hh : HZ tr H g + 1 ≤ h)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : HighEntry tr H g h E) :
    (tr.state y i).record.permits h E.root := by
  obtain ⟨⟨xo, io, jo, B, ho, hEB⟩, ⟨z, hz, m, hEm, hEh, hET⟩⟩ := hE
  have hup := hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time io)))
  exact hup.permits_high_entry hy ((le_max_left _ _).trans (le_max_right _ _)) hh ho
    ((le_max_right _ _).trans (le_max_right _ _)) hEB hz hEm hEh hET

/-- **The record half of the Healed bundle** from the height `h₀` on, for the entries `E h` of
the chain: RH, C2*⁺ (i) rows, C2*⁺ (ii) locks, and R0 at `h₀` (s4 L4.7 (a)–(c)). -/
structure HealedRecords (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (h₀ : Nat)
    (E : Nat → SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- RH: `h₀` is above the reset height. -/
  rh : HZ tr H g + 1 ≤ h₀
  /-- C2*⁺ (i): every honest row at a height `≥ h₀` names the entry at its height. -/
  rows : ∀ v ∈ H, ∀ d att, tr.SignAt v d att → h₀ ≤ att.h → att.T = (E att.h).root
  /-- C2*⁺ (ii): every honest lock at a height `≥ h₀` is `⊥` or the entry at that height. -/
  locks : ∀ y ∈ H, ∀ i h, h₀ ≤ h →
    (tr.state y i).record.lock h = none ∨ (tr.state y i).record.lock h = some (E h).root
  /-- R0: every honest record permits the entry at `h₀` at every cut. -/
  r0 : ∀ y ∈ H, ∀ i, (tr.state y i).record.permits h₀ (E h₀).root

end Consensus.Goldilocks.Healing

end
