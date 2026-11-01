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
* C2*⁺ (ii), locks: every honest `Λ.lock[h]` is `⊥` or `E h` (`high_lock_entry`);
* R0: `permits(Λ, h, E h)` at every cut (`permits_high_entry`).

`HealedRecords` collects them from a height `h₀` on, with RH (`H_z + 1 ≤ h₀`).
`healed_records_of_reset` proves it from `ResetPremises`, RH, and the high entries at the heights
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

/-- **C2*⁺ (ii) under the reset.** An honest lock at a height `h ≥ H_z + 1` is `⊥` or the entry
of the high chain at `h`. -/
theorem ResetPremises.high_lock_entry (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {h : Nat} (hh : HZ tr H g + 1 ≤ h)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : HighEntry tr H g h E) :
    (tr.state y i).record.lock h = none ∨ (tr.state y i).record.lock h = some E.root :=
  (hp.permits_high_entry hy i hh hE).2.2

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

/-- **The record half of the Healed bundle under the reset (WI-17).** From `ResetPremises`, RH
(`H_z + 1 ≤ h₀`) and the high entries `E h` at every height `h ≥ h₀`. No CH and no time
bound: the reset alone makes the honest records clean above `H_z`. -/
theorem healed_records_of_reset (hp : ResetPremises tr H proposer dg g ΔF a) {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hrh : HZ tr H g + 1 ≤ h₀)
    (hE : ∀ h, h₀ ≤ h → HighEntry tr H g h (E h)) : HealedRecords tr H g h₀ E where
  rh := hrh
  rows _ hv _ _ hs hh := hp.high_row_entry hv hs (hrh.trans hh) (hE _ hh)
  locks _ hy i _ hh := hp.high_lock_entry hy i (hrh.trans hh) (hE _ hh)
  r0 _ hy i := hp.permits_high_entry hy i hrh (hE h₀ le_rfl)

/-- **A high entry from an honest row (WI-17).** Under the reset, an honest row at a height
`h ≥ H_z + 1` names a high entry at `h`: the entry of the row's source chain, below the high
origin of an earlier fast lock of the signer (`high_row_source`) and held by the signer. -/
theorem ResetPremises.highEntry_of_row (hp : ResetPremises tr H proposer dg g ΔF a)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E, HighEntry tr H g att.h E ∧ E.root = att.T := by
  obtain ⟨r, -, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := high_row_source hp hv hs hh
  exact ⟨E, ⟨⟨v, r, l, O, hO, hEO.mono fun D hD => ⟨v, hv, r, hD⟩⟩, ⟨v, hv, r, hE, hEh, hET⟩⟩,
    hEr⟩

/-- **The record half of the Healed bundle from honest rows (WI-17).** Under the reset, with RH
(`H_z + 1 ≤ h₀`) and an honest row at every height `h ≥ h₀`, the entries that these rows name
are a family `E` of high entries (`highEntry_of_row`), and `HealedRecords` holds for `E`. The
row at each height is the only premise left of `HighEntry`; in the paper it is the output of
the justification at that height (s5). -/
theorem healed_records_of_rows (hp : ResetPremises tr H proposer dg g ΔF a) {h₀ : Nat}
    (hrh : HZ tr H g + 1 ≤ h₀)
    (hrow : ∀ h, h₀ ≤ h → ∃ v ∈ H, ∃ d att, tr.SignAt v d att ∧ att.h = h) :
    ∃ E : Nat → SA.Blk sp.n (List (FG.Att sp.n)),
      (∀ h, h₀ ≤ h → HighEntry tr H g h (E h)) ∧ HealedRecords tr H g h₀ E := by
  have hex : ∀ h, h₀ ≤ h → ∃ E, HighEntry tr H g h E := by
    intro h hh
    obtain ⟨v, hv, d, att, hs, rfl⟩ := hrow h hh
    obtain ⟨E, hE, -⟩ := hp.highEntry_of_row hv hs (hrh.trans hh)
    exact ⟨E, hE⟩
  classical
  let E : Nat → SA.Blk sp.n (List (FG.Att sp.n)) := fun h =>
    if hh : h₀ ≤ h then Classical.choose (hex h hh) else Classical.choose (hex h₀ le_rfl)
  have hE : ∀ h, h₀ ≤ h → HighEntry tr H g h (E h) := fun h hh => by
    have hc := Classical.choose_spec (hex h hh)
    simpa only [E, hh, ↓reduceDIte] using hc
  exact ⟨E, hE, healed_records_of_reset hp hrh hE⟩

/-- **A high entry from an honest record entry (WI-17).** Under the reset, a target, timeout or
lock entry `r` of an honest record at a height `h ≥ H_z + 1` is the root of a high entry at `h`
(`high_record_entry`). -/
theorem ResetPremises.highEntry_of_record (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {i h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r) :
    ∃ E, HighEntry tr H g h E ∧ E.root = r := by
  obtain ⟨x, i', j, B, ho, Z, hZB, hZr, z, hz, m, hZ, hZh, hZT⟩ := high_record_entry hp
    (height_scoped_retention sp ro proposer dg H tr g ΔF
      hp.run hp.healthy hp.noColl a hp.reset).rows hy hh hr
  exact ⟨Z, ⟨⟨x, i', j, B, ho, hZB⟩, ⟨z, hz, m, hZ, hZh, hZT⟩⟩, hZr⟩

/-- **The canonical entry family (WI-17).** At a height `h` with a high entry, a chosen high
entry (the choice does not matter: under the reset the roots agree, `high_row_entry`); at any
other height the default block `Z₀`. -/
noncomputable def canonicalEntry (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time)
    (Z₀ : SA.Blk sp.n (List (FG.Att sp.n))) (h : Nat) : SA.Blk sp.n (List (FG.Att sp.n)) := by
  classical
  exact if hx : ∃ E, HighEntry tr H g h E then Classical.choose hx else Z₀

/-- At a height with a high entry, the canonical entry is a high entry. -/
theorem canonicalEntry_highEntry {Z₀ : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hx : ∃ E, HighEntry tr H g h E) : HighEntry tr H g h (canonicalEntry tr H g Z₀ h) := by
  classical
  have hc := Classical.choose_spec hx
  simpa only [canonicalEntry, hx, ↓reduceDIte] using hc

/-- **The record half of the Healed bundle under the reset, canonical form (WI-17).** From
`ResetPremises` and RH (`H_z + 1 ≤ h₀`) alone, for every default block `Z₀`: no premise on the
existence of rows or high entries. A height without a high entry has no honest row, lock,
target or timeout entry (`highEntry_of_row`, `highEntry_of_record`), so there the fields hold
vacuously. -/
theorem healed_records_of_reset_canonical (hp : ResetPremises tr H proposer dg g ΔF a)
    {h₀ : Nat} (hrh : HZ tr H g + 1 ≤ h₀) (Z₀ : SA.Blk sp.n (List (FG.Att sp.n))) :
    HealedRecords tr H g h₀ (canonicalEntry tr H g Z₀) where
  rh := hrh
  rows _ hv _ _ hs hh := by
    obtain ⟨E, hE, -⟩ := hp.highEntry_of_row hv hs (hrh.trans hh)
    exact hp.high_row_entry hv hs (hrh.trans hh) (canonicalEntry_highEntry ⟨E, hE⟩)
  locks _ hy i h hh := by
    rcases hl : (tr.state _ i).record.lock h with _ | r
    · exact Or.inl rfl
    · obtain ⟨E, hE, -⟩ := hp.highEntry_of_record hy (hrh.trans hh) (Or.inr (Or.inr hl))
      rw [← hl]
      exact hp.high_lock_entry hy i (hrh.trans hh) (canonicalEntry_highEntry ⟨E, hE⟩)
  r0 y hy i := by
    by_cases hx : ∃ E, HighEntry tr H g h₀ E
    · exact hp.permits_high_entry hy i hrh (canonicalEntry_highEntry hx)
    · have no : ∀ r, ¬ ((tr.state y i).record.target h₀ = some r ∨
          r ∈ (tr.state y i).record.timeout h₀ ∨ (tr.state y i).record.lock h₀ = some r) :=
        fun r hr => hx ((hp.highEntry_of_record hy hrh hr).imp fun _ h => h.1)
      refine ⟨?_, fun r hr => absurd (Or.inr (Or.inl hr)) (no r), ?_⟩
      · rcases ht : (tr.state y i).record.target h₀ with _ | r
        · exact Or.inl rfl
        · exact absurd (Or.inl ht) (no r)
      · rcases hl : (tr.state y i).record.lock h₀ with _ | r
        · exact Or.inl rfl
        · exact absurd (Or.inr (Or.inr hl)) (no r)

end Consensus.Goldilocks.Healing

end
