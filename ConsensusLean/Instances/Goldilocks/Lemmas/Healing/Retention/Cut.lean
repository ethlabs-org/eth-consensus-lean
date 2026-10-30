module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Goldilocks Healing, HR.4: the cut step and the rows

The cut step (`retention_cut_step`, G1.10 at the height-scoped scope) and (R1)'s rows
(`high_rows`, the provenance of the high sources). Design: workbench#22 (`hr4-cut-scope.md`).

Interfaces: open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The cut step: G1.10 at the height-scoped scope** (claims HR.4, G1.10 "The healing reset
induction uses the same node with a height-scoped `𝓔`"; §12 "Steps available once each protected
origin is admitted"; §13 "Retaining the witnesses and the frame", "Closing the
first-violating-event induction"). (R2) after the honest call at cut `k`, from the invariant at the
earlier cuts and the votes of cut `k`: with `𝓔_B` the entries of height `≥ H_z + 1` that conflict
with `B` and `T₀ = a − Δ`, the first clause of (K1_𝓔) is HR.1 (c); the later-row clause holds
because every honest high row signed by then names an entry on the chain of a high origin
comparable with `B` (`high_rows`, `origins_compatible` over the earlier votes), and every row
signed at `a` is covered (HR.1 (c)); so no entry of `𝓔_B` is justified or left on an accepted
chain. A low finalized entry is below `B` by G1.2; a high one has a row witness whose source is
comparable with `B`. No (K0) is used. The core is `Store.quorum_free_entries` with `𝓔 = 𝓔_B`;
`Store.cut_scope` (C1.1's scope) does not apply as stated: it assumes (K0) for `Σ.J` and (K1) for
every conflicting entry above an honest `Σ.F` at `Ts`, low ones included, which fail at `a_z`. -/
theorem retention_cut_step (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') (hv : VoteInv tr H g k) :
    CacheInv tr H g a k := by
  sorry

/-- **(R1), the rows** (HR.1 (a), A1.5 with `τ = ḡ`; §16). The source `C` of an honest row signed
at or after `a` (from `c_z` on) is at or below the block of a live fast lock written after `ḡ`,
which is at or below the stored block `B` of that write; the row's height pair is `C`'s height and
entry, so `B` has state height `≥ σ[C].h ≥ H_z + 1` (a high origin), and the named entry is the
entry at that height on `B`'s chain in the writer's tree. -/
theorem high_rows (hp : ResetPremises tr H dg g ΔF a) :
    ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root := by
  sorry

end Consensus.Goldilocks.Healing

end
