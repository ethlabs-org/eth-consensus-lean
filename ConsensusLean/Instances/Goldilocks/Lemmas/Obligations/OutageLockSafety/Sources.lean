module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Candidate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyInstance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage lock safety: sources, OB-F and VA

* `source_compatible` (SRC): an FG source is the viable ancestor of a stored live fast lock
  block, so it is compatible with `P` when the stored locks are.
* `rows_sourced`: the honest attestations of a tree are sourced by blocks compatible with `P` when
  the sources of the earlier cuts are.
* `caches_compatible` (OB-F): `Σ.J` is compatible with `P` (its quorum has an honest
  attestation) and `Σ.F ⪯ Σ.J`.
* VA is `held_candidate_of_rows` (`Candidate`) at `P`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An attestation names the entry of its entry state. -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

/-- **(SRC)**: an FG source at cut `k` is compatible with `B` when every lock stored at `k`
names a held block compatible with `B`. -/
theorem source_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ (tr.state y k).ac.locks, ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧
      Compatible (tr.HonestBlocks H) L B)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC y k ℓ C) : Compatible (tr.HonestBlocks H) C B := by
  exact FamilySafety.source_compatible_instance hrun hnc hy hlocks h

/-- **Honest attestations are sourced by compatible blocks**: with every honest FG source before cut
`n` compatible with `B`, every honest attestation of `y`'s tree at `n` has an honest source
compatible with `B`. -/
theorem rows_sourced (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x ∈ H, ∀ k < n, ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C B)
    {y : Fin sp.n} (hy : y ∈ H) :
    HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n := by
  exact FamilySafety.rows_sourced_instance hrun hnc hsrc hy

/-- **OB-F**: with the honest attestations of `y`'s tree sourced by blocks compatible with a
block `B` of the honest blocks, `Σ.F` and `Σ.J` are compatible with `B`. -/
theorem caches_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {n : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H)
    (hsrc : HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n) :
    Compatible (tr.HonestBlocks H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y n).fg.J B := by
  exact FamilySafety.caches_compatible_instance hrun hnc hf hy hBU hsrc

end Consensus.Goldilocks.Compose

end
