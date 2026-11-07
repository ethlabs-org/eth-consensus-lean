module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed

public section

/-! # Frozen retention suppliers for the growing proposal pivot

These are the retention owner's contracts, copied verbatim for independent compilation.
They remain open here until integration imports the owner's implementations.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The kernel owner's finite high-origin comparison contract. -/
theorem origins_compatible_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

/-- Strict low-justification finality at an independently honest observation. -/
theorem low_finalized_below_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := by
  sorry

/-- An entry left behind a held chain has a high source signed by an observation-honest node. -/
theorem left_entry_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    {E C : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d,
      v ∈ H t ∧ d < k ∧ tr.SignAt v d att ∧ att.T = E.root ∧
        ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O := by
  sorry

/-- High justification compares an arbitrary held target with the actual frame root. -/
theorem high_J_root_of_held_at_call_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree)
    (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  sorry

/-- Low justification compares a held target using a held high seed. -/
theorem low_root_of_held_seed_at_call_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hSy : S ∈ (tr.state y i).fg.tree) (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
