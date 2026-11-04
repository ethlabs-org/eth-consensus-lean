module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.3 (c), the `Geo` half of the bridge

H.3 (c) is the bridge (claims H.3, status L), split as the paper splits it (workbench#14,
healing-simple `h3-bridge.md` at `ab8459a`) into an `Inv` half and a `Geo` half. The whole-run
`Inv` half and the combined bridge were retired with the reset-existence route (#136); this file
keeps:

* `settled_geo`, the `Geo` half (H.3 (c3)): `h3-bridge.md` §5, from HS.1 and the proposal
  sandwich (the floor and the case are fixed in a settled stable phase, `F` may advance); proved
  in `Geo` (`geo_of_settled`) over the HS.1 interface `viable_witness_retention`. It holds for
  every honest proposal of a settled phase: the reset, `T_b ≥ 8Δ`, `t_p` and `Prop⁺` are not
  used;
* the monotonicity of `Inv` (`Inv.mono`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- `Inv(t₀)` implies `Inv(t₀')` for `t₀ ≤ t₀'`: the protected blocks of `t₀'` are protected
blocks of `t₀`. -/
theorem _root_.Consensus.Goldilocks.SA.Inv.mono {sp : SAParams} {FGP : Type}
    {proposer : Nat → Fin sp.n}
    {ro : ReplayOrder sp FGP} {tr : SA.SATrace sp FGP ro} {H : Set (Fin sp.n)}
    {U : Set (SA.Blk sp.n FGP)} {t₀ t₀' : Time}
    (h : SA.Inv proposer tr H U t₀) (ht : t₀ ≤ t₀') :
    SA.Inv proposer tr H U t₀' := by
  refine fun B j hB => h B j ?_
  rcases hB with ⟨x, hx, i, CV, hj, hl, hs⟩ | ⟨x, hx, i, hj, hl, hs⟩ | ⟨hp, hP, hs, hv⟩
  · exact Or.inl ⟨x, hx, i, CV, hj, hl, by linarith⟩
  · exact Or.inr (Or.inl ⟨x, hx, i, hj, hl, by linarith⟩)
  · exact Or.inr (Or.inr ⟨hp, hP, by linarith, hv⟩)

/-- **H.3 (c3), `Geo` in a settled phase** (`h3-bridge.md` §5, from HS.1): for `T_b ≥ 8Δ`, every
honest proposal of a slot `p ≥ s_AC(a_z + T_b)` whose proposal and votes lie in one settled
effective phase has `Geo(P)` (`geo_of_settled`, which needs neither the reset nor the slot bound).
-/
theorem settled_geo {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ))
    (_hp : PropPlus tr H proposer g Gp)
    {a Tb : Time} (_ha : IsReset tr H g a) (_hTb : 8 * sp.Δ ≤ Tb) (p : Nat)
    (P : SA.Blk sp.n (List (FG.Att sp.n))) (hP : HonestProposalRun tr H proposer p P)
    (_htp : a + Tb + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p) (hph : InSettledPhase tr H g p) :
    SA.Geo proposer tr.projAC H p P :=
  geo_of_settled hrun hs hc p P hP hph

end Consensus.Goldilocks.Healing

end
