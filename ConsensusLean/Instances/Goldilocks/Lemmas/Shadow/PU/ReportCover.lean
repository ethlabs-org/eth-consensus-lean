module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots

public section

/-! # Report cover over the P-U shadow frame: the `fc_root = J` branch

The stock `ReportCover.held_target_viableHeads_or_higher_report_of_cases` (and the `FastLockRenewal`
branches that read `fc_root = J`) split on the store's fork-choice root. The shadow frame
`Node.frame'` has `fcRoot := F` and P-U viability, but the store-level `Store.fcRoot`,
`Store.Contest` and `Store.headHeightFloor` are unchanged, so the stock premises keep their meaning.

`isViable'_or_lt_floor_or_below_J` is the case analysis behind the shadow restatement: a block
`P ⪰ F` compatible with the store's `fc_root` is P-U viable, or below the stock head-height floor
(the stock higher-report premise applies), or strictly below `Σ.J` (the stock `cache_ahead_report`
with `X = J` applies). The open case "top-clean, `σ(P).h = h_j`, `J ⋠ P`" is the third branch: the
root premise, supplied today by `high_J_root_of_held_before_covered_at` (high `h_j`) and
`low_root_of_held_seed_at` (low `h_j`), forces `P ⪯ J`. No new hypothesis is needed.

The run-level statements take the shadow reset premises `ResetPremisesUpTo'` (Lane C's
`Shadow/PU/Run`), stubbed here until it lands: they are unresolved (`sorryAx`) until then. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- **The shadow viability split.** A block compatible (in the store) with the store's fork-choice
root is P-U viable, or of state height below the stock head-height floor, or strictly below
`Σ.J`. `h_j < h_max` holds at every reachable store (`cache_invariants`). -/
theorem isViable'_or_lt_floor_or_below_J {B : NodeBlock P ACP} (hjm : st.hj < st.hmax)
    (hroot : st.Anc st.fcRoot B ∨ st.Anc B st.fcRoot) :
    st.IsViable' B ∨ (st.σ B.root).h < st.headHeightFloor ∨ (st.Anc B st.J ∧ B ≠ st.J) := by
  classical
  rw [isViable'_iff]
  rcases Nat.lt_or_ge (st.σ B.root).h st.hmax with hlt | hge
  · rcases Nat.lt_or_ge ((st.σ B.root).h + 1) st.hmax with hlt2 | hge2
    · -- two or more below `h_max`: below either floor
      right; left
      unfold headHeightFloor
      split_ifs <;> omega
    · have heq : (st.σ B.root).h + 1 = st.hmax := by omega
      by_cases hgap : st.hj + 1 < st.hmax
      · exact Or.inl (Or.inr ⟨heq, Or.inl hgap⟩)
      by_cases hJ : st.Anc st.J B
      · exact Or.inl (Or.inr ⟨heq, Or.inr hJ⟩)
      by_cases hc : st.Contest
      · right; left
        unfold headHeightFloor
        simp only [hc, ite_true]
        omega
      · -- top-clean: the root is `Σ.J`, and `J ⋠ B` puts `B` strictly below it
        have htop : st.hmax = st.hj + 1 := by omega
        have hfc : st.fcRoot = st.J := by
          unfold fcRoot
          simp [htop, hc]
        rw [hfc] at hroot
        refine Or.inr (Or.inr ⟨hroot.resolve_left hJ, fun he => hJ (he ▸ .refl)⟩)
  · exact Or.inl (Or.inl hge)

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

namespace Stub

/-- Stub for Lane C's `ResetPremisesUpTo'` (`Shadow/PU/Run`): the stock
`Healing.Growing.ResetPremisesUpTo` with `run` over the growing shadow run. -/
def ResetPremisesUpTo' (tr : GoldilocksTrace' sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF a b : Time) (committee : Time → Finset (Fin sp.n)) (beta : ℚ) (hold : Time := 0) :
    Prop := by
  sorry

end Stub

variable {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time}

/-- **A held target above a high seed is P-U viable, or an earlier strictly higher report extends
it** (`ReportCover.held_target_viableHeads_or_higher_report_of_cases` over the shadow frame). The
root and floor premises are the stock ones, read from the store; the conclusion drops the stock
`Anc fcRoot P` conjunct (the shadow root is `F`). -/
theorem held_target_viableHeads'_or_higher_report_of_cases
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Stub.ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame' (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hhighroot : ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P)
    (hfloorrep : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor →
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) :
    P ∈ (Node.frame' (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  sorry

/-- The covered form: the root and floor premises discharged from `CompatibleWithOrigins`
(`ReportCover.held_target_viableHeads_or_higher_report_covered_at` over the shadow frame). -/
theorem held_target_viableHeads'_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Stub.ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame' (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ (Node.frame' (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  sorry

/-- The call form, read through the frame of an AC call (`Node.frame'`):
`held_target_viable_or_higher_report_covered_at` over the shadow frame. -/
theorem held_target_viable'_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Stub.ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    {ell : ACLabel (goldilocksNode' sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  sorry

end Consensus.Goldilocks.Healing.Growing.Shadow

end
