module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: comparing origins (extending `P_s` to `P_{s+1}`)

workbench#11 §2.1, §2.2 and §4 "Extend the origin frontier".

* **An honest supporter** (`honest_supporter`, §2.1): an origin of label `s` has an honest slot-`s`
  vote whose head extends it. For a result: the honest validators awake and joined at `t_s + Δ`
  (more than `f`, by `Sleepy`) vote in slot `s` and reach the joined writer before `t_s + 2Δ`, so
  they are among its participants; if every counted supporter were faulty, the participants would
  hold those seats and more than `f` disjoint honest ones, against the strict majority. For an
  optimistic selection: `3n/4 > f` voters.
* **Same-label origins compare** (`same_label_compatible`, §2.2): two results by the disjointness
  of conflicting supporter sets and the relay of counted votes to both writers (RR); a result and
  an optimistic selection by the relay of the `≥ 3n/4` optimistic seats (RO); two selections share
  `n/2 > f` seats (OO).
* `origins_below_succ`: an origin of label `s` and one of label `j < s` are both below the head of
  the honest supporter's vote, which extends the older one by `V_s`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **§2.1, an origin has an honest supporter**: an honest slot-`s` vote whose head extends it. -/
theorem honest_supporter (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : Origin tr H C s) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  sorry

/-- **§2.2, origins of one label are compatible** (RR, RO, OO). -/
theorem same_label_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : Origin tr H C s) (hC' : Origin tr H C' s) : Compatible (tr.HonestBlocks H) C C' := by
  sorry

/-- **Extending the origin frontier**: `P_s` and `V_s` give `P_{s+1}`. -/
theorem origins_below_succ (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H s) (hV : VotesBelow tr H s) :
    OriginsBelow tr H (s + 1) := by
  sorry

end Consensus.Goldilocks.Compose

end
