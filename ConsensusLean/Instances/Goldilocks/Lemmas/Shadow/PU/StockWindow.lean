module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window

public section

/-! # The stock frame window over a shadow run

The stock `Generic.FrameWindow … floor kindJ J` pins `head_height_floor`, the J-kind
`h_max = h_j + 1 ∧ ¬ Contest` and, in the J-kind, `J`. The P-U window `FrameWindow' … M isTop J`
pins `h_max`, the top `h_max = h_j + 1` and, at the top, `J`. Since
`head_height_floor = if Contest then h_max else h_max − 1` and a contest is at the top, the stock
window determines the P-U one exactly when no reader of the window is in a contest:

* in the J-kind, `M = floor + 1` and the window is at the top (`toFrameWindow'_of_kind`);
* outside the J-kind with no contest, `M = floor + 1` and no reader is at the top
  (`toFrameWindow'_of_noContest`).

With a contest outside the J-kind, `h_max` is `floor` at a contesting reader and `floor + 1` at a
non-top one, so neither `M` nor the top is constant. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A stock window in the J-kind is the P-U top window at `M = floor + 1`. -/
theorem toFrameWindow_of_kind {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hw : Generic.FrameWindow tr H lo hi floor kindJ J) (hk : kindJ) :
    FrameWindow' tr H lo hi (floor + 1) True J := by
  have key : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
      (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
        (tr.state y i).fg.hmax = floor + 1 := by
    intro y i hy hlo hhi
    obtain ⟨htop, hnc⟩ := (hw.kind_iff y i hy hlo hhi).2 hk
    have hfl := hw.floor_eq y i hy hlo hhi
    rw [Store.headHeightFloor, ite_eq_right hnc] at hfl
    exact ⟨htop, by omega⟩
  exact ⟨fun y i hy hlo hhi => (key y i hy hlo hhi).2,
    fun y i hy hlo hhi => iff_true_intro (key y i hy hlo hhi).1,
    fun y i hy hlo hhi _ => hw.root_eq y i hy hlo hhi hk⟩

/-- A stock window outside the J-kind in which no honest reader is in a contest is the P-U
non-top window at `M = floor + 1`. -/
theorem toFrameWindow_of_noContest {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hw : Generic.FrameWindow tr H lo hi floor kindJ J) (hk : ¬ kindJ)
    (hnoC : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
      ¬ (tr.state y i).fg.Contest) :
    FrameWindow' tr H lo hi (floor + 1) False J := by
  have key : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
      (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 ∧
        (tr.state y i).fg.hmax = floor + 1 := by
    intro y i hy hlo hhi
    have hnc := hnoC y i hy hlo hhi
    have htop : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 :=
      fun h => hk ((hw.kind_iff y i hy hlo hhi).1 ⟨h, hnc⟩)
    have hjm := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
      (Compose.Growing.reachable_at' hrun (hrun.time_nonneg i) hy
        (fun q hq => hrun.time_mono hq.le)).reachableWith
    have hfl := hw.floor_eq y i hy hlo hhi
    rw [Store.headHeightFloor, ite_eq_right hnc] at hfl
    exact ⟨htop, by omega⟩
  exact ⟨fun y i hy hlo hhi => (key y i hy hlo hhi).2,
    fun y i hy hlo hhi => iff_false_intro (key y i hy hlo hhi).1,
    fun _ _ _ _ _ h => h.elim⟩

end Consensus.Goldilocks.Healing

end
