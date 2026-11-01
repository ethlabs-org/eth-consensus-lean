module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.HealedClient

public section

/-! # Goldilocks Refinement: an awake honest node attests at each tick (L5.4 "they attest")

Workbench `fg-liveness/r14-end-to-end/s5-justify.md` §5, L5.4 step 5 ("they attest"). The run
model forces a tick at every public time at which an honest node is awake
(`LocalRun.tick_of_awake`), and every tick ends with the FG update: `ac_to_fg`, then
`fg_attest(C)` when `ac_to_fg` returns some `C` (`tickStep .fgUpdate`). So:

* `tick_toFG_attest`: every tick of an honest node has an `ac_to_fg` cut at its time; if that
  call returns `C`, the next cut is `fg_attest(C)` on the node's store and record at that cut.
* `awake_toFG_attest`: the same for every honest node awake at a public time `t ≥ 0`.
* `attest_signs_target`, `awake_signs_target`: under `HealedRecords` from `h₀`, at an entry
  state `σe` of height `h ≥ h₀` with entry `E h` and nothing sent at `h`, that `fg_attest`
  signs the target row of `σe` (`HealedRecords.createAtt_target`).

The model does **not** force `ac_to_fg` to return a block: it returns `⊥` when the node has not
joined, when no live fast lock of slot `≥ slot(t) − 2` names a viable block, or when the
deepest such block is at or below `fg_reported` (`SA.acToFG`). That return value (an AC
liveness fact) and "nothing sent at `h`" stay explicit premises. -/

namespace Consensus.Goldilocks.Refinement

open Node

section Generic

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

private theorem fgUpdate_cuts (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    (tickStep proposer dg y st t x .fgUpdate).2[0]? = some (.ac ⟨.toFG, frame st, []⟩) ∧
      ∀ C, (A.toFG st.ac (frame st) t).2.1 = some C →
        (tickStep proposer dg y st t x .fgUpdate).2[1]? =
          some (.fg (.attest C ((st.fg.attest st.record y C).map Prod.fst))) := by
  simp only [tickStep, acToFG]
  refine ⟨by split <;> simp, fun C hC => ?_⟩
  rw [hC]
  simp only [attest]
  split <;> simp_all

/-- **Every tick has an `ac_to_fg` cut, followed by `fg_attest(C)` when it returns `C`.** The
`fg_attest` reads the node's store and record at the `ac_to_fg` cut. -/
theorem tick_toFG_attest (h : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {j : Nat} {t : Time} {x : Nat} (hg : tr.GroupAt proposer dg y j t (.tick x)) :
    ∃ k, j ≤ k ∧ tr.time k = t ∧
      tr.CallAt y k (.ac ⟨.toFG, frame (tr.state y k), []⟩) ∧
      ∀ C, (A.toFG (tr.state y k).ac (frame (tr.state y k)) t).2.1 = some C →
        tr.time (k + 1) = t ∧ tr.CallAt y (k + 1)
          (.fg (.attest C (((tr.state y k).fg.attest (tr.state y k).record y C).map
            Prod.fst))) := by
  set st := tr.state y j
  set r₁ := tickStep proposer dg y st t x .acTick
  set r₂ := tickStep proposer dg y r₁.1 t x .proposal
  set r₃ := tickStep proposer dg y r₂.1 t x .fgUpdate
  have hcuts : (exec proposer dg y st t (.tick x)).2 = (r₁.2 ++ r₂.2) ++ r₃.2 := by
    simp [exec, onTick, runSteps, tickSteps, r₁, r₂, r₃]
  have hch : CutChain y t st (r₁.2 ++ r₂.2) r₂.1 :=
    Compose.chain_append y (Compose.tickStep_chain proposer dg y st t x _)
      (Compose.tickStep_chain proposer dg y _ t x _)
  set n := (r₁.2 ++ r₂.2).length
  have hgc : ∀ m c, (exec proposer dg y st t (.tick x)).2[m]? = some c →
      tr.node (j + m) = y ∧ tr.time (j + m) = t ∧ tr.label (j + m) = some c := by
    intro m c hm
    obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hm
    obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 m hk'
    exact ⟨hn, ht, hl.trans (congrArg some hc)⟩
  have hcut : ∀ m c, r₃.2[m]? = some c →
      tr.node (j + n + m) = y ∧ tr.time (j + n + m) = t ∧ tr.label (j + n + m) = some c := by
    intro m c hm
    rw [Nat.add_assoc]
    refine hgc (n + m) c ?_
    rw [hcuts, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact hm
  have hst : tr.state y (j + n) = r₂.1 := by
    refine Compose.cutChain_run h hy hch j rfl fun m hm => hgc m _ ?_
    rw [hcuts, List.getElem?_append_left hm]
    exact List.getElem?_eq_getElem hm
  obtain ⟨h0, h1⟩ := fgUpdate_cuts (proposer := proposer) (dg := dg) y r₂.1 t x
  obtain ⟨hn0, ht0, hlb0⟩ := hcut 0 _ h0
  rw [Nat.add_zero] at hn0 ht0 hlb0
  refine ⟨j + n, by omega, ht0, ⟨hn0, by rw [hlb0, hst]⟩, fun C hC => ?_⟩
  rw [hst] at hC ⊢
  obtain ⟨hn1, ht1, hlb1⟩ := hcut 1 _ (h1 C hC)
  exact ⟨ht1, hn1, hlb1⟩

/-- **An honest node awake at a public time `t ≥ 0`** has an `ac_to_fg` cut at `t`, followed by
`fg_attest(C)` when it returns `C` (`tick_toFG_attest`, `LocalRun.tick_of_awake`). -/
theorem awake_toFG_attest (h : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {t : Time} (ht : 0 ≤ t) (hp : P.IsPublic t) (hw : tr.awake y t) :
    ∃ k, tr.time k = t ∧ tr.CallAt y k (.ac ⟨.toFG, frame (tr.state y k), []⟩) ∧
      ∀ C, (A.toFG (tr.state y k).ac (frame (tr.state y k)) t).2.1 = some C →
        tr.time (k + 1) = t ∧ tr.CallAt y (k + 1)
          (.fg (.attest C (((tr.state y k).fg.attest (tr.state y k).record y C).map
            Prod.fst))) := by
  obtain ⟨j, x, hg⟩ := h.tick_of_awake y hy t ht hp hw
  obtain ⟨k, -, hk⟩ := tick_toFG_attest h hy hg
  exact ⟨k, hk⟩

end Generic

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **N0⁺ at an `fg_attest` cut.** If `fg_attest(C)` runs at cut `k + 1` on the store and record
of cut `k`, its entry state `σe = Σ.σ[Σ.σ[C].T_h]` has height `h ≥ h₀` and entry `E h`, and
the record has sent nothing at `h`, then the cut signs the target row of `σe`. -/
theorem attest_signs_target (hrun : GoldilocksRun proposer dg H tr) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hc : tr.CallAt y (k + 1)
      (.fg (.attest C (((tr.state y k).fg.attest (tr.state y k).record y C).map Prod.fst))))
    (hh : h₀ ≤ ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h)
    (hT : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
      (E ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h).root)
    (hs : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h) :
    tr.SignAt y (k + 1) ⟨y, ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h,
      ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, false,
      (tr.state y k).record.finalityPair
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th)⟩ := by
  refine ⟨C, ?_⟩
  have ha := hR.createAtt_target hrun hy k hh hT hs
  simp only [Store.attest] at hc
  rw [ha] at hc
  exact hc

/-- **"They attest" (L5.4 step 5) for one node.** An honest node `y` awake at a public time
`t ≥ 0` has an `ac_to_fg` cut `k` at `t`. If it returns `C`, and the entry state `σe` of `C` at
cut `k` has height `h ≥ h₀` with entry `E h` and `y` has sent nothing at `h`, then `y` signs the
target row of `σe` at cut `k + 1`, at time `t`. -/
theorem awake_signs_target (hrun : GoldilocksRun proposer dg H tr) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {t : Time} (ht : 0 ≤ t) (hp : sp.toParams.IsPublic t)
    (hw : tr.awake y t) :
    ∃ k, tr.time k = t ∧ tr.CallAt y k (.ac ⟨.toFG, frame (tr.state y k), []⟩) ∧
      ∀ C, ((goldilocksNode sp ro).toFG (tr.state y k).ac (frame (tr.state y k)) t).2.1 =
          some C →
        h₀ ≤ ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h →
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
          (E ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h).root →
        (∀ b ∈ (tr.state y k).record.sent,
          b.1 ≠ ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h) →
        tr.time (k + 1) = t ∧
          tr.SignAt y (k + 1) ⟨y, ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h,
            ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, false,
            (tr.state y k).record.finalityPair
              ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th)⟩ := by
  obtain ⟨k, hkt, hk, hC⟩ := awake_toFG_attest hrun.toLocalRun hy ht hp hw
  refine ⟨k, hkt, hk, fun C hc hh hT hs => ?_⟩
  obtain ⟨ht1, hc1⟩ := hC C hc
  exact ⟨ht1, attest_signs_target hrun hR hy hc1 hh hT hs⟩

end Consensus.Goldilocks.Refinement

end
