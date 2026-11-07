module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame

public section

/-! # Goldilocks under `Sleepy` with growing faults: honest rows and their sources

`HonestRowsSourcedAt tr H G y i`: every attestation of a block in the tree of `y` before cut `i`
whose signer is honest at `tr.time i` has a source satisfying `G`, held by a node honest at
`tr.time i` at a cut `k ≤ i` (the signers and the source holder are classified at the reading cut,
Lemma G). The frame lemmas of `Compose/Sleepy/Frame` lift at the cut's time `d = tr.time i`, with
`2 f_d < n`; their honest sources are held while honest at `d` (`IsHonestSourceAt`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The honest rows of `y`'s tree before cut `i` are sourced in `G`, classified at `tr.time i`. -/
def HonestRowsSourcedAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
    ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
      ((tr.state x k).fg.σ D.root).Th = a.T

theorem honestRowsSourcedAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat} :
    HonestRowsSourcedAt tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
        ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
          ((tr.state x k).fg.σ D.root).Th = a.T :=
  Iff.rfl

/-- `D` is the source of target `T` held, while honest at `d`, by a node before a cut whose earlier
cuts are at times `≤ d`. -/
def IsHonestSourceAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (T : Nat) (d : Time) : Prop :=
  ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧ D ∈ (tr.state x k).fg.tree ∧
    ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSourceAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat} {d : Time} :
    IsHonestSourceAt tr H D T d ↔ ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧
      D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An honest source of the prefix through `d` is an honest source held while honest at `d`. -/
theorem isHonestSourceAt_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {d : Time}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {T : Nat}
    (h : Compose.IsHonestSource (tr.upTo d) (H d) D T) : IsHonestSourceAt tr H D T d := by
  obtain ⟨x, hx, k, hDt, hT⟩ := Compose.isHonestSource_iff.1 h
  obtain ⟨i₀, -, hb, hs⟩ := Trace.upTo_state_exists tr hrun.time_mono x k
  rw [hs] at hDt hT
  exact ⟨x, i₀, hx, hb, hDt, hT⟩

/-- The honest rows sourced at cut `i` are the honest rows of the prefix through `tr.time i`. -/
theorem HonestRowsSourcedAt.upTo (hrun : Growing.GoldilocksRun proposer dg H tr)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat}
    (h : HonestRowsSourcedAt tr H G y i) :
    Compose.HonestRowsSourced (tr.upTo (tr.time i)) (H (tr.time i)) G y i := by
  have hm := hrun.time_mono
  refine Compose.honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  rw [Trace.upTo_state tr y fun _ hk => hm hk.le] at hX
  obtain ⟨D, hD, x, k, hx, hki, hDt, hT⟩ := h X hX a ha hav
  have hst : (tr.upTo (tr.time i)).state x k = tr.state x k :=
    Trace.upTo_state tr x fun _ hk' => hm (hk'.le.trans hki)
  exact ⟨D, hD, Compose.isHonestSource_iff.2 ⟨x, hx, k, by rw [hst]; exact hDt,
    by rw [hst]; exact hT⟩⟩

/-- **An honest row was signed while honest** (`honest_row_signed_before` at `d = tr.time i`): an
attestation of a block in the tree of a node honest at cut `i`, whose signer is honest at `i`, was
signed at an earlier cut, at which its signer was honest, before the block's acceptance. -/
theorem honest_row_signed_before_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H (tr.time i)) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a ∧ a.val ∈ H (tr.time k) := by
  have hm := hrun.time_mono
  obtain ⟨m, hmi, hA, k, hkm, hS⟩ := honest_row_signed_before
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
    (by rw [Trace.upTo_state tr y fun _ hk => hm hk.le]; exact hX) ha hav
  obtain ⟨-, hA⟩ := (RunTrace.upTo_acceptAt tr).mp hA
  obtain ⟨hkd, hS⟩ := (RunTrace.upTo_signAt tr).mp hS
  exact ⟨m, hmi, hA, k, hkm, hS, hrun.antitone hkd hav⟩

/-- **The justification has an honest source** (`justified_honest_source_before` at the cut's time
`d`, with `2 f_d < n`): at `h_j ≥ 1`, `Σ.J` of a node honest at cut `i` is an entry block of height
`h_j`, and its target has a source satisfying `G`, held while honest at `d`. -/
theorem justified_honest_source_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedAt tr H G y i) (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSourceAt tr H D (tr.state y i).fg.J.root (tr.time i) := by
  have hst := Trace.upTo_state tr y (d := tr.time i) fun _ hk => hrun.time_mono hk.le
  have h := justified_honest_source_before (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hf hy
    (hsrc.upTo hrun) (by rw [hst]; exact hj)
  rw [hst] at h
  obtain ⟨h1, h2, D, hD, hDs⟩ := h
  exact ⟨h1, h2, D, hD, isHonestSourceAt_of_upTo hrun hDs⟩

/-- **A crossing of a held block has an honest source** (`frame_crossing_source_before` at the
cut's time `d`, with `2 f_d < n`). -/
theorem frame_crossing_source_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourcedAt tr H G y i)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSourceAt tr H D E.root (tr.time i) := by
  have hst := Trace.upTo_state tr y (d := tr.time i) fun _ hk => hrun.time_mono hk.le
  have h := frame_crossing_source_before (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hf hy
    (hsrc.upTo hrun) (W := W) (by rw [hst]; exact hW) hj1 (by rw [hst]; exact hj2)
  rw [hst] at h
  obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ := h
  exact ⟨E, hE, hEW, hEh, hET, D, hD, isHonestSourceAt_of_upTo hrun hDs⟩

end Consensus.Goldilocks.Compose.Growing

end
