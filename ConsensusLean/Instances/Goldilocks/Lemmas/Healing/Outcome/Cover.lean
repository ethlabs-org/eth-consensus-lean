module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.FrameKeepsCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Healing: the run-level cover of a bracketed block (N6)

consensus-lean#135, plan N6 (workbench `notes/fg-liveness/r14-end-to-end/n6-cover.md`). Fix a
block `B₀` with the bracket `Br(B₀)`: `B₀` is high (`σ[B₀].h ≥ H_z + 1` at a holder) and below
the block `O₀` of a high origin. At every cut `j` of an honest `x` that holds `B₀` above its
finalized block (`B₀ ∈ toFrame.tree`, the CONDITIONAL input `C(x, j)`):

* P1' (`fcRoot_comparable_of_bracket`): `fcRoot ⪯ B₀ ∨ B₀ ⪯ fcRoot`;
* P2 (`floor_cover_of_bracket`): a held `Y ⪰ B₀` reaches the head height floor;
* `frameKeeps_or_root_of_bracket`: `FrameKeeps x j B₀ ∨ B₀ ⪯ fcRoot`, hence
  `viableAncestor B₀ = B₀`.

No time bound and no delivery premise. The proof uses (R1) comparability of high origins, the
entry–origin lemma and `no_high_contest`. `ResetPremisesUpTo` forms need `j`'s prefix and the
write of `O₀` within the horizon. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### Store-level cores -/

/-- The P1' case split, from a comparability supplier for high left entries. -/
private theorem fcRoot_comparable_core (hrun : GoldilocksRun proposer dg H tr)
    (hU : Coherent (tr.HonestBlocks H)) {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state x j).fg.σ B₀.root).h)
    (hcmp : ∀ E C, E ∈ (tr.state x j).fg.tree → ((tr.state x j).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state x j).fg.σ E.root).h → (tr.state x j).fg.Anc E C →
      ((tr.state x j).fg.σ E.root).h < ((tr.state x j).fg.σ C.root).h →
      (tr.state x j).fg.Anc E B₀ ∨ (tr.state x j).fg.Anc B₀ E) :
    (tr.state x j).fg.Anc (tr.state x j).fg.fcRoot B₀ ∨
      (tr.state x j).fg.Anc B₀ (tr.state x j).fg.fcRoot := by
  have hr := Compose.fg_reachable hrun.toLocalRun hx j
  have hsub : (tr.state x j).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨x, hx, j, hX⟩
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, hmax, _⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBj
  obtain rfl : E = (tr.state x j).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBjJ)
  unfold Store.fcRoot
  split_ifs with hchoose
  · rcases hcase with hg | ⟨hJh, hJT⟩
    · exact Or.inl (hg ▸ (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hB.1)
    by_cases hh : HZ tr H g + 1 ≤ (tr.state x j).fg.hj
    · exact hcmp _ Bj hJm hJT (by omega) hEB (by have := Store.hj_lt_h hr hBj; omega)
    · have hBm := hmax B₀ hB.1
      left
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, B₀, hB.1, hB.2, by omega, hn⟩
  · exact Or.inl hB.2

/-- The P2 case split, from no high contest and a comparability supplier. -/
private theorem floor_cover_core (hrun : GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state x j).fg.σ B₀.root).h)
    (hnc : ¬ ((tr.state x j).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state x j).fg.hmax))
    (hcmp : ∀ E C, E ∈ (tr.state x j).fg.tree → ((tr.state x j).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state x j).fg.σ E.root).h → (tr.state x j).fg.Anc E C →
      ((tr.state x j).fg.σ E.root).h < ((tr.state x j).fg.σ C.root).h →
      (tr.state x j).fg.Anc E B₀ ∨ (tr.state x j).fg.Anc B₀ E) :
    ∃ Y ∈ (tr.state x j).fg.tree, (tr.state x j).fg.Anc B₀ Y ∧
      (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ Y.root).h := by
  have hr := Compose.fg_reachable hrun.toLocalRun hx j
  by_cases hle : (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ B₀.root).h
  · exact ⟨B₀, hB, .refl, hle⟩
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state x j).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state x j).fg.headHeightFloor = (tr.state x j).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hr hC (h := (tr.state x j).fg.hmax - 1) (by omega) (by omega)
  rcases hcmp E C hE hET (by omega) hEC (by omega) with h | h
  · have := σ_h_le_of_anc hr h
    omega
  · exact ⟨C, hC, h.trans hEC, by rw [hfl]; omega⟩

/-! ### Whole-run forms -/

/-- **Br(ii) ⇒ comparability (N6 item 1).** If `B₀ ⪯ O₀` for a high origin `O₀`, every block
below a high origin is compatible with `B₀` ((R1) and `Anc.total`). -/
theorem bracket_compatible (hp : ResetPremises tr H proposer dg g ΔF a)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀ : Anc (tr.HonestBlocks H) B₀ O₀)
    {v : Fin sp.n} {r l : Nat} {O X : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O)
    (hXO : Anc (tr.HonestBlocks H) X O) : Compatible (tr.HonestBlocks H) X B₀ := by
  have hU := honest_coherent hp
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  rcases hret.comparable v r l O v₀ r₀ l₀ O₀ ho ho₀ with h | h
  · exact Anc.total hU (hXO.trans h) hB₀
  · exact Anc.total hU hXO (hB₀.trans h)

/-- High left entries of an honest store are comparable with a bracketed held block. -/
private theorem entry_cmp_of_bracket (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.tree)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    ∀ E C, E ∈ (tr.state x j).fg.tree → ((tr.state x j).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state x j).fg.σ E.root).h → (tr.state x j).fg.Anc E C →
      ((tr.state x j).fg.σ E.root).h < ((tr.state x j).fg.σ C.root).h →
      (tr.state x j).fg.Anc E B₀ ∨ (tr.state x j).fg.Anc B₀ E := by
  intro E C hE hET hEh hEC hlt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, O, ho, hEO⟩ :=
    left_entry_origin hp hx hE hET hEh hEC hlt
  rcases bracket_compatible hp ho₀ hB₀O ho hEO with h | h
  · exact Or.inl (anc_tree_of_anc hp hx h hB)
  · exact Or.inr (anc_tree_of_anc hp hx h hE)

/-- **P1' (N6 item 2).** Under the reset, a block `B₀` held above `F` at `(x, j)`, high at a
holder and below a high origin, is comparable with the fork-choice root of `x` at `j`. -/
theorem fcRoot_comparable_of_bracket (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    (tr.state x j).fg.Anc (tr.state x j).fg.fcRoot B₀ ∨
      (tr.state x j).fg.Anc B₀ (tr.state x j).fg.fcRoot :=
  fcRoot_comparable_core hp.run (honest_coherent hp) hx hB
    (by rw [σ_eq_run hp hx hz hB.1 hBz]; exact hBh)
    (entry_cmp_of_bracket hp hx hB.1 ho₀ hB₀O)

/-- **P2 (N6 item 3).** Under the reset, a block `B₀` held at `(x, j)`, high at a holder and
below a high origin, has a held descendant at or above the head height floor of `x` at `j`. -/
theorem floor_cover_of_bracket (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    ∃ Y ∈ (tr.state x j).fg.tree, (tr.state x j).fg.Anc B₀ Y ∧
      (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ Y.root).h :=
  floor_cover_core hp.run hx hB (by rw [σ_eq_run hp hx hz hB hBz]; exact hBh)
    (no_high_contest hp hx j) (entry_cmp_of_bracket hp hx hB ho₀ hB₀O)

/-- From P1' and P2: `FrameKeeps`, or the R0 case `B₀ ⪯ fcRoot` in the frame. -/
private theorem keeps_or_root_of_cover (hrun : GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    (h1 : (tr.state x j).fg.Anc (tr.state x j).fg.fcRoot B₀ ∨
      (tr.state x j).fg.Anc B₀ (tr.state x j).fg.fcRoot)
    (h2 : ∃ Y ∈ (tr.state x j).fg.tree, (tr.state x j).fg.Anc B₀ Y ∧
      (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ Y.root).h) :
    Compose.FrameKeeps tr x j B₀ ∨
      (tr.state x j).fg.toFrame.Anc B₀ (tr.state x j).fg.toFrame.fcRoot := by
  rcases h1 with h | h
  · obtain ⟨Y, hY, hBY, hh⟩ := h2
    exact Or.inl (Compose.frameKeeps_of_cover hrun hx j hB hY h hBY hh)
  · right
    change Goldilocks.Anc {X | X ∈ (tr.state x j).fg.tree ∧
      (tr.state x j).fg.Anc (tr.state x j).fg.F X} B₀ (tr.state x j).fg.fcRoot
    exact Anc.restrict hB.2 h

/-- **The cover (N6 item 4).** Under the reset, a bracketed `B₀` held above `F` at `(x, j)`
satisfies `FrameKeeps x j B₀` or the R0 case `B₀ ⪯ fcRoot`. -/
theorem frameKeeps_or_root_of_bracket (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    Compose.FrameKeeps tr x j B₀ ∨
      (tr.state x j).fg.toFrame.Anc B₀ (tr.state x j).fg.toFrame.fcRoot :=
  keeps_or_root_of_cover hp.run hx j hB
    (fcRoot_comparable_of_bracket hp hx j hB hz hBz hBh ho₀ hB₀O)
    (floor_cover_of_bracket hp hx j hB.1 hz hBz hBh ho₀ hB₀O)

/-- A bracketed `B₀` held above `F` is its own viable ancestor at every honest cut. -/
theorem viableAncestor_eq_self_of_bracket (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    (tr.state x j).fg.toFrame.viableAncestor B₀ = B₀ :=
  Compose.viableAncestor_eq_self_of_keeps_or_root hp.run hx j hB
    (frameKeeps_or_root_of_bracket hp hx j hB hz hBz hBh ho₀ hB₀O)

/-! ### Bounded forms (N6 item 5) -/

/-- Bounded `bracket_compatible`: both origin writes within the horizon. -/
theorem ResetPremisesUpTo.bracket_compatible {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀ : Anc (tr.HonestBlocks H) B₀ O₀)
    {v : Fin sp.n} {r l : Nat} {O X : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O)
    (hrb : tr.time r ≤ b) (hXO : Anc (tr.HonestBlocks H) X O) :
    Compatible (tr.HonestBlocks H) X B₀ := by
  have hU := hp.honest_coherent
  rcases hp.origins_compatible ho hrb ho₀ hr₀b with h | h
  · exact Anc.total hU (hXO.trans h) hB₀
  · exact Anc.total hU hXO (hB₀.trans h)

private theorem ResetPremisesUpTo.entry_cmp_of_bracket {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} (hib : ∀ q < j, tr.time q ≤ b)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state x j).fg.tree)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    ∀ E C, E ∈ (tr.state x j).fg.tree → ((tr.state x j).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state x j).fg.σ E.root).h → (tr.state x j).fg.Anc E C →
      ((tr.state x j).fg.σ E.root).h < ((tr.state x j).fg.σ C.root).h →
      (tr.state x j).fg.Anc E B₀ ∨ (tr.state x j).fg.Anc B₀ E := by
  intro E C hE hET hEh hEC hlt
  obtain ⟨_, _, _, _, _, _, d, hd, _, _, r, hr, _, O, ho, hEO⟩ :=
    hp.left_entry_origin hx hE hET hEh hEC hlt
  rcases hp.bracket_compatible ho₀ hr₀b hB₀O ho (hib r (by omega)) hEO with h | h
  · exact Or.inl (hp.anc_tree_of_anc hx h hB)
  · exact Or.inr (hp.anc_tree_of_anc hx h hE)

/-- Bounded P1': the prefix of `j` and the write of `O₀` within the horizon. -/
theorem ResetPremisesUpTo.fcRoot_comparable_of_bracket {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) (hib : ∀ q < j, tr.time q ≤ b)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    (tr.state x j).fg.Anc (tr.state x j).fg.fcRoot B₀ ∨
      (tr.state x j).fg.Anc B₀ (tr.state x j).fg.fcRoot :=
  fcRoot_comparable_core hp.run hp.honest_coherent hx hB
    (by rw [hp.σ_eq_run hx hz hB.1 hBz]; exact hBh)
    (hp.entry_cmp_of_bracket hx hib hB.1 ho₀ hr₀b hB₀O)

/-- Bounded P2: the prefix of `j` and the write of `O₀` within the horizon. -/
theorem ResetPremisesUpTo.floor_cover_of_bracket {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) (hib : ∀ q < j, tr.time q ≤ b)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    ∃ Y ∈ (tr.state x j).fg.tree, (tr.state x j).fg.Anc B₀ Y ∧
      (tr.state x j).fg.headHeightFloor ≤ ((tr.state x j).fg.σ Y.root).h :=
  floor_cover_core hp.run hx hB (by rw [hp.σ_eq_run hx hz hB hBz]; exact hBh)
    (hp.no_high_contest hx j hib) (hp.entry_cmp_of_bracket hx hib hB ho₀ hr₀b hB₀O)

/-- Bounded cover: `FrameKeeps x j B₀` or `B₀ ⪯ fcRoot`. -/
theorem ResetPremisesUpTo.frameKeeps_or_root_of_bracket {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) (hib : ∀ q < j, tr.time q ≤ b)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    Compose.FrameKeeps tr x j B₀ ∨
      (tr.state x j).fg.toFrame.Anc B₀ (tr.state x j).fg.toFrame.fcRoot :=
  keeps_or_root_of_cover hp.run hx j hB
    (hp.fcRoot_comparable_of_bracket hx j hib hB hz hBz hBh ho₀ hr₀b hB₀O)
    (hp.floor_cover_of_bracket hx j hib hB.1 hz hBz hBh ho₀ hr₀b hB₀O)

/-- Bounded: a bracketed `B₀` held above `F` is its own viable ancestor. -/
theorem ResetPremisesUpTo.viableAncestor_eq_self_of_bracket {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) (j : Nat) (hib : ∀ q < j, tr.time q ≤ b)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B₀ ∈ (tr.state x j).fg.toFrame.tree)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z m).fg.tree)
    (hBh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : HighOrigin tr H g v₀ r₀ l₀ O₀) (hr₀b : tr.time r₀ ≤ b)
    (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀) :
    (tr.state x j).fg.toFrame.viableAncestor B₀ = B₀ :=
  Compose.viableAncestor_eq_self_of_keeps_or_root hp.run hx j hB
    (hp.frameKeeps_or_root_of_bracket hx j hib hB hz hBz hBh ho₀ hr₀b hB₀O)

end Consensus.Goldilocks.Healing

end
