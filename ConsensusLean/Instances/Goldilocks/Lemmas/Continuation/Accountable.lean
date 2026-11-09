module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.HeldViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport

public section

/-! # The conviction bridge (continuation)

After the hand-over time the healthy fault bound `f < 2q − n` fails, so the healthy comparisons of
finalized and justified FG state lose their honest crossing validator. The continuation premise
`ConvictedBelow` replaces it: fewer than a third of the validators are convicted by the evidence
of any two honest views. This file carries it to the canonical trace and states the three
comparisons the continuation proof reads.

* `Compose.Growing.ChainConvictedBelow`: the trace-level form. Fewer than `n/3` validators have
  a slashable pair among the attestations on two chains held by two nodes, each honest at a time
  at or after its cuts.
* `Obligations.Growing.chainConvictedBelow_at`: `ConvictedBelow` of the engine run gives it on
  `simTraceAt` with the time-indexed honest keys.
* `Compose.Growing.finalized_compatible_of_convictedBelow`: two finalized caches of readers honest
  at read points are compatible (the `F`/`F` comparison of the continued reads).
* `Growing.GoldilocksRun.finalized_anc_of_lt_conv`: G1.2 at strict height without a fault bound
  (a low `Σ.F` below the reset seed).
* `Compose.Growing.J_eq_of_hj_eq_conv`: equal justified heights agree without a fault bound (a
  low `Σ.J` below the seed).

Each comparison ends in a crossing set of at least `2q − n ≥ n/3` validators with slashable pairs
on the two chains, which `ChainConvictedBelow` excludes. The crossing sets come from
`FGStore/HeldChains`, and the engine views of held attestations from
`Continuation/HeldViews`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Conviction below a third on held chains.** For two nodes `y` (state before cut `i`) and `z`
(before cut `j`), each honest at a time `≥ 0` at or after every cut before its state, and blocks
`X₁`, `X₂` of their trees, fewer than `n/3` validators have a slashable pair among the
attestations on the chains of `X₁` and `X₂`. The trace form of `System.ConvictedBelow` at
`α = 1/3`; consumed by `finalized_compatible_of_convictedBelow`,
`GoldilocksRun.finalized_anc_of_lt_conv`, `J_eq_of_hj_eq_conv`, and by the seeded frame facts
and the continued reads in place of the healthy fault bound. -/
def ChainConvictedBelow (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) : Prop :=
  ∀ (y z : Fin sp.n) (i j : Nat) (t t' : Time), 0 ≤ t → (∀ k < i, tr.time k ≤ t) → y ∈ H t →
    0 ≤ t' → (∀ k < j, tr.time k ≤ t') → z ∈ H t' →
    ∀ X₁ ∈ (tr.state y i).fg.tree, ∀ X₂ ∈ (tr.state z j).fg.tree, ∀ W : Finset (Fin sp.n),
      (∀ v ∈ W, ∃ a ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
        ∃ b ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
          a.val = v ∧ FG.slashable a b) →
      3 * W.card < sp.n

/-- **Finalized caches agree under conviction below a third.** The finalized caches of two
readers, each honest at a time `≥ 0` at or after every cut before its state, are compatible inside
the blocks held while honest. `finalAccountable_readPoint` gives a crossing set of `2q − n ≥ n/3`
validators otherwise. Consumed by the `F`/`F` comparison of the continued reads (the replacement
of the healthy `finalized_safe_read`). -/
theorem finalized_compatible_of_convictedBelow (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hcv : ChainConvictedBelow tr H) {y z : Fin sp.n} {i j : Nat}
    {t t' : Time} (ht : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (ht' : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t') (hz : z ∈ H t') :
    Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j) := by
  by_contra hne
  obtain ⟨X₁, hX₁, X₂, hX₂, W, hW, hw⟩ :=
    Simulation.finalAccountable_readPoint hrun hnc ht hi hy ht' hj hz hne
  have h3 := hcv y z i j t t' ht hi hy ht' hj hz X₁ hX₁ X₂ hX₂ W hw
  have hq : sp.toParams.q = (2 * sp.n + 2) / 3 := rfl
  omega

/-- **Equal justified heights agree under conviction below a third** (HR.2(a) without a fault
bound). For two blocks held by two readers, each honest at a time `≥ 0` at or after every cut
before its state, equal justified heights give equal justified roots: two distinct justified
roots at one height give a crossing set of `2q − n ≥ n/3` validators with conflicting
attestations on the two chains. Consumed by the low-`Σ.J` case of the seeded cache facts (the
active case `h_max = h_j + 1` puts `Σ.J` below the reset seed). -/
theorem J_eq_of_hj_eq_conv (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hcv : ChainConvictedBelow tr H) {y z : Fin sp.n} {i j : Nat} {t t' : Time} (ht : 0 ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) (ht' : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t')
    (hz : z ∈ H t') {B B' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) (hB' : B' ∈ (tr.state z j).fg.tree)
    (he : ((tr.state y i).fg.σ B.root).hj = ((tr.state z j).fg.σ B'.root).hj) :
    ((tr.state y i).fg.σ B.root).J = ((tr.state z j).fg.σ B'.root).J := by
  by_contra hne
  obtain ⟨W, hW, hw⟩ := Store.justified_crossing (fg_reachable_at hrun ht hi hy)
    (fg_reachable_at hrun ht' hj hz) hB hB' he hne
  have h3 := hcv y z i j t t' ht hi hy ht' hj hz B hB B' hB' W fun v hv => by
    obtain ⟨a, ha, b, hb, hav, hab⟩ := hw v hv
    exact ⟨a, Or.inl ha, b, Or.inr hb, hav, hab⟩
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  have hn : sp.toParams.n = sp.n := rfl
  omega

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Growing.GoldilocksRun

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **G1.2 at strict height under conviction below a third.** A block `F` finalized by the state
of a held `X` in the store of a reader honest at `t` is an ancestor, inside the blocks held while
honest, of every block `W` held by a reader honest at `u` whose state height exceeds the
finalized height (each reader honest at a time `≥ 0` at or after every cut before its state). The
crossing set of `finalization_meets_crossing` has `2q − n ≥ n/3` members with slashable pairs on
the chains of `X` and `W`. Consumed by the low-`Σ.F` case of the seeded cache facts (the
replacement of `low_finalized_below_origin_at`) and by the `F`/origin comparison of the continued
reads. -/
theorem finalized_anc_of_lt_conv (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hcv : Compose.Growing.ChainConvictedBelow tr H)
    {y z : Fin sp.n} {k m : Nat} {t u : Time} (ht : 0 ≤ t) (hk : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (hu : 0 ≤ u) (hm : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u)
    {X F W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree)
    (hF : F ∈ (tr.state y k).fg.tree) (hFr : F.root = ((tr.state y k).fg.σ X.root).F)
    (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W := by
  by_contra hn
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub₁ : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h => ⟨y, k, t, ht, hk, hy, h⟩
  have hsub₂ : (tr.state z m).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h => ⟨z, m, u, hu, hm, hz, h⟩
  obtain ⟨S, hS, hw⟩ := Store.finalized_crossing (Compose.Growing.fg_reachable_at hrun ht hk hy)
    (Compose.Growing.fg_reachable_at hrun hu hm hz) hX hFr hW hlt fun Y hY hYW hYF => by
      obtain rfl : Y = F := hU.1 (hsub₂ hY) (hsub₁ hF) hYF
      exact hn (Anc.mono hsub₂ hYW)
  have h3 := hcv y z k m t u ht hk hy hu hm hz X hX W hW S fun v hv => by
    obtain ⟨a, ha, b, hb, hav, hab⟩ := hw v hv
    exact ⟨a, Or.inl ha, b, Or.inr hb, hav, hab⟩
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  have hn' : sp.toParams.n = sp.n := rfl
  omega

end Consensus.Goldilocks.Growing.GoldilocksRun

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup) (A : ContractAssumptions S)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The engine premise gives the trace form.** `ConvictedBelow` of the run (at `α = 1/3`) gives
`ChainConvictedBelow` on the canonical trace with the time-indexed honest keys. A trace state
before cut `i` of a node honest at `t ≥ 0`, after every cut before `i`, maps to the engine cut `q`
after the event of its last labelled cut before `i`: its owner is honest at `cutTime q ≤ t`, and
every attestation on a chain of its tree is in its engine view `ViewIdx v q` (its blocks are
genesis or accepted before `cutMap q`, `accepted_in_view_at`). `convicted_count` then bounds the
crossing set by the convictions of the two views. Consumed by the continuation endpoint, which
supplies `ChainConvictedBelow` to the seeded invariant and the continued reads. -/
theorem chainConvictedBelow_at (hv : rho.ExecutionValid)
    (hcb : (Sys (goldilocks S) V).ConvictedBelow (K S A) ⟨E, rho⟩) :
    Compose.Growing.ChainConvictedBelow (simTraceAt S rho hn) (honestKeysAt S rho) := by
  classical
  intro y z i j t t' ht hi hy ht' hj hz X₁ hX₁ X₂ hX₂ W hW
  obtain ⟨q₁, hq₁, hh₁, hv₁⟩ := held_atts_in_view_at S rho hn hv ht hi hy
  obtain ⟨q₂, hq₂, hh₂, hv₂⟩ := held_atts_in_view_at S rho hn hv ht' hj hz
  set Vw := rho.ViewIdx (rho.key y) q₁ ∪ rho.ViewIdx (rho.key z) q₂
  have hcount := convicted_count S rho (A := Vw) W fun k hk => by
    obtain ⟨a, ha, b, hb, hak, hab⟩ := hW k hk
    have hmem : ∀ c ∈ Regimes.ChainAtts (simTraceAt S rho hn) y i X₁ ∪
        Regimes.ChainAtts (simTraceAt S rho hn) z j X₂, attObj c ∈ Vw := by
      rintro c (⟨B, hB, -, hc⟩ | ⟨B, hB, -, hc⟩)
      · exact Or.inl (hv₁ B hB c hc)
      · exact Or.inr (hv₂ B hB c hc)
    exact ⟨a, b, hmem a ha, hmem b hb, hak, hab⟩
  have hc := hcb (rho.key y) (rho.key z) q₁ q₂ hq₁ hq₂ hh₁ hh₂
  have hsub : convicted rho.Slashable Vw ⊆ convicted ((Sys (goldilocks S) V).convicts ⟨E, rho⟩)
      ((Sys (goldilocks S) V).view ⟨E, rho⟩ (rho.key y) q₁ ∪
        (Sys (goldilocks S) V).view ⟨E, rho⟩ (rho.key z) q₂) := by
    intro x hx
    simp only [convicted, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨o, ho, o', ho', h⟩ := hx
    refine ⟨o, ?_, o', ?_, h⟩
    · rcases ho with ho | ho
      · exact Or.inl ⟨o, ho, rfl⟩
      · exact Or.inr ⟨o, ho, rfl⟩
    · rcases ho' with ho' | ho'
      · exact Or.inl ⟨o', ho', rfl⟩
      · exact Or.inr ⟨o', ho', rfl⟩
  have hle := (hcount.trans (Finset.card_le_card hsub))
  have hα : (K S A).params.α = 1 / 3 := rfl
  rw [hα] at hc
  have hq : ((W.card : Nat) : ℚ) < 1 / 3 * Fintype.card V :=
    lt_of_le_of_lt (by exact_mod_cast hle) hc
  have : (3 * W.card : ℚ) < Fintype.card V := by linarith
  exact_mod_cast this

end Consensus.Goldilocks.Obligations.Growing

end
