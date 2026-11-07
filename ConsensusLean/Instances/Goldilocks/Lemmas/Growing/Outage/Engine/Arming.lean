module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query

public section

/-! # Outage engine part under growing faults: an armed ready source

`OutageArmingAt Q v`: the read tip `P` of a source `v` ready at `T`, at the end-of-`T` cut, a held
origin `C ⪰ P` within `T` of a label `σ` more than `k` labels before the cover label `j₀`,
S-vote (every vote of a slot in `(σ, j₀]` by a node honest at its cast extends `C`), and O1 at the
labels `j₀ − 1` and `j₀` for the cohort `holdersAt` (O1 at `j₀` given (F), (VA) outside root
cover and (N), with (N) over the votes of the cohort cast while honest). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **An armed ready source** of an outage query under growing faults. -/
structure OutageArmingAt (Q : OutageQueryAt S A V) (v : V) where
  /-- `P`: the confirmed read's tip at the end-of-`T` cut. -/
  tip : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  origin : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  σ : Nat
  read : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
    chainTo (Q.trace.state (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
      (tip.slot + 1) tip
  /-- `tip` is the `readAfter` read tip of `v` at the end-of-`T` cut, at clock `T`. -/
  tip_eq : tip = Regimes.readAfter Q.trace (Q.run.2.ownKey v)
    (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T
  /-- The tip and the origin are held while honest, the tip below the origin. -/
  tip_held : tip ∈ Q.trace.HonestBlocksAt Q.keys
  origin_held : origin ∈ Q.trace.HonestBlocksAt Q.keys
  tip_anc : Anc (Q.trace.HonestBlocksAt Q.keys) tip origin
  /-- Genesis tip (`origin := tip`), or an origin within `T`. -/
  armed : (tip.root = Q.params.genesisRoot ∧ origin = tip) ∨
    (Compose.Growing.OriginWithin Q.trace Q.keys origin σ Q.T ∧
      σ + Q.params.k < Compose.coverLabel Q.params Q.start)
  /-- S-vote. -/
  votes : ∀ x i e, Compose.Growing.HVoteAt Q.trace Q.keys x i e → σ < e.msg.slot →
    e.msg.slot ≤ Compose.coverLabel Q.params Q.start →
    SA.VoteExtends (Q.trace.HonestBlocksAt Q.keys) e.msg origin
  /-- O1 at `j₀ − 1`. -/
  lockPrev : ∀ w ∈ Q.holdersAt, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 2 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start - 1) ℓ ∧
      (Anc (Q.trace.HonestBlocksAt Q.keys) origin (Q.trace.state w c).fg.F ∨
       ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc origin L ∧
         (⟨L.root, Compose.coverLabel Q.params Q.start - 1, f,
           Compose.coverLabel Q.params Q.start - 1 + Q.params.k⟩ : SA.Lock) ∈
           (Q.trace.state w (c + 1)).ac.locks)
  /-- O1 at `j₀`, given (F), (VA) outside root cover and (N) at the first `j₀` update. -/
  lockCover : ∀ w ∈ Q.holdersAt, origin.root ≠ Q.params.genesisRoot →
    Q.params.ts (Compose.coverLabel Q.params Q.start) + 6 * Q.params.Δ ≤ Q.run.2.horizon →
    ∃ c ℓ, SA.UpdateAt Q.trace.projAC w c (Compose.coverLabel Q.params Q.start) ℓ ∧
      (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt Q.trace.projAC w k (Compose.coverLabel Q.params Q.start) ℓ') ∧
      (Compatible (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state w c).fg.F origin →
       (Anc (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state w c).fg.F origin →
         ℓ.frame.AncestorCandidate origin) →
       (∀ x ∈ Q.holdersAt, ∀ j e, Compose.Growing.HVoteAt Q.trace Q.keys x j e →
          e.msg.slot = Compose.coverLabel Q.params Q.start + 1 → j < c →
          SA.VoteExtends (Q.trace.HonestBlocksAt Q.keys) e.msg origin) →
       Anc (Q.trace.HonestBlocksAt Q.keys) origin (Q.trace.state w c).fg.F ∨
       (∃ L f, ℓ.frame.Anc origin L ∧
          (⟨L.root, Compose.coverLabel Q.params Q.start, f,
            Compose.coverLabel Q.params Q.start + Q.params.k⟩ : SA.Lock) ∈
            (Q.trace.state w (c + 1)).ac.locks))

end Consensus.Goldilocks.Obligations.Growing

end
