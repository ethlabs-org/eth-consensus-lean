module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay

public section

/-! # The run-facts bundles of a Goldilocks run (Option B)

The facts a Goldilocks node run provides to the healing, outage and report proofs, abstracted
over the FG finality update `u` (with `Store.FinalitySpec u`) and the node frame `frameOf`, so the
same proofs read the stock run (`u := Store.updateFinality`, `frameOf := Node.frame`) and the shadow
run (`u := Store.updateFinality'`, `frameOf := Node.frame'`); the two traces are the same type.

* `CutStepWith u frameOf`: the cut law with `Store.onBlockWith u` and `frameOf` (the stock
  `Node.CutStep` at `updateFinality`, `Node.frame`);
* `StaticRunCore`: a run with a fixed honest set (the prefix runs), its cut law, reachability,
  AC projection, trees, and the trace-level group facts its consumers read, stated over the trace,
  not over the node's handler;
* `GoldilocksRunCore`: a run under growing faults, with `upTo`, the static core of every prefix,
  and the growing facts (AC run, coherence, ancestry, finalization, relay and catch).

Each field is a stock lemma's statement (named in its doc); the stock and shadow instances fill
it from the proved lemmas. -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The core of a Goldilocks run under growing faults**: `upTo`, the static core of every
prefix on the validators honest at its end, and the growing facts. -/
structure GoldilocksRunCore
    (u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n))
    (frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (H : Time → Set (Fin sp.n)) (tr : GoldilocksTrace sp ro)
    (ini : Fin sp.n → (goldilocksNode sp ro).State) : Prop where
  finalitySpec : Store.FinalitySpec u
  frameOf_F : ∀ st, (frameOf st).F = st.fg.F
  frameOf_tree : ∀ st B, B ∈ (frameOf st).tree ↔ B ∈ st.fg.tree ∧ st.fg.Anc st.fg.F B
  antitone : Antitone H
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)
  /-- Retention: the prefix through `d` is a static core on the validators honest at `d`
  (`Growing.GoldilocksRun.upTo`). -/
  upTo : ∀ {d}, 0 ≤ d → StaticRunCore u frameOf proposer dg (H d) (tr.upTo d) ini
  /-- The cut law of a node honest at its cut. -/
  cutLaw : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    CutStepWith u frameOf y (tr.time i) (tr.state y i) c (tr.post i)
  /-- `Growing.LocalRun.att_unforgeable`. -/
  att_unforgeable : ∀ y i a, y ∈ H (tr.time i) →
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) →
    a.val ∈ H (tr.time i) → ∃ j < i, tr.SignAt a.val j a
  /-- `Growing.LocalRun.awake_of_call`. -/
  awake_of_call : ∀ y i, y ∈ H (tr.time i) → tr.IsCall y i → tr.awake y (tr.time i)
  /-- `Compose.Growing.goldilocks_ac_projection_from`. -/
  acRun : Compose.NoCollRun dg tr →
    AC.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H) ini
  /-- `Compose.Growing.honest_blocks_coherent`. -/
  coherent : Compose.NoCollRun dg tr → Coherent (tr.HonestBlocksAt H)
  /-- `Compose.Growing.held_anc_at`. -/
  held_anc_at : Compose.NoCollRun dg tr → ∀ {d y i} {A W : AC.Blk sp.n (List (FG.Att sp.n))},
    0 ≤ d → y ∈ H d → (∀ k < i, tr.time k ≤ d) → Anc (tr.HonestBlocksAt H) A W →
    W ∈ (tr.state y i).fg.tree → (tr.state y i).fg.Anc A W
  /-- `Compose.Growing.F_mono_at`. -/
  F_mono_at : ∀ {d y i k}, 0 ≤ d → y ∈ H d → (∀ q < i, tr.time q ≤ d) → k ≤ i →
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F (tr.state y i).fg.F
  /-- `Growing.LocalRun.acRelayAt`. -/
  acRelayAt : ∀ {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp ro)} {σ : Time},
    x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → y ∈ H (tr.time j) →
    tr.projAC.CallAt y j ℓ → Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
    (∀ k, tr.time k = tr.time i → x ∈ H (tr.time k) → tr.AcceptAt x k B →
      tr.IsCall y j → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j σ B) →
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ
  /-- `Growing.LocalRun.acCatchAt`. -/
  acCatchAt : ∀ {g κ : Time}, Healing.Growing.CatchRun tr H g κ →
    ∀ {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp ro)},
    x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → tr.time i < AC.gbar g →
    y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → AC.gbar g + κ ≤ tr.time j →
    Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ

end Consensus.Goldilocks

end
