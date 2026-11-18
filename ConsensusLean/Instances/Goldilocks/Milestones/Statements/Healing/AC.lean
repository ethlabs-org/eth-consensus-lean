module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events

@[expose] public section

/-! # Goldilocks milestone Healing: the AC healing vocabulary (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex` §"Healing: top-level statements":
the healing vocabulary read on an AC trace of the Goldilocks SA. `ḡ = max(g, 0)`, the lock
lifetime bound `Θ = 4(k + 1)Δ`, `Healthy(g)` (`GST(g)`, every honest validator awake from `ḡ`,
`3f ≤ n − 1`), `Catch(κ)` (accepted-old-block catch-up), **trivial frames**, **driven** AC traces,
the proposer premise `Prop(G_p)`, slow locks (`SlowLockAt`), the protected blocks (`Protected`),
the retention premise `Inv` and the proposal geometry `Geo`. The run-level healing nodes
are in `Statements/Healing/Run`.

A trivial frame is not a frame of a reachable Goldilocks run: the frame of every call of an
honest `y` is the tree of the blocks `y` has accepted, rooted at genesis, with
`F = fc_root = genesis` and every block a viable head.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- `ḡ = max(g, 0)`. -/
def gbar (g : Time) : Time := max g 0

/-- `Θ = 4(k + 1)Δ`, the time from a lock write to its expiry (claims §"Healing: top-level
statements", "Healing notation"). -/
def Θ : Time := 4 * ((sp.k : Time) + 1) * sp.Δ

variable {sp} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **`Healthy(g)` over an AC trace**: `GST(g)` for AC messages and blocks (every AC message an
honest node sends or admits, also before `g`, is processed by every honest `y` by
`max(τ, g, w_y) + Δ`, at or after `τ`; acceptance relay with the same deadline), every honest
validator awake from `ḡ` on, and `3f ≤ n − 1`. -/
def HealthyAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (g : Time) :
    Prop :=
  (∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (max (tr.time i) g) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (max (tr.time i) g)) ∧
  (∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)) ∧
  (∀ y ∈ H, ∀ t, gbar g ≤ t → tr.awake y t) ∧
  3 * Hᶜ.ncard ≤ sp.n - 1

/-- **`Catch(κ)` over an AC trace** (accepted-old-block catch-up): every block an honest node
accepts before `ḡ` is accepted before `ḡ + κ` by every honest `y` whose `Φ.F` it extends, read
at every call of `y` at or after `ḡ + κ`. -/
def CatchAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g κ : Time) : Prop :=
  ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → gbar g + κ ≤ tr.time j → Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < gbar g + κ

/-- `p`'s proposal of slot `s` is the block `P` it makes at `t_s` from `ac_proposal` (claims
§"Healing: top-level statements", "honest proposal"): its `ac_proposal` at cut `k` at `t_s`
returns the duty head `d` and the payload `pay`, and `P` has parent `d.head`, slot `s`, proposer
`p` and payload `pay`; `p` passes it to its own `ac_on_block` at a later cut at the same time.
(The parent is part of "the block made from `ac_proposal`": without it a block of the right slot
and payload on another parent would count.) -/
def HonestProposal (tr : SATrace sp FGP ro) (p : Fin sp.n) (s : Nat) (P : Blk sp.n FGP) : Prop :=
  ∃ k ℓ d pay, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧
    (acProposal sp (tr.state p k) ℓ.frame (tr.time k)).2 = some (d, pay) ∧
    tr.time k = sp.ts s ∧ P.parent = some d.head.root ∧ P.slot = s ∧ P.proposer = p ∧
    P.acPayload = pay ∧ ∃ j, k < j ∧ tr.AcceptAt p j P ∧ tr.time j = sp.ts s

/-- **A driven AC trace** (claims §"Healing: top-level statements"), besides the AC wire checks:
(a) every block other than genesis that an honest `y` passes to `ac_on_block` at time `t` has its
slot's proposer, a slot at most `slot(t)`, and a parent of smaller slot that is genesis or was
passed to `y`'s `ac_on_block` earlier; a block of an honest proposer's slot is that proposer's
proposal; (b) the AC part of the tick order (C0.4): every honest node awake at a public time `t`
runs its tick there; the honest proposer of a slot `s > 0` awake and joined at `t_s` runs
`ac_proposal` after its tick and, when it returns a payload, passes its block (on the returned
head) to its own
`ac_on_block` at once, before any object received at `t_s`. -/
structure Driven (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop where
  /-- (a) Blocks have their slot's proposer, a slot not in the future, and an earlier parent. -/
  blocks : ∀ y ∈ H, ∀ i B, tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.time i) ∧
    ∃ Pb : Blk sp.n FGP, B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
      (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt y k Pb)
  /-- (a) A block of an honest proposer's slot is that proposer's proposal. -/
  honest_slot : ∀ y ∈ H, ∀ i B, tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    proposer B.slot ∈ H → HonestProposal tr (proposer B.slot) B.slot B
  /-- (b) Every honest node awake at a public time runs its tick there. -/
  tick : ∀ y ∈ H, ∀ t, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t
  /-- (b) The honest joined proposer of slot `s > 0` runs `ac_proposal` at `t_s`, after its
  tick; when it returns a payload, it passes its block to its own `ac_on_block` at once. -/
  proposal : ∀ s, 0 < s → ∀ p ∈ H, p = proposer s → tr.awake p (sp.ts s) →
    JoinedAt tr p (sp.ts s) →
    ∃ k ℓ, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧ tr.time k = sp.ts s ∧
      ((∃ pay, ProposalAt tr p k ℓ pay) → ∃ P, HonestProposal tr p s P)
  /-- (b) No object received at a public time is processed before the tick there. -/
  tick_first : ∀ y ∈ H, ∀ i j ℓ ℓ', tr.CallAt y i ℓ → tr.CallAt y j ℓ' → ℓ'.call = .tick →
    tr.time i = tr.time j → (∃ m, ℓ.call = .message m) → j < i
  /-- (b) No object received at a slot start is processed by its honest proposer before its
  `ac_proposal` there: every AC message or block call of the node at the time of its `ac_proposal`
  comes after it (the own block, passed at once, included). -/
  proposal_first : ∀ y ∈ H, ∀ i j ℓ ℓ', tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .proposal → tr.time i = tr.time j →
    ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) → j < i

/-- **A slow lock** of slot `s` on `B`, written at cut `i` of `x`: the update of slot `s` (at
`t_s + 6Δ`, joined) returns `C` (vetoed or not), and `B` is the deepest block of `C`'s path that
conflicts with no live lock and has the `k − 1` previous saved results as descendants, written
as a lock that is not fast. -/
def SlowLockAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) : Prop :=
  ∃ ℓ C, UpdateAt tr x i s ℓ ∧ getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
    deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
      ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
      ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved j = some S.root ∧ ℓ.frame.Anc X S} =
      some B

/-- **The protected blocks `𝒫(t₀)`** (claims §"Healing: top-level statements", "Protected
blocks"): the pairs `(B, j)` such that, at an honest node joined at the write, (P1) `B` is the
block selected by a write of a fast lock of slot `j ≥ r_AC(t₀)` (the fast test or an optimistic
confirmation), before its move back; or (P2) `B` is the block of a write of a lock that is not
fast, of slot `j` with `j − k + 1 ≥ r_AC(t₀)`; or (P3) `B` is an honest proposal of a slot
`j ≥ s_AC(t₀)` and every honest vote of slot `j` is `B`. A slot `j` is `≥ r_AC(t₀)` (the least
slot with `t_r ≥ t₀ + 4Δ`) exactly when `t_j ≥ t₀ + 4Δ`, and `≥ s_AC(t₀)` (the least slot with
`t_s ≥ t₀ + 2Θ + 8Δ`) exactly when `t_j ≥ t₀ + 2Θ + 8Δ`. -/
def Protected (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (t₀ : Time) (B : Blk sp.n FGP)
    (j : Nat) : Prop :=
  (∃ x ∈ H, ∃ i CV, JoinedAt tr x (tr.time i) ∧ FastLockAt tr x i j B CV ∧
    t₀ + 4 * sp.Δ ≤ sp.ts j) ∨
  (∃ x ∈ H, ∃ i, JoinedAt tr x (tr.time i) ∧ SlowLockAt tr x i j B ∧
    t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) ∨
  (proposer j ∈ H ∧ HonestProposal tr (proposer j) j B ∧
    t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts j ∧
    ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = j → e.msg.head = B.root)

/-- **The raw-target retention premise `Inv(t₀)`**: for every `(B, j) ∈ 𝒫(t₀)` and every call of
an honest node at a time `≥ t_{j+1}`, with frame `Φ`, `B ⪯ Φ.fc_root` or `B` is in the viable
tree of `Φ.tree` (`filtered(Φ, Φ.tree)`); at a vote, moreover, `B ⪯ Φ.fc_root` or `B` is in the
viable tree of the voter block tree. `B ⪯ Φ.fc_root` is the block order inside `U` (the coherent
set of frame blocks), not ancestry inside `Φ.tree`: once `Φ.F` passes `B`, `B` is no longer in the
tree. -/
def Inv (proposer : Nat → Fin sp.n) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (t₀ : Time) : Prop :=
  ∀ B j, Protected proposer tr H t₀ B j → ∀ y ∈ H, ∀ i ℓ,
    tr.CallAt y i ℓ → sp.ts (j + 1 : Nat) ≤ tr.time i →
    (Anc U B ℓ.frame.fcRoot ∨ B ∈ ℓ.frame.viableTree ℓ.frame.tree) ∧
    ∀ e ∈ ℓ.emits, B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc U B ℓ.frame.fcRoot

/-- **Proposal geometry `Geo(P)`** for the proposal `P` of slot `p`: at every `ac_proposal` call
of the proposer at `t_p` (frame `Φ_P`) and every vote of slot `p` of an honest voter `y` (frame
`Φ_y`), `P` is a viable head of `Φ_y` (`Φ_y.allowed`), and every other block of `y`'s voter block
tree is a viable head of `Φ_y` exactly when it is one of `Φ_P`. -/
def Geo (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (p : Nat) (P : Blk sp.n FGP) : Prop :=
  ∀ k ℓP, tr.CallAt (proposer p) k ℓP → ℓP.call = .proposal → tr.time k = sp.ts p →
    ∀ y ∈ H, ∀ i ℓ e, CastAt tr y i ℓ e → e.msg.slot = p →
      P ∈ ℓ.frame.viableHeads ∧
      ∀ X ∈ voterBlockTree sp e.readPoint ℓ.frame p, X ≠ P →
        (X ∈ ℓ.frame.viableHeads ↔ X ∈ ℓP.frame.viableHeads)

end Consensus.Goldilocks.SA

end
