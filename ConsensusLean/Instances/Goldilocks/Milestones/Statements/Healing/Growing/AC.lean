module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: the AC healing statements (statements)

H.1, its corollary and H.2 (`Statements/Healing/AC`) for a time-indexed honest set `H`
(antitone), over `SA.Growing.ACRun`:

* **`Healthy(g)`** reads every sender at its send, every recipient at the reading call, every
  validator honest at a time from `ḡ` as awake then, and `3 f_t ≤ n − 1` at every `t`;
* **driven traces and trivial frames** constrain the nodes honest at the cut read; a block of the
  slot of a proposer honest at the processing cut is that proposer's proposal;
* **the proposer** of a healed slot `p` is honest through `t_p + hold` (`Regimes.Growing.hold`):
  until the votes of its slot are cast, its key cannot split them with a second proposal;
* the votes and confirmed tips claimed are those of nodes honest at their cuts.

The healing vocabulary that binds no honest set (`gbar`, `Θ`, `HonestProposal`, `SlowLockAt`)
is the static one. At `H := fun _ => H₀` each statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA.Growing

open Regimes.Growing (hold)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **`Healthy(g)` over an AC trace under growing faults.** -/
def HealthyAC (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g : Time) : Prop :=
  (∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmit x i m →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ →
      tr.deadline y j (max (tr.time i) g) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (max (tr.time i) g)) ∧
  (∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i)) ∧
  (∀ y t, gbar g ≤ t → y ∈ H t → tr.awake y t) ∧
  ∀ t, 3 * (H t)ᶜ.ncard ≤ sp.n - 1

/-- **`Catch(κ)` over an AC trace under growing faults.** -/
def CatchAC (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g κ : Time) : Prop :=
  ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → gbar g + κ ≤ tr.time j →
      Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < gbar g + κ

/-- **Trivial frames** at every call of a node honest at its call. -/
def TrivialFrames (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) : Prop :=
  ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ →
    ℓ.frame.F.root = sp.genesisRoot ∧ ℓ.frame.fcRoot = ℓ.frame.F ∧
    ℓ.frame.viableHeads = ℓ.frame.tree ∧
    ℓ.frame.tree = insert ℓ.frame.F {B | ∃ k ≤ i, tr.AcceptAt y k B}

/-- **A driven AC trace under growing faults.** -/
structure Driven (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) : Prop where
  /-- (a) Blocks have their slot's proposer, a slot not in the future, and an earlier parent. -/
  blocks : ∀ y i B, y ∈ H (tr.time i) → tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.time i) ∧
    ∃ Pb : Blk sp.n FGP, B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
      (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt y k Pb)
  /-- (a) A block of the slot of a proposer honest at the processing cut is its proposal. -/
  honest_slot : ∀ y i B, y ∈ H (tr.time i) → tr.AcceptAt y i B → B.root ≠ sp.genesisRoot →
    proposer B.slot ∈ H (tr.time i) → HonestProposal tr (proposer B.slot) B.slot B
  /-- (b) Every node honest and awake at a public time runs its tick there. -/
  tick : ∀ y t, y ∈ H t → 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t
  /-- (b) The joined proposer of slot `s > 0`, honest at `t_s`, runs `ac_proposal` at `t_s`. -/
  proposal : ∀ s : Nat, 0 < s → ∀ p, p ∈ H (sp.ts s) → p = proposer s → tr.awake p (sp.ts s) →
    JoinedAt tr p (sp.ts s) →
    ∃ k ℓ, tr.CallAt p k ℓ ∧ ℓ.call = .proposal ∧ tr.time k = sp.ts s ∧
      ((∃ pay, ProposalAt tr p k ℓ pay) → ∃ P, HonestProposal tr p s P)
  /-- (b) No object received at a public time is processed before the tick there. -/
  tick_first : ∀ y i j ℓ ℓ', y ∈ H (tr.time i) → tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .tick → tr.time i = tr.time j → (∃ m, ℓ.call = .message m) → j < i
  /-- (b) No object received at a slot start is processed before the proposer's
  `ac_proposal` there. -/
  proposal_first : ∀ y i j ℓ ℓ', y ∈ H (tr.time i) → tr.CallAt y i ℓ → tr.CallAt y j ℓ' →
    ℓ'.call = .proposal → tr.time i = tr.time j →
    ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) → j < i

/-- **H.1 under growing faults, AC healing, standalone (trivial frame).** The proposer of slot `p`
is honest through `t_p + hold`. -/
def ACHealingStandalone : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (g : Time),
    ACRun proposer tr H U → Driven proposer tr H → TrivialFrames tr H → HealthyAC tr H U g →
    CatchAC tr H U g (2 * sp.Δ) →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H (sp.ts p + hold sp) →
      HonestProposal tr (proposer p) p P →
      gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p →
      (∀ x j e, x ∈ H (tr.time j) → VoteAt tr x j e → e.msg.slot = p →
        e.msg.head = P.root) ∧
      (∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))

/-- **`Prop(G_p)` under growing faults**: for every `t ≥ ḡ` a slot `p ≥ 1` in `[t, t + G_p]` whose
proposer is honest through `t_p + hold`. -/
def PropAC (proposer : Nat → Fin sp.n) (H : Time → Set (Fin sp.n)) (g Gp : Time) : Prop :=
  ∀ t, gbar g ≤ t → ∃ p : Nat, 1 ≤ p ∧ t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
    proposer p ∈ H (sp.ts p + hold sp)

/-- **H.1, corollary, under growing faults.** -/
def ACHealingStandaloneCorollary : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (g Gp : Time),
    ACRun proposer tr H U → Driven proposer tr H → TrivialFrames tr H → HealthyAC tr H U g →
    CatchAC tr H U g (2 * sp.Δ) → PropAC proposer H g Gp →
    ∀ t, gbar g + 2 * Θ sp + 8 * sp.Δ ≤ t →
      ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
        HonestProposal tr (proposer p) p P ∧
        ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
          (tr.time j = t + Gp + 6 * sp.Δ →
            ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
          Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))

/-- **The protected blocks `𝒫(t₀)` under growing faults.** Writers are honest at their writes; a
protected proposal's proposer is honest through `t_j + hold`, and its slot's votes are those of
nodes honest at their votes. -/
def Protected (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) (t₀ : Time) (B : Blk sp.n FGP)
    (j : Nat) : Prop :=
  (∃ x i CV, x ∈ H (tr.time i) ∧ JoinedAt tr x (tr.time i) ∧ FastLockAt tr x i j B CV ∧
    t₀ + 4 * sp.Δ ≤ sp.ts j) ∨
  (∃ x i, x ∈ H (tr.time i) ∧ JoinedAt tr x (tr.time i) ∧ SlowLockAt tr x i j B ∧
    t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) ∨
  (proposer j ∈ H (sp.ts j + hold sp) ∧ HonestProposal tr (proposer j) j B ∧
    t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts j ∧
    ∀ x k e, x ∈ H (tr.time k) → VoteAt tr x k e → e.msg.slot = j → e.msg.head = B.root)

/-- **The retention premise `Inv(t₀)` under growing faults**, at every call of a node honest at
its call. -/
def Inv (proposer : Nat → Fin sp.n) (tr : SATrace sp FGP ro)
    (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (t₀ : Time) : Prop :=
  ∀ B j, Protected proposer tr H t₀ B j → ∀ y i ℓ, y ∈ H (tr.time i) →
    tr.CallAt y i ℓ → sp.ts (j + 1 : Nat) ≤ tr.time i →
    (Anc U B ℓ.frame.fcRoot ∨ B ∈ ℓ.frame.viableTree ℓ.frame.tree) ∧
    ∀ e ∈ ℓ.emits, B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc U B ℓ.frame.fcRoot

/-- **Proposal geometry `Geo(P)` under growing faults**, at the votes of slot `p` of voters
honest at their votes. -/
def Geo (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) (p : Nat) (P : Blk sp.n FGP) : Prop :=
  ∀ k ℓP, tr.CallAt (proposer p) k ℓP → ℓP.call = .proposal → tr.time k = sp.ts p →
    ∀ y i ℓ e, y ∈ H (tr.time i) → CastAt tr y i ℓ e → e.msg.slot = p →
      P ∈ ℓ.frame.viableHeads ∧
      ∀ X ∈ voterBlockTree sp e.readPoint ℓ.frame p, X ≠ P →
        (X ∈ ℓ.frame.viableHeads ↔ X ∈ ℓP.frame.viableHeads)

/-- **H.2 under growing faults, AC inclusion from the retention premise.** -/
def ACInclusion : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (g t₀ : Time),
    ACRun proposer tr H U → Driven proposer tr H → HealthyAC tr H U g →
    CatchAC tr H U g (2 * sp.Δ) →
    gbar g ≤ t₀ → Inv proposer tr H U t₀ →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H (sp.ts p + hold sp) →
      HonestProposal tr (proposer p) p P →
      t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p →
      (Geo proposer tr H p P →
        ∀ x j e, x ∈ H (tr.time j) → VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      ((∀ x j e, x ∈ H (tr.time j) → VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) →
        ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
          (tr.time j = sp.ts p + 6 * sp.Δ →
            ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
          Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))

/-- **H.1 under growing faults** for all SA parameters. -/
def ACHealingStandaloneAll : Prop := ∀ sp : SAParams, ACHealingStandalone (sp := sp)

/-- **H.1, corollary, under growing faults** for all SA parameters. -/
def ACHealingStandaloneCorollaryAll : Prop :=
  ∀ sp : SAParams, ACHealingStandaloneCorollary (sp := sp)

/-- **H.2 under growing faults** for all SA parameters. -/
def ACInclusionAll : Prop := ∀ sp : SAParams, ACInclusion (sp := sp)

end Consensus.Goldilocks.SA.Growing

end
