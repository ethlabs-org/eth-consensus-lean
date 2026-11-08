module
public import ConsensusLean.Comparison.Heal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.ACU

@[expose] public section

/-! # Slice 0 at Tier A: the AC heal profile and the signing rate (statements)

Tier A restates the Slice 0 heal profile over AC traces of the Goldilocks SA, in the vocabulary of
tight H.1 (`ACHealingStandaloneTight`) **with the unlock given** by an oracle `u`
(`StandaloneRunU`, `HonestProposalU`): every lawful unlock stage runs the parent's handlers with
its locks after the unlock related to the parent's (`ACLocalRunU m u`), so a statement for every `u`
covers every lawful stage. Its heal claim is a **proposal-inclusion heal** (unanimity of slot `p`,
and `P` in every honest confirmed tip from `t_p + 6Δ`), not ready-reader safety.

* `IncidentAC0 m u q b₀ g`: H.1's run premises at write mode `m` with the unlock `u`
  (`StandaloneRunU`: the AC trace contract, `DrivenU`, trivial frames, `Healthy(g)`, `Catch(2Δ)`), a
  constant honest set `H` every member of which is awake from `0`, at most `q.fcap` validators
  outside `H`, `Sync` for sends on `[0, b₀)`, `b₀ ≤ g` with `g − b₀ ≤ q.L·Δ`, and for `split G`
  in-group `Sync` for sends on `[b₀, g)`. At Tier A `q.fcap` caps `|Hᶜ|` (the faulty and the honest
  validators not awake from `0`); with full participation that is the fault count.
* `HealProfileAC0 d`: monotone `d`, and for every honest proposal `P` of slot `p` with
  `t_p ≥ ḡ + d(q)·Δ`, every honest vote of slot `p` is `P`, and `P ⪯ ac_confirmed` at every call of
  an honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself, from its tick there on).
* `HealProfileAC0Free`: the free static instance `d ≡ 8k + 4` at `2·fcap < n` (`⊤` elsewhere),
  for every unlock oracle, from tight H.1 for every lawful stage.
* `SigningRateAC0`: on every AC trace with the unlock given (`ACLocalRunU`), every honest node
  emits at most one vote per slot.

All static (constant `H`). -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **In-group `Sync[a, b]`** over an AC trace (`SyncAC` restricted to one group of `G`): every AC
message an honest `x` sends or admits at `τ ∈ [a, b]` is processed by every honest `y` of `x`'s
group before its deadline, and every block an honest `x` accepts at `τ ∈ [a, b]` is accepted by
every honest `y` of `x`'s group whose finalized tip it extends (inside `U`) before its deadline;
both read at every call of `y` at or after the deadline. -/
def GroupSyncAC (G : Fin sp.n → Bool) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (a b : Time)
    (tr : SATrace sp FGP ro) : Prop :=
  (∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y ∈ H, G y = G x → ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (tr.time i)) ∧
  (∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y ∈ H, G y = G x → ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i))

/-- The class's delivery guarantee during the incident `[b₀, g)` at Tier A: none for `any`,
in-group `Sync` for sends on `[b₀, g)` for `split G`. -/
def GroupSyncACOn (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (b₀ g : Time)
    (tr : SATrace sp FGP ro) : AsyncClass (Fin sp.n) → Prop
  | .any => True
  | .split G => GroupSyncAC G H U b₀ (g - 1) tr

/-- **Tier A Slice 0 incident premises** at `q` with incident `[b₀, g)` and unlock oracle `u`:
H.1's premises with the unlock given (`StandaloneRunU`), every member of the constant honest set
`H` awake from `0`, `|Hᶜ| ≤ q.fcap`, `Sync` for sends on `[0, b₀)`, `b₀ ≤ g ≤ b₀ + q.L·Δ`, and the
class's in-group guarantee. -/
def IncidentAC0 (m : WriteMode) (u : Nat → Set Lock) (q : Slice0Q (Fin sp.n)) (b₀ g : Time)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  StandaloneRunU m u tr H U proposer g ∧ (∀ y ∈ H, ∀ t, 0 ≤ t → tr.awake y t) ∧
    Hᶜ.ncard ≤ q.fcap ∧ SyncAC (goldilocksSA sp FGP ro) H U 0 (b₀ - 1) tr ∧ b₀ ≤ g ∧
    g - b₀ ≤ (q.L : Time) * sp.Δ ∧ GroupSyncACOn H U b₀ g tr q.a

variable (sp) in
/-- **The Tier A Slice 0 heal profile** with bound `d` (a `Δ`-coefficient after `ḡ`): `d` is
monotone, and for every write mode `m` of width `k` (the parent is `WriteMode.parent sp`), every
unlock oracle `u`, every run with the incident premises at `q`, and every
honest proposal `P` of slot `p` with `t_p ≥ ḡ + d(q)·Δ`: (i) every honest vote of slot `p` is `P`,
and (ii) at every call of an honest node at a time `t ≥ t_p + 6Δ` (at `t_p + 6Δ` itself, from its
tick there on), `P ⪯ ac_confirmed` after the call. -/
def HealProfileAC0 (d : Bound (Slice0Q (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (m : WriteMode), m.width = sp.k → ∀ (u : Nat → Set Lock) (FGP : Type)
    (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    (q : Slice0Q (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentAC0 m u q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposalU u tr (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))

variable (sp) in
/-- The free static bound: `8k + 4` at points with `2·fcap < n`, `⊤` elsewhere. -/
def acFree0 : Bound (Slice0Q (Fin sp.n)) := fun q =>
  if 2 * q.fcap < sp.n then ((8 * sp.k + 4 : ℕ) : WithTop ℕ) else ⊤

/-- **The free static Tier A instance**: at every SA parameter set, the Tier A Slice 0 heal profile
holds with `acFree0` (`8k + 4` at `2·fcap < n`) for every unlock oracle, hence every lawful
unlock stage (tight H.1 with the unlock given). -/
def HealProfileAC0Free : Prop := ∀ sp : SAParams, HealProfileAC0 sp (acFree0 sp)

/-- **Tier A signing rate** (static, for every unlock oracle): on every AC trace with the unlock
given at any write mode (`ACLocalRunU m u`, structural: no health premise; the vote path does
not read the mode), an honest node's vote emissions of one slot are one emission at one cut (at
most one vote per slot). -/
def SigningRateAC0 : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (u : Nat → Set Lock) (FGP : Type) (ro : ReplayOrder sp FGP)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro),
    ACLocalRunU m u H U tr → ∀ x ∈ H, ∀ i j e e', VoteAt tr x i e →
      VoteAt tr x j e' → e.msg.slot = e'.msg.slot → i = j ∧ e = e'

end Consensus.Goldilocks.Comparison

end
