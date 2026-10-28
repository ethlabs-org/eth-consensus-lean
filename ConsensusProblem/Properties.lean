module
public import ConsensusProblem.Basic

@[expose] public section

/-! # The consensus problem: properties (layer 0)

Safety, nesting, accountability and non-framing read at every event cut (a
client can expose any intermediate state). Liveness and persistence read at the
end of a time, for ready readers (honest nodes awake through a catch-up window).
Every property is about one run of an abstract system. -/

namespace Consensus

open AvailableChain (Time)

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] (S : System V) (r : S.Run)

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
def Agree (g : Out) (t₀ : Time) : Prop :=
  ∀ u ∈ (S.env r).honest, ∀ v ∈ (S.env r).honest, ∀ i j, S.InCuts r t₀ i → S.InCuts r t₀ j →
    Compatible (S.read r g u i) (S.read r g v j)

/-- Each honest node's reads of `g` only extend, cut by cut, from `t₀` on. -/
def Monotone (g : Out) (t₀ : Time) : Prop :=
  ∀ v ∈ (S.env r).honest, ∀ i j, S.InCuts r t₀ i → i ≤ j → S.InCuts r t₀ j →
    S.read r g v i <+: S.read r g v j

/-- Safety of `g` from `t₀`. -/
def Safe (g : Out) (t₀ : Time) : Prop := S.Agree r g t₀ ∧ S.Monotone r g t₀

/-- Safety from `t₀` for ready readers only: reads of nodes ready at the time
of their cut agree, and a node's reads at two cuts where it is ready only
extend. (A node asleep since long ago may hold an old fork.) -/
def ReadySafe (c : Time) (g : Out) (t₀ : Time) : Prop :=
  (∀ u v i j, S.InCuts r t₀ i → S.InCuts r t₀ j →
      S.Ready r c u (S.cutTime r i) → S.Ready r c v (S.cutTime r j) →
      Compatible (S.read r g u i) (S.read r g v j)) ∧
  (∀ v i j, S.InCuts r t₀ i → i ≤ j → S.InCuts r t₀ j →
      S.Ready r c v (S.cutTime r i) → S.Ready r c v (S.cutTime r j) →
      S.read r g v i <+: S.read r g v j)

/-- Output `g₁` is a prefix of output `g₂` in every honest read. -/
def Nested (g₁ g₂ : Out) : Prop :=
  ∀ v ∈ (S.env r).honest, ∀ i, i ≤ S.cuts r → S.read r g₁ v i <+: S.read r g₂ v i

/-- Transaction liveness of `g` from `start` with delay `D` (a duration): a
transaction submitted to every honest node by `t ≥ start` is in the read of
every ready reader at every time `t' ∈ [t + D, horizon]`. -/
def TxLive (c : Time) (g : Out) (start D : Time) : Prop :=
  ∀ x t t', start ≤ t → S.SubmittedToAll r x t → t + D ≤ t' → t' ≤ (S.env r).horizon →
    ∀ v, S.Ready r c v t' → x ∈ S.readAt r g v t'

/-- Persistence of `g` on `[b₀, b₁)`: every honest read at `T` is, at every time
of `[b₀, b₁)`, a prefix of the read of every honest node awake throughout
`[max 0 (b₀ − c − 1), t]` (ready before `b₀`, not restarted since). -/
def PersistsThrough (c : Time) (g : Out) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ (S.env r).honest, ∀ t, b₀ ≤ t → t < b₁ → ∀ w ∈ (S.env r).honest,
    (∀ u, max 0 (b₀ - c - 1) ≤ u → u ≤ t → (S.env r).awake w u = true) →
    S.readAt r g v T <+: S.readAt r g w t

/-- The validators that the evidence set `A` convicts. -/
noncomputable def convicted (A : Set S.Obs) : Finset V := by
  classical
  exact Finset.univ.filter (S.convicts r A)

/-- Accountable safety of `g` from `t₀`: two honest reads, at any nodes and
cuts, are compatible, or what the two readers saw convicts a third of the
validators. -/
def AccountablySafe (g : Out) (t₀ : Time) : Prop :=
  ∀ u ∈ (S.env r).honest, ∀ v ∈ (S.env r).honest, ∀ i j, S.InCuts r t₀ i → S.InCuts r t₀ j →
    Compatible (S.read r g u i) (S.read r g v j) ∨
      Fintype.card V ≤ 3 * (S.convicted r (S.view r u i ∪ S.view r v j)).card

/-- No honest validator is convicted by what the honest nodes saw. -/
def NonFraming : Prop :=
  ∀ v ∈ (S.env r).honest, ¬ S.convicts r (S.honestEvidence r) v

/-- Fewer than a third of the validators are not honest. -/
def BelowOneThird : Prop :=
  3 * (Finset.univ \ (S.env r).honest).card < Fintype.card V

end System

end Consensus

end
