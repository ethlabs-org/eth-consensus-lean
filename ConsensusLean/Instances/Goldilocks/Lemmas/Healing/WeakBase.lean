module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Goldilocks milestone Regimes: R.6's base for the Sleepy invariant from `s₀`

This module lives in Healing because the base uses the reset and acceptance projection lemmas;
the Compose layer is below Healing in the import matrix.

R.6's safety goes through the Sleepy record invariant started at a label `s₀` after the reset
(`Compose.sleepy_invariant_from`, over `SleepyFrom` and `SleepyBase`). This file works from
the healing premises of R.3 cut at the heal point `T` (the retired node-level R.6 premises) for a
start label `s₀` with `a + T_b ≤ t_{s₀}` (the reset `a`, `T_b` of H.3 (c)'s bridge).

`BaseFacts` names `SleepyBase`'s facts (2), (3a), (5) and (5′) at the cuts whose time satisfies a
guard. The open remainder of `SleepyBase` ((1) old live locks, and `BaseFacts` up to `T` and at
every cut) and its R.6 assembly are not stated here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **`SleepyBase`'s facts (2), (3a), (5), (5′) at the cuts whose time satisfies `P`** (the
fields of `SleepyBase` with the guard `P (tr.time i)`): at every time (`P := fun _ => True`) they
are `SleepyBase`'s fields; up to `T` (`P := (· ≤ T)`) they are what the healed configuration
and `Healthy` up to `T` can give. -/
structure BaseFacts (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s₀ : Nat)
    (P : Time → Prop) : Prop where
  /-- (2) Records (RecRet). -/
  records : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts s₀ + 6 * sp.Δ ≤ tr.time i →
    ∀ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed →
      (∃ s < s₀, Origin tr H C s) →
        OnOriginChainFrom tr H C s₀ ∨ Anc (tr.HonestBlocks H) C (tr.state y i).fg.F
  /-- (3a) Caches. -/
  caches : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    OnOriginChainFrom tr H (tr.state y i).fg.F s₀ ∧ OnOriginChainFrom tr H (tr.state y i).fg.J s₀
  /-- (5) Attestations at votes of slots `> s₀`. -/
  vote_rows : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → P (tr.time i) →
    ∀ s, e.msg.slot = s + 1 → s₀ ≤ s → ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload,
      a.val ∈ H → (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧ l ≤ s ∧
          Anc (tr.HonestBlocks H) D C
  /-- (5′) Attestations at the cuts from `t_{s₀}`. -/
  event_rows : ∀ y ∈ H, ∀ i, P (tr.time i) → sp.ts s₀ ≤ tr.time i →
    ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧
          Anc (tr.HonestBlocks H) D C

section Base

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a Tb T : Time} {s₀ : Nat}
  {proposer : Nat → Fin sp.n}

end Base

end Consensus.Goldilocks.Regimes

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- The global old inventory: an actual honest signature, its self-entry realization
at fixed replay height, and the exact old-source antecedent. None of these witnesses
is restricted to objects held at the initialization cut. -/
structure OldHonest (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s₀ : Nat)
    (E : SA.Blk sp.n (List (FG.Att sp.n))) (h : Nat) : Prop where
  signed : ∃ v ∈ H, ∃ d a, tr.SignAt v d a ∧ E.root = a.T
  entry : ∃ x ∈ H, ∃ k, E ∈ (tr.state x k).fg.tree ∧
    ((tr.state x k).fg.σ E.root).Th = E.root ∧ ((tr.state x k).fg.σ E.root).h = h
  oldSource : ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
    ((tr.state x k).fg.σ D.root).Th = E.root) ∧ Compose.Origin tr H C l ∧ l < s₀ ∧
      Anc (tr.HonestBlocks H) D C

/-- Coverage has a whole-run recent-origin witness, without an upper label bound
or an extra standalone genesis alternative. -/
def OldEntryCovered (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s₀ : Nat)
    (E : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ C l, Compose.OriginFrom tr H C l s₀ ∧ Anc (tr.HonestBlocks H) E C

theorem updateFinality_hj_le {P : Params} {ACP : Type}
    (st : Store P ACP) (σ : FG.ChainState P.n) : st.hj ≤ (st.updateFinality σ).hj := by
  rcases (Store.updateFinality_spec st σ).2.2.2.2.1 with h | ⟨_, he, _, hlex⟩
  · exact le_of_eq h.2.symm
  · rw [he]
    rcases hlex with h | h
    · exact h.le
    · exact le_of_eq h.1

/-- Honest cache height is monotone at all cuts, including sleeping intervals and
restart AC calls; readiness is not a premise. -/
theorem run_hj_mono {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {proposer : Nat → Fin sp.n} (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j) :
    (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    apply ih.trans
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      have h := hrun.cutLaw y hy j c hc
      cases c with
      | ac ℓ => rw [h.2.2.1]
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false => rw [h.2]
          | true =>
            obtain ⟨pr, σ, _, _, _, _, _, he⟩ := Store.onBlock_eq_some h.2.1
            rw [he]
            obtain ⟨atts, hatt⟩ := Store.addAtts_eq
              (Store.updateFinality _ σ) B.fgPayload
            rw [hatt]
            exact updateFinality_hj_le
              { (tr.state y j).fg with
                blocks := Function.update (tr.state y j).fg.blocks B.root (some B),
                σ := Function.update (tr.state y j).fg.σ B.root σ } σ
        | attestation a =>
          rw [h.1]
          obtain ⟨atts, he⟩ := Store.onAttestation_eq (tr.state y j).fg a
          rw [he]
        | attest C att =>
          cases att with
          | none => rw [h.2]
          | some att => rw [h.2.1]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- Conditional preservation of the all-honest old-entry inventory. The base cut
`Q` and its initialization are explicit: this does not identify `Q` with the slot
label `s₀`, nor prove that the inventory is initialized there. -/
theorem oldHonest_inventory_preserved {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {proposer : Nat → Fin sp.n} (hrun : GoldilocksRun proposer dg H tr) {s₀ Q : Nat}
    (hinit : ∀ y ∈ H, ∀ E h, OldHonest tr H s₀ E h →
      OldEntryCovered tr H s₀ E ∨ h < (tr.state y Q).fg.hj) :
    ∀ i, Q ≤ i → ∀ y ∈ H, ∀ E h, OldHonest tr H s₀ E h →
      OldEntryCovered tr H s₀ E ∨ h < (tr.state y i).fg.hj := by
  intro i hi y hy E h hE
  rcases hinit y hy E h hE with hcov | hlt
  · exact Or.inl hcov
  · exact Or.inr (hlt.trans_le (run_hj_mono hrun hy hi))

end Consensus.Goldilocks.Healing

end
