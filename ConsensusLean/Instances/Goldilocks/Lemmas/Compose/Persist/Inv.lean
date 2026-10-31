module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks Persist, part 2: the invariant of C1.1's induction

`VoteInv k`, C1.1 (i) and (ii) at the honest votes of cut `k`, and `CutInv k`, G1.10 at the scope
of C1.1 at the honest call of cut `k`; and the caches of a node's state, read off its last call
or (K0) (`state_caches`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- C1.1 (i) and (ii) at the honest votes cast at cut `k` of a slot in `(s, m]`. (i) reads "at or
below `fc_root`" in the honest blocks (claims C1.1; the frame-tree reading of `ViableAtVote` fails
once honest finality passes `B`, consensus-lean#78). -/
def VoteInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
    (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) ∧
    SA.VoteExtends (tr.HonestBlocks H) e.msg B

/-- G1.10 at the scope of C1.1 at an honest call at cut `k` in `[t_s, t_m + 2Δ)`: the caches
after the call are compatible with `B`, and a block it accepts satisfies (a) and (b). -/
def CutInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H, tr.IsCall y k → sp.ts s ≤ tr.time k → tr.time k < sp.ts m + 2 * sp.Δ →
    (Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) ∧
    ∀ X, tr.AcceptAt y k X →
      let S := (tr.post k).fg
      (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
        Compatible (tr.HonestBlocks H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocks H) X B →
        ∀ Pc, Anc (tr.HonestBlocks H) Pc X → Anc (tr.HonestBlocks H) Pc B →
          (∀ Q, Anc (tr.HonestBlocks H) Q X → Anc (tr.HonestBlocks H) Q B →
            Anc (tr.HonestBlocks H) Q Pc) →
          (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)

variable {tr H}

theorem voteInv_iff {s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {k : Nat} :
    VoteInv tr H s m B k ↔
    ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg B :=
  Iff.rfl

theorem cutInv_iff {s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {k : Nat} :
    CutInv tr H s m B k ↔
    ∀ y ∈ H, tr.IsCall y k → sp.ts s ≤ tr.time k → tr.time k < sp.ts m + 2 * sp.Δ →
      (Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
        Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) ∧
      ∀ X, tr.AcceptAt y k X →
        let S := (tr.post k).fg
        (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
          Compatible (tr.HonestBlocks H) Jb B) ∧
        (¬ Compatible (tr.HonestBlocks H) X B →
          ∀ Pc, Anc (tr.HonestBlocks H) Pc X → Anc (tr.HonestBlocks H) Pc B →
            (∀ Q, Anc (tr.HonestBlocks H) Q X → Anc (tr.HonestBlocks H) Q B →
              Anc (tr.HonestBlocks H) Q Pc) →
            (S.σ X.root).h ≤ (S.σ Pc.root).h + 1) :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time} {x : Fin sp.n}
  {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
  {proposer : Nat → Fin sp.n}

/-- The state of `y` before cut `k` is its state before cut `j ≤ k`, or the state after a call of
`y` at a cut in `[j, k)`. -/
theorem state_of_le {y : Fin sp.n} {j k : Nat} (h : j ≤ k) :
    tr.state y k = tr.state y j ∨ ∃ j', j ≤ j' ∧ j' < k ∧ tr.IsCall y j' ∧
      tr.state y k = tr.post j' := by
  induction k, h using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ k hjk ih =>
    by_cases hc : tr.IsCall y k
    · obtain ⟨c, hc'⟩ := hc
      exact Or.inr ⟨k, hjk, k.lt_succ_self, ⟨c, hc'⟩, Trace.state_succ_of_call _ hc'⟩
    · rw [Trace.state_succ_of_not _ fun c hc' => hc ⟨c, hc'⟩]
      exact ih.imp_right fun ⟨j', h₁, h₂, h₃, h₄⟩ => ⟨j', h₁, h₂.trans k.lt_succ_self, h₃, h₄⟩

/-- **The caches of a state**: at a cut `k` at or after `t_s` whose earlier cuts are in the
window, the caches of an honest node's state are those after its last call (`CutInv`) or, when
that call is before `t_s`, those at `t_s` ((K0)). -/
theorem state_caches (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (hcut : ∀ j < k, CutInv tr H s m B j) (y : Fin sp.n) (hy : y ∈ H) (hk : sp.ts s ≤ tr.time k)
    (hle : ∀ j < k, tr.time j < sp.ts m + 2 * sp.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  classical
  have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, hk⟩
  have hj₀k : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts s) :=
    ⟨Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
  rcases state_of_le (tr := tr) (y := y) hj₀k with h | ⟨j', hj', hj'k, hc, h⟩
  · rw [h]
    exact hp.clean.caches y hy _ hfirst
  · rw [h]
    exact (hcut j' hj'k y hy hc
      ((Nat.find_spec hex).trans (hrun.time_mono hj')) (hle j' hj'k)).1

end Consensus.Goldilocks.Compose

end
