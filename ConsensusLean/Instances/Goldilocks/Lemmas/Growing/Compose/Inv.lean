module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Goldilocks Persist, part 2: the invariant of C1.1's induction

`VoteInv k`, C1.1 (i) and (ii) at the honest votes of cut `k`, and `CutInv k`, G1.10 at the scope
of C1.1 at the honest call of cut `k`; and the caches of a node's state, read off its last call
or (K0) (`state_caches`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- C1.1 (i) and (ii) at the honest votes cast at cut `k` of a slot in `(s, m]`. (i) reads "at or
below `fc_root`" in the honest blocks (claims C1.1; the frame-tree reading of `ViableAtVote` fails
once honest finality passes `B`). -/
def VoteInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H (tr.time k), ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
    (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot) ∧
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B

/-- G1.10 at the scope of C1.1 at an honest call at cut `k` in `[t_s, t_m + 2Δ)`: the caches
after the call are compatible with `B`, and a block it accepts satisfies (a) and (b). -/
def CutInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H (tr.time k), tr.IsCall y k → sp.ts s ≤ tr.time k → tr.time k < sp.ts m + 2 * sp.Δ →
    (Compatible (tr.HonestBlocksAt H) (tr.post k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.post k).fg.J B) ∧
    ∀ X, tr.AcceptAt y k X →
      let S := (tr.post k).fg
      (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
        Compatible (tr.HonestBlocksAt H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocksAt H) X B →
        ∀ Pc, Anc (tr.HonestBlocksAt H) Pc X → Anc (tr.HonestBlocksAt H) Pc B →
          (∀ Q, Anc (tr.HonestBlocksAt H) Q X → Anc (tr.HonestBlocksAt H) Q B →
            Anc (tr.HonestBlocksAt H) Q Pc) →
          (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)

variable {tr H}

theorem voteInv_iff {s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {k : Nat} :
    VoteInv tr H s m B k ↔
    ∀ y ∈ H (tr.time k), ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot) ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B :=
  Iff.rfl

theorem cutInv_iff {s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {k : Nat} :
    CutInv tr H s m B k ↔
    ∀ y ∈ H (tr.time k), tr.IsCall y k → sp.ts s ≤ tr.time k → tr.time k < sp.ts m + 2 * sp.Δ →
      (Compatible (tr.HonestBlocksAt H) (tr.post k).fg.F B ∧
        Compatible (tr.HonestBlocksAt H) (tr.post k).fg.J B) ∧
      ∀ X, tr.AcceptAt y k X →
        let S := (tr.post k).fg
        (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
          Compatible (tr.HonestBlocksAt H) Jb B) ∧
        (¬ Compatible (tr.HonestBlocksAt H) X B →
          ∀ Pc, Anc (tr.HonestBlocksAt H) Pc X → Anc (tr.HonestBlocksAt H) Pc B →
            (∀ Q, Anc (tr.HonestBlocksAt H) Q X → Anc (tr.HonestBlocksAt H) Q B →
              Anc (tr.HonestBlocksAt H) Q Pc) →
            (S.σ X.root).h ≤ (S.σ Pc.root).h + 1) :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time} {x : Fin sp.n}
  {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
  {proposer : Nat → Fin sp.n}

/-- **The caches of a state**: at a cut `k` at or after `t_s` whose earlier cuts are in the
window, the caches of an honest node's state are those after its last call (`CutInv`) or, when
that call is before `t_s`, those at `t_s` ((K0)). -/
theorem state_caches (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (hcut : ∀ j < k, CutInv tr H s m B j) (y : Fin sp.n) (hy : y ∈ H (tr.time k))
    (hk : sp.ts s ≤ tr.time k)
    (hle : ∀ j < k, tr.time j < sp.ts m + 2 * sp.Δ) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B := by
  classical
  have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, hk⟩
  have hj₀k : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts s) :=
    ⟨Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
  rcases Compose.state_of_le (tr := tr) (y := y) hj₀k with h | ⟨j', hj', hj'k, hc, h⟩
  · rw [h]
    exact hp.clean.caches y _ (hrun.antitone hk hy) hfirst
  · rw [h]
    exact (cutInv_iff.mp (hcut j' hj'k) y (hrun.antitone (hrun.time_mono hj'k.le) hy) hc
      ((Nat.find_spec hex).trans (hrun.time_mono hj')) (hle j' hj'k)).1

/-- The vote half of the persistence induction uses only earlier cache and vote rows. -/
theorem vote_step (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV)
    (k : Nat) (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    VoteInv tr H s m B k := by
  rw [voteInv_iff]
  intro y hy ℓ e hc hs hsm
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl).localRun
  have hrk := hr.upTo (hr.time_nonneg k)
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hle : tr.time k ≤ sp.ts e.msg.slot + sp.Δ :=
    (Compose.cast_head_fcRoot hrk hy hc').2
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hslot : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hrk hy hc').2.1
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).mpr (by rw [hslot])
  have hk : sp.ts s ≤ tr.time k := ((SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hs.le)).trans hts
  have hlt : ∀ j < k, tr.time j < sp.ts m + 2 * sp.Δ := fun j hj => by
    have := hrun.time_mono hj.le
    have := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm)
    linarith
  have hcache := state_caches hrun hp k (fun j hj => (ih j hj).2) y hy hk hlt
  have hK2 := hp.clean.heightLead y k ℓ e hy hc hs hsm
  have hvi := vote_viable hrun hp.noColl hy hc hcache hK2
  exact ⟨hvi, vote_extends hrun hp hy hc hs hsm hvi
    fun z j hj hz e' ⟨ℓ', hc', he'⟩ h₁ h₂ =>
      (voteInv_iff.mp (ih j hj).1 z hz ℓ' e' ⟨hc', he'⟩ h₁ h₂).2⟩

end Consensus.Goldilocks.Compose.Growing

end
