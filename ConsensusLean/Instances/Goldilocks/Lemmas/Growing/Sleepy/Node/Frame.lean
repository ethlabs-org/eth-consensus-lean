module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.HeldRow
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee

public section

/-! # Goldilocks under `Sleepy` with growing faults: honest rows and their sources

`HonestRowsSourcedAt tr H G y i`: every attestation of a block in the tree of `y` before cut `i`
whose signer is honest at `tr.time i` has a source satisfying `G`, held by a node honest at
`tr.time i` at a cut `k ≤ i` (the signers and the source holder are classified at the reading cut,
Lemma G). The frame lemmas of `Compose/Sleepy/Frame` lift at the cut's time `d = tr.time i`, with
`2 f_d < n`; their honest sources are held while honest at `d` (`IsHonestSourceAt`). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}

/-- The honest rows of `y`'s tree before cut `i` are sourced in `G`, classified at `tr.time i`. -/
def HonestRowsSourcedAt (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop) (y : Fin sp.n) (i : Nat) : Prop :=
  ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
    ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
      ((tr.state x k).fg.σ D.root).Th = a.T

theorem honestRowsSourcedAt_iff {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop} {y : Fin sp.n} {i : Nat} :
    HonestRowsSourcedAt tr H G y i ↔
      ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
        ∃ D, G D ∧ ∃ x k, x ∈ H (tr.time i) ∧ k ≤ i ∧ D ∈ (tr.state x k).fg.tree ∧
          ((tr.state x k).fg.σ D.root).Th = a.T :=
  Iff.rfl

/-- `D` is the source of target `T` held, while honest at `d`, by a node before a cut whose earlier
cuts are at times `≤ d`. -/
def IsHonestSourceAt (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (D : AC.Blk sp.n (List (FG.Att sp.n))) (T : Nat) (d : Time) : Prop :=
  ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧ D ∈ (tr.state x k).fg.tree ∧
    ((tr.state x k).fg.σ D.root).Th = T

theorem isHonestSourceAt_iff {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {T : Nat} {d : Time} :
    IsHonestSourceAt tr H D T d ↔ ∃ x k, x ∈ H d ∧ (∀ k' < k, tr.time k' ≤ d) ∧
      D ∈ (tr.state x k).fg.tree ∧ ((tr.state x k).fg.σ D.root).Th = T :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- **An honest row was signed while honest** (`honest_row_signed_before` at `d = tr.time i`): an
attestation of a block in the tree of a node honest at cut `i`, whose signer is honest at `i`, was
signed at an earlier cut, at which its signer was honest, before the block's acceptance. -/
theorem honest_row_signed_before_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H (tr.time i)) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a ∧ a.val ∈ H (tr.time k) := by
  have hm := hrun.time_mono
  obtain ⟨m, hmi, hA, k, hkm, hS⟩ := honest_row_signed_before
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
    (by rw [Trace.upTo_state tr y fun _ hk => hm hk.le]; exact hX) ha hav
  obtain ⟨-, hA⟩ := (RunTrace.upTo_acceptAt tr).mp hA
  obtain ⟨hkd, hS⟩ := (RunTrace.upTo_signAt tr).mp hS
  exact ⟨m, hmi, hA, k, hkm, hS, hrun.antitone hkd hav⟩

/-- **No optimistic check before a held row** under growing faults (R, the committee count at the
check's cut `c`): at a slot-`(s+1)` vote of a node honest at its cut `i`, no block accepted at
`m < i` holds an attestation, by a signer honest at `m`, signed at `k < m` after an optimistic
check of slot `s + 1` at `c < k` by a node honest at `c`, when `2 |K(s+1) ∩ (H t_c)ᶜ| <
committeeSize`. The signing is at `t_{s+1}` or `t_{s+1} + Δ`. At `t_{s+1} + Δ` the voter's own tick
votes before the block arrives (on the prefix through `tr.time i`); at `t_{s+1}` the check's honest
seats are the slot's proposer, so the slot-`(s+1)` committee is one member (on the prefix through
`tr.time c`), the voter (a member by the gate), and the voter has a second slot-`(s+1)` vote. -/
theorem no_optimistic_before_held_row_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} {s : Nat} (hy : y ∈ H (tr.time i))
    (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) {m : Nat}
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hacc : tr.AcceptAt y m X) (hmi : m < i)
    {a : FG.Att sp.n} (hav : a.val ∈ H (tr.time m)) {k : Nat} (hkm : k < m)
    (hsign : tr.SignAt a.val k a) {z : Fin sp.n} {c : Nat}
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hz : z ∈ H (tr.time c))
    (hck : c < k) (hO : AC.OptimisticLockAt tr.projAC z c (s + 1) C CV)
    (hfK : 2 * (K.committee (s + 1) ∩ (H (tr.time c))ᶜ).ncard < sp.committeeSize) : False := by
  have hm := hrun.time_mono
  obtain ⟨-, -, -, hslc, -⟩ := id hO
  change sp.slot (tr.time c) = s + 1 at hslc
  have hkm' := hm hkm.le
  have hmi' := hm hmi.le
  rcases Compose.held_row_sign_time (hrun.upTo (hrun.time_nonneg k)) (hrun.antitone hkm' hav)
      ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hsign⟩) (hrun.time_nonneg c) hslc (hm hck.le)
      (hkm'.trans (hmi'.trans (by rw [← hs]; exact (cast_head_fcRoot_at hrun hnc hy hc).2)))
    with ⟨hT0, htc⟩ | hT
  · -- at `t_{s+1}`, on the prefix through the check
    obtain ⟨u, hu, hall, j', hj', e', hv', hs'⟩ := Compose.held_row_early_count
      (hrun.upTo (hrun.time_nonneg c)) (hnc.upTo _) K
      (by rw [RunTrace.upTo_projAC]; exact AC.CommitteePAt.upTo hm hrun.antitone hKB.hP (tr.time c))
      hKB.hsize hfK
      (hrun.antitone ((hm hck.le).trans hkm') hav)
      ((RunTrace.upTo_signAt tr).mpr ⟨htc.ge, hsign⟩) hT0 hz hck
      (by rw [RunTrace.upTo_projAC]; exact (AC.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hO⟩)
    rw [RunTrace.upTo_projAC] at hv'
    obtain ⟨hjd, hv'⟩ := AC.upTo_voteAt.mp hv'
    have hyK : y ∈ K.committee (s + 1) := by
      rw [← hs]
      exact (hKB.hGate (tr.time i) (hrun.time_nonneg i) y hy i (fun k hk => hm hk.le) _).1
        (mayVote_of_castAt_at hrun hnc hy hc)
    obtain rfl : u = y := (hall y hyK).symm
    have := (one_vote_per_slot_at hrun hnc (hVoteAt_iff.2 ⟨hrun.antitone hjd hu, hv'⟩)
      (hVoteAt_iff.2 ⟨hy, ℓ, hc.1, hc.2⟩) (hs'.trans hs.symm)).1
    omega
  · -- at `t_{s+1} + Δ`, on the prefix through the vote
    exact Compose.held_row_late_absurd (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
      (by rw [RunTrace.upTo_projAC]; exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩) hs
      ((RunTrace.upTo_acceptAt tr).mpr ⟨hmi', hacc⟩) hmi hkm hT

end Consensus.Goldilocks.Compose.Growing

end
