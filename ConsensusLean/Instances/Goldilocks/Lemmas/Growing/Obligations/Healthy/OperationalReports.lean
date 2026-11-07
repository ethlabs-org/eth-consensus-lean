module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportsPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalPending
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Operational reports of a unanimous slot, under growing faults

The growing forms of the first lemmas of `Healing/OperationalReports`, with each node honest at its
own cut:

* `restart_before_unanimous_slot_at`: a restart of a node honest at it, by the horizon, precedes
  every post-drain slot;
* `honest_votes_in_slot_at`: every node honest at the vote deadline `t_u + Δ` votes in slot `u`;
* `old_origin_below_unanimous_at`: a high origin before a unanimous post-drain slot `u` is below
  its proposal. The witness voter is any node honest at `t_u + Δ` (the origin's writer may be
  compromised by then); retention R2 makes its slot-`u` vote extend the origin. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A restart of a node honest at it, by the horizon, is by `t_{u-1}` for every slot `u` with
`drainTime a ≤ t_{u+1}`. -/
theorem restart_before_unanimous_slot_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} {r : Nat} (hy : y ∈ H (tr.time r)) (hr : tr.RestartAt y r)
    (hrb : tr.time r ≤ b) : tr.time r ≤ sp.ts ((u : Int) - 1) := by
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  rw [Healing.cutZ_eq] at hca
  have hqa := (SA.ts_le_iff_le_slot sp ha0 _).1 hca.le
  rw [Healing.drainTime_eq] at hR
  have hAu := (SA.ts_le_iff sp).1 hR
  apply (hp.restart_le_before_at hy hr hrb).trans
  apply (SA.ts_le_iff sp).2
  push_cast at hqa hAu ⊢
  omega

/-- Every node honest at the vote deadline `t_u + Δ` of a post-drain slot votes in it by then. -/
theorem honest_votes_in_slot_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y, y ∈ H (sp.ts u + sp.Δ) → ∃ j e, SA.VoteAt tr.projAC y j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  intro y hy
  have hΔ := sp.toParams.hΔ
  have hd0 : 0 ≤ sp.ts u + sp.Δ := by have := SA.gbar_nonneg g; linarith
  have hS := healthy_base_of_reset_catch_before_at hp hc hd0 hub
  obtain ⟨j, e, ⟨ℓ, hcj, hej⟩, hs, hjt⟩ := SA.honest_votes_in_slot_before hS hgu le_rfl
    (fun x hx r hr hrs => by
      obtain ⟨ℓ, hcr, hrl⟩ := hrs
      have hcr' := ((Trace.upTo_callAt _).mp hcr).2
      have hxr : x ∈ H (tr.time r) := hp.run.antitone hr hx
      exact restart_before_unanimous_slot_at hp hR hxr
        (Compose.projAC_restartAt.mp ⟨ℓ, hcr', hrl⟩) (hr.trans hub)) y hy
  exact ⟨j, e, ⟨ℓ, ((Trace.upTo_callAt _).mp hcj).2, hej⟩, hs, hjt⟩

/-- A high origin before a unanimous post-drain slot `u` is below its proposal `P`. -/
theorem old_origin_below_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {x : Fin sp.n} {r m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m B) (ht : tr.time r < sp.ts u) :
    Anc (tr.HonestBlocksAt H) B P := by
  have hΔ := sp.toParams.hΔ
  have hmu : m < u := by
    obtain ⟨-, -, ⟨CV, ℓ, D, -, hfl, -⟩, -⟩ := ho
    rcases hfl with ⟨ell, C, hu, _⟩ | ⟨ell, A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts u := by linarith
      have := (SA.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have hlt := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) (u : Int)).not.mp
        (not_le.mpr ht)
      omega
  have hT0 : 0 ≤ sp.ts u + sp.Δ := by
    have := SA.gbar_nonneg g; linarith
  obtain ⟨w, hw⟩ : (H (sp.ts u + sp.Δ)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hf := hp.faults _ hT0 hub
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
    have := Fin.pos x
    omega
  obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot_at hp hc hgu hR hub w hw
  have hwq : w ∈ H (tr.time q) := hp.run.antitone hq hw
  obtain ⟨ell, hcast⟩ := hv
  have hrb : tr.time r ≤ b := by linarith
  obtain ⟨Hd, hHd, he, hBH⟩ :=
    hp.high_origin_votes_before_at q (hq.trans hub) x r m B ho hrb w ell e hwq hcast (by omega)
  have heq : Hd = P := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hHd hP
    (he.trans (hun w q e hwq ⟨ell, hcast⟩ (hq.trans hub) hs))
  exact heq ▸ hBH

end Consensus.Goldilocks.Healing.Growing

end
