module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Weak
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs

public section

/-! # Goldilocks milestone Regimes: R.6's base for the Sleepy invariant from `s₀`

`healed_safe_until` (R.6, `Lemmas/Compose/Regimes/Weak`) goes through the Sleepy record invariant
started at a label `s₀` after the reset (`Compose.sleepy_invariant_from`, over `SleepyFrom` and
`SleepyBase`). This file derives both from `WeakPremises` (the healing premises of R.3 cut at the
heal point `T`) for a start label `s₀` with `a + T_b ≤ t_{s₀}` (the reset `a`, `T_b` of H.3 (c)'s
bridge), early enough before `T` (`t_{s₀+k} ≤ T`, `t_{s₀+2} + 6Δ ≤ T`), split by owner
(consensus-lean#17, 2026-10-31):

* `weak_sleepyFrom`: `Sync` and `f < h_t` from `t_{s₀}` (`GST(g)` from `ḡ`; every honest node
  awake and joined on `[ḡ, T]`, the ready ones from `T`) (acbase; open);
* `weak_base_locks`, `weak_base_sources`, `weak_base_old_blocks`: `SleepyBase`'s (1) (a read-point
  lock of a slot `< s₀` is live only at votes of slots `< s₀ + k`, so before `T`, under `Healthy`
  and H.2's drain), (3b) (A1.5: a source is below the stored block of a recent fast lock) and (6)
  (`Catch(2Δ)` for the acceptances before `ḡ`, `GST(g)`'s relay for those in `[ḡ, t_{s₀})`, the
  voter joined) (acbase; open);
* `weak_base_until`: the facts (2), (3a), (5) and (5′) at the cuts up to `T` (`BaseFacts` at
  `· ≤ T`), the paper obligation of the T3 orb (open);
* `weak_base_extend`: the same facts at every cut (`BaseFacts` at every time), from those up to
  `T` and the run after `T` (amp-orbs service; open). Not by monotonicity alone: a `Σ.F` that moves
  past `T` needs a covering origin, and a row first held after `T` is not covered by the facts up
  to `T`.

`weak_sleepyBase` assembles `SleepyBase` from them. -/

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
  /-- (5) Rows at votes of slots `> s₀`. -/
  vote_rows : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → P (tr.time i) →
    ∀ s, e.msg.slot = s + 1 → s₀ ≤ s → ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload,
      a.val ∈ H → (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧ l ≤ s ∧
          Anc (tr.HonestBlocks H) D C
  /-- (5′) Rows at the cuts from `t_{s₀}`. -/
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

/-- **`Sync` and `f < h_t` from `t_{s₀}`** under `Weak` (open; acbase). -/
theorem weak_sleepyFrom (hrun : GoldilocksRun dg H tr) (hw : WeakPremises tr H dg g ΔF Gp a Tb T)
    (hs₀ : a + Tb ≤ sp.ts s₀) : SleepyFrom tr H ΔF s₀ := by
  sorry

/-- **(1) Old live locks** (open; acbase): a read-point lock of a slot `< s₀` is live at a vote
of a slot `> s₀` only before `t_{s₀+k} ≤ T`, where `Healthy` and H.2's drain hold. -/
theorem weak_base_locks (hrun : GoldilocksRun dg H tr) (hw : WeakPremises tr H dg g ΔF Gp a Tb T)
    (hs₀ : a + Tb ≤ sp.ts s₀) (hk : sp.ts (s₀ + sp.k : Nat) ≤ T) :
    ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s₀ < e.msg.slot →
      ∀ L ∈ SA.liveLockBlocks sp {l ∈ e.readPoint.locks | l.slot < s₀} ℓ.frame (tr.time i),
        ∀ C j, OriginFrom tr H C j s₀ → j < e.msg.slot → Compatible (tr.HonestBlocks H) L C := by
  sorry

/-- **(3b) Sources** (open; acbase): A1.5. -/
theorem weak_base_sources (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀) :
    ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
      (∃ C' l, Origin tr H C' l ∧ l < s₀ ∧ Anc (tr.HonestBlocks H) C C') →
        OnOriginChainFrom tr H C s₀ := by
  sorry

/-- **(6) Old blocks caught up** (open; acbase): `Catch(2Δ)` and `GST(g)`'s relay. -/
theorem weak_base_old_blocks (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀) :
    ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → ∀ s, e.msg.slot = s + 1 →
      s₀ ≤ s → ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
        Anc (tr.HonestBlocks H) ℓ.frame.F B →
          SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ) := by
  sorry

/-- **(2), (3a), (5), (5′) up to `T`** (open; the T3 orb's paper obligation). -/
theorem weak_base_until (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) :
    BaseFacts tr H s₀ (· ≤ T) := by
  sorry

/-- **(2), (3a), (5), (5′) at every cut** from those up to `T` (open; amp-orbs service). -/
theorem weak_base_extend (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) (hbase : BaseFacts tr H s₀ (· ≤ T)) :
    BaseFacts tr H s₀ fun _ => True := by
  sorry

/-- **`SleepyBase` at `s₀` under `Weak`**, assembled. -/
theorem weak_sleepyBase (hrun : GoldilocksRun dg H tr)
    (hw : WeakPremises tr H dg g ΔF Gp a Tb T) (hs₀ : a + Tb ≤ sp.ts s₀)
    (hk : sp.ts (s₀ + sp.k : Nat) ≤ T) (hT : sp.ts (s₀ + 2 : Nat) + 6 * sp.Δ ≤ T) :
    SleepyBase tr H s₀ := by
  have hb := weak_base_extend hrun hw hs₀ hT (weak_base_until hrun hw hs₀ hT)
  exact ⟨weak_base_locks hrun hw hs₀ hk,
    fun y hy i hi => hb.records y hy i trivial hi,
    fun y hy i hi => hb.caches y hy i trivial hi,
    weak_base_sources hrun hw hs₀,
    fun y hy i ℓ e hc => hb.vote_rows y hy i ℓ e hc trivial,
    fun y hy i hi => hb.event_rows y hy i trivial hi,
    weak_base_old_blocks hrun hw hs₀⟩

end Base

end Consensus.Goldilocks.Regimes

end
