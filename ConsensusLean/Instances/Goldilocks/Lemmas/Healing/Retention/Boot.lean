module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Goldilocks Healing, HR.4: the base case, activation, the vote premises and the records

HBoot (`boot_caches`), the activation of pending origins (`activation_caches`), the label bound,
(K2)/R5 at votes (`vote_height_lead`), the low-`Σ.J` root (`low_root_compatible`), `Carry`
(`first_carry`, `later_carry`), half the committee (`half_committee`) and (R4) (`high_records`).

Interfaces: open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### Interfaces from the paper (open) -/

/-- **The label bound of a high origin** (§11, "Historical finality and acceptance": `j ≥ slot(c)`).
The writer accepted the counted heads, of state height `≥ H_z + 1`, before `t_j + 2Δ`; no honest
node accepts such a block at or before `c_z` (the definition of `H_z`), so `t_j + 2Δ > c_z`, and
`t_j ≥ c_z` since both are slot starts. -/
theorem cutZ_le_ts_of_highOrigin (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j := by
  sorry

/-- **HBoot, the caches before the reset** (§11 "Historical finality and acceptance";
`t1-proof.md` §9). At a state all of whose earlier cuts are before `a`: no honest `Σ.J` is high
(a justification at `h ≥ H_z + 1` needs an honest row at `h`, none before `a`, HR.1 (c)), and
`Σ.F`, of height `≤ H_z` (no chain has crossed `H_z + 1`, G0.2 (a)), is below every high origin:
its finality quorum meets the crossing quorum on a counted head's chain at its height in an honest
validator (G1.2, G0.5, `f < 2q − n`). -/
theorem boot_caches (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  sorry

/-- **Activation of a high origin** (§13 "Activation uses earlier labels, not D's own transfer",
"Retaining the witnesses and the frame"; §12, the pending boundary case). At the state at
`t_{j+1}` after the reset (immediately before the first-transfer votes of the origin's label `j`,
even when its write is later), every honest `Σ.F`, and every high honest `Σ.J`, is compatible with
the origin's block: low finalized entries by G1.2, high ones through their row witnesses, whose
sources are comparable with `B` by the label split (earlier labels by their votes, the same label
by TSQ, later labels excluded by R4). -/
theorem activation_caches (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k₁ : Nat} (hk₁ : tr.FirstCutFrom k₁ (sp.ts (j + 1 : Nat)))
    (ha : a < sp.ts (j + 1 : Nat))
    (ih : ∀ k' < k₁, VoteInv tr H g k' ∧ CacheInv tr H g a k') :
    Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k₁).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.J B) := by
  sorry

/-- **(K2) at a vote, R5** (§5 Lemma R5; §11 item 1 for the votes through the ticks at `a_z`;
§13 "Retaining the witnesses and the frame"; `t1-proof.md` §9 base case). At an honest vote of a
slot `> j`, the voter block tree holds a viable descendant of the origin's block `B`, or
`B ⪯ fc_root`: in the low-frontier regime `B` itself (height `H_z + 1`, relayed before the freeze);
above it, the supporting head of an earlier comparable high source that crossed the floor (R4,
R5). -/
theorem vote_height_lead (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot) :
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **A low `Σ.J` does not veto a high origin** (§11, "an old conflicting J merely causes a
contest"; `t1-proof.md` §9, the geometric statement). When the voter's root is a low `Σ.J`
(`h_max = h_j + 1 ≤ H_z + 1`, no contest) and its voter block tree holds a descendant `D` of the
origin's block `B`, then `D` has state height `h_max` (`≥ σ[B].h ≥ H_z + 1`), so it extends `Σ.J`
(no contest), and `Σ.J` is compatible with `B`. -/
theorem low_root_compatible (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hroot : (tr.state y k).fg.hmax = (tr.state y k).fg.hj + 1 ∧ ¬ (tr.state y k).fg.Contest)
    (hlow : (tr.state y k).fg.hj ≤ HZ tr H g) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hD : D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)
    (hBD : Anc (tr.HonestBlocks H) B D) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  sorry

/-- **`Carry` at a first-transfer vote** (§11 "Historical finality and acceptance", §13
"Retaining the witnesses and the frame"). At an honest vote of slot `j + 1` at which `B` is not
below `fc_root` (so `Σ.F ⪯ B`), the voter holds the counted votes of the origin and has accepted
their heads before `t_j + 3Δ`: the heads, of height `≥ H_z + 1`, were first accepted after `c_z`
and before `t_j + 2Δ`, and extend `Σ.F`, so acceptance relay delivers them. -/
theorem first_carry (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  sorry

/-- **`Carry` at a later vote** (§11 "First-violating-vote induction", §13 "Retaining the
witnesses and the frame"). At an honest vote of slot `m' + 1`, `m' > j`, at which `B` is not below
`fc_root`, the voter holds the honest slot-`m'` votes and has accepted their heads (which extend
`B`, by the earlier votes, hence `Σ.F`) before `t_{m'} + 3Δ`, by relay. -/
theorem later_carry (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  sorry

/-- **Half of the committee votes** (`Healthy(g)`): in a slot `s'` with `t_{s'} ≥ c_z`, every
honest validator is awake and joined (no honest restart after `max(g, 0)`) and votes by
`t_{s'} + Δ` (`tryVote`), and the honest validators are at least half of the committee
(`3f ≤ n − 1`). -/
theorem half_committee (hp : ResetPremises tr H dg g ΔF a) {s' : Nat}
    (hs : cutZ sp.toParams g ≤ sp.ts s') :
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard := by
  sorry

/-- **(R4), the high-record lemma** (§16). From (R1): before `a` no honest row has height
`≥ H_z + 1` (HR.1 (c)), and its finality pair is below its height pair (G0.5), so the high record
coordinates start empty; every later record write at `h ≥ H_z + 1` names the entry at `h` of the
writing source's chain, which lies on the chain of a high origin (R1, rows), and the high origins
are pairwise comparable (R1), so two named entries at one height are equal (entry constancy on a
chain). Induction over the serialized honest client calls. -/
theorem high_records (hp : ResetPremises tr H dg g ΔF a)
    (hcomp : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B → HighOrigin tr H g x' i' j' B' →
      Compatible (tr.HonestBlocks H) B B')
    (hrows : ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root) :
    ∀ h, HZ tr H g + 1 ≤ h →
      {r | ∃ y ∈ H, ∃ i, (tr.state y i).record.target h = some r ∨
        r ∈ (tr.state y i).record.timeout h ∨
        (tr.state y i).record.lock h = some r}.Subsingleton := by
  sorry

end Consensus.Goldilocks.Healing

end
