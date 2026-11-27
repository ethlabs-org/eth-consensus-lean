module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Finite healing service and reset premises under growing faults

Delivery remains owed after its sender is compromised. A receiver is required to be honest
at its receiving call; only signed-row service is restricted to the finite horizon.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The healed floors of the reset `a`: lock members from `cleanLabel a + k + 2`, origins from
`k − 1` labels later (the floors `(r, r + k − 1)` of `Continuation`). -/
abbrev healedLockFloor (sp : ACParams) (a : Time) : Nat := cleanLabel sp a + sp.k + 2

/-- The origin floor of the healed family of the reset `a`. -/
abbrev healedOriginFloor (sp : ACParams) (a : Time) : Nat := healedLockFloor sp a + sp.k - 1

/-- **The high-source cover through `b`** after the deep quarantine: the deep quarantine ends at
least `4Δ` before the drain of `a` is over (`drain_le`, the slack the seeded hand-over needs), and
the healed family of `a` satisfies S1 (members are pairwise compatible) and S2 (an honest vote
of a slot after a member's label extends it) through `b`. -/
structure HighSourceCover (g a b : Time) : Prop where
  drain_le : ∀ D, sp.deepDepth = some D →
    drainTime sp a + 4 * sp.Δ ≤ cutZ sp.toParams g + 4 * D * sp.Δ
  s1 : ∀ C s C' s',
    Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b →
    Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C' s' b →
      Compatible (tr.HonestBlocksAt H) C C'
  s2 : ∀ C s,
    Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b →
    ∀ y i e, Compose.Growing.HVoteAt tr H y i e → tr.time i ≤ b → s < e.msg.slot →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg C

/-- GST service, with signed rows consumed by the finite horizon. With a release hold `hold > 0`
a signing is served only when its signer is still honest at `max (time i) g + hold`
and the hold is within `ΔF` (`Generic.Service`); at `hold = 0` both are implied. -/
structure ResetService (g ΔF b : Time) (hold : Time := 0) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
    (∀ k ≤ i, tr.SignAt x k att → tr.time k = tr.time i → hold ≠ 0 →
      x ∈ H (max (tr.time i) g + hold)) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧
        tr.time k < tr.deadline y k (max (tr.time i) g) ΔF
  hold_le : hold ≤ ΔF

/-- The AC part of the reset service, with the positivity of the FG delay: message, block and
relay delivery from GST, without the signed-row clause. It needs neither a horizon nor a
release hold, so it is the service of a run that is only sleepy after a hand-over. -/
structure ACResetService (g ΔF : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B

variable {tr H} in
/-- The AC part of a reset service, at any horizon and release hold. -/
theorem ResetService.toAC {g ΔF b hold : Time} (hs : ResetService tr H g ΔF b hold) :
    ACResetService tr H g ΔF :=
  ⟨hs.deltaF, hs.message, hs.block, hs.relay⟩

/-- The shared HS premises through a finite observation horizon, with the release hold `hold` of
the signed-row service (`hold = 0`: the signer need only be honest at its signing). -/
structure HSSharedUpTo
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF b : Time) (hold : Time := 0) :
    Prop where
  noColl : Compose.NoCollRun dg tr
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  sync : ResetService tr H g ΔF b hold
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  noRestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k →
    tr.time k ≤ b → tr.time k ≤ gbar g
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)

/-- A finite reset and service, with node honesty read separately at each cut; the service at
release hold `hold` (default `0`). -/
structure ResetPremisesUpTo (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a b : Time)
    (committee : Time → Finset (Fin sp.n)) (beta : ℚ) (hold : Time := 0) : Prop where
  beta_le : beta ≤ 1 / 2
  run : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
    (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp committee))
  committee_pos : 0 < sp.committeeSize
  committeeFacts : Compose.Growing.CommitteeFacts tr H (Generic.dictOfTime sp committee)
  committeeFaults : Generic.CommitteeFaultsUpTo beta committee H g b
  noColl : Compose.NoCollRun dg tr
  sync : ResetService tr H g ΔF b hold
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b
  catchUp : CatchRun tr H g (2 * sp.Δ)
  noRestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k →
    tr.time k ≤ b → tr.time k ≤ gbar g
  timeoutDelay : ∀ s, sp.toParams.slotTime s + 6 * sp.Δ + ΔF ≤
    sp.toParams.slotTime (s + sp.toParams.δt)
  nonempty : (H b).Nonempty
  /-- With deep FG sources on at depth `D`: the horizon is within the deep quarantine after `c_z`
  (`c_z + 4DΔ`), so no high deep FG source is used by `b`; or the high sources are covered by the
  healed family of `a`, with S1 and S2 through `b`. -/
  deepCover : ∀ D, sp.deepDepth = some D →
    b ≤ cutZ sp.toParams g + 4 * D * sp.Δ ∨ HighSourceCover tr H g a b

end Consensus.Goldilocks.Healing.Growing

end
