module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked

public section

/-! # Goldilocks Healing, HR.4: the premises, the invariant and the run facts

`ResetPremises`, the invariant over the cut index (`VoteInv`; see `Lemmas/Healing/Retention`), and
the restart bound of `Healthy(g)` the steps use (`restart_le`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n)) {K : AC.CommitteeDict sp.n}

/-- **The premises of HR.4** for the reset `a`: a Goldilocks run from the committee start of the
slot dictionary `K` under `Healthy(g)` and `NoColl`, with the committee facts of `K` and CS2 for
every slot after the slot of `ḡ`, and `a` is the reset `a_z`. -/
structure ResetPremises (K : AC.CommitteeDict sp.n) (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a : Time) :
    Prop where
  run : GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K)
  healthy : tr.HealthyRun H ΔF g
  noColl : Compose.NoCollRun dg tr
  reset : IsReset tr H g a
  /-- The committee facts of `K`. -/
  committee : Compose.Growing.CommitteeFacts tr (fun _ => H) K
  /-- CS2 for the slots after `ḡ`. -/
  twoK : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
    2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard

/-- Reset service keeps the AC message/block/relay contracts, but requests only
signed-attestation delivery by the deadline, without an attestation processing lower bound. -/
structure ResetService (g ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x ∈ H, ∀ i att, tr.SignAt x i att →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧
        tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- The AC part of the reset service: message, block and relay delivery, without the
signed-attestation clause. -/
structure ACService (g : Time) : Prop where
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B

/-- The reset service's AC part. -/
theorem ResetService.toACService {g ΔF b : Time} (hs : ResetService tr H g ΔF b) :
    ACService tr H g :=
  ⟨hs.message, hs.block, hs.relay⟩

/-- Full GST supplies the weaker signed-attestation service. -/
theorem ResetService.of_gst {g ΔF b : Time} (h : tr.GSTRun H ΔF g) :
    ResetService tr H g ΔF b := by
  refine ⟨h.deltaF, fun x hx i m hs => h.message x hx i m hs trivial,
    fun x hx i B hs => h.block x hx i B hs trivial, h.relay, ?_⟩
  intro x hx i att hs y hy j hj _ hd
  obtain ⟨k, hk, hp, ht⟩ := h.attestation x hx i att (Or.inl hs) trivial y hy j hj hd
  exact ⟨k, hk, hp, ht⟩

/-- Finite reset premises. Reset existence and its cutoff are inputs, not consequences of
bounded health. GST quantifies actual receiver calls, so remains finite-satisfiable.
Progress and Catch are separate premises of the consumers that need them. -/
structure ResetPremisesUpTo (K : AC.CommitteeDict sp.n) (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a b : Time) : Prop where
  run : GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K)
  noColl : Compose.NoCollRun dg tr
  sync : ResetService tr H g ΔF b
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b
  /-- The committee facts of `K`. -/
  committee : Compose.Growing.CommitteeFacts tr (fun _ => H) K
  /-- CS2 for the slots after `ḡ`. -/
  twoK : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
    2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard

/-- Whole-run premises restrict to any horizon containing the actual reset. -/
theorem ResetPremises.toUpTo {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a b : Time}
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hab : a ≤ b) :
    ResetPremisesUpTo tr H K proposer dg g ΔF a b := by
  classical
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  obtain ⟨⟨y, hy, k, att, hs, hh, hka⟩, _⟩ := hp.reset
  change tr.time k = a at hka
  have hck : cutZ sp.toParams g < tr.time k := hka ▸ hca
  have hex : ∃ k, cutZ sp.toParams g < tr.time k := ⟨k, hck⟩
  have hfirst : FirstCutAfter tr (Nat.find hex) (cutZ sp.toParams g) :=
    ⟨fun q hq => not_lt.1 (Nat.find_min hex hq), Nat.find_spec hex⟩
  have hkb : tr.time (Nat.find hex) ≤ b :=
    (hp.run.time_mono (Nat.find_min' hex hck)).trans (hka ▸ hab)
  refine ⟨hp.run, hp.noColl, ?_, fun y hy t ht _ => hp.healthy.2.1 y hy t ht,
    hp.healthy.2.2, hp.reset, hab, ⟨Nat.find hex, hfirst, hkb⟩, hp.committee, hp.twoK⟩
  exact ResetService.of_gst tr H hp.healthy.1

/-- (R3) at the honest votes cast at cut `k`, for every high origin `(B, j)` of the run: a vote
of a slot `> j` extends `B`, and at that vote `B` is in the viable voter block tree or
`B ⪯ fc_root` (in the honest blocks). -/
def VoteInv (g : Time) (k : Nat) : Prop :=
  ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ ℓ e, AC.CastAt tr.projAC y k ℓ e →
    j < e.msg.slot →
      AC.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.F)

variable {tr H} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

theorem voteInv_iff {g : Time} {k : Nat} : VoteInv tr H g k ↔
    ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ ℓ e, AC.CastAt tr.projAC y k ℓ e →
      j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocks H) e.msg B ∧
        (B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
          Anc (tr.HonestBlocks H) B ℓ.frame.F) := Iff.rfl

/-- **No honest restart after `t_{slot(ḡ)+1}`** (`Healthy(g)`): a restart follows a time `u` at
which the node was asleep with no call in `[u, restart)`; `u ≥ ḡ` contradicts `Healthy(g)`, and
`u < ḡ` contradicts the tick at the public time `t_{slot(ḡ)+1} ≥ ḡ`, at which the node is awake. -/
theorem restart_le_before {b : Time} (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hp.run.sleep_of_restart y hy k hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr
      (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hp.awake y hy u hgu (huk.le.trans hkb))
  · obtain ⟨j, _x, _fgDue, hne, hcs, -⟩ :=
      hp.run.tick_of_awake y hy _ ((AC.gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [ACParams.ts]; ring⟩
      (hp.awake y hy _ hp₀ ((lt_of_not_ge hlt).le.trans hkb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hp.run.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- Whole-run specialization of the causal restart bound. -/
theorem restart_le (hp : ResetPremises tr H K proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : tr.RestartAt y k) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) :=
  restart_le_before (hp.toUpTo tr H (le_max_left a (tr.time k))) hy hk (le_max_right _ _)

end Consensus.Goldilocks.Healing

end
