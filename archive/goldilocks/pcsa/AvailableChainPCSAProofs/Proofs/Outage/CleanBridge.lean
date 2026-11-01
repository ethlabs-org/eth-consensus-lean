module
public import AvailableChainPCSAProofs.Proofs.Outage.SlowRun

public section

/-! The Clean-lane ARM item (b) of ARM-healthy (pcsa34-r4.3 §5.4.2) from the
Clean facts at the pending labels. CI and `CleanDisseminationClaim` reach only
the labels with `d_j ≤ b₀`; ARM (b) reads the honest acks of every label with
`v_j < b₀`. `CutChain` records four facts at the cut: honest results are
not empty (5.2.2 (c)), the results chain at the labels whose early reads are
in the prefix (CI (i)), the HEAD cone (a block below every honest HEAD of
label `i − 1` with `e_{i−1} ≤ b₀` is below every honest HEAD of label `i`),
and dissemination at the pending label (5.2.3). ARM (b) uses only the
vote-time cone (`v_i ≤ b₀`) and dissemination. The Outage assembly proves
every field; the HEAD cone records `CleanConeItems` (full cone, C10) and
`CleanVoteConeItems` (vote-time cone, C8) come from the Clean-lane cone
theorems. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

variable (p c) in
omit [Fintype V] in
/-- [pcsa34-r4.3 §5.2.2 (i), (c), §5.2.3, §5.5 step 2] The Clean facts
of one run at the pending labels of the cut `b₀`. -/
structure CutChain (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ : Time) :
    Prop where
  nonempty : ∀ i : Slot, SA.earlyTime p.toParams i ≤ b₀ → ∀ x ∈ rho.honest,
    gateResultAt p c E rho x i ≠ some none
  chain : ∀ (i i' : Slot) (x y : V) (X Y : Block), i < i' → SA.earlyTime p.toParams i' ≤ b₀ →
    x ∈ rho.honest → y ∈ rho.honest →
    gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
    Block.Preceq X Y
  cone : ∀ (i : Slot) (B : Block), 0 < i → SA.earlyTime p.toParams (i - 1) ≤ b₀ →
    (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
    ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H
  dis : ∀ (s : Slot) (y : V) (B : Block), HonestAckAt p c E rho y s B →
    (SA.voteTime p.toParams (s + 1) ≤ b₀ →
      ∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
    (SA.earlyTime p.toParams (s + 1) ≤ b₀ → ∀ x ∈ rho.honest, ∀ X,
      gateResultAt p c E rho x (s + 1) = some (some X) → Block.Preceq B X)

/-- [pcsa34-r4.3 §5.2.2, §5.2.3] The Clean facts at the pending labels of every
clean stage-1 run with `a < ⌈n/2⌉`. -/
def CleanCutChainItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      CutChain p c E rho b₀

theorem CleanCutChainItems_def (p : Params) : CleanCutChainItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
        CutChain p c E rho b₀) := by
  delta CleanCutChainItems
  rfl

/-- [pcsa34-r4.3 §5.5 step 2; tip-stability `pending-cone-repair.md`] The HEAD
cone (`CutChain.cone`) in every clean stage-1 run with `a < ⌈n/2⌉`: for
`0 < i` with `e_{i−1} ≤ b₀`, a block below every honest HEAD of label `i − 1`
is below every honest HEAD of label `i`. The Outage assembly proves it
(`pcsa_cleanConeItems`). -/
def CleanConeItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (i : Slot) (B : Block), 0 < i → SA.earlyTime p.toParams (i - 1) ≤ b₀ →
      (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
      ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H

theorem CleanConeItems_def (p : Params) : CleanConeItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (i : Slot) (B : Block), 0 < i → SA.earlyTime p.toParams (i - 1) ≤ b₀ →
        (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
        ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H) := by
  delta CleanConeItems
  rfl

/-- [pcsa34-r4.3 §5.4.2 (b)] The vote-time HEAD cone in every clean stage-1 run
with `a < ⌈n/2⌉`: the cone of `CleanConeItems` at the labels `i` with
`v_i ≤ b₀`. C8 reads only this form. The Outage assembly proves it
(`pcsa_cleanVoteConeItems`). -/
def CleanVoteConeItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (i : Slot) (B : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
      (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
      ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H

theorem CleanVoteConeItems_def (p : Params) : CleanVoteConeItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (i : Slot) (B : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
        (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
        ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H) := by
  delta CleanVoteConeItems
  rfl

/-! ### Slot times -/

omit [DecidableEq V] [Fintype V] in
/-- The gate of the previous label is the early time. -/
theorem pcsa_gate_pred_early (s : Slot) (hs : 0 < s) :
    SA.gateTime p.toParams (s - 1) = SA.earlyTime p.toParams s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
  rw [Nat.add_sub_cancel]
  change 4 * p.Δ * (s' : Int) + 6 * p.Δ = 4 * p.Δ * ((s' + 1 : Nat) : Int) + 2 * p.Δ
  push_cast
  ring

omit [DecidableEq V] [Fintype V] in
/-- Early times increase with the slot. -/
theorem pcsa_early_mono {a b : Slot} (h : a ≤ b) :
    SA.earlyTime p.toParams a ≤ SA.earlyTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 2 * p.Δ ≤ 4 * p.Δ * (b : Int) + 2 * p.Δ
  have : (a : Int) ≤ b := by exact_mod_cast h
  nlinarith

omit [DecidableEq V] [Fintype V] in
/-- The early time of a slot is before the vote time of every later slot. -/
theorem pcsa_early_lt_vote_of_lt {a b : Slot} (h : a < b) :
    SA.earlyTime p.toParams a < SA.voteTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 2 * p.Δ < 4 * p.Δ * (b : Int) + p.Δ
  have : (a : Int) + 1 ≤ b := by exact_mod_cast h
  nlinarith

omit [Fintype V] in
/-- [§5.5 step 2] The HEAD cone along the labels: a block below every honest
HEAD of label `j` is below every honest HEAD of label `j + n + 1` when
`e_{j+n} ≤ b₀`. -/
theorem pcsa_cone_up {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (hK : CutChain p c E rho b₀) {B : Block} {j : Slot}
    (hB : ∀ y G, HonestHeadAt p c E rho y j G → Block.Preceq B G) :
    ∀ n : Nat, SA.earlyTime p.toParams (j + n) ≤ b₀ →
      ∀ x H, HonestHeadAt p c E rho x (j + n + 1) H → Block.Preceq B H := by
  intro n
  induction n with
  | zero =>
    intro he
    exact hK.cone (j + 0 + 1) B (Nat.succ_pos _) he hB
  | succ n ih =>
    intro he
    exact hK.cone (j + (n + 1) + 1) B (Nat.succ_pos _) he
      (ih (le_trans (pcsa_early_mono (Nat.le_succ (j + n))) he))

omit [Fintype V] in
/-- [§5.4.2 (b)] The vote-time HEAD cone along the labels: given the one-step
cone at the labels `i` with `v_i ≤ b₀`, a block below every honest HEAD of
label `j` is below every honest HEAD of label `j + n + 1` when
`v_{j+n+1} ≤ b₀`. -/
theorem pcsa_voteCone_up {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (hvc : ∀ (i : Slot) (B : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
      (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
      ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H)
    {B : Block} {j : Slot} (hB : ∀ y G, HonestHeadAt p c E rho y j G → Block.Preceq B G) :
    ∀ n : Nat, SA.voteTime p.toParams (j + n + 1) ≤ b₀ →
      ∀ x H, HonestHeadAt p c E rho x (j + n + 1) H → Block.Preceq B H := by
  intro n
  induction n with
  | zero =>
    intro hv
    exact hvc (j + 0 + 1) B (Nat.succ_pos _) hv hB
  | succ n ih =>
    intro hv
    exact hvc (j + (n + 1) + 1) B (Nat.succ_pos _) hv
      (ih (le_trans (pcsa_vote_mono (Nat.le_succ (j + n + 1))) hv))

omit [Fintype V] in
/-- The vote-time cone of one run from its full cone (`e_{i−1} < v_i`). -/
theorem pcsa_cutChain_voteCone {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)}
    {b₀ : Time} (hK : CutChain p c E rho b₀) :
    ∀ (i : Slot) (B : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
      (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
      ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H :=
  fun i B hi hv hB =>
    hK.cone i B hi (le_of_lt (lt_of_lt_of_le (pcsa_early_lt_vote_of_lt (Nat.sub_lt hi
      Nat.one_pos)) hv)) hB

/-- The vote-time cone from the full cone (`e_{i−1} < v_i`). -/
theorem pcsa_cleanVoteConeItems_of_cone (p : Params) (hcone : CleanConeItems p) :
    CleanVoteConeItems p := by
  rw [CleanVoteConeItems_def]
  rw [CleanConeItems_def] at hcone
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr i B hi hv hB
  exact hcone c m E rho b₀ ΔF hC hf hfr i B hi
    (le_of_lt (lt_of_lt_of_le (pcsa_early_lt_vote_of_lt (Nat.sub_lt hi Nat.one_pos)) hv)) hB

/-! ### ARM item (b) -/

omit [Fintype V] in
/-- An honest ack of slot `s` has a gate result of label `s − 1` at its node. -/
theorem pcsa_ack_gateResult (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {y : V} {s : Slot} {X : Block} (h0 : 0 < s)
    (hX : HonestAckAt p c E rho y s X) :
    (∃ r, gateResultAt p c E rho y (s - 1) = some r) ∧
      SA.earlyTime p.toParams s ≤ rho.horizon := by
  obtain ⟨-, -, hread⟩ := hX
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, -⟩ := Option.map_eq_some_iff.mp hread
  obtain ⟨k, hk, -⟩ := pcsa_postClock_some E rho hnd
  refine ⟨?_, pcsa_tick_le_horizon E rho hs hk⟩
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def, pcsa_gate_pred_early s h0,
    pcsa_tickIdx_of_event E rho hs hk]
  exact ⟨_, rfl⟩

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (b)] In a clean prefix, every honest ack
of a later label with `v_{s'} < b₀` extends the target of a PC held by an
honest node, given pending-label dissemination at the vote cutoff (`hdis`)
and the vote-time HEAD cone (`hvc`). Dissemination puts the target
below every honest HEAD of label `s + 1`; the vote-time cone carries it to
the label of the ack. -/
theorem pcsa_cleanArmAcks_of_vote (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho)
    (hdis : ∀ (s : Slot) (y : V) (B : Block), HonestAckAt p c E rho y s B →
      SA.voteTime p.toParams (s + 1) ≤ b₀ →
      ∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H)
    (hvc : ∀ (i : Slot) (B : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
      (∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G) →
      ∀ x H, HonestHeadAt p c E rho x i H → Block.Preceq B H) :
    CleanArmAcks p c E rho b₀ := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  rw [CleanArmAcks_def]
  intro v hv T d _ _ hd y s' X hs' hvs hX
  rw [pcsa_storeAt_index E rho hs] at hd
  obtain ⟨-, x₀, hx₀⟩ := pcsa_held_pc_ack E rho h hf v hv _ d hd
  obtain ⟨z, hz⟩ := pcsa_honest_ack_head E rho h hf hfr y s' X hX
  have hB : ∀ x H, HonestHeadAt p c E rho x (d.slot + 1) H → Block.Preceq d.target H :=
    hdis d.slot x₀ d.target hx₀ (le_trans (pcsa_vote_mono hs') (le_of_lt hvs))
  rcases Nat.lt_or_eq_of_le hs' with hlt | heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact pcsa_voteCone_up hvc hB n (le_of_lt hvs) z X hz
  · rw [← heq] at hz
    exact hB z X hz

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (b)] The acks item from the Clean facts
at the pending labels (OPEN: `hK`): its dissemination field and the
vote-time form of its cone. -/
theorem pcsa_cleanArmAcks_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hK : CutChain p c E rho b₀) :
    CleanArmAcks p c E rho b₀ :=
  pcsa_cleanArmAcks_of_vote E rho hC hf hfr (fun s y B hB => (hK.dis s y B hB).1)
    (pcsa_cutChain_voteCone hK)

/-- [pcsa34-r4.3 §5.4.2] The two ARM items from the relay item and the Clean
facts at the pending labels (OPEN: `hK`). -/
theorem pcsa_cleanArmItems_of (p : Params) (hrel : CleanRelayItems p)
    (hK : CleanCutChainItems p) : CleanArmItems p := by
  rw [CleanArmItems_def]
  rw [CleanRelayItems_def] at hrel
  rw [CleanCutChainItems_def] at hK
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact ⟨hrel c m E rho b₀ ΔF hC hf hfr,
    pcsa_cleanArmAcks_of E rho hC hf hfr (hK c m E rho b₀ ΔF hC hf hfr)⟩

end AvailableChain.PCSA.Run
end
