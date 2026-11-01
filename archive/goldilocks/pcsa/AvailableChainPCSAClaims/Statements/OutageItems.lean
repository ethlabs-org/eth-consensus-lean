module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims; pcsa34-r4.3 §5.4.2, §5.5] The statement-only items of the
Outage lane: the lock row of a store, the two ARM-healthy items
(`CleanHeldPCRelay`, `CleanArmAcks`) and the slow P1 boundary at the cut
(`CleanSlowBoundary`). They are not claims and not fields of `PCSAClaims`.
The Outage lane proves C8 and C10 from them. The Outage assembly proves the
relay item, and derives the others from the Clean claims and the Clean HEAD
cone theorems (records `CleanVoteConeItems` for C8 and `CleanConeItems` for
C10). -/

namespace AvailableChain.PCSA

variable {n : Nat}

/-- A lock row on `A` of level `g` with deadline at least `D`. -/
def LockRow (st : State n) (A : Block) (g : Nat) (D : Time) : Prop :=
  ∃ row ∈ st.base.obligations, row.1 = A ∧ row.2.1 = g ∧ D ≤ row.2.2

theorem LockRow_def (st : State n) (A : Block) (g : Nat) (D : Time) :
    LockRow st A g D = ∃ row ∈ st.base.obligations, row.1 = A ∧ row.2.1 = g ∧ D ≤ row.2.2 := by
  delta LockRow
  rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

variable (p c) in
omit [Fintype V] in
/-- [Clean-lane fact; pcsa34-r4.3 §5.4.2 ARM-healthy (a), §5.2.3 relay] In a
clean prefix up to `b₀`, a PC held by an honest node at `T ≥ 0` with
`T + Δ ≤ b₀` is held by every honest node after the ticks of every time
`≥ T + Δ` (strict relay within `Δ`, stage-1 monotonicity). -/
def CleanHeldPCRelay (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ : Time) :
    Prop :=
  ∀ v ∈ rho.honest, ∀ (T : Time) (d : PC p.n), 0 ≤ T → T + E.Δ ≤ b₀ →
    d ∈ (storeAt p c E rho v T).pcs →
    ∀ y ∈ rho.honest, ∀ t : Time, T + E.Δ ≤ t → PCStampedBefore p c E rho y t d.slot d.target

variable (p c) in
omit [Fintype V] in
theorem CleanHeldPCRelay_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (b₀ : Time) : CleanHeldPCRelay p c E rho b₀ =
      (∀ v ∈ rho.honest, ∀ (T : Time) (d : PC p.n), 0 ≤ T → T + E.Δ ≤ b₀ →
        d ∈ (storeAt p c E rho v T).pcs →
        ∀ y ∈ rho.honest, ∀ t : Time, T + E.Δ ≤ t →
          PCStampedBefore p c E rho y t d.slot d.target) := by
  delta CleanHeldPCRelay
  rfl

variable (p c) in
omit [Fintype V] in
/-- [Clean-lane fact; pcsa34-r4.3 §5.4.2 ARM-healthy (b), CI 5.2.2 (d)] In a
clean prefix up to `b₀`, for a PC held by an honest node at `T ≥ 0` with
`T + 3Δ ≤ b₀`, every honest ack of a later slot `s'` with `v_{s'} < b₀` has a
target `⪰` the PC target. -/
def CleanArmAcks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ (T : Time) (d : PC p.n), 0 ≤ T → T + 3 * E.Δ ≤ b₀ →
    d ∈ (storeAt p c E rho v T).pcs →
    ∀ y s' X, d.slot + 1 ≤ s' → SA.voteTime p.toParams s' < b₀ →
      HonestAckAt p c E rho y s' X → Block.Preceq d.target X

variable (p c) in
omit [Fintype V] in
theorem CleanArmAcks_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (b₀ : Time) : CleanArmAcks p c E rho b₀ =
      (∀ v ∈ rho.honest, ∀ (T : Time) (d : PC p.n), 0 ≤ T → T + 3 * E.Δ ≤ b₀ →
        d ∈ (storeAt p c E rho v T).pcs →
        ∀ y s' X, d.slot + 1 ≤ s' → SA.voteTime p.toParams s' < b₀ →
          HonestAckAt p c E rho y s' X → Block.Preceq d.target X) := by
  delta CleanArmAcks
  rfl

/-- [Clean-lane facts; pcsa34-r4.3 §5.4.2] Both ARM items hold in every
clean stage-1 run with `a < ⌈n/2⌉`. -/
def CleanArmItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    CleanHeldPCRelay p c E rho b₀ ∧ CleanArmAcks p c E rho b₀

theorem CleanArmItems_def (p : Params) : CleanArmItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      CleanHeldPCRelay p c E rho b₀ ∧ CleanArmAcks p c E rho b₀) := by
  delta CleanArmItems
  rfl

/-- [Clean-lane fact; pcsa34-r4.3 §5.4.2 ARM-healthy (a)] The relay item in
every clean stage-1 run with `a < ⌈n/2⌉`. The model relays every installed PC
(`handlesS`); `pcsa_heldPCRelay_of` proves the item when the PC target is
received within `Δ`. -/
def CleanRelayItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    CleanHeldPCRelay p c E rho b₀

theorem CleanRelayItems_def (p : Params) : CleanRelayItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      CleanHeldPCRelay p c E rho b₀) := by
  delta CleanRelayItems
  rfl

variable (p c) in
omit [Fintype V] in
/-- [Clean-lane facts; pcsa34-r4.3 §5.5 steps 1–2, CI 5.2.2] The facts at the
cut `b₀` for a block `A ≠ genesis` (`A = S_u(T)`) and the pending label `p*`
(`ps`, the first label with `d_{p*} > b₀`):
- every honest node at `b₀` has `S ⪰ A`, only locks compatible with `A`,
  and `A` stored (no lock on `A` is required before `d_{p*}`: no gate runs
  in `(b₀, d_{p*})`);
- the `k − 1` labels before `p*` have saved results `⪰ A` (step 1);
- every existing pending-gate read is nonempty and covers `A`, and is
  compatible with every lock held at `b₀` (step 2, CI (iv)); the gate exists
  only when `d_{p*}` is in the run;
- every honest ack of a label with `v_s ≤ b₀` is compatible with `A` (CL4 and
  dissemination);
- every honest HEAD of a label `r` with `v_r ≤ b₀ < q_r` and `q_r` in the run
  is compatible with `A` (CI (ii));
- every honest HEAD of a label `r` with `b₀ < v_r < d_{p*}` and `e_r` in the
  run is `⪰ A` (step 2: the HEAD past the cut, `r = p* + 1`). -/
structure CleanSlowBoundary (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (A : Block) (b₀ : Time) (ps : Slot) : Prop where
  pending : b₀ < SA.gateTime p.toParams ps
  first : ∀ s, b₀ < SA.gateTime p.toParams s → ps ≤ s
  window : p.k ≤ ps + 1
  stable : ∀ x ∈ rho.honest, Block.Preceq A (storeAt p c E rho x b₀).base.stableRecord
  locks : ∀ x ∈ rho.honest, ∀ row ∈ (storeAt p c E rho x b₀).base.obligations,
    Block.Compatible row.1 A
  tree : ∀ x ∈ rho.honest, A ∈ (storeAt p c E rho x b₀).base.blocks
  saved : ∀ x ∈ rho.honest, ∀ j < p.k - 1, ∃ C,
    GridCO.savedGenuine (storeAt p c E rho x b₀).base (ps - (j + 1)) = some (some C) ∧
      Block.Preceq A C
  result : ∀ x ∈ rho.honest, ∀ r, gateResultAt p c E rho x ps = some r → ∃ h, r = some h ∧
    Block.Preceq A h ∧
      ∀ row ∈ (storeAt p c E rho x b₀).base.obligations, Block.Compatible row.1 h
  acks : ∀ y s X, HonestAckAt p c E rho y s X → SA.voteTime p.toParams s ≤ b₀ →
    Block.Compatible X A
  heads : ∀ y r H, HonestHeadAt p c E rho y r H → b₀ < SA.releaseTime p.toParams r →
    SA.releaseTime p.toParams r ≤ rho.horizon → SA.voteTime p.toParams r ≤ b₀ →
    Block.Compatible H A
  pendingHeads : ∀ z r H, HonestHeadAt p c E rho z r H → b₀ < SA.voteTime p.toParams r →
    SA.voteTime p.toParams r < SA.gateTime p.toParams ps →
    SA.earlyTime p.toParams r ≤ rho.horizon → Block.Preceq A H

/-- [Clean-lane facts; pcsa34-r4.3 §5.5 steps 1–2] In every OUTAGE stage-1 run
with `a < ⌈n/2⌉`, the boundary facts hold for `S_u(T)` of every honest `u`
with `S_u(T) ≠ genesis`, for some pending label. -/
def CleanSlowItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
    Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ u ∈ rho.honest, (storeAt p c E rho u T).base.stableRecord ≠ .genesis →
      ∃ ps, CleanSlowBoundary p c E rho (storeAt p c E rho u T).base.stableRecord b₀ ps

theorem CleanSlowItems_def (p : Params) : CleanSlowItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
      Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ u ∈ rho.honest, (storeAt p c E rho u T).base.stableRecord ≠ .genesis →
        ∃ ps, CleanSlowBoundary p c E rho (storeAt p c E rho u T).base.stableRecord b₀ ps) := by
  delta CleanSlowItems
  rfl

end AvailableChain.PCSA.Run

end
