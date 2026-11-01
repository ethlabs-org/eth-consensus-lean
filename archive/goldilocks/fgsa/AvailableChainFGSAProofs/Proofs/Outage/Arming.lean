module
public import AvailableChainFGSAClaims.Statements.Channels

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §§6–8; plan O-ARM §4 fields 1–9. Class (iii).
DC: INTENTIONAL; the finite-cut arming certificate of a protected stable
read B. The label `l` is the last gate label at or before the cut and
`l + 1` is the pending label. The witnesses are the actual origin
(node `u`, label `s`, result `C`, tick `iₛ`) and the comparison maximum `D`
with its FG lift `Dh`. All later fields refer to the same witnesses.
Field 9 quantifies over actual pending gate ticks only. -/
structure ArmingCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ b₁ : Time)
    (B : Block) (l : Slot) (u : V) (s : Slot) (C : Block) (iₛ : Nat) (D : Block)
    (Dh : FGBlock (Fin p.n)) : Prop where
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 1: the actual origin of the protected read. -/
  origin_honest : u ∈ rho.honest
  origin_pos : 1 ≤ s
  origin_tick : IsGateTick p c rho iₛ u s
  origin_passed : gatePassedAt p c E rho iₛ
  origin_result : gateResultAt p c E rho iₛ = some (some C)
  origin_time : SA.gateTime p.toParams s ≤ T
  origin_cover : Block.Preceq B C
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 2: the actual comparison maximum through label `l` at the cut. -/
  max_lift : eraseFG Dh = D
  max_read : Block.Preceq B D
  max_mem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀)
  max_le : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
    Block.Preceq X D
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 3: the cut arithmetic and the mode label distance. -/
  gate_le_cut : SA.gateTime p.toParams l ≤ b₀
  cut_lt_pending : b₀ < SA.gateTime p.toParams (l + 1)
  early_eq_gate : SA.earlyTime p.toParams (l + 1) = SA.gateTime p.toParams l
  end_lt_deadline : b₁ < SA.gateTime p.toParams (l + 1) + L p
  mode_gap : if fast then s + 2 ≤ l + 1 else s + p.k ≤ l + 1
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 4: actual honest sources and named row entries before the pending gate. -/
  source_below : ∀ y r X, y ∈ rho.honest →
    p.actionTime r < SA.gateTime p.toParams (l + 1) →
    actionSource p c E rho y r = some (some X) → Block.Preceq X D
  entry_below : ∀ i y r (a : RowWire p.n) e, HonestRowAt p c E rho i y r a →
    p.actionTime r < SA.gateTime p.toParams (l + 1) →
    namedEntry a.payload.height_pair = some e → EntryBelow p e Dh
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 5: every honest local state up to the strict pending read. -/
  prefix_state : ∀ i y, i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
    i ≤ rho.events.length → y ∈ rho.honest →
    Block.Preceq (F_at p c E rho i y) D ∧ Block.Preceq (J_at p c E rho i y) D ∧
    Block.Preceq (eraseFG (FGSA.controls p (storeAt p c E rho i y)).Z) D ∧
    (FGSA.controls p (storeAt p c E rho i y)).contest = false ∧
    (FGSA.controls p (storeAt p c E rho i y)).lo ≤ (heightView p Dh).h ∧
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 6: the last healthy label-`(l + 1)` batch, at every honest receiver. -/
  healthy_batch : ∀ y (q : Fin p.n), y ∈ rho.honest →
    rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
    E.awake (rho.seatOf (.base (.head (l + 1))) q) (SA.voteTime p.toParams (l + 1)) = true →
    ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
      Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
      baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho k y).base.votes ∧
      K ∈ (storeAt p c E rho k y).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho k y).base
        (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
        SA.earlyTime p.toParams (l + 1) ∧
      GridCO.stampBlock (storeAt p c E rho k y).base K < SA.earlyTime p.toParams (l + 1)
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 7: coverage, duties and F compatibility before the pending gate. -/
  pending_cover : ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Preceq B (S_at p c E rho (timeIdx rho t) y)
  pending_duties : ∀ y o t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → V2.D.Run.emits E rho y o t →
    (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)
  pending_compat : ∀ y t, y ∈ rho.honest → 0 ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Compatible B (F_at p c E rho (timeIdx rho t) y)
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 8: the unique in-flight label and its honest HEAD emissions. -/
  inflight_label : ∀ r : Slot, SA.voteTime p.toParams r ≤ SA.gateTime p.toParams (l + 1) →
    SA.gateTime p.toParams (l + 1) < SA.releaseTime p.toParams r → r = l + 2
  inflight_heads : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
    o.auth = .seat (.base (.head (l + 2))) q → HeadTargetAtEmission p c E rho y o t H →
        Block.Preceq B H
  /-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Field 9: the input of every actual pending gate tick. -/
  pending_input : ∀ i y, IsGateTick p c rho i y (l + 1) → y ∈ rho.honest →
    let P := FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
    GridCO.savedGenuine P.base (l + 1) = none ∧
    (∃ Cj, SA.Root.confirmationFrom p.toParams (eraseFG P.fg.F) (FGSA.actView P) (l + 1) =
      some Cj ∧ Block.Preceq D Cj) ∧
    (∀ row ∈ (FGSA.actView P).obligations, Block.Preceq row.1 D) ∧
    B ∈ (FGSA.actView P).blocks ∧ Block.Compatible (F_at p c E rho i y) B ∧
    (fast = true → SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams (FGSA.actView P) (l + 1) B) ∧
    (fast = false → p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine P.base (l + 1 - (a + 1)) = some (some Ca) ∧ Block.Preceq B Ca)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §§6–8; plan O-ARM §4. Class (iii). DC: INTENTIONAL; the arming
certificate with existential witnesses at the cut label of `b₀`. -/
def ArmingData (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ b₁ : Time)
    (B : Block) : Prop :=
  ∃ u s C iₛ D Dh, ArmingCert p c E rho fast T b₀ b₁ B
    (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) u s C iₛ D Dh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §§6–8; plan O-ARM §4. Class (iii). DC: INTENTIONAL; equation
for this module's certificate predicate. -/
theorem ArmingData_def (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ b₁ : Time)
    (B : Block) :
    ArmingData p c E rho fast T b₀ b₁ B =
      ∃ u s C iₛ D Dh, ArmingCert p c E rho fast T b₀ b₁ B
        (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) u s C iₛ D Dh := by
  apply propext
  constructor <;> exact fun h => h

end AvailableChain.FGSA.Run
end
