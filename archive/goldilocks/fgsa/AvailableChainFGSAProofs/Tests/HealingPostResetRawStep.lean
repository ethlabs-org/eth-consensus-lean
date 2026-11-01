module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw -- shake: keep (J5A fixtures)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRawStep -- shake: keep (J5-A-2)

set_option linter.privateModule false

/-! Blueprint 21 H.16:2924–2945; plan J5A; B1/B13/B17/B18.
DC: INTENTIONAL reset leases; SAME raw-result and reader witnesses.
Each fixture is labelled as a pure/model or conditional package. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetRawStep
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- C0, pure/model: the empty cut has no guarded stored read.
example (w : HealingWitness) : PostResetResetLeaseCompatible p c E rho w 0 := by
  rw [PostResetResetLeaseCompatible_def]
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

-- C2 base, conditional package: the exact reset cut is the base.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) :
    PostResetResetLeaseCompatible p c E rho w
      (afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) :=
  postReset_resetLease_base p c E rho h0r

-- C0, conditional package: a concrete live stored row uses the separate predicate.
example {w : HealingWitness} {i j : Nat} {x : V} {row : Block × Nat × Time}
    (hreset : PostResetResetLeaseCompatible p c E rho w i) (hji : j < i)
    (hx : x ∈ rho.honest)
    (hcut : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ j)
    (hrow : row ∈ (storeAt p c E rho j x).base.obligations)
    (hlive : (storeAt p c E rho j x).base.now < row.2.2) :
    Block.Compatible row.1 w.CStar := by
  rw [PostResetResetLeaseCompatible_def] at hreset
  exact hreset j hji x hx hcut row hrow hlive

-- C1, conditional package: delivery cannot create a row at any reader node.
example {i : Nat} {x y : V} {o : Obj p} {t : Time} {row : Block × Nat × Time}
    (he : rho.events[i]? = some (.deliver x o t))
    (hrow : row ∈ (storeAt p c E rho (i + 1) y).base.obligations) :
    row ∈ (storeAt p c E rho i y).base.obligations :=
  postReset_delivery_no_obligation p c E rho he hrow

-- C1/P2, conditional package: a renewed row remains compatible.
example (w : HealingWitness) (st : State p.n)
    (hlease : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) (B : Block) (g : Nat) (d : Time)
    (hB : Block.Compatible B w.CStar) {row : Block × Nat × Time}
    (hrow : row ∈ (GridCO.writeObligation st.base B g d).obligations)
    (hlive : st.base.now < row.2.2) : Block.Compatible row.1 w.CStar :=
  (postReset_resetLease_preserve p w st hlease 0 0 B g d hB).2.2.2 row hrow hlive

section Raw
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {s : Slot} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    {ix : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))

-- Shared supporter, conditional package: an actual raw result has an earlier honest HEAD.
example : ∃ k z, z ∈ rho.honest ∧
    rho.events[k]? = some (.tick z (SA.voteTime p.toParams s)) ∧
    Block.Preceq C (headAtIdx p c E rho k s) ∧ k < ix :=
  healing_gate_result_supporter p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) hgst hCut hx hix hres

-- A2, conditional package, anti-vacuity: LOW-support or vetoed concrete raw result.
example {B : FGBlock (Fin p.n)} (heB : eraseFG B = C)
    (_hcase : SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C <
        SA.releaseThreshold p.toParams ∨ ¬ gatePassedAt p c E rho ix)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJoin : joinedAtTime p (storeAt p c E rho iy y).restartTime
      (SA.releaseTime p.toParams s) = true)
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X)
    (hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 C) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) :=
  healing_first_transfer_raw_domain p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) hgst hx hix hres heB hy hiy hJoin hXv
    (fun W hW A _hFA hAW => hXc W hW A hAW) hD hlease

end Raw
-- Shared slow-window helper, conditional package: an actual saved result covers a reset extension.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {j : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest)
    (hsaved : GridCO.savedGenuine (storeAt p c E rho i x).base j = some (some C))
    (hB : Block.Preceq w.CStar (eraseFG B)) (hBC : Block.Preceq (eraseFG B) C) :
    E.t_GST < SA.voteTime p.toParams j :=
  postReset_slow_window_sync p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) h0r hx hsaved hB hBC

section ResetSteps
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include hrec emittedNonempty emittedName

-- P0, conditional package: the actual reset release removes every conflicting row.
example (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w) {x : V} (hx : x ∈ rho.honest)
    {row : Block × Nat × Time}
    (hrow : row ∈ (storeAt p c E rho
      (afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) x).base.obligations) :
    Block.Compatible row.1 w.CStar :=
  postReset_resetLease_at_reset p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName xing cap source
    h0r x hx row hrow

-- C2, conditional package, anti-vacuity: consume the NEW stored instance j=i.
example (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hinv : PostResetInv p c E rho w i) (hreset : PostResetResetLeaseCompatible p c E rho w i)
    {x : V} (hx : x ∈ rho.honest)
    (hcut : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ i)
    {row : Block × Nat × Time} (hrow : row ∈ (storeAt p c E rho i x).base.obligations)
    (hlive : (storeAt p c E rho i x).base.now < row.2.2) : Block.Compatible row.1 w.CStar := by
  have h := postReset_resetLease_succ p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    xing cap source h0r hinv hreset
  rw [PostResetResetLeaseCompatible_def] at h
  exact h i (Nat.lt_succ_self i) x hx hcut row hrow hlive

-- A1(b), conditional package: current result at event i can use the PREVIOUS carrier.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hinv : PostResetInv p c E rho w i) {x : V} {j : Slot} {C : Block}
    (hx : x ∈ rho.honest) (hj : w.sStar ≤ j) (hi : IsGateTick p c rho i x j)
    (hres : gateResultAt p c E rho i = some (some C)) : Block.Compatible w.CStar C :=
  postReset_raw_reset_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName h0r hinv
    hx hj hi hres le_rfl

-- P1, conditional package: a concrete passing write at event i has a compatible target.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hinv : PostResetInv p c E rho w i) {x : V} {j : Slot} {C B : Block} {g : Nat}
    (hx : x ∈ rho.honest) (hj : w.sStar ≤ j) (hi : IsGateTick p c rho i x j)
    (hpass : gatePassedAt p c E rho i) (hres : gateResultAt p c E rho i = some (some C))
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams j))) j C) :
    Block.Compatible B w.CStar :=
  postReset_noRewrite p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName h0r hinv
    hx hj hi hpass hres le_rfl hkey

end ResetSteps

section Release
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)

include hrec emittedNonempty emittedName writes

-- A1, conditional package, anti-vacuity: concrete raw result, release read and live row.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) {i k : Nat}
    (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {y x : V} {j : Slot} {C : Block} {nd : Node p} {row : Block × Nat × Time}
    (hy : y ∈ rho.honest) (hj : w.sStar ≤ j) (hk : IsGateTick p c rho k y j)
    (hres : gateResult p c E rho y j = some (some C)) (hki : k ≤ i) (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (SA.releaseTime p.toParams j) = some nd)
    (hrow : row ∈ nd.st.base.obligations) (hlive : nd.st.base.now < row.2.2) :
    Block.Compatible row.1 C :=
  postReset_raw_release_compatible p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName writes
    h0r hinv hresetNext hleaseNext hy hj hk hres hki hx hnd row hrow hlive


-- R5-moving-raw, conditional package: an actual raw result and a concrete moving lease.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {l : Slot} (hsl : s + 1 ≤ l)
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq C H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    {row : Block × Nat × Time}
    (hrow : row ∈ (FGSA.clock p (storeAt p c E rho iy y) t).base.obligations) :
    Block.Compatible row.1 C :=
  postReset_raw_moving_lease_compat p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName writes h0r
    hinv hresetNext hx hlabel hix hxi hres hsl hbatch hy hiy hyi hafter hupper row hrow

end Release

-- A3 domain and parent, conditional package: a concrete honest proposal consumes both wrappers.
example [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {r : Slot} {B : FGBlock (Fin p.n)} {Q : Block}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (hCut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG B) K)
    (hp : HonestProposal E rho (fgsaInterface p c) (r + 1) Q)
    (hdomain : ∀ ip, rho.events[ip]? = some
      (.tick (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))
        (SA.proposalTime p.toParams (r + 1))) →
      ∃ X : Finset (FGBlock (Fin p.n)),
        X ⊆ (storeAt p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))).fg.TF ∧
        (∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X) ∧
        B ∈ D_at p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1)) X)
    (hlease : ∀ ip, rho.events[ip]? = some
      (.tick (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))
        (SA.proposalTime p.toParams (r + 1))) →
      ∀ row ∈ (FGSA.clock p
        (storeAt p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1)))
        (SA.proposalTime p.toParams (r + 1))).base.obligations,
        Block.Compatible row.1 (eraseFG B)) : Block.Preceq (eraseFG B) Q.parent :=
  healing_proposal_moving_parent p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) mono hgst hCut hcover hp hdomain hlease

-- A4, conditional package: the concrete pre-event output index has the exact HealSuffix guard.
example [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {s : Slot} {B : Block} {cut : Nat}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCut : HealingWindow p E 1 s)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon)
    (hheads : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z l = some K → Block.Preceq B K)
    (hfinality : ∀ b, b ≤ cut → ∀ y, y ∈ rho.honest →
      V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b →
      Block.Compatible (F_at p c E rho b y) B)
    (hlease : ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y (s + 1) → j ≤ cut →
      Block.Preceq (F_at p c E rho j y) B →
      ∀ row ∈ (storeAt p c E rho j y).base.obligations, Block.Compatible row.1 B) :
    ∀ a y, y ∈ rho.honest → a ≤ cut →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq B (S_at p c E rho a y) :=
  healing_output_moving_suffix_at p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) mono hgst
    (fun l hsl _ hhor => (healing_recovery_joined_counts E rho hrec l
      (hCut.cut_mono (Nat.le_of_succ_le hsl)).2
      (hCut.cut_mono (Nat.le_of_succ_le hsl)).sync hhor).2)
    hguard hheads hfinality hlease

-- Lead step range, conditional package: the public zero producer starts the joint induction.
example {w : HealingWitness} (h0r : H0Reset p c E rho w) :
    PostResetResetLeaseCompatible p c E rho w 0 := postReset_resetLease_zero p c E rho h0r

-- Lead step range, conditional package: every cut before reset release has no raw source witness.
example (hs : V2.D.ScheduleWellFormed E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (hi : i ≤ afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) :
    PostResetRawTransfer p c E rho w i := postReset_rawTransfer_before_reset p c E rho hs h0r hi

-- C2 joint adapter, conditional package: the exact published prior triple is sufficient.
example [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hprev : PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      (∀ k, k < i → ∀ x v Q, x ∈ rho.honest → IsGateTick p c rho k x v →
        HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
        ∀ r, v = r * p.R →
          let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
          ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st))) :
    PostResetResetLeaseCompatible p c E rho w (i + 1) :=
  postReset_resetLease_step p c E rho hrec
    (healing_raw_service_scope_recovery E rho hrec mono) emittedNonempty emittedName
    xing cap source h0r hprev

end AvailableChain.FGSA.Run.Tests.HealingPostResetRawStep
end

namespace AvailableChain.FGSA.Run.Tests.HealingPostResetRawStep
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (source : TSrc p c E rho) (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)


-- R1-above, conditional package: an actual raw result strictly above CStar.
example {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (_hCB : Block.Preceq w.CStar C) (_hne : C ≠ w.CStar)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) :=
  postReset_raw_first_head p c E rho hrec emittedNonempty emittedName writes mono source xing
    origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hy hiy

-- C2-all, conditional package: the joint induction consumes the exact named step.
example (cap : RCap p c E rho) (source : TSrc p c E rho) :
    ∀ i, PostResetResetLeaseStep p c E rho w i :=
  postReset_resetLease_succ_all p c E rho hrec emittedNonempty emittedName mono xing h0r cap source


-- R4-all-cuts, conditional package: consume the exact joint successor, including terminal cuts.
example {i : Nat}
    (hprev : PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      PostResetOpeningDomain p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    (hfprovNext : PostResetFProv p c E rho w (i + 1)) :
    PostResetRawTransfer p c E rho w (i + 1) := by
  have hstep := postReset_rawTransfer_succ p c E rho hrec emittedNonempty emittedName writes
    mono source xing origin h0r i
  rw [PostResetRawStep_def] at hstep
  exact hstep hprev hresetNext hleaseNext hfprovNext

end AvailableChain.FGSA.Run.Tests.HealingPostResetRawStep
