module
public import AvailableChainFGSAProofs.Proofs.Finality.FrontierBound -- shake: keep (FF7 tests)

set_option linter.privateModule false
set_option maxRecDepth 8192

namespace AvailableChain.FGSA.Run.Tests.FrontierBound

open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 3, δt := 6, RLarge := by decide, digest :=
        fun d => ⟨d.slot + 1⟩ }

private def targets (h : Nat) (U : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h U.root false, none⟩, ⟨1, .vote h U.root false, none⟩,
    ⟨2, .vote h U.root false, none⟩]
private def opening : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ 0 (targets 1 .genesis)
private def entry : FGBlock (Fin 4) := .node opening 2 ⟨2⟩ 0 (targets 2 opening)
private def archive : Finset (FGBlock (Fin 4)) := {.genesis, opening, entry}

-- Pure/model: H_t ≤ m+1, including an ancestor that carries older rows.
example : (heightView p opening).h = 2 ∧
    (targets 1 .genesis).toFinset ⊆ chainRows entry ∧
    frontierView (heightView p) archive ≤ (heightView p opening).h + 1 := by
  decide +kernel

-- Pure/model: H_t > m+1 is excluded for this archive.
example : ¬ (heightView p opening).h + 1 < frontierView (heightView p) archive := by
  decide +kernel

-- Pure/model: height(U₁) = H_t is allowed; the first cap is inclusive.
example : (heightView p entry).h = frontierView (heightView p) archive ∧
    (heightView p entry).h = (heightView p opening).h + 1 := by
  decide +kernel

-- Pure/model: the supremum proof needs no maximum or nonempty-frontier premise.
example : frontierView (heightView p) ∅ = 1 ∧
    (∅ : Finset (Fin 4)).sup (fun _ => (0 : Nat)) = 0 := by
  decide +kernel

private def laterRow : RowWire 4 :=
  ⟨.seat .fg 0, .vote ⟨.vote 2 opening.root false, none⟩⟩
private def laterOrigin : V2.D.Run (Fin 4) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 30
  events := [.tick 0 18, .deliver 0 (ofRow p laterRow) 18]
  seatOf := fun l j => match l with | .base _ => j | .prop _ => 0
  input := fun _ _ => ()

-- Pure/model: a row in an old declared block can have a later delivery time.
-- The delivery at t is included by timeIdx and excluded by the read-phase cut.
-- This tests event cuts only; it is not an ExecutionValid or HealingInput witness.
example : entry.slot = 2 ∧ entry.slot < 3 ∧
    SA.proposalTime p.toParams entry.slot < (18 : Time) ∧
    laterRow.toRow? = some ⟨0, .vote 2 opening.root false, none⟩ ∧
    (⟨0, .vote 2 opening.root false, none⟩ : Row (Fin 4)) ∈ chainRows entry ∧
    eventTime laterOrigin 0 = some (p.actionTime 1) ∧
    laterOrigin.events[1]? = some (.deliver 0 (ofRow p laterRow) 18) ∧
    afterTicksIdx laterOrigin 18 = 1 ∧ timeIdx laterOrigin 18 = 2 ∧
    ¬ (18 : Time) < p.actionTime 1 := by
  decide +kernel

section Conditional
variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (w : HealingWitness) (ΔF : Time) (input : HealingInput p c E rho w ΔF)
    (r : Nat) (A : Block) (Afg : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (r * p.R) A)
    (eraseA : eraseFG Afg = A) (highA : w.M + 1 ≤ (heightView p Afg).h)
    (t : Time) (ht : t < p.actionTime r)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

-- Conditional package: the listed opening, healing and origin inputs prove the cap.
include base faultQ input hA eraseA highA ht hNames hOrigin in
example : honestFrontier p c E rho t ≤ (heightView p Afg).h + 1 ∧
    ¬ (heightView p Afg).h + 1 < honestFrontier p c E rho t := by
  have cap := honestFrontier_le_opening p c E rho base faultQ w ΔF input
    r A Afg hA eraseA highA t ht hNames hOrigin
  exact ⟨cap, not_lt.mpr cap⟩
end Conditional

end AvailableChain.FGSA.Run.Tests.FrontierBound
