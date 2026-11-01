module
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (FF7 fixtures)

set_option linter.privateModule false
set_option maxRecDepth 8192

namespace AvailableChain.FGSA.Run.Tests.Above
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 3, δt := 6, RLarge := by decide, digest :=
        fun d => ⟨d.slot + 1⟩ }

private def targets (h : Nat) (U : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h U.root false, none⟩, ⟨1, .vote h U.root false, none⟩,
    ⟨2, .vote h U.root false, none⟩]
private def opening : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ 0 (targets 1 .genesis)
private def first : FGBlock (Fin 4) := .node opening 2 ⟨2⟩ 0 (targets 2 opening)
private def second : FGBlock (Fin 4) := .node first 3 ⟨3⟩ 0 (targets 3 first)
private def archive : Finset (FGBlock (Fin 4)) := {.genesis, opening, first}

-- Pure/model: the first height equals H_t; only the second height is above H_t.
-- Paper 22:1438–1447; plan §7 F-ABOVE-B; DC: FF7.
example : frontierView (heightView p) archive = (heightView p first).h ∧
    ¬ frontierView (heightView p) archive < (heightView p first).h ∧
    FGBlock.Preceq first second ∧
    (heightView p second).h = (heightView p first).h + 1 ∧
    frontierView (heightView p) archive < (heightView p second).h := by
  decide +kernel

private def firstWindowPrefix : V2.D.Run (Fin 4) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 73
  events := []
  seatOf := fun l j => match l with | .base _ => j | .prop _ => 0
  input := fun _ _ => ()

-- Pure/model: a finite prefix admits the first FE window and excludes the second budget.
-- This is a horizon fixture; it is not an ExecutionValid or HealingInput witness.
example : Gen.Pure.FGoodE_W
      (fun s => 0 < s ∧ SA.proposalTime p.toParams s ≤ firstWindowPrefix.horizon)
      p.R (kappaF p 6) 2 ∧
    (24 : Time) + W_W p 6 1 ≤ firstWindowPrefix.horizon ∧
    ¬ (24 : Time) + W_W p 6 1 + W_W p 6 1 ≤ firstWindowPrefix.horizon := by
  constructor
  · rw [Gen.Pure.FGoodE_W_def]
    exact ⟨by decide +kernel, by decide +kernel,
      ⟨12, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
  · decide +kernel

-- Conditional package: the same prefix cannot satisfy the frozen two-window premise.
example (E : Generic.Env (Fin 4)) (G : Time) (w : HealingWitness) (form : FinFormW) :
    ¬ AboveFrontierPrem_W p unitCodec G 6 form 1 w E firstWindowPrefix ⟨24⟩ := by
  intro h
  have hh := h.hhor
  have hn : ¬ (24 : Time) + W_W p 6 1 + W_W p 6 1 ≤ firstWindowPrefix.horizon := by
    decide +kernel
  exact hn hh

-- Pure/model: κ=R, ΔF>2Δ; both selected carrier tails precede their strict deadlines.
-- The second trigger is the first kernel deadline, not the first carrier time.
example : kappaF p 6 = p.R ∧ 2 * p.Δ < (6 : Time) ∧
    W_W p 6 1 = 49 ∧
    carrierTimeW p 6 (2 + 2) = 60 ∧ kernelDeadlineW p 6 (2 + 2) = 61 ∧
    carrierTimeW p 6 (6 + 2) = 108 ∧ kernelDeadlineW p 6 (6 + 2) = 109 ∧
    carrierTimeW p 6 (2 + 2) < kernelDeadlineW p 6 (2 + 2) ∧
    carrierTimeW p 6 (6 + 2) < kernelDeadlineW p 6 (6 + 2) ∧
    kernelDeadlineW p 6 (2 + 2) < 24 + W_W p 6 1 ∧
    kernelDeadlineW p 6 (6 + 2) < kernelDeadlineW p 6 (2 + 2) + W_W p 6 1 ∧
    kernelDeadlineW p 6 (2 + 2) + W_W p 6 1 ≤ 24 + 2 * W_W p 6 1 ∧
    kernelDeadlineW p 6 (6 + 2) < 24 + 2 * W_W p 6 1 := by
  decide +kernel

-- Conditional package: exact frozen FE/F4 heads, including both receipt horizons.
example (p : Params) :
    AboveFrontierRecFEClaim_W p :=
  fgsa_aboveFrontierRecFE_W p
example (p : Params) :
    AboveFrontierRecF4Claim_W p :=
  fgsa_aboveFrontierRecF4_W p

end AvailableChain.FGSA.Run.Tests.Above
