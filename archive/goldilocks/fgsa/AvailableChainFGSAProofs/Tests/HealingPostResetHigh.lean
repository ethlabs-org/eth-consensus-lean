module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHigh -- shake: keep (THigh fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.13:2668–2813, H.14:2826–2861; post-reset plan J3,
Risks; B1/B13/B17/B18. Pure/model and conditional package fixtures.
DC: SAME selected-source labels and reset compatibility. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetHigh
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- pure/model: no selected action precedes the empty event cut.
example (C : FGBlock (Fin p.n)) (s : Slot) : ¬ SelectedBefore p c E rho 0 C s := by
  rw [SelectedBefore_def]
  rintro ⟨j, -, -, hj, -⟩
  exact Nat.not_lt_zero j hj

-- conditional package: an emitted source projects to the selected-action predicate.
example {i : Nat} {C : FGBlock (Fin p.n)} {s : Slot}
    (h : SourceBefore p c E rho i C s) : SelectedBefore p c E rho i C s :=
  selectedBefore_of_sourceBefore p c E rho h

section Consumers
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hScopes : LossServiceScope p c E rho)
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
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec hScopes mono emittedNonempty emittedName writes xing origin h0r

variable (cap : RCap p c E rho) (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

variable (hSame : SameLabelServiceScope E rho w.sStar)

include cap source hSame rowCovered

-- conditional package: A supplies the label bound; the no-row clause restates hnoRow.
example {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C)
    (hnoRow : ∀ j a, ¬ HonestRowAt p c E rho j x r a) :
    w.sStar ≤ r * p.R ∧ ¬ ∃ j a, HonestRowAt p c E rho j x r a := by
  refine ⟨postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap h0r hx hsrc hh, ?_⟩
  rintro ⟨j, a, ha⟩
  exact hnoRow j a ha

-- conditional package: B2 consumes the actual selected source, without a row witness.
example {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C) :
    Block.Compatible (eraseFG C) w.CStar :=
  postReset_selected_reset_compatible p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r hSame cap source rowCovered hx hsrc hh

-- conditional package: D0 supplies general keep without the seven-field carrier.
example {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))} {C B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (htick : ∃ t, rho.events[i]? = some (V2.Event.tick x t) ∧
      SA.releaseTime p.toParams w.sStar ≤ t)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (hreset : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar)
    (hhigh : ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K'))
    (path : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hBC : Block.Compatible (eraseFG B) w.CStar)
    (hBK : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K)) : Kept p c E rho i x X B := by
  obtain ⟨-, -, -, -, -, hk⟩ := postReset_rKeep_body_reset p c E rho
    hrec hScopes mono emittedNonempty emittedName writes xing origin h0r
    i x X C hx hX htick hC he cover hreset hhigh
  exact hk B path hBC hBK

end Consumers
end AvailableChain.FGSA.Run.Tests.HealingPostResetHigh
end
