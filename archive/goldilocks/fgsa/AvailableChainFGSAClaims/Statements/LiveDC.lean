module
public import AvailableChainFGSAClaims.Statements.Regimes

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- LIVE-DC: FF5 window, raw proposer gap, then FF6 window.
DC Generic/Properties.lean:105: INTENTIONAL explicit finite-horizon deadline. -/
def liveDCDeadline_W (p : Params) (ΔF G : Time) (g : Nat) : Time :=
  2 * W_W p ΔF g + G

theorem liveDCDeadline_W_def (p : Params) (ΔF G : Time) (g : Nat) :
    liveDCDeadline_W p ΔF G g = 2 * W_W p ΔF g + G := rfl

/-- LIVE-DC; DC Generic/Properties.lean:99–112: SAME one honest proposal
strictly after the trigger. INTENTIONAL stable-record comparison and
strict-before finalization, with one FG representative for all three clauses. -/
def LiveDCConcl_W (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t deadline : Time) : Prop :=
  ∃ Xfg : FGBlock (Fin p.n),
    (∃ s : Slot, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      HonestProposal E rho (fgsaInterface p c) s (eraseFG Xfg)) ∧
    (∀ x, confirmedReader p c E rho x t →
      Block.Prec (V2.D.Run.readAt E rho t x).st.base.stableRecord (eraseFG Xfg)) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg deadline

theorem LiveDCConcl_W_def (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t deadline : Time) :
    LiveDCConcl_W p c E rho t deadline =
  (∃ Xfg : FGBlock (Fin p.n),
    (∃ s : Slot, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      HonestProposal E rho (fgsaInterface p c) s (eraseFG Xfg)) ∧
    (∀ x, confirmedReader p c E rho x t →
      Block.Prec (V2.D.Run.readAt E rho t x).st.base.stableRecord (eraseFG Xfg)) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg deadline) := by
  rfl

/-- LIVE-DC proof composition interface; DC Generic/Properties.lean:105.
INTENTIONAL internal service from the local FF5/FF6 results. Assembly supplies
its proved producer; it adds no premise to the top-level GST claim. -/
def LiveDCFromWindowsStatement (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (g : Nat) (t : Time),
    RecoverySleep₂ p c E rho G ΔF → recoveryStart p E ≤ t →
    (∃ U : FGBlock (Fin p.n),
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.Run.readAt E rho t x).st.base.stableRecord (eraseFG U)) ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (t + W_W p ΔF g)) →
    (∀ s X, HonestProposal E rho (fgsaInterface p c) s X →
      t ≤ V2.D.proposalTime (fgsaInterface p c) s →
      V2.D.proposalTime (fgsaInterface p c) s + W_W p ΔF g ≤ rho.horizon →
      ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = X ∧
        ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg
          (V2.D.proposalTime (fgsaInterface p c) s + W_W p ΔF g)) →
    t + liveDCDeadline_W p ΔF G g ≤ rho.horizon →
    LiveDCConcl_W p c E rho t (t + liveDCDeadline_W p ΔF G g)

theorem LiveDCFromWindowsStatement_def (p : Params) :
    LiveDCFromWindowsStatement p =
  (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (g : Nat) (t : Time),
    RecoverySleep₂ p c E rho G ΔF → recoveryStart p E ≤ t →
    (∃ U : FGBlock (Fin p.n),
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.Run.readAt E rho t x).st.base.stableRecord (eraseFG U)) ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (t + W_W p ΔF g)) →
    (∀ s X, HonestProposal E rho (fgsaInterface p c) s X →
      t ≤ V2.D.proposalTime (fgsaInterface p c) s →
      V2.D.proposalTime (fgsaInterface p c) s + W_W p ΔF g ≤ rho.horizon →
      ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = X ∧
        ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg
          (V2.D.proposalTime (fgsaInterface p c) s + W_W p ΔF g)) →
    t + liveDCDeadline_W p ΔF G g ≤ rho.horizon →
    LiveDCConcl_W p c E rho t (t + liveDCDeadline_W p ΔF G g)) := by
  rfl

end AvailableChain.FGSA.Run
end
