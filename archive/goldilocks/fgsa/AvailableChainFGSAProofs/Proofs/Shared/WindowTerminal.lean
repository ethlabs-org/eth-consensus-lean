module
public import AvailableChainFGSAClaims.Statements.Windows
public import AvailableChainFGSA.Proofs.WindowTerminal

public section

namespace AvailableChain.FGSA.Run

/-- The named terminal-retention contract (f07w item 12, F8-W) follows from
the scalar window theorem. Stage 5 supplies the cap at the actual terminal parent. -/
theorem fgsa_terminalRetentionW (p : Params) : TerminalRetention_W p := by
  rw [TerminalRetention_W_def]
  intro A P d U ancestry retained latest cap
  have before : p.actionTime (0 + 1) - 1 < p.actionTime (0 + 1) :=
    sub_lt_self _ (by decide : (0 : Time) < 1)
  exact Window.terminalRetentionW p A P d U 0 (p.actionTime (0 + 1) - 1)
    ancestry retained latest before (fun _ => cap)

end AvailableChain.FGSA.Run
end
