module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

set_option linter.privateModule false

section

/-! P3 App. A.10 regression tests. The old shape stays private.
F-28 forbids these theorem declarations in Claims Tests. -/
namespace AvailableChain.FGSA.Run.Tests.Channels
open AvailableChain.SimplexFG
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def oldSrcFrameAbove (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat) : Prop :=
  ∀ i x, x ∈ rho.honest →
    (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) →
      c₀ ≤ hOf p.E p.cfg e → Φ e) →
    (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      c₀ ≤ hOf p.E p.cfg e → Φ e) ∧ FrameBelow p Φ c₀ (R_at p c E rho i x)

private def oldSrcFrameAboveStmt : Prop :=
  ∀ (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat),
    AncestorClosed p Φ → oldSrcFrameAbove p c E rho Φ c₀

private theorem source_stmt_initial_obstruction (x : V) (hx : x ∈ rho.honest)
    (hg : FGBlock.genesis ∈ (storeAt p c E rho 0 x).fg.TF) :
    ¬ oldSrcFrameAboveStmt p c E rho := by
  intro hs
  have hf := hs (fun _ => False) 0 ⟨fun _ _ _ h => h⟩ 0 x hx
  have hrows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho 0 y r a →
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) →
      0 ≤ hOf p.E p.cfg e → False := by
    intro y r a e ha
    rw [HonestRowBefore_def] at ha
    obtain ⟨j, hj, _⟩ := ha
    exact False.elim (Nat.not_lt_zero j hj)
  have hcert : FGBlock.genesis ∈ certified p (.genesis : FGBlock (Fin p.n)) := by
    rw [certified_def]
    exact ⟨.genesis,
      AvailableChain.FGSA.Run.srcFrame_genesis_preceq p .genesis 0 (Nat.zero_le _), Or.inl rfl⟩
  exact (hf hrows).1 .genesis hg .genesis hcert (Nat.zero_le _)

#print axioms source_stmt_initial_obstruction
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_preceq
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_compatible

end AvailableChain.FGSA.Run.Tests.Channels
end
