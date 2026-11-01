module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSARun.Proofs.Excludes

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Fixed store data persist through a restart-free interval. The KitV2 core
uses the E-16 own-record fold; FG-SA clock/process supply all six fields. -/
theorem fgsa_store_cumulative_on {i j : Nat} (hij : i ≤ j) (x : V)
    (hrf : V2.D.restartFree rho x i j) :
    let a := storeAt p c E rho i x
    let b := storeAt p c E rho j x
    a.fg.TF ⊆ b.fg.TF ∧ a.base.blocks <+: b.base.blocks ∧
    a.base.blockStamp <+: b.base.blockStamp ∧ a.base.voteStamp <+: b.base.voteStamp ∧
    a.proposals <+: b.proposals ∧ a.rowPool <+: b.rowPool := by
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => a.fg.TF ⊆ nd.st.fg.TF ∧ a.base.blocks <+: nd.st.base.blocks ∧
      a.base.blockStamp <+: nd.st.base.blockStamp ∧ a.base.voteStamp <+: nd.st.base.voteStamp ∧
      a.proposals <+: nd.st.proposals ∧ a.rowPool <+: nd.st.rowPool)
    ?_ ?_ (fun _ _ h => h) E rho hij x hrf
    ⟨subset_rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
      List.prefix_refl _, List.prefix_refl _⟩
  · intro nd t h
    change a.fg.TF ⊆ (clock p nd.st t).fg.TF ∧
      a.base.blocks <+: (clock p nd.st t).base.blocks ∧
      a.base.blockStamp <+: (clock p nd.st t).base.blockStamp ∧
      a.base.voteStamp <+: (clock p nd.st t).base.voteStamp ∧
      a.proposals <+: (clock p nd.st t).proposals ∧ a.rowPool <+: (clock p nd.st t).rowPool
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := clock_cumulative p nd.st t
    rw [h1, h2, h3, h4, h5, h6]
    exact h
  · intro nd o h
    have hc := process_cumulative p nd.st (toWire p o)
    exact ⟨Finset.Subset.trans h.1 hc.1, h.2.1.trans hc.2.1,
      h.2.2.1.trans hc.2.2.1, h.2.2.2.1.trans hc.2.2.2.1,
      h.2.2.2.2.1.trans hc.2.2.2.2.1, h.2.2.2.2.2.trans hc.2.2.2.2.2⟩

/-- Durable store data persist through restarts. Stamps are local to an epoch. -/
theorem fgsa_store_durable {i j : Nat} (hij : i ≤ j) (x : V) :
    let a := storeAt p c E rho i x
    let b := storeAt p c E rho j x
    a.fg.TF ⊆ b.fg.TF ∧ a.base.blocks <+: b.base.blocks ∧
    a.proposals <+: b.proposals ∧ a.rowPool <+: b.rowPool := by
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => a.fg.TF ⊆ nd.st.fg.TF ∧ a.base.blocks <+: nd.st.base.blocks ∧
      a.proposals <+: nd.st.proposals ∧ a.rowPool <+: nd.st.rowPool)
    ?_ ?_ (fun _ _ h => h) E rho hij x ?_
    ⟨subset_rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
  · intro nd t h
    obtain ⟨h1, h2, -, -, h5, h6⟩ := clock_cumulative p nd.st t
    change a.fg.TF ⊆ (clock p nd.st t).fg.TF ∧
      a.base.blocks <+: (clock p nd.st t).base.blocks ∧
      a.proposals <+: (clock p nd.st t).proposals ∧ a.rowPool <+: (clock p nd.st t).rowPool
    rwa [h1, h2, h5, h6]
  · intro nd o h
    obtain ⟨h1, h2, -, -, h5, h6⟩ := process_cumulative p nd.st (toWire p o)
    exact ⟨h.1.trans h1, h.2.1.trans h2, h.2.2.1.trans h5, h.2.2.2.trans h6⟩
  · intro nd t h
    change a.fg.TF ⊆ (acRestart p nd.st t).fg.TF ∧
      a.base.blocks <+: (acRestart p nd.st t).base.blocks ∧
      a.proposals <+: (acRestart p nd.st t).proposals ∧
      a.rowPool <+: (acRestart p nd.st t).rowPool
    rwa [acRestart_fg, acRestart_blocks, acRestart_proposals, acRestart_rowPool]

/-- The legacy cumulative form follows from the local epoch form. -/
theorem fgsa_store_cumulative (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V) :
    let a := storeAt p c E rho i x
    let b := storeAt p c E rho j x
    a.fg.TF ⊆ b.fg.TF ∧ a.base.blocks <+: b.base.blocks ∧
    a.base.blockStamp <+: b.base.blockStamp ∧ a.base.voteStamp <+: b.base.voteStamp ∧
    a.proposals <+: b.proposals ∧ a.rowPool <+: b.rowPool :=
  fgsa_store_cumulative_on p c E rho hij x (hnr.restartFree x i j)

/-- Volatile HEAD votes persist only in the named receiver epoch. -/
theorem fgsa_votes_cumulative_on {i j : Nat} (hij : i ≤ j) (x : V)
    (hRF : V2.D.restartFree rho x i j) :
    (storeAt p c E rho i x).base.votes ⊆ (storeAt p c E rho j x).base.votes := by
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => (storeAt p c E rho i x).base.votes ⊆ nd.st.base.votes)
    ?_ ?_ (fun _ _ h => h) E rho hij x hRF (List.Subset.refl _)
  · intro nd t h
    change _ ⊆ (clock p nd.st t).base.votes
    rwa [(clock_vn nd.st t).1]
  · intro nd o h
    exact List.Subset.trans h (process_votes_subset nd.st (toWire p o))

end AvailableChain.FGSA.Run
end
