module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

public section

/-! # Goldilocks: a unanimous update writes a fresh lock floor

consensus-lean#135, item N3. Under `Unanimous tr H p P`, the slot-`p` update of an honest node at
`t_p + 6Δ` has result `P`, no veto, and `P` passes the fast test (`first_update_post`). When `P`
is its own viable ancestor, the update writes the fast lock `⟨P.root, p, true⟩`
(`fastLock_mem_updateConfirmation`, the step `hlock` of `candidate_after_fast_update`, stated
here without the viable-tree premise). So after the tick the node has the floor of slot `p` on
every `B₀ ⪯ P` of its frame (`floor_of_unanimous_update`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **A fast update writes a fresh fast lock**: result `P`, no veto, fast selection `P`, the
lock live at `t`, and `P` its own viable ancestor. -/
theorem fastLock_mem_updateConfirmation {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {u : Nat} {P : Blk sp.n FGP} (hPt : P ∈ Φ.tree) (hva : Φ.viableAncestor P = P)
    (hconf : getConfirmation sp A Φ u = some P) (hnv : ¬ conflictsWithLock sp A.locks Φ t P)
    (hfast : fastSelect sp A Φ u P = some P) (hlive : sp.slot t ≤ u + sp.k) :
    (⟨P.root, u, true⟩ : Lock) ∈ (updateConfirmation sp A Φ t u).locks := by
  unfold updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  change _ ∈ addLocks sp _ Φ t u _
  refine ⟨⟨P.root, u, true⟩, Or.inr ?_, P, hPt, rfl, hlive, ?_⟩
  · exact ⟨(P.root, true), Or.inl ⟨P, hfast, rfl⟩, rfl⟩
  · rw [hva]

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g : Time}

/-- **A unanimous update writes a fresh floor** (N3). At an honest node's tick at `t_p + 6Δ`,
with every honest slot-`p` vote on `P`, every live lock comparing with `P`, `P` a non-genesis
block of the frame and its own viable ancestor, and `B₀ ⪯ P` in the frame: after the tick the
node holds the floor of slot `p` above `B₀`. -/
theorem floor_of_unanimous_update (hrun : GoldilocksRun proposer dg H tr)
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g) {p : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hun : Unanimous tr H p P) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ)
    (hcall : ℓ.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) (hPt : P ∈ ℓ.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot) (hva : ℓ.frame.viableAncestor P = P)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k),
      Compatible (tr.HonestBlocks H) L P)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (hB0 : ℓ.frame.Anc B₀ P) :
    Compose.FloorAt tr y (k + 1) B₀ p := by
  have hΦ : FrameOK ℓ.frame := (SA.frameIn_of_callAt hS.run.localRun hy hc).1
  obtain ⟨hconf, hnv, hf, hpost⟩ := SA.first_update_post hS hp4 hun hy hc hcall htk hPt hlocks
  have hfast := SA.fastSelect_eq_result hΦ hPt hPg hf
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (p + 1 : Nat) = sp.ts p + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts2 : sp.ts (p + 1 + 1 : Nat) = sp.ts (p + 1 : Nat) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.time k) = p + 1 :=
    SA.slot_of_mem sp (p + 1) (by rw [htk, hts1]; linarith)
      (by rw [htk, hts2, hts1]; linarith)
  have hk2 := sp.two_le_k
  have hmem := SA.fastLock_mem_updateConfirmation hPt hva hconf hnv hfast
    (by change sp.slot (tr.time k) ≤ _; rw [hslot]; omega)
  rw [← hpost] at hmem
  have hst : (tr.state y (k + 1)).ac = tr.projAC.post k := by
    rw [← Compose.projAC_state hrun.toLocalRun hy (k + 1)]
    simp [Trace.state, hc.1, hc.2]
  have hfg : (tr.state y (k + 1)).fg = (tr.state y k).fg := by
    rw [tr.state_succ_of_call (Compose.projAC_callAt.mp hc)]
    exact (Compose.ac_cut_fg_unchanged hrun hy hc).1
  have hfr := Compose.frame_of_projAC hrun hy hc
  rw [hfr] at hPt hB0
  refine ⟨_, hst ▸ hmem, rfl, P, ?_, rfl, ?_⟩
  · rw [hfg]
    exact hPt
  · rw [hfg]
    exact hB0

end Consensus.Goldilocks.Healing

end
