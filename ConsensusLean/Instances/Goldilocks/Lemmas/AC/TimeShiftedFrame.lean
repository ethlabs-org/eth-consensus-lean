module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedJoined
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FrameStatements
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry

public section

namespace Consensus.Goldilocks.SA.TimeShifted

variable {sp : SAParams} {FGP : Type} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : ACTrace (instanceAC sp FGP)} {ini : Fin sp.n → SAState sp.n} {y : Fin sp.n}

private theorem frame_in (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {i l} (hc : tr.CallAt y i l) : FrameOK l.frame ∧ l.frame.tree ⊆ U := by
  rcases hr.frameLaw y hy i l hc with ⟨_, _, _, _, law⟩ | ⟨_, _, _, _, _, law⟩ <;> exact law.1

private theorem frame_step {Φ Ψ : Frm sp.n FGP} {t : Time} {c : (instanceAC sp FGP).Call}
    (coh : Coherent U) (old : FrameOK Φ ∧ Φ.tree ⊆ U) (law : (instanceAC sp FGP).CallOK U Φ t c Ψ) :
    Anc U Φ.F Ψ.F ∧ ∀ B ∈ Φ.tree, Anc U Ψ.F B → B ∈ Ψ.tree := by
  obtain ⟨new, input⟩ := law
  cases c with
  | message v => obtain ⟨rfl, _⟩ := input; exact ⟨.refl, fun _ h _ => h⟩
  | tick | proposal | toFG | restart => subst Ψ; exact ⟨.refl, fun _ h _ => h⟩
  | block B =>
    obtain ⟨step, _, _⟩ := input
    have hb := (frameStepAddsBlock_iff.mp frame_step_adds_block _ _ _ _ _ _ step).1
    let frames : Nat → Frm sp.n FGP := fun i => if i = 0 then Φ else Ψ
    have seq : FrameSeqIn frames U := by
      refine ⟨frameSeq_iff.mpr ?_, old.1.rooted, ?_, coh⟩
      · rintro (_ | i)
        · exact Or.inr ⟨B, step⟩
        · exact Or.inl rfl
      · rintro (_ | i)
        · exact old.2
        · exact new.2
    exact ⟨step.F_anc_F'.mono (Set.insert_subset (new.2 hb) old.2),
      frameRetention_iff.mp frame_retention _ _ _ _ _ seq 0 1 (by decide)⟩

private theorem retained (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {i l} (hc : tr.CallAt y i l) : ∀ j r, tr.CallAt y j r → i ≤ j →
    ∀ B ∈ l.frame.tree, Anc U r.frame.F B → B ∈ r.frame.tree := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro r rc ij B hb above
    rcases ij.eq_or_lt with rfl | ij
    · obtain rfl := Option.some.inj (hc.2.symm.trans rc.2); exact hb
    rcases hr.frameLaw y hy j r rc with ⟨none, _⟩ | ⟨k, p, kj, pc, gap, law⟩
    · exact (none i (Nat.zero_le _) ij l hc).elim
    have ik : i ≤ k := by_contra fun h => gap i (by omega) ij l hc
    have step := frame_step hr.coherent (frame_in hr hy pc) law
    exact step.2 B (ih k kj p pc ik B hb (step.1.trans above)) above

/-- A relayed vote head accepted by a TSQ reader remains resolvable by root across its
subsequent frames, provided the head extends the later finalized tip. Ancestry is recovered
in the later frame, not assumed equal across readers. This does not assert a stamp cutoff. -/
theorem head_lookup_at_call (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {i j r B C} (received : tr.AcceptAt y i B) (ij : i ≤ j) (rc : tr.CallAt y j r)
    (floor : Anc U r.frame.F B) (child : C ∈ r.frame.tree) (branch : Anc U C B) :
    lookup r.frame B.root = some B ∧ AncR r.frame C B.root := by
  obtain ⟨l, hc, blk⟩ := received
  have before : B ∈ l.frame.tree := by
    rcases hr.frameLaw y hy i l hc with ⟨_, _, _, _, law⟩ | ⟨_, _, _, _, _, law⟩ <;>
      rw [blk] at law <;> exact (frameStepAddsBlock_iff.mp frame_step_adds_block
        _ _ _ _ _ _ law.2.1).1
  have after := retained hr hy hc j r rc ij B before floor
  obtain ⟨ok, sub⟩ := frame_in hr hy rc
  exact ⟨lookup_of_mem ok after, B, after, rfl,
    anc_tree_of_anc_U hr.coherent ok sub child branch after⟩

/-- A block accepted by the source either before the service window (old-block catch-up)
or inside it (timed relay) resolves in the reader's current frame once due. Neither route
requires equal frames or the proposal to have been adopted. -/
theorem relayed_head_at_call (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) {a b κ : Time}
    (sync : SyncACWindowBefore H U a b tr) (catchup : CatchACWindowBefore tr H U a κ b)
    {x : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {i j r B C} (sent : tr.AcceptAt x i B)
    (rc : tr.CallAt y j r) (horizon : tr.time j ≤ b)
    (due : if tr.time i < a then a + κ ≤ tr.time j else tr.deadline y j (tr.time i) ≤ tr.time j)
    (floor : Anc U r.frame.F B) (child : C ∈ r.frame.tree) (branch : Anc U C B) :
    lookup r.frame B.root = some B ∧ AncR r.frame C B.root := by
  split_ifs at due with old
  · obtain ⟨k, kj, accepted, _⟩ := catchup.relay x hx i B sent old y hy j r rc due horizon floor
    exact head_lookup_at_call hr hy accepted kj rc floor child branch
  · obtain ⟨k, kj, accepted, _⟩ := sync.relay x hx i B sent (not_lt.mp old) y hy j r rc
      (due.trans horizon) due floor
    exact head_lookup_at_call hr hy accepted kj rc floor child branch

end Consensus.Goldilocks.SA.TimeShifted

end
