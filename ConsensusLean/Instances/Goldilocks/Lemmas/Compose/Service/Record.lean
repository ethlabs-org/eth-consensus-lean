module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks milestone Service: A1.6, head extends the record

A1.6 (`head_extends_record`) from the served-cut facts (`sleepy_served_facts`, a consequence of
the Sleepy invariant) and the fork-choice lemmas (`SA.anc_acHead`, `SA.acConfirmed_eq`) at the
frame of the cut, which is well formed since every FG cut of an honest node runs an FG handler.
The record part follows cut by cut over the served window. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-- The frame of an honest node before every cut is well formed. -/
theorem frameOK_state {P : Params} {A : NodeAC P}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} {proposer : Nat → Fin P.n} {ini : Fin P.n → A.State}
    (hrun : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    FrameOK (Node.frame (tr.state y i)) :=
  (Store.frame_realization P A.Payload _ _ (fg_reachable hrun hy i)).1

/-- **The head extends a supported record, which is the confirmed tip**: at a cut of an honest node,
the head extends the record's block `R` when `R` has `HeadSupport`, and `ac_confirmed` is `R`. -/
theorem head_confirmed_of_support {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R)
    (hs : HeadSupport tr y i R) :
    (Node.frame (tr.state y i)).Anc R (tr.headAt y i) ∧ tr.confirmedAt y i = R := by
  have hΦ := frameOK_state hrun.toLocalRun hy i
  have hH := SA.anc_acHead hΦ hR.1 hs.anchor_compatible hs.support
  exact ⟨hH, SA.acConfirmed_eq hΦ hR.1 hR.2 hH⟩

/-- **A1.6, head extends the record under synchrony.** -/
theorem head_extends_record : HeadExtendsRecord := by
  intro sp ro proposer dg H tr ΔF hstock hrun hnc hsl y hy i hs R hR
  refine ⟨head_confirmed_of_support hrun hy hR
      ((sleepy_served_facts hrun hnc hsl hy hs hstock).head R hR),
    fun i' hii' hserv R' hR' => ?_⟩
  have hcoh :=
    (ac_projection _ _ dg H _ tr proposer
      (requirements sp ro) (fun y _ => payloadFrom_initial (requirements sp ro) y)
      hrun.toLocalRun hnc).coherent
  -- the record's block moves forward along the window
  have key : ∀ m, i ≤ m → m ≤ i' → ∃ E ∈ tr.HonestBlocks H,
      E.root = (tr.state y m).ac.latestConfirmed ∧ Anc (tr.HonestBlocks H) R E := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun _ => ⟨R, ⟨y, hy, i, hR.1.1⟩, hR.2, Relation.ReflTransGen.refl⟩
    | succ m hm ih =>
      intro hm'
      obtain ⟨E, hE, hEr, hRE⟩ := ih (Nat.le_of_succ_le hm')
      by_cases hn : tr.node m = y ∧ tr.label m ≠ none
      · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hn.2
        have hsm := hserv m hm (Nat.le_of_succ_le hm') ⟨c, hn.1, hc⟩
        obtain ⟨E', hE', hE'r, hEE'⟩ :=
          (sleepy_served_facts hrun hnc hsl hy hsm hstock).record_step E hE hEr
        exact ⟨E', hE', hE'r, hRE.trans hEE'⟩
      · have : tr.state y (m + 1) = tr.state y m := by simp only [Trace.state, hn, ↓reduceIte]
        exact ⟨E, hE, this ▸ hEr, hRE⟩
  obtain ⟨E, hE, hEr, hRE⟩ := key i' hii' le_rfl
  have hR'H : R' ∈ tr.HonestBlocks H := ⟨y, hy, i', hR'.1.1⟩
  rwa [hcoh.1 hR'H hE (hR'.2.trans hEr.symm)]

end Consensus.Goldilocks.Compose

end
