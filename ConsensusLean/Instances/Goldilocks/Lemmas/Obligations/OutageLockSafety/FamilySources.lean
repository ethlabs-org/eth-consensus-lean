module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyCount
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyCandidate
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Actual source events and generic FG provenance

The source event is the candidate's own return. This consumer requests only S5's
viability conjunct; no equation with the SA's source handler is assumed.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- Exactly S5's viability conjunct, independently of lock or report semantics. -/
def SourceViableAt (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop :=
  ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr.projAC x i ℓ C → C ∈ ℓ.frame.viableTree ℓ.frame.tree

/-- The original source vocabulary is the generic source event's concrete instance. -/
theorem toFGAt_goldilocks {tr : GoldilocksTrace sp ro} {x : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} :
    ACToFGAt tr.projAC x i ℓ C ↔ SA.ToFGAt tr.projAC x i ℓ C := Iff.rfl

/-- Only Goldilocks's discharge inspects its deepest-candidate computation. -/
theorem sourceViableAt_goldilocks {tr : GoldilocksTrace sp ro}
    (_hr : GoldilocksRun proposer dg H tr) :
    SourceViableAt (A := SA.goldilocksOperations sp _ ro) tr H := by
  intro x hx i ℓ C hc
  exact (Compose.toFG_candidate hc.2.2).1

/-- The live-lock branch of S5. Candidates with other source evidence supply its
compatibility consequence separately instead of pretending it is a stored lock. -/
def SourceLockAt (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop :=
  ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr.projAC x i ℓ C →
    (∃ l ∈ ((F.proj tr.projAC).state x i).locks, ∃ B ∈ ℓ.frame.tree,
      B.root = l.block ∧ ℓ.frame.Anc C B) ∨ F.sourceEvidence tr.projAC x i C

/-- Goldilocks always takes the live-lock branch. -/
theorem sourceLockAt_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    SourceLockAt (SA.goldilocksFamily sp _ ro) tr H := by
  intro x hx i ℓ C hc
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hac hx hc.1
  obtain ⟨hCv, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlC, -, -⟩ :=
    Compose.toFG_candidate hc.2.2
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hΦ.coherent.1 hCv.1 hvt hlC.symm
  exact Or.inl ⟨l₀, hl₀, B₀, hB₀, hB₀r, hva⟩

/-- Source compatibility needs only the live-lock branch, not the report update,
the lock's freshness bound or a deepest-candidate equation. -/
theorem source_compatible_family (hr : FamilyRun F proposer dg H sg tr)
    (hs5 : SourceLockAt F tr H) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlocks : ∀ l ∈ ((F.proj tr.projAC).state y k).locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L B)
    (hevidence : ∀ C, F.sourceEvidence tr.projAC y k C → Compatible (tr.HonestBlocks H) C B)
    {ℓ : ACLabel A.toAC} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : ACToFGAt tr.projAC y k ℓ C) : Compatible (tr.HonestBlocks H) C B := by
  have hU := hr.observation.coherent
  have hfr := (hr.cutLaw y hy k _ (Compose.projAC_callAt.mp h.1)).1
  rcases hs5 y hy k ℓ C h with ⟨l, hl, B₀, hB₀, hB₀r, hCB⟩ | he
  swap
  · exact hevidence C he
  rw [hfr] at hB₀ hCB
  obtain ⟨L, hL, hLr, hLB⟩ := hlocks l hl
  obtain rfl : B₀ = L := hU.1 ⟨y, hy, k, hB₀.1⟩ ⟨y, hy, k, hL⟩ (hB₀r.trans hLr.symm)
  exact compatible_of_anc_family hU (hCB.mono fun _ hX => ⟨y, hy, k, hX.1⟩) hLB

private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

/-- Honest rows are signed before the holder's acceptance, over the actual FG run. -/
theorem honest_row_signed_before (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y i).fg.tree) {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a := by
  rw [← store_eq hr hy i] at hX
  rcases Store.tree_accepted hf hy hX with rfl | ⟨m, hm, hA⟩
  · simp [Params.genesisBlock] at ha
  · exact ⟨m, hm, Compose.projFG_callAt.mp hA,
      hr.att_unforgeable y hy m a (Or.inr ⟨X, ⟨true, Compose.projFG_callAt.mp hA⟩, ha⟩) hav⟩

/-- Actual source events bridge the signed rows to the observed invariant. -/
theorem rows_sourced_family (hr : FamilyRun F proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hs5 : SourceViableAt tr H) {B : SA.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hsrc : ∀ x ∈ H, ∀ k < n, ∀ ℓ C, ACToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C B) {y : Fin sp.n} (hy : y ∈ H) :
    HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n := by
  apply honestRowsSourced_iff.mpr
  intro X hX a ha hav
  obtain ⟨m, hmn, -, k, hkm, src, hcall⟩ := honest_row_signed_before hr.toLocalRun hf hy hX ha hav
  obtain ⟨j, rfl, ℓ, hcj, hcl, -, hC, hfg⟩ := Compose.attest_source hr.toLocalRun hav hcall
  have hfr := (hr.cutLaw a.val hav j _ hcj).1
  have hto : ACToFGAt tr.projAC a.val j ℓ src :=
    ⟨Compose.projAC_callAt.mpr hcj, hcl, by rw [Compose.projAC_state hr.toLocalRun hav j]; exact hC⟩
  have hst : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := (hs5 a.val hav j ℓ src hto).1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (Compose.fg_reachable hr.toLocalRun hav (j + 1)) _ hst
  have hT := createAtt_T (hr.cutLaw a.val hav (j + 1) _ hcall).1
  rw [← hEr, hET] at hT
  exact ⟨src, hsrc a.val hav j (by omega) ℓ src hto,
    isHonestSource_iff.mpr ⟨a.val, hav, j + 1, hst, hT.symm⟩⟩

/-- Compatible honest sources give compatible finalized and justified caches. -/
theorem caches_compatible_family (hr : Node.LocalRun proposer dg H sg tr)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {n : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H)
    (hsrc : HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D B) y n) :
    Compatible (tr.HonestBlocks H) (tr.state y n).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y n).fg.J B := by
  have hJ := J_compatible_before hr hfg hf hy hsrc (fun _ h => h) hBU
  obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ (Compose.fg_reachable hr hy n)
  exact ⟨compatible_of_anc_family hfg.coherent (hFJ.mono fun _ hX => ⟨y, hy, n, hX⟩) hJ, hJ⟩

end Consensus.Goldilocks.FamilySafety

end
