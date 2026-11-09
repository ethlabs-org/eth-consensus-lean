module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- A floor in one frame, independent of either a node trace or an execution law. -/
def LockFloor (L : Set SA.Lock) (Φ : SA.Frm sp.n (List (FG.Att sp.n)))
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) (j m : Nat) : Prop :=
  ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B

/-- Keep is deliberately separate from backward release. The candidate supplies its
own keep predicate and the premise under which honest compatible votes establish it.
The floor and read-floor clauses are the retention exits of S2/S3 and U.locks.
They say nothing about the other post-state fields. -/
structure RetentionFacts (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) where
  Keeps : Fin sp.n → Nat → SA.Blk sp.n (List (FG.Att sp.n)) → Prop
  keep : ∀ W : Set (Fin sp.n), 2 * (Hᶜ ∪ W).ncard < sp.n → ∀ x ∈ H, ∀ k B,
    B ∈ (Node.frame (tr.state x k)).tree →
    (∀ y ∈ H, y ∉ W → ∀ c < k, ∀ e, SA.VoteAt (F.proj tr.projAC) y c e →
      (e.msg.slot : Int) = (sp.slot (tr.time k) : Int) - 1 →
      Compose.VoteCompat (tr.HonestBlocks H) e.msg B) → Keeps x k B
  step : ∀ x ∈ H, ∀ k B j m, FloorAt F tr x k B j m → sp.slot (tr.time k) ≤ m →
    B ∈ (Node.frame (tr.state x k)).tree → B ∈ (Node.frame (tr.state x (k + 1))).tree →
    (Node.frame (tr.state x k)).viableAncestor B = B →
    ((sp.slot (tr.time k) : Int) - 1 ≤ j ∨ Keeps x k B) → FloorAt F tr x (k + 1) B j m
  read : ∀ x ∈ H, ∀ k ℓ e, SA.CastAt (F.proj tr.projAC) x k ℓ e → ∀ B (j m : Nat),
    B ∈ ℓ.frame.tree → ℓ.frame.viableAncestor B = B → sp.slot (tr.time k) ≤ m →
    ((sp.slot (tr.time k) : Int) - 1 ≤ j ∨ Keeps x k B) →
    LockFloor ((F.proj tr.projAC).state x k).locks ℓ.frame B j m →
    ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time k), ℓ.frame.Anc B C

/-- The vote-head exit of S2 plus the separately scoped start dominance law.
Taking this at every cut is stronger than the lead's post-settlement guarantee. -/
structure VoteDominance (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop where
  head : ∀ x ∈ H, ∀ k ℓ e, SA.CastAt (F.proj tr.projAC) x k ℓ e →
    ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head
  above : ∀ x ∈ H, ∀ k ℓ e, SA.CastAt (F.proj tr.projAC) x k ℓ e →
    ∀ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time k),
    ∀ B, ℓ.frame.Anc B C → ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc B Hd

/-- Goldilocks supplies its ordinary keep rule, not a rule inferred from UnlocksRel. -/
noncomputable def retentionFacts_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hkeep : ∀ W : Set (Fin sp.n), 2 * (Hᶜ ∪ W).ncard < sp.n → ∀ x ∈ H, ∀ k B,
      B ∈ (Node.frame (tr.state x k)).tree →
      (∀ y ∈ H, y ∉ W → ∀ c < k, ∀ e, SA.VoteAt tr.projAC y c e →
        (e.msg.slot : Int) = (sp.slot (tr.time k) : Int) - 1 →
        Compose.VoteCompat (tr.HonestBlocks H) e.msg B) → Compose.UnlockKeeps tr x k B) :
    RetentionFacts (SA.goldilocksFamily sp _ ro) tr H where
  Keeps := Compose.UnlockKeeps tr
  keep := by
    intro W hf x hx k B hB hv
    exact hkeep W hf x hx k B hB hv
  step := by
    intro x hx k B j m hfl hk hB hB' hva hu
    apply (floorAt_goldilocks hr hx).mpr
    exact Compose.floor_run_view hr hx k ((floorAt_goldilocks hr hx).mp hfl) hk hB hB' hva
      (fun ℓ hc => hu.imp_right (fun h => h ℓ hc))
  read := by
    intro x hx k ℓ e hc B j m hB hva hk hu hfl
    have hfr := frame_of_observation (hr.family hnc) hx hc.1
    apply SA.exists_readPoint_liveLockBlocks_floor
      (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun hx hc hB hva hk
    · rcases hu with hu | hu
      · exact Or.inl hu
      · have hh := hu ℓ (Compose.projAC_callAt.mp hc.1)
        apply Or.inr
        change SA.unlockTarget sp ℓ.frame
          (SA.unlockView (tr.projAC.state x k) ℓ.frame (tr.time k) ℓ.call)
          ((sp.slot (tr.time k) : Int) - 1) B = B
        rw [hfr, Compose.projAC_state hr.toLocalRun hx k]
        exact hh
    · exact hfl

/-- Goldilocks's start dominates at every cut. -/
theorem voteDominance_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    VoteDominance (SA.goldilocksFamily sp _ ro) tr H := by
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun
  constructor
  · intro x hx k ℓ e hc
    obtain ⟨Hd, hHd, hHdr, -⟩ := SA.honest_head_frame hac hx hc
    exact ⟨Hd, hHd, hHdr⟩
  · intro x hx k ℓ e hc C hC B hBC
    exact SA.castAt_head_anc hac hx hc (Or.inl hC)
      (SA.castAt_compatible_of_live hac hx hc (Or.inl hC)) hBC

/-- The candidate's keep law discharges exactly the OL-W vote condition. -/
theorem OutageVoteInv.unlockKeeps (hr : RetentionFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) {D : OutageLockPremises F tr H proposer dg sg}
    {k : Nat} (hvi : OutageVoteInv D k) {y : Fin sp.n} (hy : y ∈ H)
    (hP : D.P ∈ (Node.frame (tr.state y k)).tree)
    (hs : (D.j₀ : Int) + 1 ≤ sp.slot (tr.time k)) : hr.Keeps y k D.P :=
  hr.keep D.W D.two_mul_lt y hy k D.P hP fun x hx hxW k' hk' e hv hes =>
    hvi.voteCompat_of_not_lateWaker ht hx hxW hk' hv (by omega)

/-- Protection carries through one cut using only retention and actual FG geometry. -/
theorem OutageVoteInv.prot_step (hr : RetentionFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {D : OutageLockPremises F tr H proposer dg sg} {k : Nat} (hvi : OutageVoteInv D k)
    {x : Fin sp.n} (hx : x ∈ H) {j m : Nat} (hj : D.j₀ ≤ j + 1)
    (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (k + 1)).fg.F D.P)
    (hp : Prot D x k j m) : Prot D x (k + 1) j m := by
  have hFm := Healing.run_F_mono D.hrun.toLocalRun hx (Nat.le_succ k)
  rcases prot_iff.mp hp with hfl | hroot
  swap
  · exact prot_iff.mpr (Or.inr (hroot.trans hFm))
  by_cases hroot : Anc (tr.HonestBlocks H) D.P (tr.state x (k + 1)).fg.F
  · exact prot_iff.mpr (Or.inr hroot)
  have hFP := hF.resolve_right hroot
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP := SA.mem_of_anc hPB hB
  have hPt := Compose.tree_mono D.hrun.toLocalRun hx (Nat.le_succ k) hP.1
  have hP' : D.P ∈ (Node.frame (tr.state x (k + 1))).tree :=
    ⟨hPt, honest_held_anc D.hrun.toLocalRun hfg hx hFP hPt⟩
  apply prot_iff.mpr ∘ Or.inl
  apply hr.step x hx k D.P j m ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ hk hP hP'
    (SA.viableAncestor_self (Compose.frameOK_state D.hrun.toLocalRun hx k) hP (hva hP).symm)
  by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
  · exact Or.inl hs
  · exact Or.inr (hvi.unlockKeeps hr ht hx hP (by omega))

/-- A cast under the protection needs the keep law and unscoped vote dominance. -/
theorem OutageVoteInv.vote_extends_of_prot (hr : RetentionFacts F tr H)
    (hd : VoteDominance F tr H) (ht : VoteTiming (F.proj tr.projAC) H)
    {D : OutageLockPremises F tr H proposer dg sg} {k : Nat} (hvi : OutageVoteInv D k)
    {x : Fin sp.n} (hx : x ∈ H) {j m : Nat} (hj : D.j₀ ≤ j + 1)
    (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hp : Prot D x k j m) {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt (F.proj tr.projAC) x k e) : SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  obtain ⟨ℓ, hc, he⟩ := hv
  have hcast : SA.CastAt (F.proj tr.projAC) x k ℓ e := ⟨hc, he⟩
  have hfr := frame_of_observation D.hrun hx hc
  obtain ⟨hΦ, hΦU⟩ := D.hrun.observation.frameIn hx hc
  rcases prot_iff.mp hp with hfl | hroot
  swap
  · obtain ⟨Hd, hHd, hHdr⟩ := hd.head x hx k ℓ e hcast
    have hFHd := hΦ.rooted.2 Hd hHd
    rw [hfr] at hFHd
    exact ⟨Hd, hΦU hHd, hHdr,
      hroot.trans (hFHd.mono fun X hX => ⟨x, hx, k, hX.1⟩)⟩
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP := SA.mem_of_anc hPB hB
  have hva0 := SA.viableAncestor_self (Compose.frameOK_state D.hrun.toLocalRun hx k) hP
    (hva hP).symm
  have hu : (sp.slot (tr.time k) : Int) - 1 ≤ j ∨ hr.Keeps x k D.P := by
    by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
    · exact Or.inl hs
    · exact Or.inr (hvi.unlockKeeps hr ht hx hP (by omega))
  change D.P ∈ (Node.frame (tr.state x k)).tree at hP
  change (Node.frame (tr.state x k)).viableAncestor D.P = D.P at hva0
  change B ∈ (Node.frame (tr.state x k)).tree at hB
  change (Node.frame (tr.state x k)).Anc D.P B at hPB
  rw [← hfr] at hP hva0 hB hPB
  obtain ⟨C, hC, hPC⟩ := hr.read x hx k ℓ e hcast D.P j m hP hva0 hk hu
    ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩
  obtain ⟨Hd, hHd, hHdr, hPHd⟩ := hd.above x hx k ℓ e hcast C hC D.P hPC
  exact ⟨Hd, hΦU hHd, hHdr, hPHd.mono hΦU⟩

end Consensus.Goldilocks.FamilySafety

end
