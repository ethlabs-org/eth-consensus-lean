module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.OwnBlockReady
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy

public section

/-! # Reading a sealed proposal payload

The seal runs in the proposer frame, but scores are read in the reader frame. In particular,
an opponent's head need not extend the target: coverage uses *every held reader-frame head*.
-/

namespace Consensus.Goldilocks

open AC (ACParams Blk Payload ReplayOrder)

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP}

open Classical in
/-- The effective seal point, computed before the proposal root is known. -/
noncomputable def sealPoint (st : Store P ACP) (parent : NodeBlock P ACP) (slot : Nat) :
    NodeBlock P ACP :=
  let r := P.fg.finalityPreview (st.σ parent.root) slot (st.proposalAttestations parent)
  match st.blocks r with
  | some F => if st.Anc st.F F then F else st.F
  | none => st.F

/-- The preview resolves before assembly: counting attestations changes bits, and finalization
chooses either the old finalized block or a pending entry of the parent's chain. -/
theorem proposal_preview_resolves {st : Store P ACP} (hr : st.Reachable acp₀)
    {parent : NodeBlock P ACP} (hparent : parent ∈ st.toFrame.tree) (slot : Nat) :
    ∃ F, st.blocks (P.fg.finalityPreview (st.σ parent.root) slot
      (st.proposalAttestations parent)) = some F ∧ st.Anc F parent ∧
      Compatible st.tree st.F F := by
  obtain ⟨f, p, tg, he⟩ := FG.ChainState.foldl_processAtt_eq
    {st.σ parent.root with s := slot} (st.proposalAttestations parent)
  rw (config := { transparency := .default }) [FG.FGParams.finalityPreview_eq, he]
  let σ : FG.ChainState P.n :=
    { st.σ parent.root with s := slot, fin := f, prog := p, target := tg }
  change ∃ F, st.blocks (P.fg.finalizePrune σ).F = some F ∧ _
  suffices ∃ F ∈ st.tree, F.root = (P.fg.finalizePrune σ).F ∧ st.Anc F parent by
    obtain ⟨F, hF, hrF, hFp⟩ := this
    exact ⟨F, hrF ▸ (show st.blocks F.root = some F from hF), hFp,
      Anc.total (accepted_tree _ _ _ _ hr).2.1 hparent.2 hFp⟩
  cases hb : P.fg.bestFinal σ with
  | none =>
    obtain ⟨_, ⟨F, hF, hrF, hFp⟩, _⟩ := entry_state_of_source _ _ _ _ hr parent hparent.1
    exact ⟨F, hF, by simpa only [FG.FGParams.finalizePrune, hb] using hrF, hFp⟩
  | some r =>
    have hm : r ∈ (st.σ parent.root).pending := (P.fg.bestFinal_eq_some hb).1
    obtain ⟨F, hF, hFp, hrF, _, _⟩ := (Healing.chain_pairs_entry hr hparent.1).2 r hm
    exact ⟨F, hF, by simpa only [FG.FGParams.finalizePrune, hb] using hrF, hFp⟩

/-- The default and the advancing case both supply an in-frame point. -/
theorem sealPoint_mem_frame {st : Store P ACP} (hr : st.Reachable acp₀)
    (parent : NodeBlock P ACP) (slot : Nat) : st.sealPoint parent slot ∈ st.toFrame.tree := by
  have hF : st.F ∈ st.toFrame.tree := ⟨(cache_invariants _ _ _ _ hr).1, .refl⟩
  unfold sealPoint
  dsimp only
  split
  · rename_i F hF'
    split_ifs with ha
    · refine ⟨?_, ha⟩
      change st.blocks F.root = some F
      rwa [hr.blocks_root hF']
    · exact hF
  · exact hF

end Store

namespace AC

variable {sp : ACParams}

/-- The cross-frame form of `sealed_supporters_eq`, also covering opponents: a mark only
needs to survive if its head is in the scoring frame, regardless of the target's branch. -/
private theorem scores_eq_of_covered_heads {FGP : Type} {Φ Ψ : Frm sp.n FGP}
    {F : Blk sp.n FGP} {raw : Payload sp.n}
    (hkeep : ∀ x ∈ raw.2, InTree Ψ x.head → AncR Φ F x.head) (s : Int) (X : Blk sp.n FGP) :
    supporters Ψ (View.ofLists (sealSupport Φ F raw)) s X = supporters Ψ (View.ofLists raw) s X ∧
    opponents sp Ψ (View.ofLists (sealSupport Φ F raw)) s X =
      opponents sp Ψ (View.ofLists raw) s X := by
  constructor
  · ext i
    change (_ ∉ equivocators {v | v ∈ (sealSupport Φ F raw).1} ∧
      ∃ x ∈ (sealSupport Φ F raw).2, x.val = i ∧ (x.slot : Int) = s ∧ AncR Ψ X x.head) ↔ _
    rw [sealSupport_declared]
    constructor
    · rintro ⟨hne, x, hx, hi, hs, ha⟩
      exact ⟨hne, x, (mem_sealSupport.mp hx).1, hi, hs, ha⟩
    · rintro ⟨hne, x, hx, hi, hs, ha⟩
      exact ⟨hne, x, mem_sealSupport.mpr ⟨hx, hkeep x hx (ha.imp fun _ h =>
        ⟨h.1, h.2.1⟩)⟩, hi, hs, ha⟩
  · ext i
    change (i ∈ equivocators {v | v ∈ (sealSupport Φ F raw).1} ∨
      ∃ x ∈ (sealSupport Φ F raw).2, x.val = i ∧ (x.slot : Int) = s ∧
        ∃ H ∈ Ψ.tree, H.root = x.head ∧ ¬ Compatible Ψ.tree H X) ↔ _
    rw [sealSupport_declared]
    constructor
    · rintro (he | ⟨x, hx, hi, hs, ha⟩)
      · exact Or.inl he
      · exact Or.inr ⟨x, (mem_sealSupport.mp hx).1, hi, hs, ha⟩
    · rintro (he | ⟨x, hx, hi, hs, H, hH, hr, hc⟩)
      · exact Or.inl he
      · exact Or.inr ⟨x, mem_sealSupport.mpr ⟨hx, hkeep x hx ⟨H, hH, hr⟩⟩,
          hi, hs, H, hH, hr, hc⟩

section Reader

variable {acp₀ : Payload sp.n} {src reader : Store sp.toParams (Payload sp.n)}
  {U : Set (Blk sp.n (List (FG.Att sp.n)))} {parent B : Blk sp.n (List (FG.Att sp.n))}
  {raw : Payload sp.n}

/-- If the carrier's preview lies below the reader's frame, sealing preserves the scores of
the raw proposal in that frame. The carrier binds the parent's root and the assembly attestations;
coherence and replay identify its preview with the one used before assembly. -/
theorem sealed_reader_scores_eq (hsrc : src.Reachable acp₀) (hreader : reader.Reachable acp₀)
    (hU : Coherent U) (hsub : src.tree ⊆ U) (hsub' : reader.tree ⊆ U)
    (hparent : parent ∈ src.toFrame.tree) (hB : B ∈ reader.tree)
    (hp : B.parent = some parent.root) (hatts : B.fgPayload = src.proposalAttestations parent)
    (hraw : ∀ x ∈ raw.2, InTree src.toFrame x.head)
    (hpreview : ∃ F ∈ reader.tree,
      F.root = sp.toParams.fg.finalityPreview (reader.σ parent.root) B.slot B.fgPayload ∧
        ∀ Y ∈ reader.toFrame.tree, reader.Anc F Y)
    (s : Int) (X : Blk sp.n (List (FG.Att sp.n))) :
    let sealed := sealSupport src.toFrame (src.sealPoint parent B.slot) raw
    supporters reader.toFrame (View.ofLists sealed) s X =
        supporters reader.toFrame (View.ofLists raw) s X ∧
      opponents sp reader.toFrame (View.ofLists sealed) s X =
        opponents sp reader.toFrame (View.ofLists raw) s X := by
  obtain ⟨pr, hpr, hprr, _⟩ := Healing.Store.step_σ hreader hB hp
  have hpr' : parent ∈ reader.tree := (hU.1 (hsub' hpr) (hsub hparent.1) hprr) ▸ hpr
  have hσ := Healing.Store.σ_eq_of_mem hsrc hreader hU.1 hsub hsub' hparent.1 hpr'
  obtain ⟨F, hF, _, _⟩ := Store.proposal_preview_resolves hsrc hparent B.slot
  obtain ⟨G, hG, hGr, hanc⟩ := hpreview
  have hFt : F ∈ src.tree := by
    change src.blocks F.root = some F
    rwa [hsrc.blocks_root hF]
  have he : F = G := by
    have hFr := hsrc.blocks_root hF
    rw [hσ, ← hatts, ← hGr] at hFr
    exact hU.1 (hsub hFt) (hsub' hG) hFr
  subst G
  apply scores_eq_of_covered_heads
  rintro x hx ⟨Y, hY, hYr⟩
  obtain ⟨Z, hZ, hZr⟩ := hraw x hx
  obtain rfl : Y = Z := hU.1 (hsub' hY.1) (hsub hZ.1) (hYr.trans hZr.symm)
  refine ⟨Y, hZ, hYr, ?_⟩
  have hFY := Store.anc_of_anc_universe hsrc hU hsub ((hanc Y hY).mono hsub') hZ.1
  unfold Store.sealPoint
  dsimp only
  simp only [hF]
  split_ifs with hle
  · exact Anc.restrict hle hFY
  · exact Anc.restrict .refl hZ.2

end Reader

section Run

variable {src : Store sp.toParams (Payload sp.n)}
  {parent B : Blk sp.n (List (FG.Att sp.n))} {raw : Payload sp.n}

/-- Reader scores agree under the healthy/reset FG quorum bound. -/
theorem sealed_reader_scores_eq_of_fault_bound {acp₀ : Payload sp.n} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n (List (FG.Att sp.n)))} {tr : FGTrace sp.toParams (Payload sp.n)}
    (hr : FGLocalRun acp₀ H U tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H)
    (hsrc : src.Reachable acp₀) (hsub : src.tree ⊆ U)
    (hparent : parent ∈ src.toFrame.tree) (hB : B ∈ (tr.store y j).tree)
    (hp : B.parent = some parent.root) (hatts : B.fgPayload = src.proposalAttestations parent)
    (hraw : ∀ x ∈ raw.2, InTree src.toFrame x.head)
    (s : Int) (X : Blk sp.n (List (FG.Att sp.n))) :
    let Ψ := (tr.store y j).toFrame
    let sealed := sealSupport src.toFrame (src.sealPoint parent B.slot) raw
    supporters Ψ (View.ofLists sealed) s X = supporters Ψ (View.ofLists raw) s X ∧
      opponents sp Ψ (View.ofLists sealed) s X = opponents sp Ψ (View.ofLists raw) s X :=
  sealed_reader_scores_eq hsrc (Store.store_reachable hr hy j) hr.coherent hsub
    (hr.tree_subset y hy j) hparent hB hp hatts hraw
    (Store.held_preview_ancestor_frame hr hf hy hB hp) s X

/-- Reader scores agree under the sleepy/seeded run's chain-conviction premise, at independent
honest observations of the proposer and reader. No numeric fault bound is needed. -/
theorem sealed_reader_scores_eq_of_conviction {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hr : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hcv : Compose.Growing.ChainConvictedBelow tr H)
    {y : Fin sp.n} {j : Nat} {t : Time} (ht : 0 ≤ t) (hj : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t)
    {x : Fin sp.n} {i : Nat} {u : Time} (hu : 0 ≤ u) (hi : ∀ k < i, tr.time k ≤ u) (hx : x ∈ H u)
    (hsrc : src = (tr.state x i).fg)
    (hparent : parent ∈ src.toFrame.tree) (hB : B ∈ (tr.state y j).fg.tree)
    (hp : B.parent = some parent.root) (hatts : B.fgPayload = src.proposalAttestations parent)
    (hraw : ∀ x ∈ raw.2, InTree src.toFrame x.head)
    (s : Int) (X : Blk sp.n (List (FG.Att sp.n))) :
    let Ψ := (tr.state y j).fg.toFrame
    let sealed := sealSupport src.toFrame (src.sealPoint parent B.slot) raw
    supporters Ψ (View.ofLists sealed) s X = supporters Ψ (View.ofLists raw) s X ∧
      opponents sp Ψ (View.ofLists sealed) s X = opponents sp Ψ (View.ofLists raw) s X := by
  subst src
  exact sealed_reader_scores_eq (Healing.Growing.fg_reachable_at hr hu hi hx)
    (Healing.Growing.fg_reachable_at hr ht hj hy) (Compose.Growing.honest_blocks_coherent hr hnc)
    (fun _ h => ⟨x, i, u, hu, hi, hx, h⟩) (fun _ h => ⟨y, j, t, ht, hj, hy, h⟩)
    hparent hB hp hatts hraw
    (Healing.Growing.held_preview_ancestor_frame_of_conviction hr hnc hcv ht hj hy hB hp) s X

end Run

end AC
end Consensus.Goldilocks

end
