module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Sleepy frame geometry and provenance

FG cache certificates and signed rows anchor the run's own frames. Viability
remains conditional on compatibility of the supplied confirmation events.
-/

namespace Consensus.Goldilocks.Compose

open FrameGeometry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini}
  (hr : Node.LocalRun proposer dg H sg tr ini)
  (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
  (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
  {G : A.Blk → Prop}

include hr hfg hy

private theorem held_σ_eq {z : Fin P.n} (hz : z ∈ H) {j : Nat} {B : A.Blk}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root := by
  rw [← store_eq hr hy i] at hBy ⊢
  rw [← store_eq hr hz j] at hBz ⊢
  exact Store.σ_eq_of_held hfg hy hz hBy hBz

private theorem source_entry_eq {D D' E E' : A.Blk}
    (hDD' : Compatible (tr.HonestBlocks H) D D') (hD : IsHonestSource tr H D E.root)
    (hD' : IsHonestSource tr H D' E'.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hE' : E' ∈ (tr.state y i).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h) : E = E' := by
  have key : ∀ {D D' E E' : A.Blk}, Anc (tr.HonestBlocks H) D D' →
      IsHonestSource tr H D E.root → IsHonestSource tr H D' E'.root → E ∈ (tr.state y i).fg.tree →
      E' ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h → E = E' := by
    intro D D' E E' hDD hD hD' hE hE' hh
    obtain ⟨x, hx, k, -, hEt, hED, -, hET⟩ := honest_source_entry hr hfg hD ⟨y, hy, i, hE⟩ rfl
    obtain ⟨x', hx', k', hD't, hE't, hE'D', -, hE'T⟩ :=
      honest_source_entry hr hfg hD' ⟨y, hy, i, hE'⟩ rfl
    have hED' : (tr.state x' k').fg.Anc E D' :=
      honest_held_anc hr hfg hx' ((hED.mono (fg_tree_subset_honest hx k)).trans hDD) hD't
    have hEt' := anc_mem hED' hD't
    refine held_entry_unique hr hfg hx' hD't hED' hE'D' ?_ ?_ hE'T
    · rw [held_σ_eq hr hfg hx' hy hEt' hE, held_σ_eq hr hfg hx' hy hE't hE']
      exact hh
    · rw [held_σ_eq hr hfg hx' hx hEt' hEt]
      exact hET
  rcases hDD' with h | h
  · exact key h hD hD' hE hE' hh
  · exact (key h hD' hD hE' hE hh.symm).symm

private theorem below_entry {B D E : A.Blk}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H D E.root) (hDB : Compatible (tr.HonestBlocks H) D B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hr hfg hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height hr hfg hy (honest_held_anc hr hfg hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hfg.coherent h hEDU with h' | h'
    · exact honest_held_anc hr hfg hy h' hE
    · exact absurd h' no

include hf

private theorem frame_no_contest_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D') :
    ¬ (tr.state y i).fg.Contest := by
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable hr hy i
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  obtain ⟨hJh, hJT, D, hD, hDs⟩ := justified_honest_source_of hr hfg hf hy hsrc (by omega)
  obtain ⟨E, hE, hEX, hEh, hET, D', hD', hD's⟩ :=
    frame_crossing_source_of hr hfg hf hy hsrc hX (j := (tr.state y i).fg.hj) le_rfl (by omega)
      (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ hR).2.1
  rw [source_entry_eq hr hfg hy (hGG D D' hD hD') hDs hD's hJ hE (hJh.trans hEh.symm)] at hJX
  exact hJX hEX

private theorem J_compatible (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy]
    exact Or.inl (honest_genesis_anc hr hB).2
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of hr hfg hf hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hr hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D :=
    hJD.mono (fg_tree_subset_honest hx k)
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hfg.coherent hJDU h

private theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    split_ifs with h
    · exact absurd h (frame_no_contest_of hr hfg hf hy hsrc hGG)
    · rfl
  by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl hle
  right
  obtain ⟨-, -, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨X, hX, hXh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ (fg_reachable hr hy i)
  have hB1 := (honest_held_chain hr hy hB).1
  have hZ1 := (honest_held_chain hr hy hZ).2.1
  have hZ2 := hZm Z hZ
  obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ :=
    frame_crossing_source_of hr hfg hf hy hsrc hX (j := (tr.state y i).fg.hmax - 1) (by omega)
      (by omega) (by omega)
  refine ⟨D, E, X, hD, hDs, hE, below_entry hr hfg hy hB hE hDs (hGB D hD) (by omega),
    hEh.trans hfl.symm, hX, hEX, ?_⟩
  change (tr.state y i).fg.headHeightFloor ≤ _
  omega

private theorem held_viable_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := hfg.coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hr hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact J_compatible hr hfg hf hy hsrc hGB (hsU hBt.1)
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (Frame.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  rcases floor_or_crossing_of hr hfg hf hy hsrc hGG hGB hBt.1 with hle | ⟨-, E, X, -, -, -, hBE,
    -, hX, hEX, hXv⟩
  · exact ⟨hBt, hΦfB, B, hBt, ⟨hBt.1, hBt.2, Anc.mono hΦs hΦfB, hle⟩, .refl⟩
  · have hBX := hBE.trans hEX
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      Frame.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Generic.SleepyLayer1

theorem frame_acceptance {P : Params} {A : NodeAC P} : FrameAcceptance (A := A) := by
  intro src src' dst B pr hs hp hg
  rcases hg with hdup | ⟨hnew, hheld, hstate, hanc⟩
  · have hnone : dst.onBlock B = none := by
      unfold Store.onBlock
      rw [hp]
      simp [hdup]
    simpa only [hnone, Option.getD_none, Store.tree, Set.mem_ofPred_eq] using hdup
  · obtain ⟨dst', hd⟩ := Store.onBlock_transfer hs hp hnew hheld hstate hanc
    obtain ⟨-, -, -, -, -, -, hb, -⟩ := Store.onBlock_fields hd
    change (dst.onBlock B |>.getD dst).blocks B.root = some B
    rw [hd, Option.getD_some, hb, Function.update_self]

theorem cache_provenance {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}
    (C : ACCorrectLocal A sg) (D : Data A) : CacheProvenance C D := by
  intro cm proposer dg H tr b hrun hnc y i t hread hf hrows
  obtain ⟨hy, ⟨hi, -⟩, ht0, htb⟩ := hread
  have hr := C.run.run_local hrun
  have hs := Trace.upTo_state tr y hi
  have hlocal := hr.upTo ht0
  have hfg := Compose.fg_projection_from
    (fun z _ => C.run.run_requirements hrun z) (C.run.run_root hrun) hlocal (hnc.upTo _)
  have hcoh := Compose.Growing.honest_blocks_coherent_local hr hnc
  have hR := Compose.fg_reachable hlocal hy i
  rw [hs] at hR
  have hcache : ∀ X ∈ ({(tr.state y i).fg.J, (tr.state y i).fg.F} : Set A.Blk),
      X ∈ (tr.state y i).fg.tree → Anchored D tr H b t X := by
    intro X hX hXt
    rcases Compose.cache_quorum hR X hX with hg | ⟨Q, hQ, hv⟩
    · exact Or.inl hg
    have honest : ∃ v ∈ Q, v ∈ H t := by
      by_contra hn
      simp only [not_exists, not_and] at hn
      have hcard : (Q : Set (Fin P.n)).ncard ≤ (H t)ᶜ.ncard :=
        Set.ncard_le_ncard (fun v hv => hn v hv) (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hcard
      have hq : P.fg.q = (2 * P.n + 2) / 3 := rfl
      omega
    obtain ⟨v, hvQ, hvH⟩ := honest
    obtain ⟨Z, hZ, a, ha, hav, haT⟩ := hv v hvQ
    have hZ' : Z ∈ ((tr.upTo t).projFG.store y i).tree := by
      rw [Compose.FrameGeometry.store_eq hlocal hy i, hs]
      exact hZ
    rcases Store.tree_accepted hfg hy hZ' with hg | ⟨m, hmi, hm⟩
    · subst Z
      simp [Params.genesisBlock] at ha
    have hcall := Compose.projFG_callAt.1 hm
    obtain ⟨hmt, hcall⟩ := (Trace.upTo_callAt _).1 hcall
    have hy' := hr.antitone hmt hy
    have hva : a.val ∈ H t := hav ▸ hvH
    have hva' := hr.antitone hmt hva
    obtain ⟨k, hkm, hsign⟩ := hr.att_unforgeable y m a hy'
      (Or.inr ⟨Z, ⟨true, hcall⟩, ha⟩) hva'
    have hkt : tr.time k ≤ t := (hr.time_mono hkm.le).trans hmt
    obtain ⟨E, hE, hEr, hanchor⟩ := hrows a.val k a (hr.antitone hkt hva) hsign hkt
      (hkt.trans htb)
    have hXH : X ∈ tr.HonestBlocksAt H := ⟨y, i, t, ht0, hi, hy, hXt⟩
    obtain rfl : X = E := hcoh.1 hXH hE (haT.symm.trans hEr.symm)
    rcases hanchor with hg | ⟨B, he, hEB⟩
    · exact Or.inl hg
    · obtain ⟨x, j, s, hx, hjk, hjb, hevent⟩ := he
      exact Or.inr ⟨B, ⟨x, j, s, hx, hjk.trans hkt, hjb, hevent⟩, hEB⟩
  obtain ⟨hF, hJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  exact ⟨hcache _ (Or.inr rfl) hF, hcache _ (Or.inl rfl) hJ⟩

theorem row_provenance {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}
    (C : ACCorrectLocal A sg) (D : Data A) : RowProvenance C D := by
  intro hsource cm proposer dg H tr b hrun hnc x k a hx hs hkb
  have hr := C.run.run_local hrun
  have hd := hr.time_nonneg k
  have hret := hr.upTo hd
  obtain ⟨src, hc⟩ := hs
  obtain ⟨j, hk, ℓ, hj, hto, ht, hsrc, hfg⟩ :=
    Compose.attest_source hret hx ((Trace.upTo_callAt _).2 ⟨le_rfl, hc⟩)
  have state : ∀ m, m ≤ k → (tr.upTo (tr.time k)).state x m = tr.state x m :=
    fun m hm => RunTrace.upTo_state_of_le hr.time_mono (hr.time_mono hm)
  have hjk : j < k := by omega
  have hj' := ((Trace.upTo_callAt _).1 hj).2
  change tr.time j = tr.time k at ht
  rw [state j hjk.le] at hsrc
  rw [state k le_rfl, state j hjk.le] at hfg
  have hreport : ReportAt tr x j src := ⟨ℓ, hj', hto, hsrc⟩
  have hxj : x ∈ H (tr.time j) := ht ▸ hx
  have hheld := (C.healing.report_in_frame hrun hxj hreport).1
  have hst : src ∈ (tr.state x k).fg.tree := hfg ▸ hheld
  have hR := Compose.fg_reachable hret hx k
  rw [state k le_rfl] at hR
  obtain ⟨⟨E, hE, hEr, hEC, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ hR src hst
  have hcut := (hr.cutLaw x k _ hc hx).1
  have hT := Compose.createAtt_T hcut
  have hTE : a.T = E.root := by rw [hT, ← hEr, hET, hEr]
  have hsub : (tr.state x k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨x, k, tr.time k, hd, fun m hm => hr.time_mono hm.le, hx, hX⟩
  have hEU := hsub hE
  have hsrcU := hsub hst
  have hECU := hEC.mono hsub
  refine ⟨j, src, E, hjk, ht, hreport, hc, hE, hTE.symm, hEr, hECU, ?_⟩
  rcases hsource cm proposer dg H tr b hrun hnc x j src hxj (ht ▸ hkb) hreport with
    hg | ⟨m, s, B, hmj, hxm, hmb, hevent, hsrcB⟩
  · have hcoh := Compose.Growing.honest_blocks_coherent_local hr hnc
    have hgen : P.genesisBlock A.genesisPayload ∈ tr.HonestBlocksAt H := by
      have hG := (Store.accepted_tree _ _ _ _ hR).2.2.1
      exact hsub hG
    obtain rfl : src = P.genesisBlock A.genesisPayload := hcoh.1 hsrcU hgen hg
    have hEs : E = P.genesisBlock A.genesisPayload := by
      cases hECU with
      | refl => rfl
      | tail h hp => cases hp.2.2
    exact Or.inl (hEs ▸ rfl)
  · exact Or.inr ⟨B, ⟨x, m, s, hxm, (hr.time_mono hmj).trans ht.le, hmb, hevent⟩,
      hECU.trans hsrcB⟩

theorem conditional_viability {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}
    (C : ACCorrectLocal A sg) (D : Data A) : ConditionalViability C D := by
  intro cm proposer dg H tr b hrun hnc y i t hread hf hrows hcompare B hB hBc
  obtain ⟨hy, ⟨hi, -⟩, ht0, htb⟩ := hread
  have hr := C.run.run_local hrun
  have hs := Trace.upTo_state tr y hi
  have hlocal := hr.upTo ht0
  have hfg := Compose.fg_projection_from
    (fun z _ => C.run.run_requirements hrun z) (C.run.run_root hrun) hlocal (hnc.upTo _)
  have hcoh := Compose.Growing.honest_blocks_coherent_local hr hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hr.time_mono ht0
  let G : A.Blk → Prop := fun X =>
    X ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anchored D tr H b t X
  have hsrc : Compose.FrameGeometry.RowsAbove (tr.upTo t) (H t) G y i
      ((tr.upTo t).state y i).fg.hj := by
    apply Compose.FrameGeometry.rowsAbove_iff.2
    intro X hX a ha hav hE hh
    have hX' : X ∈ ((tr.upTo t).projFG.store y i).tree := by
      rwa [Compose.FrameGeometry.store_eq hlocal hy i]
    rcases Store.tree_accepted hfg hy hX' with hg | ⟨m, hmi, hm⟩
    · subst X
      simp [Params.genesisBlock] at ha
    have hac := Compose.projFG_callAt.1 hm
    obtain ⟨hmt, hac⟩ := (Trace.upTo_callAt _).1 hac
    obtain ⟨k, hkm, hsign⟩ := hr.att_unforgeable y m a (hr.antitone hmt hy)
      (Or.inr ⟨X, ⟨true, hac⟩, ha⟩) (hr.antitone hmt hav)
    have hkt := (hr.time_mono hkm.le).trans hmt
    obtain ⟨E, hEU, hEr, hanchor⟩ := hrows a.val k a (hr.antitone hkt hav) hsign hkt
      (hkt.trans htb)
    obtain ⟨src, hc⟩ := hsign
    have hcut := (hr.cutLaw a.val k _ hc (hr.antitone hkt hav)).1
    have hT := Compose.createAtt_T hcut
    have hkstate := Trace.upTo_state tr a.val (fun j hj => (hr.time_mono hj.le).trans hkt)
    have hR := Compose.fg_reachable hlocal hav k
    rw [hkstate] at hR
    obtain ⟨j, hjk, ℓ, hj, hto, ht, hsrc, hfgstate⟩ :=
      Compose.attest_source hlocal hav ((Trace.upTo_callAt _).2 ⟨hkt, hc⟩)
    have hjt : tr.time j ≤ t := ((Trace.upTo_callAt _).1 hj).1
    have hjstate := Trace.upTo_state tr a.val (fun m hm => (hr.time_mono hm.le).trans hjt)
    rw [hjstate] at hsrc
    rw [hkstate, hjstate] at hfgstate
    have hheld : src ∈ (tr.state a.val k).fg.tree := by
      rw [hfgstate]
      exact (C.healing.report_in_frame hrun (hr.antitone hjt hav)
        ⟨ℓ, ((Trace.upTo_callAt _).1 hj).2, hto, hsrc⟩).1
    obtain ⟨⟨E', hE', hE'r, hE's, hE'h, hE'T⟩, -⟩ :=
      Store.entry_state_of_source _ _ _ _ hR src hheld
    have hE'U : E' ∈ tr.HonestBlocksAt H :=
      ⟨a.val, k, t, ht0, fun j hj => (hr.time_mono hj.le).trans hkt, hav, hE'⟩
    have hTE' : a.T = E'.root := by
      rw [← hE'r, hE'T] at hT
      exact hT.trans hE'r.symm
    have heq : E' = E := hcoh.1 hE'U hEU (hTE'.symm.trans hEr.symm)
    subst E'
    refine ⟨E, ?_, Compose.FrameGeometry.isHonestSource_iff.2 ⟨a.val, hav, k, ?_, ?_⟩⟩
    · refine ⟨⟨a.val, hav, k, by rwa [hkstate]⟩, ?_⟩
      rcases hanchor with hg | ⟨W, ⟨z, j, s, hz, hjk, hjb, he⟩, hEW⟩
      · exact Or.inl hg
      · exact Or.inr ⟨W, ⟨z, j, s, hz, hjk.trans hkt, hjb, he⟩, hEW⟩
    · rwa [hkstate]
    · rw [hkstate]
      exact (hE'T.trans hE'r.symm).trans hTE'.symm
  have hGG : ∀ X Y, G X → G Y → Compatible ((tr.upTo t).HonestBlocks (H t)) X Y := by
    intro X Y ⟨hXU, hX⟩ ⟨hYU, hY⟩
    have gen : ∀ Z, Z ∈ (tr.upTo t).HonestBlocks (H t) →
        Anc (tr.HonestBlocksAt H) (P.genesisBlock A.genesisPayload) Z :=
      fun Z hZ => ((Compose.FrameGeometry.honest_genesis_anc hlocal hZ).2).mono hsub
    have hgen := hsub (Compose.FrameGeometry.honest_genesis_anc hlocal hXU).1
    have hglobal : Compatible (tr.HonestBlocksAt H) X Y := by
      rcases hX with hg | ⟨W, hW, hXW⟩
      · obtain rfl : X = P.genesisBlock A.genesisPayload := hcoh.1 (hsub hXU) hgen hg
        exact Or.inl (gen Y hYU)
      rcases hY with hg | ⟨W', hW', hYW'⟩
      · obtain rfl : Y = P.genesisBlock A.genesisPayload := hcoh.1 (hsub hYU) hgen hg
        exact Or.inr (gen X hXU)
      rcases hcompare W W' hW hW' with h | h
      · exact Anc.total hcoh (hXW.trans h) hYW'
      · exact Anc.total hcoh hXW (hYW'.trans h)
    rcases hglobal with h | h
    · exact Or.inl (RunTrace.anc_upTo_of_right hr hnc ht0 hYU h)
    · exact Or.inr (RunTrace.anc_upTo_of_right hr hnc ht0 hXU h)
  have hBU : B ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hs]; exact hB.1⟩
  have hGB : ∀ X, G X → Compatible ((tr.upTo t).HonestBlocks (H t)) X B := by
    intro X ⟨hXU, hX⟩
    have hglobal : Compatible (tr.HonestBlocksAt H) X B := by
      rcases hX with hg | ⟨W, hW, hXW⟩
      · have hgU := (Compose.FrameGeometry.honest_genesis_anc hlocal hBU).1
        obtain rfl : X = P.genesisBlock A.genesisPayload := hcoh.1 (hsub hXU) (hsub hgU) hg
        exact Or.inl ((Compose.FrameGeometry.honest_genesis_anc hlocal hBU).2.mono hsub)
      rcases hBc W hW with h | h
      · exact Anc.total hcoh hXW h
      · exact Or.inl (hXW.trans h)
    rcases hglobal with h | h
    · exact Or.inl (RunTrace.anc_upTo_of_right hr hnc ht0 hBU h)
    · exact Or.inr (RunTrace.anc_upTo_of_right hr hnc ht0 hXU h)
  have hBt : B ∈ (Node.frame ((tr.upTo t).state y i)).tree := by rwa [hs]
  have hv := Compose.held_viable_of hlocal hfg hf hy hsrc hGG hGB hBt
  rwa [hs] at hv

end Consensus.Goldilocks.Generic.SleepyLayer1

end
