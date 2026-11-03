module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready

public section

/-! # Conditional post-stop outage adapters -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-- Among a slow lock's consecutive labels, at least one is outside the outage pollution
window, under the gap budget `(4k − 5)Δ`: the polluted slot starts lie in the open interval
`(start − 2Δ, stop − Δ)`, of length at most `(4k − 4)Δ`, so at most `k − 1` of them. -/
theorem exists_unpolluted_label (sp : SA.SAParams) {start stop : Time}
    (hgap : stop - start ≤ (4 * (sp.k : Time) - 5) * sp.Δ) (s : Int) :
    ∃ m : Int, s - (sp.k : Int) < m ∧ m ≤ s ∧
      (sp.ts m + 2 * sp.Δ ≤ start ∨ stop ≤ sp.ts m + sp.Δ) := by
  have hk : (2 : Int) ≤ sp.k := by exact_mod_cast sp.two_le_k
  by_contra hn
  have hfirst : start < sp.ts (s - sp.k + 1) + 2 * sp.Δ := by
    by_contra h
    exact hn ⟨s - sp.k + 1, by omega, by omega, Or.inl (le_of_not_gt h)⟩
  have hlast : sp.ts s + sp.Δ < stop := by
    by_contra h
    exact hn ⟨s, by omega, le_rfl, Or.inr (le_of_not_gt h)⟩
  simp only [SA.SAParams.ts] at hfirst hlast
  nlinarith

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A single compatible result in the slow window suffices to make a stored slow lock
compatible. The unpolluted-result producer is an explicit hypothesis. -/
theorem slow_lock_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {l : SA.Lock} (hl : l ∈ (tr.state x i).ac.locks) (hlf : l.fast = false)
    (hgood : ∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < i → SA.ResultAt tr.projAC x c m.toNat C CV →
        Compatible (tr.HonestBlocks H) C B) :
    ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L B := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hl' : l ∈ (tr.projAC.state x i).locks := by
    rw [projAC_state hrun.toLocalRun hx i]; exact hl
  obtain ⟨c, hci, ℓ, C, CV, hu, hC, Lb, hLb, hLbC, ⟨L, hL, hLr, hLLb⟩, hsave⟩ :=
    SA.slow_lock_saved hr hx i l hl' hlf
  obtain ⟨m, hm, hms, hm0, hgood⟩ := hgood
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hx hu.1
  have down : ∀ {X Y}, Anc (tr.HonestBlocks H) X Y → Compatible (tr.HonestBlocks H) Y B →
      Compatible (tr.HonestBlocks H) X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hr.coherent hXY h
  refine ⟨L, hL, hLr, down hLLb ?_⟩
  rcases hms.lt_or_eq with hms | hms
  · obtain ⟨S, hS, hsaved, hLbS⟩ := hsave m hm hms
    have hmn : (m.toNat : Int) = m := Int.toNat_of_nonneg hm0
    obtain ⟨k, hkc, C', CV', hC', hroot⟩ := SA.saved_result hr hx c m.toNat (by
      simpa only [hmn] using hsaved)
    obtain ⟨ℓ', hu', hconf, -⟩ := id hC'
    have hC'mem := (SA.frameIn_of_callAt hr hx hu'.1).2 (SA.deepest_mem hconf).1.1
    have heq : C' = S := hr.coherent.1 hC'mem (hΦU hS) hroot
    exact down (Anc.mono hΦU hLbS) (heq ▸ hgood k C' CV' (hkc.trans hci) hC')
  · have hmn : m.toNat = l.slot := by omega
    exact down (Anc.mono hΦU hLbC) (hgood c C CV hci (hmn ▸ hC))

end Consensus.Goldilocks.Compose
