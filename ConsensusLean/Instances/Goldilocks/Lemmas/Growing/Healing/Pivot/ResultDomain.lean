module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.VoterReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.TargetOlder
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.TargetCompare
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.WriterCompatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Windows
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Result-prefix domains below the clean vote induction

The only additional supplier is the original frozen held-target vote-domain contract.
In particular this leaf does not import clean source votes or protected-source compatibility.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The result-prefix reduction uses the frozen vote-domain supplier, not its row-bound helper. -/
theorem result_prefix_vote_domain_before_of_domain_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    (hdomain : ∀ {x y v : Fin sp.n} {r i q m : Nat}
      {B S : SA.Blk sp.n (List (FG.Att sp.n))},
      x ∈ H (tr.time r) → y ∈ H (tr.time i) → B ∈ (tr.state x r).fg.tree → tr.time r ≤ b →
      ∀ {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))},
      SA.CastAt tr.projAC y i ell e → tr.time i ≤ b →
      (Anc (tr.HonestBlocksAt H) ell.frame.F B →
        B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) →
      HighOrigin tr H g v q m S → tr.time q ≤ b → m < e.msg.slot →
      Compatible (tr.HonestBlocksAt H) B S →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O → Compatible (tr.HonestBlocksAt H) B O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O → Compatible (tr.HonestBlocksAt H) S O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O') →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hcoh := hac.localRun.coherent
  obtain ⟨v, d, m, S, hseed, hda, hm⟩ := hp.reset_seed_at
  have hdb := hda.trans hp.reset_le
  have hms : m < s := by rw [Healing.cleanLabel_eq] at hs; omega
  have hts : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin_at hseed hdb).trans ((SA.ts_le_iff sp).mpr (by omega))
  have htiming : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  obtain ⟨z, hz, q, hqr, ev, hv, _, hvs, hVB⟩ :=
    result_supporter_at hp hc hx hres hBC hrb hts
  have hzq := hp.run.antitone (hp.run.time_mono hqr.le) hz
  have hqb := (hp.run.time_mono hqr.le).trans hrb
  obtain ⟨ellX, hupd, hconf, hCV⟩ := hres
  have hCx := (frame_tree_subset_at hp.run hp.noColl hx hupd.1).2 (SA.deepest_mem hconf).1.1
  have hBx : B ∈ (tr.state x r).fg.tree := by
    have ht := hp.run.time_nonneg r
    exact mem_of_honest_anc_at hp.run hp.noColl ht
      (fun _ hq => hp.run.time_mono hq.le) hx hBC hCx
  have hreset : ∀ w c, w ∈ H (tr.time c) → tr.time c ≤ b → tr.projAC.RestartAt w c →
      tr.time c ≤ sp.ts s := by
    intro w c hw hcb hrest
    apply (restart_le_before_at hp hw (Compose.projAC_restartAt.mp hrest) hcb).trans
    have hh := (SA.ts_le_iff sp).mp ((Healing.cutZ_eq sp g) ▸ hts)
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hgs : g ≤ sp.ts s := by linarith [le_gbar g, sp.toParams.hΔ]
  apply hdomain hx hy hBx hrb hcast hib
    (raw_writer_voterBlockTree_before_at hp hc hx hy
      (Or.inl ⟨ellX, hupd, hconf, hCV⟩) hBC htiming hcast hsi)
    hseed hdb (by omega)
    (target_compatible_older_origin_at hp hseed hdb hzq hv hqb hvs hms hVB)
  · intro w c n O hci ho
    have hcb := (hp.run.time_mono hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact target_compatible_older_origin_at hp ho hcb hzq hv hqb hvs hn hVB
    · obtain ⟨ellD, D, DV, _, hfl, hOD⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
      have hsvc := hp.sync.ac_service_at hp.run (lo := g) (hi := b) le_rfl
      have hcomp : Compatible (tr.HonestBlocksAt H) C D := by
        rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            (SA.frameIn_of_callAt (hac.upTo (hp.run.time_nonneg c)).localRun ho.1
              ((Trace.upTo_callAt _).mpr ⟨le_rfl, huD.1⟩)).2
          have hRR := SA.Growing.result_result_compatible_window_before_at hac hsvc hgs hx ho.1
            ⟨ellX, hupd, hconf, hCV⟩ ⟨ellD, huD, hR, rfl⟩ hrb hcb
            (fun k hk hrest => hreset x k (hp.run.antitone (hp.run.time_mono hk) hx)
              ((hp.run.time_mono hk).trans hrb) hrest)
            (fun k hk hrest => hreset w k (hp.run.antitone (hp.run.time_mono hk) ho.1)
              ((hp.run.time_mono hk).trans hcb) hrest)
          rcases hRR with h | h
          · exact SA.anc_total hcoh h hDR
          · exact Or.inr (hDR.trans h)
        · exact SA.Growing.result_optimistic_compatible_window_before_at hac hsvc hgs hx ho.1
            ⟨ellX, hupd, hconf, hCV⟩ hop hrb hcb
            (fun k hk hrest => hreset x k (hp.run.antitone (hp.run.time_mono hk) hx)
              ((hp.run.time_mono hk).trans hrb) hrest)
      rcases hcomp with h | h
      · exact SA.anc_total hcoh (hBC.trans h) hOD
      · exact SA.anc_total hcoh hBC (hOD.trans h)
    · exact KernelProof.target_compatible_later_origin_before_at hp ho hci hcb hn hprior
  · intro w c n O hci ho
    exact hp.origins_compatible_at hseed hdb ho ((hp.run.time_mono hci.le).trans hib)
  · intro w c n O hci ho w' c' n' O' hci' ho'
    exact hp.origins_compatible_at ho ((hp.run.time_mono hci.le).trans hib)
      ho' ((hp.run.time_mono hci'.le).trans hib)

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
