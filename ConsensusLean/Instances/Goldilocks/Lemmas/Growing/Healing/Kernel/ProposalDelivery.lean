module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Historical releases delivered to a proposal

Service remains owed after the sender is compromised. Only the recipient's local
laws are read on the proposal prefix; the sender is honest at each release.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {T : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- A historically honest release and head acceptance reach an honest proposal reader.
Equivocation is retained as an alternative to membership, even if the voter is compromised. -/
theorem heldAtProposal_of_writer_at
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsvc : ServiceWindowBefore H U a₀ b T) {s : Nat}
    (ha₀ : a₀ ≤ sp.ts s) (hb : sp.ts s + 3 * sp.Δ ≤ b)
    {w x : Fin sp.n} {i : Nat} (hx : x ∈ H (T.time i))
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : T.CallAt x i ell)
    (ht : T.time i = sp.ts (s + 1 : Nat))
    (hrs : ∀ k ≤ i, T.RestartAt x k → T.time k < sp.ts s)
    {v : Vote sp.n} (hvs : v.slot = s)
    (hsend : ∃ k, w ∈ H (T.time k) ∧ T.SendOrAdmit w k v ∧
      sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ)
    (hhead : ∃ B ∈ U, B.root = v.head ∧ Anc U ell.frame.F B ∧
      (B.root = sp.genesisRoot ∨
        (∃ k, w ∈ H (T.time k) ∧ T.AcceptAt w k B ∧
          a₀ ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∨
        ∃ k ≤ i, T.AcceptAt x k B ∧ T.time k < sp.ts s + 3 * sp.Δ)) :
    HeldAtProposal (T.state x i) ell.frame s v := by
  have hm := hr.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := ts_succ s
  have hpre := hr.upTo (hr.time_nonneg i)
  have hc' := (Trace.upTo_callAt T).mpr (And.intro le_rfl hc)
  have hs : (T.upTo (T.time i)).state x i = T.state x i :=
    Trace.upTo_state T x fun _ hk => hm hk.le
  have hrs' : ∀ k ≤ i, ACTrace.RestartAt (T.upTo (T.time i)) x k →
      (T.upTo (T.time i)).time k < sp.ts s := by
    intro k hk hrest
    exact hrs k hk ((ACTrace.upTo_restartAt).mp hrest).2
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hpre hx hc'
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      T.deadline x k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t htk
    have h := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hk) hr').le) t
    change T.deadline x k t ≤ max t (sp.ts s) + sp.Δ at h
    have hmax := max_lt htk (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith)
    linarith
  refine heldAtProposal_iff.mpr ⟨?_, ?_⟩
  · obtain ⟨k, hw, hsend, hk1, hk2⟩ := hsend
    have hv := sync_window_before_forward hr hsvc hw hsend (ha₀.trans hk1)
      (by linarith) hx hc (fun k' hk' hr' => (hrs k' hk' hr').le.trans hk1)
      (by rw [ht, hts]; linarith) (fun t ht1 ht2 => by
        have hslot : sp.slot t = s := slot_of_mem sp s (hk1.trans ht1)
          (by rw [hts]; linarith)
        rw [hslot, hvs]
        omega)
    simpa only [hvs] using hv
  · obtain ⟨B, hBU, hBr, hFB, hacc⟩ := hhead
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hpre hx i ell hc'
    obtain ⟨hBt, hAB⟩ : B ∈ ell.frame.tree ∧
        AcceptedBefore (T.upTo (T.time i)) x B (sp.ts s + 3 * sp.Δ) := by
      rcases hacc with hg | ⟨k, hw, hak, hka, hkt⟩ | ⟨k, hki, hak, hkt⟩
      · refine ⟨?_, Or.inl hg⟩
        obtain rfl : B = G := hpre.coherent.1 hBU hGU (hg.trans hGr.symm)
        obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hFB
        · exact h ▸ hPhi.rooted.1
        · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
      · obtain ⟨q, hqi, haq, hqt⟩ := hsvc.relay w k B hw hak hka x i ell hx hc
          (le_of_lt ((hdl i le_rfl _ hkt).trans_le hb))
          (by rw [ht, hts]; linarith [hdl i le_rfl _ hkt]) hFB
        have haq' := (ACTrace.upTo_acceptAt).mpr ⟨hm hqi, haq⟩
        exact ⟨mem_tree_of_acceptAt sp hpre hx haq' hqi hc' hFB,
          Or.inr ⟨q, haq', hqt.trans (hdl q hqi _ hkt)⟩⟩
      · have hak' := (ACTrace.upTo_acceptAt).mpr ⟨hm hki, hak⟩
        exact ⟨mem_tree_of_acceptAt sp hpre hx hak' hki hc' hFB,
          Or.inr ⟨k, hak', hkt⟩⟩
    refine ⟨B, hBt, hBr, ?_⟩
    rw [← hs]
    exact (blockStamp_lt_of_acceptedBefore sp hpre hx hc' hBt hAB
      (fun k hk hrk => (hrs' k hk hrk).trans (by linarith))
      (Or.inl (by change _ ≤ T.time i; rw [ht, hts]; linarith))).trans
        (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))

end Consensus.Goldilocks.SA.Growing

end
