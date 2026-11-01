module
public import AvailableChainFGCompose.Statements.ExecutionAcceptance
public import AvailableChainFGCompose.Proofs.Finality.Accept -- shake: keep (policy)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHistoricalReads P.State Body) (Wr : FGDependencyWireReads P Body Wire)
variable (O : FGExecutionObs V P)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)

/- The two pure store lemmas below reproduce the local algebra of Finality/Accept.
Its helpers are private; no ordinary execution induction is transported. -/
/-- DC: SAME entry comparison on one path, with the window height view. -/
private theorem acceptance_J_path (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (st : Store (Fin n))
    (hI : KitFG.FGStoreInvariant (KitFG.Window.certificateHeight Ef cfg K)
      (KitFG.Window.certificateFinality Ef cfg K) st)
    (W : FGBlock (Fin n)) (hpath : FGBlock.Preceq st.J W) :
    FGBlock.Preceq (KitFG.Window.certificateHeight Ef cfg K W).J st.J ∨
      st.h_j < (KitFG.Window.certificateHeight Ef cfg K W).h_j := by
  have hH := (KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height
  have hJ : FGJustificationLaws (KitFG.Window.certificateHeight Ef cfg K) :=
    FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge Ef cfg K hK)
  have hJW := KitFG.preceq_trans (hH.justified_preceq_entry W) (hH.entry_preceq W)
  rcases KitFG.preceq_total_of_common hJW hpath with h | h
  · exact Or.inl h
  by_cases hz : (KitFG.Window.certificateHeight Ef cfg K W).h_j = 0
  · exact Or.inl (hJ.J_zero W hz ▸ KitFG.genesis_preceq st.J)
  by_cases hs : st.h_j = 0
  · right
    rw [hs]
    exact Nat.pos_of_ne_zero hz
  obtain ⟨C, _, _, hc, he⟩ := hI.pair.1
  have hsh : (KitFG.Window.certificateHeight Ef cfg K st.J).h = st.h_j := by
    rw [he, hJ.J_height C (fun h => hs (hc.trans h)), ← hc]
  have hwh := hJ.J_height W hz
  have hle := hH.h_mono h
  rw [hsh, hwh] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  left
  have hp := hH.entry_plateau h (hsh.trans (heq.trans hwh.symm))
  rw [he, hJ.J_entry C, hJ.J_entry W] at hp
  rw [he, hp]
  exact KitFG.preceq_refl _

/-- DC: INTENTIONAL selected handler guards accept the window finality. -/
private theorem acceptance_update (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (st : Store (Fin n))
    (hI : KitFG.FGStoreInvariant (KitFG.Window.certificateHeight Ef cfg K)
      (KitFG.Window.certificateFinality Ef cfg K) st)
    (W : FGBlock (Fin n))
    (hF : FGBlock.Preceq st.F (SimplexFG.Window.derive Ef cfg K W).F)
    (hmem : (SimplexFG.Window.derive Ef cfg K W).F ∈ insert W st.TF)
    (hj : FGBlock.Preceq st.J W ∨ st.h_j < (SimplexFG.Window.derive Ef cfg K W).h_j)
    (hcap : max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) ≤
      (SimplexFG.Window.derive Ef cfg K W).h + 1) :
    FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
      (SimplexFG.Window.update_finality Ef cfg K { st with TF := insert W st.TF } W).F := by
  classical
  have hσJ : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
      (SimplexFG.Window.derive Ef cfg K W).J := KitFG.Window.window_F_preceq_J Ef cfg K hne hK W
  have hFJ := KitFG.preceq_trans hF hσJ
  have hj' : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).J st.J ∨
      st.h_j < (SimplexFG.Window.derive Ef cfg K W).h_j := by
    rcases hj with hj | hj
    · exact acceptance_J_path Ef cfg K hne hK st hI W hj
    · exact Or.inr hj
  have hJW : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).J W :=
    KitFG.preceq_trans
      ((KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height.justified_preceq_entry W)
      ((KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height.entry_preceq W)
  let st1 : Store (Fin n) :=
    { st with TF := insert W st.TF, h_max := max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) }
  let st2 := if FGBlock.preceq st.F (SimplexFG.Window.derive Ef cfg K W).J &&
      decide (lexKey (st.h_j, st.J) <
        lexKey ((SimplexFG.Window.derive Ef cfg K W).h_j, (SimplexFG.Window.derive Ef cfg K W).J))
    then { st1 with
      J := (SimplexFG.Window.derive Ef cfg K W).J
      h_j := (SimplexFG.Window.derive Ef cfg K W).h_j } else st1
  have h2F : st2.F = st.F := by dsimp only [st2]; split_ifs <;> rfl
  have h2T : st2.TF = insert W st.TF := by dsimp only [st2]; split_ifs <;> rfl
  have h2H : st2.h_max = max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) := by
    dsimp only [st2]; split_ifs <;> rfl
  have h2J : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J := by
    dsimp only [st2]
    split_ifs with hu
    · exact hσJ
    · rcases hj' with hj | hj
      · exact KitFG.preceq_trans hσJ hj
      · exfalso
        apply hu
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hFJ, Prod.Lex.left _ _ hj⟩
  have hv : (SimplexFG.Window.derive Ef cfg K W).F ∈
      SimplexFG.Window.acceptViable Ef cfg K st2 := by
    rw [SimplexFG.Window.acceptViable_def]
    apply Finset.mem_filter.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2T.symm ▸ hmem, ?_, ?_⟩
    · exact h2F.symm ▸ hF
    · refine ⟨W, h2T.symm ▸ Finset.mem_insert_self _ _, KitFG.preceq_trans hσJ hJW, ?_⟩
      rw [h2H]
      simp only [Height] at hcap ⊢
      omega
  rw [SimplexFG.Window.update_finality_def]
  change FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
    (if FGBlock.preceq st2.F (SimplexFG.Window.derive Ef cfg K W).F &&
      decide (st2.F ≠ (SimplexFG.Window.derive Ef cfg K W).F) &&
      FGBlock.preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J &&
      decide ((SimplexFG.Window.derive Ef cfg K W).F ∈ SimplexFG.Window.acceptViable Ef cfg K st2)
    then { st2 with F := (SimplexFG.Window.derive Ef cfg K W).F } else st2).F
  by_cases he : st2.F = (SimplexFG.Window.derive Ef cfg K W).F
  · simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
      Bool.false_and]
    rw [ite_eq_right (by decide)]
    exact he.symm ▸ KitFG.preceq_refl _
  · have ht : (FGBlock.preceq st2.F (SimplexFG.Window.derive Ef cfg K W).F &&
        decide (st2.F ≠ (SimplexFG.Window.derive Ef cfg K W).F) &&
        FGBlock.preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J &&
        decide ((SimplexFG.Window.derive Ef cfg K W).F ∈
          SimplexFG.Window.acceptViable Ef cfg K st2)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨h2F.symm ▸ hF, he⟩, h2J⟩, hv⟩
    rw [ht, ite_eq_left rfl]
    exact KitFG.preceq_refl _

omit [DecidableEq V] in
/-- F ancestry propagates along the bounded receiver-local microstep sequence. -/
theorem acceptance_F_keep (L : FGObservedFinalityLaws R rho O) (x : V)
    {i k : Nat} (hik : i ≤ k) (hk : k ≤ O.cutLength x) :
    FGBlock.Preceq (R.core (O.cutState x i)).fg.F (R.core (O.cutState x k)).fg.F := by
  induction k, hik using Nat.le_induction with
  | base => exact KitFG.preceq_refl _
  | succ k hik ih =>
    exact KitFG.preceq_trans (ih (by omega)) (L.f_step x k (by omega))

/-- The accepted X1a retention statement, with the same selected step and target. -/
theorem selectedAcceptance_keep
    (update : Store (Fin n) → FGBlock (Fin n) → Store (Fin n)) :
    SelectedAcceptanceKeepStatement R S E rho H Wr O update := by
  rw [SelectedAcceptanceKeepStatement_def]
  intro L x W U d A hU k hk hlen
  exact KitFG.preceq_trans hU (acceptance_F_keep R rho O L x hk hlen)

/-- An actual event's post-leaf F reaches the strict deadline prefix. Completion may
add more blocks; only F ancestry, cut order and the event's strict time are used. -/
theorem acceptance_at_strict_read (OL : FGExecutionObsLaws E rho O)
    (FL : FGObservedFinalityLaws R rho O) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {j k : Nat} {e : V2.Event V P.Object} {U : FGBlock (Fin n)} {d : Time}
    (he : rho.events[j]? = some e) (hk : k ≤ O.done x j) (ht : e.time < d)
    (hU : FGBlock.Preceq U (R.core (O.cutState x k)).fg.F) :
    AcceptsFinalBefore_obs R rho O x U d := by
  have hj := (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).2 ht
  have hlen : V2.D.Run.idxBefore rho d ≤ rho.events.length := by
    rw [V2.D.Run.idxBefore_def]
    exact List.length_filter_le ..
  obtain ⟨m, hm⟩ : ∃ m, V2.D.Run.idxBefore rho d = m + 1 :=
    ⟨V2.D.Run.idxBefore rho d - 1, by omega⟩
  have hmLen : m < rho.events.length := by omega
  have hem := List.getElem?_eq_getElem hmLen
  have hjm : j ≤ m := by omega
  have hkm : k ≤ O.done x m := by
    rcases Nat.eq_or_lt_of_le hjm with rfl | hlt
    · exact hk
    · have ho := OL.event_order j m e rho.events[m] x he hem hlt
      have hc := OL.cut_order m rho.events[m] x hem
      omega
  have hbound := (OL.cut_order m rho.events[m] x hem).2.2.2
  have hret := KitFG.preceq_trans hU (acceptance_F_keep R rho O FL x hkm hbound)
  rw [OL.done_state m rho.events[m] x hem] at hret
  simpa only [AcceptsFinalBefore_obs_def, obsStrictState_def, hm] using hret

/-- Conditional selected acceptance at the actual cut, retaining the original token. -/
theorem acceptBefore_driver : AcceptBeforeDriverStatement R S E rho H Wr O Ef cfg K := by
  rw [AcceptBeforeDriverStatement_def]
  intro hne hK OL hs x W U d A EL _ hfinal G
  have hbound := (OL.accept_origin x A.step A.token A.accepts).1
  have hcover : FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F := by
    by_cases hc : FGBlock.Preceq U (R.core (O.cutState x A.step)).fg.F
    · exact KitFG.preceq_trans hc (EL.finality.f_step x A.step hbound)
    have hF := G.finCmp.resolve_right hc
    rw [A.effect]
    exact KitFG.preceq_trans hfinal
      (acceptance_update Ef cfg K hne hK _ G.invariant W
        (KitFG.preceq_trans hF hfinal)
        EL.leaf.2
        (G.jPath hc) (G.cap hc))
  refine ⟨(OL.accept_time x A.step A.token A.accepts).trans_lt A.before_deadline,
    hcover, ?_, ?_⟩
  · obtain ⟨e, he⟩ := A.event_some
    have ht := OL.segment_time A.eventIndex e x A.step he A.segment.1 A.segment.2.le
    exact acceptance_at_strict_read R E rho O OL EL.finality hs he A.segment.2
      (ht ▸ A.before_deadline) hcover
  · intro k hk hlen
    exact KitFG.preceq_trans hcover (acceptance_F_keep R rho O EL.finality x hk hlen)

/-- Pending fold followed by acceptance of exactly the same carrier and target. -/
theorem finalizePending_driver : FinalizePendingDriverStatement R S E rho H Wr O Ef cfg K := by
  rw [FinalizePendingDriverStatement_def]
  intro hne hK OL hs x y U X d A EL hhor fold G
  have hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F := by
    obtain ⟨child, e, he, hj, hX, Q, hQ, cover⟩ := fold
    cases X with
    | genesis => exact (child rfl).elim
    | node B s root body rows =>
      have hc : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ row ∈ rows,
          row.signer = i ∧ row.finality_pair = some ⟨e.j, e.X.root⟩ := by
        intro i hi
        rcases cover i hi with hb | ⟨row, hrow, hsign, hf⟩
        · exact Or.inl hb
        · exact Or.inr ⟨row, hrow, hsign, by rw [hj, hX]; exact hf⟩
      have r := KitFG.Window.window_finality_of_cover Ef cfg K hne hK B s root body rows e he
        Q hQ hc
      rw [hX] at r
      exact r.1
  exact acceptBefore_driver R S E rho H Wr O Ef cfg K hne hK OL hs x X U d A EL hhor hfinal G

/-- Ordinary bridge, IFF: the actual strict-prefix conclusion is the frozen strict-time
read under the sorted schedule. This equivalence asserts coverage, not a receipt. -/
theorem ordinary_acceptsFinalBefore_iff (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (U : FGBlock (Fin n)) (d : Time) :
    AcceptsFinalBefore_obs R rho (ordinaryFGExecutionObs E rho) x U d ↔
      AcceptsFinalBefore R E rho x U d := by
  rw [AcceptsFinalBefore_obs_def, obsStrictState_def]
  change FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho
    (V2.D.Run.idxBefore rho d) x)).fg.F ↔ _
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
  rfl

end AvailableChain.FGCompose
end
