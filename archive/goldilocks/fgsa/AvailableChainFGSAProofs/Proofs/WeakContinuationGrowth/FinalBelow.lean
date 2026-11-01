module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepService
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Interfaces
public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.8; DC a finalized source is served before its finality action. -/
theorem wcg_finalBelow (hcausal : WCFinalityTargetEarlierStatement p c E rho) {ΔF : Time} {w :
  HealingWitness} {iStar : Nat} :
    WCGFinalBelowStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs hinv i x y hi hx hy
  have inv := hinv i hi
  obtain ⟨D, hD, hF⟩ := ((inv.finite i hi.1 le_rfl).store x hx).fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · exact Gen.Pure.block_preceq_trans
      (inv.lowFinalized i x D _ _ hi.1 le_rfl ⟨hx, hD⟩ hF rfl hlo)
      (Gen.Pure.block_preceq_trans hs.sourcePrefix (inv.served i y hi.1 le_rfl hy))
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at *; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at *; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, v, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, hgate, hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ
      (hroots.toNamedRootCollisionFree E rho) hheldRows hfinalHead hqc
      hemitted i x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E rho i x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt v rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
      (Gen.Pure.block_preceq_trans (heq ▸ hbelow) (inv.served i y hi.1 le_rfl hy))
  have hafter : iStar ≤ jt := Nat.le_of_not_gt hbefore
  have ht : IsGateTick p c rho jt v (rt * p.R) := haT.2.1
  have hlabel' : w.u < rt * p.R := by
    by_contra hn
    have hle : rt * p.R ≤ w.u := Nat.le_of_not_gt hn
    have htime : SA.gateTime p.toParams (rt * p.R) ≤ SA.gateTime p.toParams w.u := by
      have hcast : ((rt * p.R : Nat) : Int) ≤ w.u := Int.ofNat_le.mpr hle
      change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ
      nlinarith [p.deltaPos]
    have hf := V2.D.Engine.filter_false_of_index_ge hvalid.toScheduleWellFormed
      (cutPred (SA.gateTime p.toParams w.u)) (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      (show afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ jt from hs.cut ▸ hafter) ht
    have hc : cutPred (SA.gateTime p.toParams w.u)
        (.tick v (SA.gateTime p.toParams (rt * p.R)) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (htime.lt_or_eq.imp id (fun he => ⟨he, le_rfl⟩)))
    rw [hc] at hf
    cases hf
  have hhor : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ ≤ rho.horizon :=
    hgap.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? haf.2.1)).2
  have hcut : afterTicksIdx rho (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ) ≤ i := by
    apply le_trans (b := jf) _ (Nat.le_of_lt hjf)
    by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hm : V2.Event.tick z (p.actionTime rf) ∈ rho.events.filter
        (cutPred (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)) := by
      rw [V2.D.Engine.filter_eq_take hvalid.toScheduleWellFormed _ (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := jf)
      change (rho.events.take (afterTicksIdx rho
        (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)))[jf]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact haf.2.1
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have htime : p.actionTime rf ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with ht | ⟨ht, _⟩
      · exact ht.le
      · exact ht.le
    exact (not_lt.mpr htime) hgap
  have hraw := (gateResultAt_eq_gateResult p c E rho hvalid.toScheduleWellFormed ht).trans hgate
  have hserved := wcg_service4 hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv jt v (rt * p.R) B haT.1 hafter ht hlabel' hraw hhor
    i y hcut hi.2 hy
  exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
    (Gen.Pure.block_preceq_trans hKB hserved)

end AvailableChain.FGSA.Run
end
