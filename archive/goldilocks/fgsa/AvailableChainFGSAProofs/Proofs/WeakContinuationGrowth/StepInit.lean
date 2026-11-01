module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Origins
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! WC plan §6.5; DC finite initialization at the completed seed gate. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC the seed supplies the initial state and earlier high sources. -/
theorem wcg_init : WCGInitStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF _hfaultQ
    haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows hscopeRows _hfinalHead hs hwithin
  have noResult : ∀ j x s B, ¬ WCResult p c E rho w iStar iStar j x s B := by
    intro j x s B hr
    exact Nat.not_lt_of_ge hr.afterCut hr.completed
  have noGate : ∀ j x s, j < iStar → w.u < s → ¬ IsGateTick p c rho j x s := by
    intro j x s hj hlabel he
    have htime : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams w.u := by
      have hcut := V2.D.Engine.filter_eq_take hvalid.toScheduleWellFormed
        (cutPred (SA.gateTime p.toParams w.u)) (by
          intro e f hk hf
          exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      have hm : V2.Event.tick x (SA.gateTime p.toParams s) ∈
          rho.events.filter (cutPred (SA.gateTime p.toParams w.u)) := by
        rw [hcut]
        apply List.mem_of_getElem? (i := j)
        change (rho.events.take (afterTicksIdx rho (SA.gateTime p.toParams w.u)))[j]? = _
        rw [List.getElem?_take_of_lt (show j < afterTicksIdx rho
          (SA.gateTime p.toParams w.u) from hs.cut ▸ hj)]
        exact he
      have hk := of_decide_eq_true (List.mem_filter.mp hm).2
      rcases Prod.Lex.toLex_le_toLex.mp hk with ht | ⟨ht, _⟩
      · exact le_of_lt ht
      · exact le_of_eq ht
    have hd := p.deltaPos
    have hl : (w.u : Int) < (s : Int) := Int.ofNat_lt.mpr hlabel
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ at htime
    nlinarith
  refine {
    interval := ⟨le_rfl, hwithin⟩
    nonempty := ?_
    ordered := ?_
    sameLabel := ?_
    retrospective := ?_
    preCutHigh := ?_
    suffixSources := ?_
    highCertificates := ?_
    lowFinalized := ?_
    liveTargets := ?_
    oldLiveTargets := ?_
    suffixSaved := ?_
    suffixFast := ?_
    outputOrigin := ?_
    served := ?_
    transitions := ?_
    finite := ?_
    carrier := ?_ }
  · intro j x s hle hlt
    omega
  · intro j k x y s r B C hr
    exact (noResult j x s B hr).elim
  · intro j k x y s B C hr
    exact (noResult j x s B hr).elim
  · intro j x s B hr
    exact (noResult j x s B hr).elim
  · intro j x r a e hj ha he hh
    obtain ⟨K, B, hK, heq, _, _, _, hbelow⟩ := hs.highSources j x r a e hj ha he hh
    exact ⟨K, hK, heq, hbelow⟩
  · intro j x r K hle hlt
    omega
  · intro k x W X hle hge hx hW hX hn hh
    have hk : k = iStar := Nat.le_antisymm hge hle
    subst k
    have ho := hs.finite.certified x hx W hW X hX hn
    refine ⟨ho, ⟨Or.inl ?_⟩⟩
    obtain ⟨j, y, r, a, K, B, hj, ha, he, hK, hXK, _⟩ := ho.origin
    obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources j y r a _ hj ha he hh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow)
  · intro k x D X h _ _ hD hF hh hlow
    exact (wcg_lowFinalized (hroots.toNamedRootCollisionFree E rho) haccountable hs D X h
      (wcg_finalizedOccurrence hscopeRows hnoslash D X h
        (rootScope_store hD.1 hD.2) hF hh) hlow).1
  · intro k x row hle hge hx hr ht
    have hk : k = iStar := Nat.le_antisymm hge hle
    subst k
    exact ⟨Or.inl (hs.liveTargets x hx row hr ht)⟩
  · intro k x row hle hge hx hr _ ht
    have hk : k = iStar := Nat.le_antisymm hge hle
    subst k
    exact hs.liveTargets x hx row hr ht
  · intro k x s B hle hge hx hlabel hB
    have hk : k = iStar := Nat.le_antisymm hge hle
    subst k
    obtain ⟨j, hj, _hrf, he, _⟩ := hs.finite.saved x hx s B hB
    exact (noGate j x s hj hlabel he.1).elim
  · intro k x s X hle hge hx hlabel hX
    have hk : k = iStar := Nat.le_antisymm hge hle
    subst k
    obtain ⟨j, hj, _hrf, he, _⟩ := hs.finite.fastWrites x hx s X hX
    exact (noGate j x s hj hlabel he.1).elim
  · intro k x hle hge hx
    have hk : k = iStar := Nat.le_antisymm hge hle
    exact Or.inl (hk ▸ hs.refreshed x hx)
  · intro k x hle hge hx
    have hk : k = iStar := Nat.le_antisymm hge hle
    rw [hk, hs.refreshed x hx.1.1]
    exact Gen.Pure.block_preceq_refl _
  · intro k x hle hlt
    omega
  · intro k hle hge
    exact (Nat.le_antisymm hge hle) ▸ hs.finite
  · obtain ⟨W, hW, hh, _, hstored⟩ := hs.carrier
    refine ⟨W, hW, hh, ?_⟩
    intro k x hle hge hx
    exact (Nat.le_antisymm hge hle) ▸ hstored x hx

end AvailableChain.FGSA.Run
end
