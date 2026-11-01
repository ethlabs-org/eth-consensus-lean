module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Origins -- shake: keep (WC interface)
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainKitFG.CausalCapCore

public section

/-! WC plan §6.8; DC the target action strictly precedes the finality action. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.8; DC finality uses the earlier target source read by its honest signer. -/
theorem wc_finalityTargetEarlier : WCFinalityTargetEarlierStatement p c E rho := by
  classical
  intro hvalid hlinked hfaultQ hroots hheldRows hfinalHead _hqc hemitted i x D X h hD
    hpos hF hh
  let bad := Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base .fg) k ∉ rho.honest)
  have hsub : bad.image (rho.seatOf (.base .fg)) ⊆ Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ((@Finset.mem_filter (Fin p.n)
      (fun k => rho.seatOf (.base .fg) k ∉ rho.honest)
      (fun _ => @instDecidableNot _ (Classical.propDecidable _)) Finset.univ k).mp hk).2
  have hinj : Function.Injective (rho.seatOf (.base .fg)) :=
    (hlinked.toCStar (.base .fg) trivial).1
  have hcard : bad.card ≤ (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective bad hinj).symm.trans_le (Finset.card_le_card hsub)
  have hw : p.E.weightOf bad = bad.card := by
    change (∑ _ ∈ bad, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  have hcap : p.E.weightOf bad < p.E.q := by
    rw [hw, hq]
    exact hcard.trans_lt hfaultQ.lt
  have honestRow : ∀ k v W, HeldAt p c E rho k v W →
      ∀ a ∈ chainRows W, a.signer ∉ bad →
      ∃ j z r wire, j < k ∧ HonestRowAt p c E rho j z r wire ∧
        RowSigner p c rho wire z ∧ wire.toRow? = some a ∧
        wire.payload.height_pair = a.height_pair ∧
        ∃ l o t, l < k ∧ rho.events[l]? = some (.deliver v o t) ∧ p.actionTime r ≤ t := by
    intro k v W hW a ha hgood
    have hz : rho.seatOf (.base .fg) a.signer ∈ rho.honest := by
      by_contra hn
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    obtain ⟨wire, r, hd, hauth, l, o, t, hl, he, horigin⟩ := hheldRows k v W hW a ha
    have hsign : RowSigner p c rho wire (rho.seatOf (.base .fg) a.signer) :=
      ⟨a.signer, hauth, rfl⟩
    obtain ⟨⟨j, hj, hemit⟩, ht⟩ := horigin _ hsign hz
    refine ⟨j, _, r, wire, hj, hemit, hsign, hd, ?_, l, o, t, hl, he, ht⟩
    have heq : wire.payload.toRow a.signer = a :=
      Option.some.inj (by simpa only [RowWire.toRow?, RowWire.decode?, hauth,
        Option.map_some] using hd)
    exact congrArg Row.height_pair heq
  obtain ⟨uf, huf, hufgood, _, hpair⟩ := finalityCap_row_of_certificate p.E
    (heightView p) (finalityView p) (fgCertificateLaws p) bad hcap h D
    (fun _ => True) (fun _ _ _ => trivial) hpos (by rw [hh])
  obtain ⟨jf, z, rf, af, hjf, haf, hsign, hdecode, _, _⟩ :=
    honestRow i x D hD uf huf hufgood
  rw [hF, hh] at hpair
  obtain ⟨H, hH, hheight, hroot, hqc⟩ :=
    hfinalHead jf z rf af uf haf hsign hdecode ⟨h, X.root⟩ hpair
  have hHX : (heightView p H).J = X := rootScope_eq hroots
    (rootScope_justified (rootScope_store hH.1 hH.2))
    (hF ▸ rootScope_finalized (rootScope_store hD.1 hD.2)) hroot.symm
  obtain ⟨Q, hQ, hrows⟩ := hqc
  obtain ⟨seat, hseat, hgood⟩ := honest_in_quorum p.E bad hQ hcap
  obtain ⟨carrier, ut, hc, hu, hsigner, htarget⟩ := hrows seat hseat
  have hut : ut ∈ chainRows H := mem_chainRows_of_carrier hc hu
  obtain ⟨jt, y, rt, aT, hjt, haT, _, hdecodeT, hfields, l, o, t, hl, he, ht⟩ :=
    honestRow jf z H hH ut hut (hsigner ▸ hgood)
  rw [hHX] at htarget
  have hname : namedEntry aT.payload.height_pair = some (h, X.root) := by
    rw [hfields, htarget]
    rfl
  obtain ⟨K, B, hK, hkey, hpre, hgate, hKB, _⟩ := hemitted jt y rt aT _ haT hname
  have hentry : X = (derive p.E p.cfg K).T_h := rootScope_eq hroots
    (hF ▸ rootScope_finalized (rootScope_store hD.1 hD.2))
    (rootScope_ancestor (rootScope_source haT.1 hK) (entry_preceq p.E p.cfg K))
    (congrArg Prod.snd hkey)
  have htime : p.actionTime rt < p.actionTime rf := by
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hfl, hfe⟩ := List.getElem?_eq_some_iff.mp haf.2.1
    have hk := (List.pairwise_iff_getElem.mp hvalid.sorted) l jf hll hfl hl
    rw [hle, hfe] at hk
    have hlt : t < p.actionTime rf := by
      change toLex (t, (2 : Nat)) ≤ toLex (p.actionTime rf, 1) at hk
      rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨_, hbad⟩
      · exact hlt
      · omega
    exact ht.trans_lt hlt
  have hround : rt < rf := by
    by_contra hn
    have hm : (rf * p.R : Nat) ≤ rt * p.R := Nat.mul_le_mul_right _ (Nat.le_of_not_gt hn)
    have hm' : ((rf * p.R : Nat) : Int) ≤ (rt * p.R : Nat) := Int.ofNat_le.mpr hm
    change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ <
      4 * p.Δ * (rf * p.R : Nat) + 6 * p.Δ at htime
    nlinarith [p.deltaPos]
  have hgap : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ < p.actionTime rf := by
    have hm : rt * p.R + 2 ≤ rf * p.R := by
      have ha := Nat.mul_le_mul_right p.R hround
      rw [Nat.succ_mul] at ha
      have hb := p.RLarge
      omega
    have hm' : ((rt * p.R : Nat) : Int) + 2 ≤ (rf * p.R : Nat) := by exact_mod_cast hm
    change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ + 4 * p.Δ <
      4 * p.Δ * (rf * p.R : Nat) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hqTarget : TargetQCAt p.E H h X := by
    rw [← hHX]
    exact ⟨Q, hQ, hrows⟩
  exact ⟨jf, z, rf, af, uf, H, jt, y, rt, aT, ut, K, B, hjf, haf, hsign, hdecode,
    huf, hpair, hH, hheight.symm, hHX, hqTarget, hjt, haT, hdecodeT, hut, htarget, hK,
    hentry ▸ hpre, hgate, hKB, hgap⟩

end AvailableChain.FGSA.Run
end
