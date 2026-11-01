module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Origins
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! WC plan §6.4; DC conditional frame bounds permit low contests. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.4; DC the decoded row preserves its signed height pair. -/
private theorem decoded_height {n : Nat} {wire : RowWire n} {a : Row (Fin n)}
    (hd : wire.toRow? = some a) : wire.payload.height_pair = a.height_pair := by
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label k =>
    cases label with
    | head s => cases hd
    | fg => exact congrArg Row.height_pair (Option.some.inj hd)

/-- WC plan §6.4; DC every controlling high row has its original source below B. -/
theorem wcg_seededFrame : WCGSeededFrameStatement p c E rho ΔF w iStar := by
  classical
  intro _hvalid hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF _hfaultQ
    haccountable _hpart hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel hqc _hstrat hnoslash hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows hscopeRows _hfinalHead hs i x phase st WStar B Bfg hd hx _hi hW hWe hhW
    hQB hBe hhigh
  have hfg : st.fg = (storeAt p c E rho i x).fg := by
    obtain ⟨t, _, hprop | hhead | hgate | haction⟩ := hd.input
    · obtain ⟨s, _, _, rfl⟩ := hprop
      exact clock_fg p _ t
    · obtain ⟨s, _, _, rfl⟩ := hhead
      exact clock_fg p _ t
    · obtain ⟨s, _, _, rfl⟩ := hgate
      exact clockPre_fg p _ t
    · obtain ⟨r, _, _, rfl⟩ := haction
      exact clock_fg p _ t
  have hI : FGStoreInvariant (heightView p) (finalityView p) st.fg := by
    rw [hfg]
    exact (hstore i x hx).1.fg
  have scope : ∀ D ∈ st.fg.TF, RootBlockInRun p c E rho (eraseFG D) := by
    intro D hD
    exact rootScope_store hx (hfg ▸ hD)
  have rowBelow (a : Row (Fin p.n)) (hc : WCControllingRow p st a)
      (X : FGBlock (Fin p.n)) (m : Height)
      (hX : RootBlockInRun p c E rho (eraseFG X))
      (hm : w.M + 1 ≤ m) (hp : namedEntry a.height_pair = some (m, X.root))
      (j : Nat) (y : V) (r : Nat) (wire : RowWire p.n)
      (hj : j < i) (hr : HonestRowAt p c E rho j y r wire)
      (hdecode : wire.toRow? = some a) : FGBlock.Preceq X Bfg := by
    have hname : namedEntry wire.payload.height_pair = some (m, X.root) := by
      rw [decoded_height hdecode]
      exact hp
    obtain ⟨K, G, hK, hpair, hpre, _⟩ := hemitted j y r wire _ hr hname
    have hKB := hhigh.below a hc j y r wire _ K hj hr hdecode hname hm hK
    have heq : X = (derive p.E p.cfg K).T_h :=
      rootScope_eq (hroots.toNamedRootCollisionFree E rho) hX
      (rootScope_ancestor (rootScope_source hr.1 hK) (entry_preceq p.E p.cfg K))
      (congrArg Prod.snd hpair)
    apply eraseFG_preceq_iff.mp
    rw [hBe]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq (heq ▸ hpre)) hKB
  have justified (D : FGBlock (Fin p.n)) (hD : D ∈ st.fg.TF)
      (hm : w.M + 1 ≤ (heightView p D).h_j) : FGBlock.Preceq (heightView p D).J Bfg := by
    have hn : (heightView p D).h_j ≠ 0 := by
      simp only [Height] at *
      omega
    obtain ⟨Q, hQ, hr⟩ := (fgCertificateLaws p).height.justification_certificate D hn
    choose carrier a hc ha hsign hp using fun k hk => hr k hk
    let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) :=
      fun k => if hk : k ∈ Q then (carrier k hk, a k hk) else
        (.genesis, ⟨k, .empty, none⟩)
    have hrows : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 D ∧
        (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
        (rows k).2.height_pair =
          .vote (heightView p D).h_j (heightView p D).J.root false := by
      intro k hk
      simp only [rows, dite_eq_left hk]
      exact ⟨hc k hk, ha k hk, hsign k hk, hp k hk⟩
    obtain ⟨k, hk, y, r, wire, ⟨j, hj, hrow⟩, hdecode, _⟩ :=
      (hqc i x D hx (hfg ▸ hD)).2.1 Q rows hn hQ hrows
    have hcRow : WCControllingRow p st (rows k).2 := by
      refine ⟨D, hD, D, preceq_refl D,
        mem_chainRows_of_carrier (hrows k hk).1 (hrows k hk).2.1, Or.inl ?_⟩
      exact ⟨_, _, rfl, rfl, ⟨Q, hQ, hr⟩, (hrows k hk).2.2.2⟩
    exact rowBelow _ hcRow _ _ (rootScope_justified (scope D hD)) hm
      (by rw [(hrows k hk).2.2.2]; rfl) j y r wire hj hrow hdecode
  have crossing (D : FGBlock (Fin p.n)) (hD : D ∈ st.fg.TF) (m : Height)
      (hm : w.M + 1 ≤ m) (hlt : m < (heightView p D).h) :
      ∃ X, FGBlock.Preceq X D ∧ (heightView p X).h = m ∧
        FGBlock.Preceq X Bfg := by
    have hpos : 1 ≤ m := by simp only [Height] at *; omega
    obtain ⟨X, hXD, hheight, Q, hQ, hr⟩ :=
      (fgCertificateLaws p).height.height_crossing D m hpos hlt
    choose carrier a hc ha hsign hp using fun k hk => hr k hk
    let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) :=
      fun k => if hk : k ∈ Q then (carrier k hk, a k hk) else
        (.genesis, ⟨k, .empty, none⟩)
    have hrows : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 D ∧
        (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
        (rows k).2.height_pair.matchesEntry m X.root = true := by
      intro k hk
      simp only [rows, dite_eq_left hk]
      exact ⟨hc k hk, ha k hk, hsign k hk, hp k hk⟩
    obtain ⟨k, hk, y, r, wire, ⟨j, hj, hrow⟩, hdecode, _⟩ :=
      (hqc i x D hx (hfg ▸ hD)).1 m X Q rows hpos hlt hXD hheight hQ hrows
    have hcRow : WCControllingRow p st (rows k).2 := by
      refine ⟨D, hD, D, preceq_refl D,
        mem_chainRows_of_carrier (hrows k hk).1 (hrows k hk).2.1, Or.inr (Or.inr ?_)⟩
      refine ⟨m, X, Q, hpos, hlt, hXD, hheight, hQ, ?_, (hrows k hk).2.2.2, ?_⟩
      · simpa only [(hrows k hk).2.2.1] using hk
      · intro l hl
        exact ⟨(rows l).2, mem_chainRows_of_carrier (hrows l hl).1 (hrows l hl).2.1,
          (hrows l hl).2.2.1, (hrows l hl).2.2.2⟩
    have hname : namedEntry (rows k).2.height_pair = some (m, X.root) := by
      have hp := (hrows k hk).2.2.2
      cases hh : (rows k).2.height_pair with
      | empty => rw [hh] at hp; cases hp
      | vote n root tm =>
        rw [hh] at hp
        change decide (n = m ∧ root = X.root) = true at hp
        obtain ⟨rfl, rfl⟩ := of_decide_eq_true hp
        rfl
    exact ⟨X, hXD, hheight, rowBelow _ hcRow _ _ (rootScope_ancestor (scope D hD) hXD)
      hm hname j y r wire hj hrow hdecode⟩
  have hWB : FGBlock.Preceq WStar Bfg := eraseFG_preceq_iff.mp (by
    rw [hWe, hBe]
    exact Gen.Pure.block_preceq_trans hs.sourcePrefix hQB)
  have hBheight : w.M + 1 ≤ (heightView p Bfg).h := by
    rw [← hhW]
    exact (fgCertificateLaws p).height.h_mono hWB
  have hFB : FGBlock.Preceq st.fg.F Bfg := by
    obtain ⟨D, hD, hDF⟩ := hI.Fcar
    by_cases hlo : (finalityView p D).h_F ≤ w.M
    · have hf := (wcg_lowFinalized (hroots.toNamedRootCollisionFree E rho) haccountable hs
        D st.fg.F _ (wcg_finalizedOccurrence hscopeRows hnoslash D st.fg.F _
          (scope D hD) hDF rfl) hlo).2
      exact eraseFG_preceq_iff.mp (hBe ▸ Gen.Pure.block_preceq_trans hf hQB)
    · have hn : (finalityView p D).h_F ≠ 0 := by simp only [Height] at *; omega
      obtain ⟨C, D₀, hCD, hDD, hbirth, _⟩ := (fgCertificateLaws p).finality_origin D hn
      have hC : C ∈ st.fg.TF := ancestor_closed_of_parent_closed _ hI.closed D hD C
        (preceq_trans hCD.1 hDD)
      have hj := justified C hC (by rw [hbirth.2.2.2.1]; simp only [Height] at *; omega)
      rwa [hbirth.2.2.2.2.1, hDF] at hj
  have hFZ : FGBlock.Preceq st.fg.F (frameR p st).Z := by
    change FGBlock.Preceq st.fg.F
      (if (frameR p st).rootIsJ then st.fg.J else st.fg.F)
    cases (frameR p st).rootIsJ
    · exact preceq_refl _
    · exact hI.FJ
  have hJB : w.M + 1 ≤ st.fg.h_j → FGBlock.Preceq st.fg.J Bfg := by
    intro hj
    obtain ⟨D, hD, _, hheight, hJ⟩ := hI.pair.1
    rw [hJ]
    exact justified D hD (hheight ▸ hj)
  have hZB : FGBlock.Preceq (frameR p st).Z Bfg := by
    change FGBlock.Preceq (if (frameR p st).rootIsJ then st.fg.J else st.fg.F) Bfg
    split
    · next hroot =>
      by_cases hj : w.M + 1 ≤ st.fg.h_j
      · exact hJB hj
      · have hroot' : st.fg.h_max = st.fg.h_j + 1 ∧ (frameR p st).contest = false := by
          change (decide (st.fg.h_max = st.fg.h_j + 1) &&
            !(frameR p st).contest) = true at hroot
          obtain ⟨hh, hc⟩ := Bool.and_eq_true_iff.mp hroot
          exact ⟨of_decide_eq_true hh, by simpa only [Bool.not_eq_true'] using hc⟩
        have hmax : (heightView p WStar).h ≤ st.fg.h_max :=
          (Finset.le_sup hW).trans (hI.hmax.symm ▸ le_sup_left)
        have htop : (heightView p WStar).h = st.fg.h_max := by
          rw [hhW] at *
          simp only [Height] at *
          omega
        have hc : ¬ ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
            (heightView p W).h = st.fg.h_max ∧
            ¬ FGBlock.Preceq st.fg.J W := by
          have hh := hroot'.2
          change (decide (st.fg.h_max = st.fg.h_j + 1) && decide _) = false at hh
          simpa only [hroot'.1, decide_true, Bool.true_and, decide_eq_false_iff_not] using hh
        have hJW : FGBlock.Preceq st.fg.J WStar := by
          by_contra hn
          obtain ⟨K, _, _, hKh, hKJ⟩ := hI.pair.1
          have hnz : (heightView p K).h_j ≠ 0 := by
            intro hz
            exact hn (hKJ ▸ (fgJustificationLaws p).J_zero K hz ▸ genesis_preceq WStar)
          have hJh : (heightView p st.fg.J).h = st.fg.h_j := by
            rw [hKJ, (fgJustificationLaws p).J_height K hnz, ← hKh]
          have hFW : FGBlock.Preceq st.fg.F WStar := by
            rcases preceq_total_of_common hFB hWB with hp | hp
            · exact hp
            · have hh := (fgCertificateLaws p).height.h_mono (preceq_trans hp hI.FJ)
              rw [hJh, hhW] at hh
              exact (hj hh).elim
          exact hc ⟨WStar, hW, hFW, htop, hn⟩
        exact preceq_trans hJW hWB
    · exact hFB
  have hfloor : (frameR p st).lo ≤ (heightView p Bfg).h := by
    by_cases hm : st.fg.h_max ≤ w.M + 1
    · exact (Controls.lo_le_H (frameR p st)).trans (hm.trans hBheight)
    have hfront : ∃ D ∈ st.fg.TF, (heightView p D).h = st.fg.h_max := by
      obtain ⟨D, hD, he⟩ := Finset.exists_mem_eq_sup st.fg.TF ⟨_, hI.gen⟩
        (fun D => (heightView p D).h)
      refine ⟨D, hD, ?_⟩
      have hmax := hI.hmax
      rw [he] at hmax
      simp only [Height] at *
      omega
    cases hc : (frameR p st).contest with
    | false =>
      obtain ⟨D, hD, hh⟩ := hfront
      obtain ⟨X, _, hXh, hXB⟩ := crossing D hD (st.fg.h_max - 1)
        (by simp only [Height] at *; omega) (by rw [hh]; simp only [Height] at *; omega)
      have hb := (fgCertificateLaws p).height.h_mono hXB
      change (if (frameR p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _
      rwa [hc, hXh] at *
    | true =>
      have hcontest : st.fg.h_max = st.fg.h_j + 1 ∧
          ∃ D ∈ st.fg.TF, FGBlock.Preceq st.fg.F D ∧
            (heightView p D).h = st.fg.h_max ∧
            ¬ FGBlock.Preceq st.fg.J D := by
        change (decide (st.fg.h_max = st.fg.h_j + 1) &&
          decide (∃ D ∈ st.fg.TF, FGBlock.Preceq st.fg.F D ∧
            (heightView p D).h = st.fg.h_max ∧
            ¬ FGBlock.Preceq st.fg.J D)) = true at hc
        have hh := Bool.and_eq_true_iff.mp hc
        exact ⟨of_decide_eq_true hh.1, of_decide_eq_true hh.2⟩
      obtain ⟨htop, D, hD, _, hh, hn⟩ := hcontest
      have hj : w.M + 1 ≤ st.fg.h_j := by simp only [Height] at *; omega
      obtain ⟨X, hXD, hXh, hXB⟩ := crossing D hD st.fg.h_j hj
        (by rw [hh, htop]; exact Nat.lt_succ_self _)
      have hJX := preceq_total_of_common (hJB hj) hXB
      have hJentry : (heightView p st.fg.J).T_h = st.fg.J := by
        obtain ⟨C, _, _, _, hJ⟩ := hI.pair.1
        rw [hJ]
        exact (fgJustificationLaws p).J_entry C
      have hJh : (heightView p st.fg.J).h = st.fg.h_j := by
        obtain ⟨C, _, _, hh, hJ⟩ := hI.pair.1
        rw [hJ, (fgJustificationLaws p).J_height C (by simp only [Height] at *; omega), ← hh]
      have hJXD : FGBlock.Preceq st.fg.J X := by
        rcases hJX with hp | hp
        · exact hp
        · have he := (fgCertificateLaws p).height.entry_plateau hp (hXh.trans hJh.symm)
          rw [hJentry] at he
          exact he ▸ (fgCertificateLaws p).height.entry_preceq X
      exact (hn (preceq_trans hJXD hXD)).elim
  exact ⟨eraseFG_preceq hFZ, hBe ▸ eraseFG_preceq hZB, Bfg, hBe, hfloor⟩

/-- WC plan §6.4; DC the live start uses targets in the same duty input. -/
theorem wcg_seededFrameLive : WCGSeededFrameLiveStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x phase st WStar Bfg hd hx hi hW hWe hhW hQB hhigh htarget view hview hsub
  have hf := wcg_seededFrame hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x phase st WStar (eraseFG Bfg) Bfg hd hx hi hW hWe hhW
    hQB rfl hhigh
  refine ⟨hview, hf, htarget, hsub, fgsa_Z_preceq_liveRoot p st, ?_⟩
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    exact hf.rootBelow
  · obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hm
    split at he
    · next hc =>
      rw [← Option.some.inj he]
      exact htarget row hr (of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1)
    · cases he

/-- WC plan §6.4; DC parent closure supplies every prefix in the exact duty view. -/
theorem wcg_seededFramePath : WCGSeededFramePathStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x phase st WStar Bfg hd hx hi hW hWe hhW hQB hhigh htarget view hview hsub
    hclosed hmem
  have hl := wcg_seededFrameLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x phase st WStar Bfg hd hx hi hW hWe hhW hQB hhigh
    htarget view hview hsub
  obtain ⟨Y, he, hf⟩ := hl.frame.floor
  have heq : Y = Bfg := eraseFG_injective he
  subst Y
  refine ⟨hl, hmem, hclosed, ?_⟩
  intro X hZX hXB
  apply (mem_filteredFromView (heightView p) (frameR p st) view X).mpr
  exact ⟨ancestor_closed_of_parent_closed view hclosed Bfg hmem X hXB,
    preceq_trans (eraseFG_preceq_iff.mp hl.frame.finalRoot) hZX, hZX,
    Bfg, hmem, hXB, hf⟩

end AvailableChain.FGSA.Run
end
