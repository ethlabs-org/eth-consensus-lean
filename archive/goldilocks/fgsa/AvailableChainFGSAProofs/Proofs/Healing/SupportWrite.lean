module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1012–1018; plan H-SUPPORT §7 step 3.
DC: SAME a slow-policy write key is a non-genesis stored prefix of the result at the
single SA level, admitted by the fast test or by the executable slow window. -/
theorem healing_support_key_cases {st : GridCO.State p.n .root} {w : Slot} {C B : Block} {g : Nat}
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      st w C) :
    B ∈ st.blocks ∧ B ≠ .genesis ∧ Block.Preceq B C ∧
      g = SA.releaseThreshold p.toParams ∧
      (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams st w B ∨
        GridCO.slowEligible p.toParams.engine st w B = true) := by
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hkey
  obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hkey
  obtain ⟨g', hg', he⟩ := List.mem_map.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hb
  have hc := Bool.and_eq_true_iff.mp hcond
  refine ⟨hmem, by simpa using hc.1, hc.2, ?_⟩
  unfold GridCO.admissionLevels at hg'
  split at hg'
  · split at hg'
    · rename_i hlev
      refine ⟨List.mem_singleton.mp hg', ?_⟩
      rcases Bool.or_eq_true_iff.mp hlev with h | h
      · exact Or.inl (of_decide_eq_true h)
      · exact Or.inr h
    · exact (List.not_mem_nil hg').elim
  · rename_i hn
    exact (hn rfl).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:628–650; plan H-SUPPORT §7 step 3 (scheduled reader bridge).
DC: SAME the scheduled gate tick is the unique gate input and post-clock read. -/
theorem healing_support_gate_reads (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {w : Slot} (ht : IsGateTick p c rho j x w) :
    gateIn p c E rho x w =
        some (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)) ∧
      postClock E rho x (SA.gateTime p.toParams w) =
        some ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (SA.gateTime p.toParams w)) := by
  have hidx := fgsa_tickIdx_of_event p c E rho hs ht
  constructor
  · rw [gateIn_def, preTick_def, hidx]
    rfl
  · rw [postClock_def, preTick_def, hidx]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:628–650; plan H-SUPPORT §7 step 3.
DC: SAME a fresh scheduled gate saves its fast set at its own label; the post-clock
read finds exactly that row. -/
theorem healing_support_fastWrite (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {w : Slot} (ht : IsGateTick p c rho j x w)
    (hj : joinedAtTime p (storeAt p c E rho j x).restartTime
      (SA.gateTime p.toParams w) = true) :
    (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
        (SA.gateTime p.toParams w)).st w).getD [] =
      fastSet p (eraseFG (storeAt p c E rho j x).fg.F)
        (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w := by
  let nd := V2.D.Run.stateBefore E rho j x
  let st := ((fgsa p c).clock nd (SA.gateTime p.toParams w)).st
  let fs := fastSet p (eraseFG nd.st.fg.F)
    (actView (clockPre p nd.st (SA.gateTime p.toParams w))) w
  have hinv := (storeBundle_postClock E rho j x (SA.gateTime p.toParams w)).cstore
  have hfw : st.fastWrite = nd.st.fastWrite ++ [(w, fs)] := by
    have hb := congrArg State.fastWrite (fgsa_gate_clock_bridge E rho hs ht hj)
    rw [normalizeS_fields] at hb
    exact hb
  have hrow : (w, fs) ∈ st.fastWrite := by
    rw [hfw]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hfind : st.fastWrite.find? (fun row => row.1 == w) = some (w, fs) := by
    cases he : st.fastWrite.find? (fun row => row.1 == w) with
    | none => have hn := List.find?_eq_none.mp he _ hrow; simp at hn
    | some row =>
      have hk : row.1 = w := by simpa using List.find?_some he
      exact congrArg some (List.inj_on_of_nodup_map hinv.fastDom.1
        (List.mem_of_find?_eq_some he) hrow hk)
  change ((st.fastWrite.find? (fun row => row.1 == w)).map Prod.snd).getD [] = fs
  rw [hfind]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:628–680, 1012–1018; plan H-SUPPORT §7 step 3.
DC: INTENTIONAL the actual passed write gate of a slow-policy key supplies the exact
frozen PhaseBody: a fast key is in the gate's fast-write set; a slow key gives the
slow witnesses. The synchronous window is a premise only of the slow arm. -/
theorem healing_support_phaseBody_of_write (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {w : Slot} {C B : Block} {g : Nat} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho j x w) (hpass : gatePassedAt p c E rho j)
    (hres : gateResultAt p c E rho j = some (some C))
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k)) :
    PhaseBody p c E rho w B := by
  let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)
  obtain ⟨hmem, hne, hBC, _, hcase⟩ := healing_support_key_cases p hkey
  obtain ⟨hin, hpost⟩ := healing_support_gate_reads p c E rho hs ht
  have hgr : gateResult p c E rho x w = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres
  obtain ⟨hjoined, hraw⟩ := fgsa_gate_raw_of_nonempty p c E rho hs ht hgr
  have hconf : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C := by
    exact hraw
  refine ⟨x, hx, ?_⟩
  rcases hcase with hfast | hslow
  · left
    refine ⟨_, hpost, ?_⟩
    rw [healing_support_fastWrite p c E rho hs ht hjoined]
    have hF : eraseFG (storeAt p c E rho j x).fg.F = eraseFG pre.fg.F := by
      rw [clockPre_fg]
    obtain ⟨x', w', ⟨ht', _⟩, _, h, hh, hguard⟩ := hpass
    obtain ⟨hxx, hw⟩ : x' = x ∧ SA.gateTime p.toParams w' = SA.gateTime p.toParams w := by
      have he := ht'.symm.trans ht
      simp only [Option.some.injEq, V2.Event.tick.injEq] at he
      exact he
    subst hxx
    have hww : w' = w := by
      change 4 * p.Δ * (w' : Int) + 6 * p.Δ = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
      have hd := p.deltaPos
      have he : (w' : Int) = w := by nlinarith
      exact_mod_cast he
    subst w'
    have hhC : h = C := Option.some.inj (hh.symm.trans hconf)
    subst h
    unfold fastSet
    rw [hF, hconf]
    dsimp only
    simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    refine List.mem_filter.mpr ⟨hmem, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨hne, hBC⟩, hfast⟩
  · right
    exact ⟨hwindow, pre, C, j, hin, hgr, hne, hBC, hslow, ht, hpass⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1004–1018; plan H-SUPPORT S3 (§7); ruling B27.
DC: INTENTIONAL the last actual write of an extant key is classified at the cutoff:
an old write has the displayed deadline bound; a write at or after the cutoff gives
Transfers at its own label through TPerm. The `writes` premise is spelled inline;
Assembly discharges it with fgsa_leaseOrigins_lastWrite. Renewals are new writes.
No earlier frame is assumed; the cutoff window is only synchronous. -/
theorem healing_last_write_support (hs : V2.D.ScheduleWellFormed E rho)
    (perm : TPerm p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m bcut : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hcurrent : u ≤ SA.voteTime p.toParams bcut)
    (hsyncWindow : E.t_GST ≤ SA.voteTime p.toParams (bcut + 1 - p.k)) :
    ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C ∧
        row.2.2 = SA.gateTime p.toParams w + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (w + p.k) ∧
        (∀ k a D, j < k → k < i → IsGateTick p c rho k x a →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams a)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base a = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) a = some D →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 D) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) a D) ∧
        ((w < bcut ∧
            row.2.2 ≤ SA.gateTime p.toParams (bcut - 1) + SA.lifetime p.toParams) ∨
          (bcut ≤ w ∧ Transfers p c E rho w row.1 v)) := by
  intro i x row hiv hx hr
  obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, hkey, hd, hq, hlast⟩ := writes i x row hr
  refine ⟨j, hji, w, C, ht, hpass, hres, hrow, hkey, hd, hq, hlast, ?_⟩
  have hd0 := p.deltaPos
  by_cases hwb : w < bcut
  · left
    refine ⟨hwb, ?_⟩
    rw [hd]
    have hc : ((bcut - 1 : Nat) : Int) = (bcut : Int) - 1 := by
      rw [Nat.cast_sub (Nat.lt_of_le_of_lt (Nat.zero_le w) hwb)]
      rfl
    have hw : (w : Int) + 1 ≤ (bcut : Int) := by exact_mod_cast hwb
    change 4 * p.Δ * (w : Int) + 6 * p.Δ + SA.lifetime p.toParams ≤
      4 * p.Δ * ((bcut - 1 : Nat) : Int) + 6 * p.Δ + SA.lifetime p.toParams
    rw [hc]
    nlinarith
  · right
    have hbw : bcut ≤ w := Nat.le_of_not_gt hwb
    refine ⟨hbw, ?_⟩
    have hgv : SA.gateTime p.toParams w ≤ v :=
      (V2.D.Engine.index_lt_read_length_iff hs v ht).mp (hji.trans_le hiv)
    have hu : u ≤ SA.voteTime p.toParams w := by
      refine hcurrent.trans ?_
      change 4 * p.Δ * (bcut : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      have hbw' : (bcut : Int) ≤ w := by exact_mod_cast hbw
      nlinarith
    have hwin : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k) := by
      refine hsyncWindow.trans ?_
      change 4 * p.Δ * ((bcut + 1 - p.k : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
      have hm : ((bcut + 1 - p.k : Nat) : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
        exact_mod_cast Nat.sub_le_sub_right (Nat.succ_le_succ hbw) p.k
      nlinarith
    exact perm u v m J contested w row.1 hready hphase hu hgv
      (healing_support_phaseBody_of_write p c E rho hs hx ht hpass hres hkey hwin)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:972, 988; plan H-SUPPORT §7 specializations.
DC: SAME grid arithmetic: a write at label w expires by v_l when w + k + 1 ≤ l. -/
theorem healing_support_deadline_le_vote {w l : Nat} (hwl : w + p.k + 1 ≤ l) :
    SA.gateTime p.toParams w + SA.lifetime p.toParams ≤ SA.voteTime p.toParams l := by
  change 4 * p.Δ * (w : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ ≤
    4 * p.Δ * (l : Int) + p.Δ
  have h : (w : Int) + p.k + 1 ≤ l := by exact_mod_cast hwl
  have hd := p.deltaPos
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:972, 988; plan H-SUPPORT §7 specializations.
DC: SAME a later proposal has its preceding HEAD at or after v_l. -/
theorem healing_support_vote_before_proposal {l s : Nat}
    (hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s) :
    SA.voteTime p.toParams l ≤ SA.voteTime p.toParams (s - 1) := by
  have hd := p.deltaPos
  have hlt : l < s := by
    change 4 * p.Δ * (l : Int) < 4 * p.Δ * (s : Int) at hls
    have h : (l : Int) < s := by nlinarith
    exact_mod_cast h
  change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ
  have h : (l : Int) ≤ ((s - 1 : Nat) : Int) := by exact_mod_cast Nat.le_sub_one_of_lt hlt
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:915–972 (H.6); plan H-SUPPORT §7 specialization A; ruling B27.
DC: INTENTIONAL two-lease budget. With β the first proposal after u, use the cutoff
β + k − 1 and l = β + 2k − 1: an old last write expires by v_l, hence at or before the
preceding HEAD of every proposal after t_l; a later write has Transfers at its label.
A fast row with β ≤ w < β + k − 1 stays in the old class. -/
theorem healing_last_write_two_lease (hs : V2.D.ScheduleWellFormed E rho)
    (perm : TPerm p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m β : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hβ : u < SA.proposalTime p.toParams β) :
    ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        ((row.2.2 ≤ SA.voteTime p.toParams (β + 2 * p.k - 1) ∧
            ∀ s, SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s →
              row.2.2 ≤ SA.voteTime p.toParams (s - 1)) ∨
          (β + p.k - 1 ≤ w ∧ Transfers p c E rho w row.1 v)) := by
  have hk := p.kLarge
  have hd := p.deltaPos
  have hwin : β + p.k - 1 + 1 - p.k = β := by omega
  have hcur : u ≤ SA.voteTime p.toParams (β + p.k - 1) := by
    refine hβ.le.trans ?_
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + p.k - 1 : Nat) : Int) + p.Δ
    have h : (β : Int) ≤ ((β + p.k - 1 : Nat) : Int) := by
      exact_mod_cast (show β ≤ β + p.k - 1 by omega)
    nlinarith
  have hsync : E.t_GST ≤ SA.voteTime p.toParams (β + p.k - 1 + 1 - p.k) := by
    rw [hwin]
    refine (by
      have := healing_recovery_start_lower (p := p) E
      linarith [p.deltaPos] : E.t_GST ≤ u).trans (hβ.le.trans ?_)
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * (β : Int) + p.Δ
    linarith
  intro i x row hiv hx hr
  obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, _, hd', _, _, hcase⟩ :=
    healing_last_write_support p c E rho hs perm writes hready hphase hcur hsync i x row hiv hx hr
  refine ⟨j, hji, w, C, ht, hpass, hres, hrow, ?_⟩
  rcases hcase with ⟨hwb, _⟩ | hnew
  · left
    have hwl : w + p.k + 1 ≤ β + 2 * p.k - 1 := by
      have e : β + 2 * p.k - 1 = (β + p.k - 1) + p.k := by omega
      rw [e]
      exact Nat.succ_le_of_lt (Nat.add_lt_add_right hwb p.k)
    have hold : row.2.2 ≤ SA.voteTime p.toParams (β + 2 * p.k - 1) :=
      hd' ▸ healing_support_deadline_le_vote p hwl
    exact ⟨hold, fun s hs' => hold.trans (healing_support_vote_before_proposal p hs')⟩
  · exact Or.inr hnew

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:988–1018 (H.6-S); plan H-SUPPORT §7 specialization B; ruling B27.
DC: INTENTIONAL one-lease budget. With b the first HEAD label at or after u and a
synchronous window GST ≤ v_(b+1−k), use the cutoff b and l = b + k: an old last write
expires by v_l; a later write has Transfers at its label. The earlier window labels
may be in other phases. The producer of the window premise is H.6-C work. -/
theorem healing_last_write_one_lease (hs : V2.D.ScheduleWellFormed E rho)
    (perm : TPerm p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m b : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hb : u ≤ SA.voteTime p.toParams b)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
    ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        ((row.2.2 ≤ SA.voteTime p.toParams (b + p.k) ∧
            ∀ s, SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s →
              row.2.2 ≤ SA.voteTime p.toParams (s - 1)) ∨
          (b ≤ w ∧ Transfers p c E rho w row.1 v)) := by
  intro i x row hiv hx hr
  obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, _, hd', _, _, hcase⟩ :=
    healing_last_write_support p c E rho hs perm writes hready hphase hb hwindow i x row hiv hx hr
  refine ⟨j, hji, w, C, ht, hpass, hres, hrow, ?_⟩
  rcases hcase with ⟨hwb, _⟩ | hnew
  · left
    have hwl : w + p.k + 1 ≤ b + p.k := Nat.succ_le_of_lt (Nat.add_lt_add_right hwb p.k)
    have hold : row.2.2 ≤ SA.voteTime p.toParams (b + p.k) :=
      hd' ▸ healing_support_deadline_le_vote p hwl
    exact ⟨hold, fun s hs' => hold.trans (healing_support_vote_before_proposal p hs')⟩
  · exact Or.inr hnew

end AvailableChain.FGSA.Run
end
