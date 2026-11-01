module
public import AvailableChainFGCompose.Statements.FinalityRecords
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainGeneric.Proofs.V2.Duty.Fields

public import AvailableChainFGCompose.Proofs.Population.HighTarget

public import AvailableChainFGCompose.Proofs.Population.Seats

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)} {cfg : FGConfig}
variable {pt : FGServicePoint}
variable (hh : ∀ horizon, FGHistoricalHighChain R O T E rho pt horizon)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (hreflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
variable {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
variable {SourceService : V → Nat → FGBlock (Fin n) → Prop}
variable (hqc : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
variable (hhead : HighRecordHead R S O E rho)
variable (hsrc : ∀ nd, (S.inputs nd).1 = R.source nd)
variable (hheight : ∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
  ((O.height C).h, (O.height C).T_h.root))
variable (J : FGSafetyClientLaws S Ef cfg)
variable (emission : HighRecordEmission S T E rho Ef cfg)
variable (hown : HighRecordOwnOrigin S T E rho)
variable (hnames : HighRecordNames R S O T E rho D)

/-- The statement predicate uses the exact self-visible emission list. -/
theorem HighRecordOwnOrigin_def : HighRecordOwnOrigin S T E rho =
    (∀ j x o u, x ∈ rho.honest → o ∈ V2.D.Engine.ownReleasedAt E rho x j →
      S.decodeObject o = some u →
      ∃ r a, HonestRowAt S E rho T j x r a ∧ S.decode a = some u) := by
  delta HighRecordOwnOrigin
  simp only [V2.D.Engine.ownReleasedAt_def]

include hh cert hreflect in
/-- High sources at equal height have the same entry, including before service starts. -/
theorem high_source_entry_eq (x z : V) (r s : Nat) (C B : FGBlock (Fin n))
    (hx : x ∈ rho.honest) (hz : z ∈ rho.honest)
    (hC : actionSourceFG R E rho T x r = some (some C))
    (hB : actionSourceFG R E rho T z s = some (some B))
    (hhighC : high R O pt.reset C) (hhighB : high R O pt.reset B)
    (heq : (O.height C).h = (O.height B).h) :
    (O.height C).T_h = (O.height B).T_h := by
  have hcompat := (hh (max (T.action r) (T.action s)) x z r s C B hx hz hC hB
    hhighC hhighB (le_max_left _ _) (le_max_right _ _)).1
  change ((R.erase C).preceq (R.erase B) || (R.erase B).preceq (R.erase C)) = true at hcompat
  rw [Bool.or_eq_true] at hcompat
  rcases hcompat with h | h
  · exact cert.height.entry_plateau (hreflect C B h) heq
  · exact (cert.height.entry_plateau (hreflect B C h) heq.symm).symm

include hh cert hreflect in
private theorem d7r_entry_source (x : V) (r : Nat) (C : FGBlock (Fin n))
    (hx : x ∈ rho.honest) (hs : actionSourceFG R E rho T x r = some (some C))
    (hhigh : high R O pt.reset C) :
    highRecordEntry R O T E rho (O.height C).h = (O.height C).T_h.root := by
  classical
  unfold highRecordEntry
  split_ifs with h
  · obtain ⟨hz, hB, heq⟩ := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))
    exact congrArg FGBlock.root (high_source_entry_eq hh cert hreflect _ x _ r _ C
      hz hx hB hs (by delta high at *; simpa only [heq] using hhigh) hhigh heq)
  · exact (h ⟨x, r, C, hx, hs, rfl⟩).elim

private theorem d7r_height_pair_some_def (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair) : height_pair Λ (some (y, T)) fp =
      if Λ.timeout y then .vote y T true else
        match own_lock Λ y fp with
        | some locked => if locked = T then .vote y T false else .empty
        | none => match Λ.target y with
          | some recorded => if recorded = T then .vote y T false else .vote y T true
          | none => .vote y T false := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: the three record guards give a target, including the own lock.
DC: Protocol/ValidatorClient.lean:216–229, height-pair branches. -/
theorem high_record_target_choice (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair)
    (ht : Λ.target y = none ∨ Λ.target y = some T)
    (hn : Λ.timeout y = false)
    (hl : Λ.lock y = none ∨ Λ.lock y = some T)
    (hf : ∀ f, fp = some f → f.height = y → f.target = T) :
    height_pair Λ (some (y, T)) fp = .vote y T false := by
  exact high_record_target_choice_core Λ y T fp ht hn hl hf

include hh cert hreflect hqc hhead in
private theorem d7r_finality_source (i : Nat) (x : V) (t : Time)
    (Λ : Record) (fp : FinalityPair) (hx : x ∈ rho.honest)
    (hf : finality_pair Λ (S.inputs (P.clock (V2.D.Run.stateBefore E rho i x) t)).2 = some fp)
    (hy : pt.reset.M + 1 ≤ fp.height) :
    fp.target = highRecordEntry R O T E rho fp.height := by
  classical
  rcases hhead i x t hx with hzero | ⟨K, hK, hfields⟩
  · rw [hzero] at hf
    delta finality_pair at *
    simp only [Nat.lt_irrefl, false_and, ite_false] at hf
    cases hf
  · rw [hfields] at hf
    obtain ⟨hheight, hroot, _, _⟩ := provenance_finalityRow_of_heightLaws Ef
      O.height O.finality cert.height Λ K fp hf
    have hnz : (O.height K).h_j ≠ 0 := by simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := cert.height.justification_certificate K hnz
    have hw' : ∀ k, ∃ W a, k ∈ Q → FGBlock.Preceq W K ∧ a ∈ W.rows ∧
        a.signer = k ∧ a.height_pair = .vote (O.height K).h_j (O.height K).J.root false := by
      intro k
      by_cases h : k ∈ Q
      · obtain ⟨W, a, ha⟩ := hw k h
        exact ⟨W, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun hk => (h hk).elim⟩
    choose W a ha using hw'
    obtain ⟨k, hkQ, z, r, wire, hb, _, _, C, hC, hn, _⟩ :=
      (hqc i x K hx hK).2.1 Q (fun k => (W k, a k)) hnz hQ ha
    have hname : namedEntry (a k).height_pair =
        some ((O.height K).h_j, (O.height K).J.root) := by
      rw [(ha k hkQ).2.2.2]; rfl
    rw [hname] at hn
    have heq := Option.some.inj hn
    have hyC : (O.height C).h = fp.height :=
      (congrArg Prod.fst heq).symm.trans hheight.symm
    have hTC : (O.height K).J.root = (O.height C).T_h.root := congrArg Prod.snd heq
    obtain ⟨j, _, hj⟩ := hb
    have hentry := d7r_entry_source hh cert hreflect z r C hj.1 hC
      (by change _ ≤ _; rw [hyC]; exact hy)
    rw [hyC] at hentry
    exact hroot.trans (hTC.trans hentry.symm)

private theorem d7r_write (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce)
    (a : Row (Fin n)) (hg : HighRecordInvariant M entry Λ)
    (hh : ∀ y T timeout, a.height_pair = .vote y T timeout → M + 1 ≤ y →
      T = entry y ∧ timeout = false)
    (hf : ∀ f, a.finality_pair = some f → M + 1 ≤ f.height → f.target = entry f.height) :
    HighRecordInvariant M entry (record_row_once Λ a) := by
  intro y hy
  obtain ⟨ht, hn, hl, hb⟩ := hg y hy
  have hf' : ∀ f, a.finality_pair = some f → f.height = y → f.target = entry y := by
    intro f hfp hfy
    simpa only [hfy] using hf f hfp (hfy ▸ hy)
  have hlock : own_lock Λ.toRecord y a.finality_pair = none ∨
      own_lock Λ.toRecord y a.finality_pair = some (entry y) := by
    cases hp : a.finality_pair with
    | none => simpa only [own_lock, hp] using hl
    | some f =>
      by_cases he : f.height = y
      · right; simp only [own_lock, he, ite_true, hf' f hp he]
      · simpa only [own_lock, hp, he, ite_false] using hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord a).target y = none ∨
      (record_row Λ.toRecord a).target y = some (entry y)
    rcases a with ⟨seat, pair, fp⟩
    cases pair with
    | empty => cases fp <;> simpa [record_row, Record.with_lock] using ht
    | vote g T timeout =>
      by_cases he : y = g
      · subst g
        obtain ⟨rfl, rfl⟩ := hh y T timeout rfl hy
        cases fp <;> simp only [record_row, Record.with_lock]
        all_goals
          by_cases htarget : Λ.target y = none
          · simp [htarget, Record.with_target]
          · simpa [htarget] using ht
      · cases timeout <;> cases fp <;> simp only [record_row] <;>
          (try split) <;> simpa [Record.with_lock, Record.with_timeout,
            Record.with_target, he] using ht
  · change (record_row Λ.toRecord a).timeout y = false
    apply KitFG.record_row_timeout_false_of_ne _ _ hn
    intro T hp
    have := (hh y T true hp hy).2
    cases this
  · exact (KitFG.record_row_lock Λ.toRecord a y) ▸ hlock
  · intro b hmem T timeout hpair
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh y T timeout hpair hy
    · exact hb b hmem T timeout hpair

include hh cert hreflect hqc hhead emission in
private theorem d7r_released_pair (j : Nat) (x : V) (r : Nat) (a : Wire)
    (u : Row (Fin n)) (ha : HonestRowAt S E rho T j x r a) (hd : S.decode a = some u)
    (hg : HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho)
      (S.record (V2.D.Run.stateBefore E rho j x)))
    (y : Nat) (U : BlockId) (timeout : Bool)
    (hp : u.height_pair = .vote y U timeout) (hy : pt.reset.M + 1 ≤ y)
    (hsource : ∃ C, actionSourceFG R E rho T x r = some (some C) ∧
      (O.height C).h = y ∧ (O.height C).T_h.root = U) :
    U = highRecordEntry R O T E rho y ∧ timeout = false := by
  let nd := P.clock (V2.D.Run.stateBefore E rho j x) (T.action r)
  let Λ := S.record (V2.D.Run.stateBefore E rho j x)
  obtain ⟨g, B, tm, hpair, he, _, _, _⟩ :=
    createRowOnce_released Ef cfg Λ u.signer (S.inputs nd).1 (S.inputs nd).2
      (emission j x r a u ha hd)
  have hhp := congrArg Row.height_pair he
  rw [hp] at hhp
  cases hhp
  have hfields := height_pair_vote_fields hpair
  rw [hfields] at hpair
  obtain ⟨C, hs, hC, ht⟩ := hsource
  have hentry := d7r_entry_source hh cert hreflect x r C ha.1 hs
    (by change _ ≤ _; rw [hC]; exact hy)
  rw [hC, ht] at hentry
  obtain ⟨htr, hto, hlock, _⟩ := hg y hy
  have hchoice := high_record_target_choice Λ.toRecord y U
    (finality_pair Λ.toRecord (S.inputs nd).2)
    (by simpa only [hentry] using htr) hto (by simpa only [hentry] using hlock)
    (by
      intro fp hf hfy
      have hfroot := d7r_finality_source hh cert hreflect hqc hhead j x (T.action r)
        Λ.toRecord fp ha.1 hf (hfy ▸ hy)
      rw [hfy, hentry] at hfroot
      exact hfroot)
  rw [hchoice] at hpair
  cases hpair
  exact ⟨hentry.symm, rfl⟩

include hh cert hreflect hqc hhead emission in
private theorem d7r_released_finality (j : Nat) (x : V) (r : Nat) (a : Wire)
    (u : Row (Fin n)) (ha : HonestRowAt S E rho T j x r a) (hd : S.decode a = some u)
    (f : FinalityPair) (hf : u.finality_pair = some f) (hy : pt.reset.M + 1 ≤ f.height) :
    f.target = highRecordEntry R O T E rho f.height := by
  obtain ⟨_, _, _, _, he, _, _, _⟩ := createRowOnce_released Ef cfg _ u.signer _ _
    (emission j x r a u ha hd)
  have hfp := congrArg Row.finality_pair he
  rw [hf] at hfp
  exact d7r_finality_source hh cert hreflect hqc hhead j x (T.action r) _ f
    ha.1 (Option.filter_eq_some_iff.mp hfp.symm).1 hy

include J in
private theorem d7r_record_fold (i : Nat) (x : V) :
    S.record (V2.D.Run.stateBefore E rho i x) =
      (V2.D.Engine.ownReleased E rho x 0 i).foldl (safetyRecordStep S) RecordOnce.initial := by
  have h := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
    J.clock_record J.process_record J.own_record E rho (Nat.zero_le i) x
    (fun _ t _ _ _ => J.restart_record _ t)
  change S.record (V2.D.Run.stateBefore E rho i x) =
    (V2.D.Engine.ownReleased E rho x 0 i).foldl (safetyRecordStep S) (S.record P.init) at h
  rwa [J.initial_record] at h

include hh cert hreflect hqc hhead J emission hown hnames in
private theorem d7r_all (i : Nat) (x : V) (hx : x ∈ rho.honest) :
    HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho)
      (S.record (V2.D.Run.stateBefore E rho i x)) := by
  induction i with
  | zero =>
    rw [d7r_record_fold J, V2.D.Engine.ownReleased_self]
    intro y _
    exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | succ i ih =>
    have hstep := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
      J.clock_record J.process_record J.own_record E rho (Nat.le_succ i) x
      (fun _ t _ _ _ => J.restart_record _ t)
    rw [V2.D.Engine.ownReleased_succ E rho x (le_refl i), V2.D.Engine.ownReleased_self,
      List.nil_append] at hstep
    rw [hstep]
    have preserve : ∀ o ∈ V2.D.Engine.ownReleasedAt E rho x i, ∀ Λ,
        HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho) Λ →
        HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho) (safetyRecordStep S Λ o) := by
      intro o ho Λ hg
      unfold safetyRecordStep
      cases hd : S.decodeObject o with
      | none => exact hg
      | some u =>
        obtain ⟨r, a, ha, hdecode⟩ := (HighRecordOwnOrigin_def.mp hown) i x o u hx ho hd
        apply d7r_write _ _ Λ u hg
        · intro y U timeout hp hy
          have hn : namedEntry (D.heightPair a) = some (y, U) := by
            rw [D.decode_height a u hdecode, hp]; rfl
          obtain ⟨C, hs, heq⟩ := hnames i x r a _ ha hn
          exact d7r_released_pair hh cert hreflect hqc hhead emission i x r a u ha hdecode ih
            y U timeout hp hy ⟨C, hs, (congrArg Prod.fst heq).symm,
              (congrArg Prod.snd heq).symm⟩
        · exact d7r_released_finality hh cert hreflect hqc hhead emission i x r a u ha hdecode
    have foldGood (ls : List P.Object) (hls : ls ⊆ V2.D.Engine.ownReleasedAt E rho x i)
        (Λ : RecordOnce) (hg : HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho) Λ) :
        HighRecordInvariant pt.reset.M (highRecordEntry R O T E rho)
          (ls.foldl (safetyRecordStep S) Λ) := by
      induction ls generalizing Λ with
      | nil => exact hg
      | cons o ls ih =>
        exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
          (preserve o (hls List.mem_cons_self) Λ hg)
    exact foldGood _ (List.Subset.refl _) _ ih

include hh cert hreflect hqc hhead J emission hown hnames in
/-- The durable write induction constructs one entry and all high record guards. -/
theorem high_entry_record_invariant :
    ∃ entry : Nat → BlockId,
      (∀ x r C, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some C) →
        high R O pt.reset C → entry (O.height C).h = (O.height C).T_h.root) ∧
      (∀ i x, x ∈ rho.honest →
        HighRecordInvariant pt.reset.M entry (S.record (V2.D.Run.stateBefore E rho i x))) := by
  exact ⟨highRecordEntry R O T E rho, d7r_entry_source hh cert hreflect,
    d7r_all hh cert hreflect hqc hhead J emission hown hnames⟩

private theorem d7s_target_sign (Λ : Record) (y : Nat) (U : BlockId)
    (fp : Option FinalityPair) (timeout : Bool)
    (ht : Λ.target y = none ∨ Λ.target y = some U) (hn : Λ.timeout y = false)
    (hp : height_pair Λ (some (y, U)) fp = .vote y U timeout) : timeout = false := by
  cases hl : own_lock Λ y fp with
  | some locked => exact (height_pair_of_own_lock hn hl hp).1
  | none =>
    rcases ht with ht | ht <;>
      simp only [d7r_height_pair_some_def, hn, Bool.false_eq_true, ite_false, hl, ht,
        ite_true] at hp <;> cases hp <;> rfl

include J emission hown in
/-- The old shield alone derives the seed guards, including exclusion of the first timeout.
The premise ranges over actual emitted rows, including private and delayed rows. -/
theorem shield_record_before_cut (X : FGBlock (Fin n)) (b : Nat) (cutoff : Time)
    (hb : 1 ≤ b) (shield : HighRecordShieldRows R S O T E rho D X b cutoff)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hold : ∀ j r a, j < i → HonestRowAt S E rho T j x r a → T.action r < cutoff) :
    HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root)
      (S.record (V2.D.Run.stateBefore E rho i x)) := by
  induction i with
  | zero =>
    rw [d7r_record_fold J, V2.D.Engine.ownReleased_self]
    intro y _
    exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | succ i ih =>
    have prior := ih (fun j r a hj ha => hold j r a (Nat.lt_succ_of_lt hj) ha)
    have hstep := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
      J.clock_record J.process_record J.own_record E rho (Nat.le_succ i) x
      (fun _ t _ _ _ => J.restart_record _ t)
    rw [V2.D.Engine.ownReleased_succ E rho x (le_refl i), V2.D.Engine.ownReleased_self,
      List.nil_append] at hstep
    rw [hstep]
    have preserve : ∀ o ∈ V2.D.Engine.ownReleasedAt E rho x i, ∀ Λ,
        HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root) Λ →
        HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root)
          (safetyRecordStep S Λ o) := by
      intro o ho Λ hg
      unfold safetyRecordStep
      cases hd : S.decodeObject o with
      | none => exact hg
      | some u =>
        obtain ⟨r, a, ha, hdecode⟩ := (HighRecordOwnOrigin_def.mp hown) i x o u hx ho hd
        obtain ⟨g, U, timeout, hpair, he, _, _, _⟩ :=
          createRowOnce_released Ef cfg _ u.signer _ _ (emission i x r a u ha hdecode)
        have hp := congrArg Row.height_pair he
        have hs := shield i x r a g U timeout ha (hold i r a (Nat.lt_succ_self i) ha)
          ((D.decode_height a u hdecode).trans hp)
        have hcap := hs.1
        apply d7r_write _ _ Λ u hg
        · intro y W sign hpy hy
          rw [hp] at hpy
          cases hpy
          have hgb : g = b := by simp only [Height] at *; omega
          have hU := hs.2 hgb
          refine ⟨hU, ?_⟩
          obtain ⟨ht, hn, _, _⟩ := prior g hy
          rw [height_pair_vote_fields hpair] at hpair
          exact d7s_target_sign _ g U _ timeout (by simpa only [hU] using ht) hn hpair
        · intro f hf hy
          have hfp := congrArg Row.finality_pair he
          rw [hf] at hfp
          have hfg := of_decide_eq_true (Option.filter_eq_some_iff.mp hfp.symm).2
          simp only [Height] at *
          omega
    have foldGood (ls : List P.Object) (hls : ls ⊆ V2.D.Engine.ownReleasedAt E rho x i)
        (Λ : RecordOnce)
        (hg : HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root) Λ) :
        HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root)
          (ls.foldl (safetyRecordStep S) Λ) := by
      induction ls generalizing Λ with
      | nil => exact hg
      | cons o ls ih =>
        exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
          (preserve o (hls List.mem_cons_self) Λ hg)
    exact foldGood _ (List.Subset.refl _) _ prior

private theorem d7r_fresh_write (y : Nat) (Λ : RecordOnce)
    (a : Row (Fin n)) (hg : HighRecordFresh y Λ)
    (hh : ∃ g T timeout, a.height_pair = .vote g T timeout ∧ g < y)
    (hf : ∀ f, a.finality_pair = some f → f.height < y) :
    HighRecordFresh y (record_row_once Λ a) := by
  obtain ⟨g, T, timeout, hp, hgy⟩ := hh
  rcases a with ⟨seat, pair, fp⟩
  dsimp only at hp
  subst pair
  obtain ⟨ht, hn, hl, hb⟩ := hg
  have hne : y ≠ g := by simp only [Height] at *; omega
  have hlock : own_lock Λ.toRecord y fp = none := by
    cases fp with
    | none => exact hl
    | some f =>
      have hfy : f.height ≠ y := by have := hf f rfl; simp only [Height] at *; omega
      change (if f.height = y then some f.target else Λ.lock y) = none
      rw [ite_eq_right hfy]
      exact hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).target y = none
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using ht
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).timeout y = false
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using hn
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).lock y = none
    rw [KitFG.record_row_lock]
    exact hlock
  · intro b hm U tm he
    rcases List.mem_cons.mp hm with rfl | hm
    · have := (NamedHeightPair.vote.inj he).1
      simp only [Height] at *; omega
    · exact hb b hm U tm he

include hown in
private theorem d7r_own_origin (i : Nat) (x : V) (o : P.Object) (u : Row (Fin n))
    (hx : x ∈ rho.honest) (ho : o ∈ V2.D.Engine.ownReleased E rho x 0 i)
    (hd : S.decodeObject o = some u) :
    ∃ j r a, j < i ∧ HonestRowAt S E rho T j x r a ∧ S.decode a = some u := by
  rw [V2.D.Engine.ownReleased_def] at ho
  obtain ⟨j, hj, ho⟩ := List.mem_flatMap.mp ho
  have hji : j < i := by simpa using hj
  obtain ⟨r, a, ha, hd⟩ := (HighRecordOwnOrigin_def.mp hown) j x o u hx ho hd
  exact ⟨j, r, a, hji, ha, hd⟩

private theorem d7r_row_height_eq (a : Wire) (pair : NamedHeightPair)
    (hp : D.heightPair a = pair) :
    historyRowHeight S D a = (fun value : NamedHeightPair =>
      match value with | .empty => none | .vote h _ _ => some h) pair := by
  exact congrArg (fun pair : NamedHeightPair =>
    match pair with | .empty => none | .vote h _ _ => some h) hp

include J emission hown in
/-- Strict bounds on all earlier rows leave the target, timeout, lock and sent fields fresh. -/
theorem high_record_fresh_at_cut (i : Nat) (x : V) (y : Nat) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h < y) :
    HighRecordFresh y (S.record (V2.D.Run.stateBefore E rho i x)) := by
  rw [d7r_record_fold J]
  have preserve : ∀ o ∈ V2.D.Engine.ownReleased E rho x 0 i, ∀ Λ,
      HighRecordFresh y Λ → HighRecordFresh y (safetyRecordStep S Λ o) := by
    intro o ho Λ hg
    unfold safetyRecordStep
    cases hd : S.decodeObject o with
    | none => exact hg
    | some u =>
      obtain ⟨j, r, a, hji, ha, hdecode⟩ := d7r_own_origin hown i x o u hx ho hd
      obtain ⟨g, U, timeout, _, he, _, _, _⟩ :=
        createRowOnce_released Ef cfg _ u.signer _ _ (emission j x r a u ha hdecode)
      have hp := congrArg Row.height_pair he
      have hrow : historyRowHeight S D a = some g := by
        exact d7r_row_height_eq a _ ((D.decode_height a u hdecode).trans hp)
      have hgy := hbefore j r a g hji ha hrow
      apply d7r_fresh_write y Λ u hg
      · exact ⟨g, U, timeout, hp, hgy⟩
      · intro f hf
        have hfp := congrArg Row.finality_pair he
        rw [hf] at hfp
        have hfg := of_decide_eq_true (Option.filter_eq_some_iff.mp hfp.symm).2
        exact hfg.trans hgy
  have foldFresh (ls : List P.Object) (hls : ls ⊆ V2.D.Engine.ownReleased E rho x 0 i)
      (Λ : RecordOnce) (hg : HighRecordFresh y Λ) :
      HighRecordFresh y (ls.foldl (safetyRecordStep S) Λ) := by
    induction ls generalizing Λ with
    | nil => exact hg
    | cons o ls ih =>
      exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
        (preserve o (hls List.mem_cons_self) Λ hg)
  exact foldFresh _ (List.Subset.refl _) RecordOnce.initial
    ⟨rfl, rfl, rfl, fun _ h => (List.not_mem_nil h).elim⟩

include hh cert hreflect hqc hhead J emission hown hnames in
/-- The seed shield derives old records; complete historical compatibility covers every
later prefix, including the cutoff and the interval before service starts. For the full
reset threshold, `hh` also covers the earlier history, as required by the PC history leaf. -/
theorem shield_high_entry_record_invariant (X : FGBlock (Fin n)) (b : Nat) (cutoff : Time)
    (seed : HighRecordSeedLeaves R S O T E rho D pt X b cutoff) :
    ∃ entry : Nat → BlockId,
      (∀ x r C, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some C) →
        high R O pt.reset C → entry (O.height C).h = (O.height C).T_h.root) ∧
      (∀ i x, x ∈ rho.honest →
        HighRecordInvariant pt.reset.M entry (S.record (V2.D.Run.stateBefore E rho i x))) ∧
      (∀ i x, x ∈ rho.honest →
        (∀ j r a, j < i → HonestRowAt S E rho T j x r a → T.action r < cutoff) →
        HighRecordInvariant (b - 1) (fun _ => (O.height X).T_h.root)
          (S.record (V2.D.Run.stateBefore E rho i x)) ∧
        ∀ y, b < y → HighRecordFresh y (S.record (V2.D.Run.stateBefore E rho i x))) := by
  obtain ⟨entry, sources, records⟩ :=
    high_entry_record_invariant hh cert hreflect hqc hhead J emission hown hnames
  refine ⟨entry, sources, records, ?_⟩
  intro i x hx hold
  have hb : 1 ≤ b := (Nat.le_add_left 1 pt.reset.M).trans seed.2.2.1
  have shield := seed.2.2.2.2
  refine ⟨shield_record_before_cut J emission hown X b cutoff hb shield i x hx hold, ?_⟩
  intro y hy
  apply high_record_fresh_at_cut (D := D) J emission hown i x y hx
  intro j r a h hj ha hh
  cases hp : D.heightPair a with
  | empty =>
    have he := d7r_row_height_eq a _ hp
    rw [he] at hh
    cases hh
  | vote g U timeout =>
    have hgh : g = h := Option.some.inj ((d7r_row_height_eq a _ hp).symm.trans hh)
    have hcap := (shield j x r a g U timeout ha (hold j r a hj ha) hp).1
    simp only [Height] at *
    omega

include J emission hown in
/-- The inclusive reset cut uses the published c2 emission cap. -/
theorem high_record_reset_fresh (w : FGResetHistory) (start : Time)
    (h0 : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) start w)
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (hx : x ∈ rho.honest)
    (y : Nat) (hy : w.M + 1 ≤ y) :
    HighRecordFresh y (S.record (V2.D.Run.stateBefore E rho (afterTicksIdx rho w.u0) x)) := by
  apply high_record_fresh_at_cut (D := D) J emission hown _ x y hx
  intro j r a h hj ha hh
  have hf := V2.D.Engine.filter_eq_take hs (cutPred w.u0) (by
    intro e f hk hmem
    exact decide_eq_true (hk.trans (of_decide_eq_true hmem)))
  have hm : (.tick x (T.action r) : V2.Event V P.Object) ∈
      rho.events.filter (cutPred w.u0) := by
    rw [hf]
    apply List.mem_of_getElem? (i := j)
    change j < (rho.events.filter (cutPred w.u0)).length at hj
    rw [List.getElem?_take_of_lt hj]
    exact ha.2.1
  have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
  have ht : T.action r ≤ w.u0 := by
    change toLex (T.action r, (1 : Nat)) ≤ toLex (w.u0, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  cases hp : D.heightPair a with
  | empty =>
    have he := d7r_row_height_eq a _ hp
    rw [he] at hh
    cases hh
  | vote g U timeout =>
    have hgh : g = h := Option.some.inj ((d7r_row_height_eq a _ hp).symm.trans hh)
    have hcap := h0.rowCap j x r a g U (T.action r) ha ha.2.1 ht (by rw [hp]; rfl)
    simp only [Height] at *
    omega

include hh cert hreflect hqc hhead J emission hown hnames in
/-- High guards at y and strict freshness at y+1 share the same durable record. -/
theorem high_record_guards_and_fresh
    (z : V) (r : Nat) (C : FGBlock (Fin n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG R E rho T z r = some (some C))
    (y : Nat) (hheight : (O.height C).h = y) (hy : pt.reset.M + 1 ≤ y)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h < y + 1) :
    HighRecordGuard_W (S.record (V2.D.Run.stateBefore E rho i x)) y (O.height C).T_h ∧
      HighRecordFresh (y + 1) (S.record (V2.D.Run.stateBefore E rho i x)) := by
  have hentry := d7r_entry_source hh cert hreflect z r C hz hsource
    (by change _ ≤ _; rw [hheight]; exact hy)
  rw [hheight] at hentry
  obtain ⟨ht, hn, hl, _⟩ := d7r_all hh cert hreflect hqc hhead J emission hown hnames i x hx y hy
  rw [hentry] at ht hl
  exact ⟨⟨ht, hn, hl⟩, high_record_fresh_at_cut J emission hown i x (y + 1) hx hbefore⟩

include hh cert hreflect hqc hhead J emission hown hnames in
/-- The own-finality lock at the actual head agrees with the high source entry. -/
theorem high_action_target_choice (z : V) (r : Nat) (C : FGBlock (Fin n))
    (hz : z ∈ rho.honest) (hsource : actionSourceFG R E rho T z r = some (some C))
    (hhigh : high R O pt.reset C) (i : Nat) (x : V) (t : Time) (hx : x ∈ rho.honest) :
    let Λ := S.record (V2.D.Run.stateBefore E rho i x)
    height_pair Λ.toRecord (some ((O.height C).h, (O.height C).T_h.root))
      (finality_pair Λ.toRecord (S.inputs (P.clock (V2.D.Run.stateBefore E rho i x) t)).2) =
        .vote (O.height C).h (O.height C).T_h.root false := by
  have hentry := d7r_entry_source hh cert hreflect z r C hz hsource hhigh
  obtain ⟨ht, hn, hl, _⟩ := d7r_all hh cert hreflect hqc hhead J emission hown hnames i x hx
    (O.height C).h hhigh
  apply high_record_target_choice
  · simpa only [hentry] using ht
  · exact hn
  · simpa only [hentry] using hl
  · intro fp hf hfy
    have hr := d7r_finality_source hh cert hreflect hqc hhead i x t
      (S.record (V2.D.Run.stateBefore E rho i x)).toRecord fp hx hf (hfy ▸ hhigh)
    simpa only [hfy, hentry] using hr

omit [DecidableEq V] in
private theorem d7r_tick_strict (hs : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {v : V} {t u : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hj : rho.events[j]? = some (.tick v u)) (hij : i < j) : t < u := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
  rw [hie, hje] at hk
  have htu := V2.D.Engine.time_le_of_key_le _ _ hk
  change t ≤ u at htu
  have hne : t ≠ u := by
    intro he
    have hevent : rho.events[i] = rho.events[j] := by rw [hie, hje, he]
    have := (List.Nodup.getElem_inj_iff hs.nodup).mp hevent
    omega
  exact lt_of_le_of_ne htu hne

private theorem d7r_action_mono (hT : FGTimingLaws T) : Monotone T.action := by
  intro r q hrq
  have hmul : ((r * T.roundSlots : Nat) : Time) ≤ ((q * T.roundSlots : Nat) : Time) := by
    exact_mod_cast Nat.mul_le_mul_right T.roundSlots hrq
  rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq,
    hT.proposal_eq, hT.proposal_eq]
  have := hT.delta_pos
  nlinarith

include hh cert hreflect hqc hhead J emission hown hnames in
/-- Clock retention transports the prefix guards to the actual action read. -/
theorem high_record_guards_and_fresh_at_action (hT : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho)
    (z : V) (r : Nat) (C : FGBlock (Fin n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG R E rho T z r = some (some C))
    (y : Nat) (hheight : (O.height C).h = y) (hy : pt.reset.M + 1 ≤ y)
    (q : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, r < q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h < y + 1) :
    ∀ nd, postClock E rho x (T.action q) = some nd →
      HighRecordGuard_W (S.record nd) y (O.height C).T_h ∧
        HighRecordFresh (y + 1) (S.record nd) := by
  intro nd hnd
  unfold postClock preTick at hnd
  cases hi : V2.D.Run.tickIdx? rho x (T.action q) with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hnd
    have hj := V2.D.Run.tickIdx?_spec hi
    have hr : S.record (V2.D.Run.stateBefore E rho i x) = S.record nd :=
      (J.clock_record _ (T.action q)).symm.trans (congrArg S.record hnd)
    have hg := high_record_guards_and_fresh hh cert hreflect hqc hhead J emission hown hnames
      z r C hz hsource y hheight hy i x hx (by
        intro j r a h hji ha hah
        have ht := d7r_tick_strict hs ha.2.1 hj hji
        have hrq : r < q := by
          by_contra hn
          exact (not_lt.mpr (d7r_action_mono hT (Nat.le_of_not_gt hn))) ht
        exact hbefore j r a h hrq ha hah)
    simpa only [hr] using hg

include hh cert hreflect hqc hhead J emission hown hnames in
private theorem d7r_honest_pair (j : Nat) (x : V) (r : Nat) (a : Wire) (u : Row (Fin n))
    (ha : HonestRowAt S E rho T j x r a) (hd : S.decode a = some u)
    (y : Nat) (U : BlockId) (hn : namedEntry u.height_pair = some (y, U))
    (hy : pt.reset.M + 1 ≤ y) :
    u.height_pair = .vote y (highRecordEntry R O T E rho y) false := by
  cases hp : u.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote g B timeout =>
    delta namedEntry at hn
    rw [hp] at hn
    have he : (g, B) = (y, U) := Option.some.inj hn
    cases he
    have hnwire : namedEntry (D.heightPair a) = some (y, U) := by
      rw [D.decode_height a u hd, hp]; rfl
    obtain ⟨C, hs, heq⟩ := hnames j x r a _ ha hnwire
    obtain ⟨hroot, htimeout⟩ := d7r_released_pair hh cert hreflect hqc hhead emission
      j x r a u ha hd
      (d7r_all hh cert hreflect hqc hhead J emission hown hnames
        j x ha.1)
      y U timeout hp hy ⟨C, hs, (congrArg Prod.fst heq).symm,
        (congrArg Prod.snd heq).symm⟩
    rw [hroot, htimeout]

include hh cert hreflect in
private theorem d7r_qc_source
    (i : Nat) (z : V) (r : Nat) (wire : Wire) (a : Row (Fin n))
    (C : FGBlock (Fin n)) (y : Nat) (U : BlockId)
    (hb : HonestRowBefore S E rho T i z r wire)
    (hs : actionSourceFG R E rho T z r = some (some C))
    (hn : namedEntry a.height_pair = some ((O.height C).h, (O.height C).T_h.root))
    (hp : namedEntry a.height_pair = some (y, U)) (hy : pt.reset.M + 1 ≤ y) :
    z ∈ rho.honest ∧ high R O pt.reset C ∧ (O.height C).h = y ∧
      U = (O.height C).T_h.root ∧ U = highRecordEntry R O T E rho y := by
  obtain ⟨j, _, ha⟩ := hb
  have he := Option.some.inj (hn.symm.trans hp)
  have hc : (O.height C).h = y := congrArg Prod.fst he
  have ht : U = (O.height C).T_h.root := (congrArg Prod.snd he).symm
  have hhigh : high R O pt.reset C := by change _ ≤ _; rw [hc]; exact hy
  have hentry := d7r_entry_source hh cert hreflect z r C ha.1 hs hhigh
  rw [hc] at hentry
  exact ⟨ha.1, hhigh, hc, ht, ht.trans hentry.symm⟩

private theorem d7r_quorum_honest (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (Q : Finset (Fin n)) (hQ : Ef.IsQuorum Q) :
    ∃ k ∈ Q, safetyHolder S rho k ∈ rho.honest := by
  classical
  obtain ⟨k, hk, hn⟩ := honest_in_quorum Ef (historyFaulty S rho) hQ hweight
  exact ⟨k, hk, by delta historyFaulty at *; simpa only [Finset.mem_filter, Finset.mem_univ,
    true_and, not_not] using hn⟩

include hh cert hreflect hqc hhead J emission hown hnames in
/-- Every stored high quorum has the identity constructed by the record induction. -/
theorem ff2_stored_high_qc_identity
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (hOrigin : ∀ i x W, HeldAt R E rho i x W → ∀ a ∈ chainRows W,
      ∃ (wire : Wire) (r : Nat), S.decode wire = some a ∧
        D.signer wire = some a.signer ∧
        ∀ z, RowSigner S rho D.signer wire z → z ∈ rho.honest →
          HonestRowBefore S E rho T i z r wire) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG R E rho T z r = some (some C) → high R O pt.reset C →
        entry (O.height C).h = (O.height C).T_h.root) ∧
      ∀ i x W, HeldAt R E rho i x W →
        (∀ y U (Q : Finset (Fin n)),
          pt.reset.M + 1 ≤ y → Ef.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
            a.height_pair.matchesEntry y U = true) →
          U = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG R E rho T z r = some (some C) ∧ high R O pt.reset C ∧
            (O.height C).h = y ∧ U = (O.height C).T_h.root ∧
            ∃ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
              a.height_pair = .vote y (entry y) false) ∧
        (∀ fp (Q : Finset (Fin n)), pt.reset.M + 1 ≤ fp.height → Ef.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧ a.finality_pair = some fp) →
          fp.target = entry fp.height) := by
  classical
  refine ⟨highRecordEntry R O T E rho, d7r_entry_source hh cert hreflect, ?_⟩
  intro i x W hW
  refine ⟨?_, ?_⟩
  · intro y U Q hy hQ hrows
    obtain ⟨k, hk, hz⟩ := d7r_quorum_honest hweight Q hQ
    obtain ⟨a, ha, hs, hm⟩ := hrows k hk
    obtain ⟨wire, r, hd, hauth, ho⟩ := hOrigin i x W hW a ha
    have hsign : RowSigner S rho D.signer wire (safetyHolder S rho k) := by
      exact ⟨k, by rw [hauth, hs], rfl⟩
    obtain ⟨j, hji, hem⟩ := ho _ hsign hz
    have hn : namedEntry a.height_pair = some (y, U) := by
      cases hp : a.height_pair with
      | empty => rw [hp] at hm; cases hm
      | vote g B timeout =>
        rw [hp] at hm
        have he : g = y ∧ B = U := of_decide_eq_true hm
        rw [he.1, he.2]; rfl
    have hnwire : namedEntry (D.heightPair wire) = some (y, U) := by
      rw [D.decode_height wire a hd]; exact hn
    obtain ⟨C, hsource, hc⟩ := hnames j _ r wire _ hem hnwire
    obtain ⟨hz', hhigh, hhC, ht, he⟩ := d7r_qc_source hh cert hreflect i _ r wire
      a C y U ⟨j, hji, hem⟩ hsource (by rw [hn, hc]) hn hy
    exact ⟨he, _, r, C, hz', hsource, hhigh, hhC, ht, k, hk, a, ha, hs,
      d7r_honest_pair hh cert hreflect hqc hhead J emission hown hnames
        j _ r wire a hem hd y U hn hy⟩
  · intro fp Q hy hQ hrows
    obtain ⟨k, hk, hz⟩ := d7r_quorum_honest hweight Q hQ
    obtain ⟨a, ha, hs, hfp⟩ := hrows k hk
    obtain ⟨wire, r, hd, hauth, ho⟩ := hOrigin i x W hW a ha
    have hsign : RowSigner S rho D.signer wire (safetyHolder S rho k) := by
      exact ⟨k, by rw [hauth, hs], rfl⟩
    obtain ⟨j, _, hem⟩ := ho _ hsign hz
    exact d7r_released_finality hh cert hreflect hqc hhead emission j _ r wire a hem hd fp hfp hy

include hh cert hreflect hqc hhead J emission hown hnames in
/-- Selected progress, target and finality certificates retain one high identity. -/
theorem ff2_high_qc_identity
    (hstore : ∀ i x, x ∈ rho.honest →
      FGStoreInvariant O.height O.finality (R.core (V2.D.Run.stateBefore E rho i x)).fg) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG R E rho T z r = some (some C) → high R O pt.reset C →
        entry (O.height C).h = (O.height C).T_h.root) ∧
      ∀ i x W, x ∈ rho.honest → W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
        (∀ y X (Q : Finset (Fin n))
            (rows : Fin n → FGBlock (Fin n) × Row (Fin n)),
          pt.reset.M + 1 ≤ y → y < (O.height W).h →
          FGBlock.Preceq X W → (O.height X).h = y → Ef.IsQuorum Q →
          (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
            (rows k).2.signer = k ∧
            (rows k).2.height_pair.matchesEntry y X.root = true) →
          X.root = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG R E rho T z r = some (some C) ∧ high R O pt.reset C ∧
            (O.height C).h = y ∧ X.root = (O.height C).T_h.root ∧
            ∃ k ∈ Q, (rows k).2.height_pair = .vote y (entry y) false) ∧
        (pt.reset.M + 1 ≤ (O.height W).h_j →
          (O.height W).J.root = entry (O.height W).h_j ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG R E rho T z r = some (some C) ∧ high R O pt.reset C ∧
            (O.height C).h = (O.height W).h_j ∧
            (O.height W).J.root = (O.height C).T_h.root) ∧
        (pt.reset.M + 1 ≤ (O.finality W).h_F →
          (O.finality W).F.root = entry (O.finality W).h_F ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG R E rho T z r = some (some C) ∧ high R O pt.reset C ∧
            (O.height C).h = (O.finality W).h_F ∧
            (O.finality W).F.root = (O.height C).T_h.root) := by
  classical
  refine ⟨highRecordEntry R O T E rho, d7r_entry_source hh cert hreflect, ?_⟩
  intro i x W hx hW
  have ho := hqc
  have hoW := ho i x W hx hW
  refine ⟨?_, ?_, ?_⟩
  · intro y X Q rows hy hlt hX hheight hQ hrows
    obtain ⟨k, hk, z, r, wire, hb, hd, _, C, hs, hn, _⟩ :=
      hoW.1 y X Q rows (by simp only [Height] at *; omega) hlt hX hheight hQ hrows
    have hp : namedEntry (rows k).2.height_pair = some (y, X.root) := by
      cases he : (rows k).2.height_pair with
      | empty => have hm := (hrows k hk).2.2.2; rw [he] at hm; cases hm
      | vote g U timeout =>
        have hm := (hrows k hk).2.2.2
        rw [he] at hm
        have hgu : g = y ∧ U = X.root := of_decide_eq_true hm
        rw [hgu.1, hgu.2]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := d7r_qc_source hh cert hreflect i z r wire
      (rows k).2 C y X.root hb hs hn hp hy
    obtain ⟨j, _, ha⟩ := hb
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht, k, hk,
      d7r_honest_pair hh cert hreflect hqc hhead J emission hown hnames j z r wire (rows k).2 ha hd
        y X.root hp hy⟩
  · intro hy
    have hnz : (O.height W).h_j ≠ 0 := by simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := cert.height.justification_certificate W hnz
    have hw' : ∀ k, ∃ B a, k ∈ Q → FGBlock.Preceq B W ∧ a ∈ B.rows ∧
        a.signer = k ∧
        a.height_pair = .vote (O.height W).h_j (O.height W).J.root false := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨B, a, ha⟩ := hw k hk
        exact ⟨B, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose B a ha using hw'
    obtain ⟨k, hk, z, r, wire, hb, _, _, C, hs, hn, _⟩ :=
      hoW.2.1 Q (fun k => (B k, a k)) hnz hQ ha
    have hp : namedEntry (a k).height_pair =
        some ((O.height W).h_j, (O.height W).J.root) := by
      rw [(ha k hk).2.2.2]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := d7r_qc_source hh cert hreflect i z r wire
      (a k) C _ _ hb hs hn hp hy
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht⟩
  · intro hy
    obtain ⟨B, hBW, hBJ, hj⟩ := KitFG.provenance_finality_of_certificate Ef
      (O.height) (O.finality) cert W (by simp only [Height] at *; omega)
    have hB := KitFG.ancestor_closed_of_parent_closed _
      (hstore i x hx).closed W hW B hBW
    have hnz : (O.height B).h_j ≠ 0 := by rw [hj]; simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := cert.height.justification_certificate B hnz
    have hw' : ∀ k, ∃ D a, k ∈ Q → FGBlock.Preceq D B ∧ a ∈ D.rows ∧
        a.signer = k ∧
        a.height_pair = .vote (O.height B).h_j (O.height B).J.root false := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨D, a, ha⟩ := hw k hk
        exact ⟨D, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose D a ha using hw'
    obtain ⟨k, hk, z, r, wire, hb, _, _, C, hs, hn, _⟩ :=
      (ho i x B hx hB).2.1 Q (fun k => (D k, a k)) hnz hQ ha
    have hp : namedEntry (a k).height_pair =
        some ((O.finality W).h_F, (O.finality W).F.root) := by
      rw [(ha k hk).2.2.2, hj, hBJ]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := d7r_qc_source hh cert hreflect i z r wire
      (a k) C _ _ hb hs hn hp hy
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht⟩


include hh cert hreflect hqc hhead J emission hown hnames in
/-- Store reachability and the approved root premise exclude high contests. -/
theorem ff2_no_high_contest
    (hstore : ∀ i x, x ∈ rho.honest →
      FGStoreInvariant O.height O.finality (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hobs : FGObservationLaws R O)
    (hroots : ∀ i x, x ∈ rho.honest →
      SimplexFG.ViewRootInj (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) :
    ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
      let controls := O.controls (V2.D.Run.stateBefore E rho i x)
      controls.contest = true → controls.H ≤ pt.reset.M + 1 := by
  classical
  obtain ⟨entry, _, hidentity⟩ := ff2_high_qc_identity
    hh cert hreflect hqc hhead J emission hown hnames hstore
  intro i x _hi hx
  let st := R.core (V2.D.Run.stateBefore E rho i x)
  change (O.controls (V2.D.Run.stateBefore E rho i x)).contest = true →
    (O.controls (V2.D.Run.stateBefore E rho i x)).H ≤ pt.reset.M + 1
  rw [hobs.controls_eq]
  rw [KitFG.treeStoreControlsView_def]
  intro ht
  change (decide (st.fg.h_max = st.fg.h_j + 1) &&
    decide (∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
      (O.height W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W)) = true at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  obtain ⟨htop, W, hW, _hFW, hw, hbad⟩ := ht
  change st.fg.h_max ≤ pt.reset.M + 1
  by_contra hlarge
  have hjhigh : pt.reset.M + 1 ≤ st.fg.h_j := by simp only [Height] at *; omega
  have hI : KitFG.FGStoreInvariant (O.height) (O.finality) st.fg :=
    hstore i x hx
  obtain ⟨K, hK, _, hjK, hJK⟩ := hI.pair.1
  have hJmem : st.fg.J ∈ st.fg.TF := by
    rw [hJK]
    exact ancestor_closed_of_parent_closed _ hI.closed K hK _
      (preceq_trans (cert.height.justified_preceq_entry K) (cert.height.entry_preceq K))
  have hJroot : st.fg.J.root = entry st.fg.h_j := by
    rw [hJK, hjK]
    exact ((hidentity i x K hx hK).2.1 (hjK ▸ hjhigh)).1
  have allWitnesses : ∀ D ∈ st.fg.TF, (O.height D).h = st.fg.h_max →
      FGBlock.Preceq st.fg.J D := by
    intro D hD hd
    obtain ⟨X, hXD, hXheight, Q, hQ, hwit⟩ :=
      cert.height.height_crossing D st.fg.h_j
        (by simp only [Height] at *; omega)
        (by rw [hd, htop]; exact Nat.lt_succ_self _)
    have hwit' : ∀ k, ∃ B a, k ∈ Q → FGBlock.Preceq B D ∧ a ∈ B.rows ∧
        a.signer = k ∧ a.height_pair.matchesEntry st.fg.h_j X.root = true := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨B, a, ha⟩ := hwit k hk
        exact ⟨B, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose B a ha using hwit'
    have hXroot := ((hidentity i x D hx hD).1 st.fg.h_j X Q
      (fun k => (B k, a k)) hjhigh
      (by rw [hd, htop]; exact Nat.lt_succ_self _) hXD hXheight hQ ha).1
    have he : st.fg.J = X := hroots i x hx
      _ _ ⟨st.fg.J, hJmem, KitFG.preceq_refl _⟩
      ⟨D, hD, hXD⟩ (hJroot.trans hXroot.symm)
    exact he ▸ hXD
  exact hbad (allWitnesses W hW hw)

/-- The high-record guard is exactly its three durable fields. -/
theorem HighRecordGuard_W_def (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) :
    HighRecordGuard_W Λ y U =
      ((Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
        (Λ.lock y = none ∨ Λ.lock y = some U.root)) := rfl

include hh cert hreflect hqc hhead J emission hown hnames in
/-- The kernel guard is a consequence of the complete record induction. -/
theorem ff2_high_record_guards :
    ∀ a r C, a ∈ rho.honest → actionSourceFG R E rho T a r = some (some C) →
      high R O pt.reset C → ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
        HighRecordGuard_W (S.record (V2.D.Run.stateBefore E rho i x))
          (O.height C).h (O.height C).T_h := by
  intro a r C ha hs hhigh i x _hi hx
  have hentry := d7r_entry_source hh cert hreflect a r C ha hs hhigh
  obtain ⟨ht, hn, hl, _⟩ := d7r_all hh cert hreflect hqc hhead J emission hown hnames
    i x hx (O.height C).h hhigh
  simpa only [hentry] using And.intro ht (And.intro hn hl)

private theorem d7r_sent_origin (ls : List P.Object) (Λ : RecordOnce)
    (b : NamedHeightPair × Option FinalityPair)
    (hm : b ∈ (ls.foldl (safetyRecordStep S) Λ).sent) :
    b ∈ Λ.sent ∨ ∃ o ∈ ls, ∃ u, S.decodeObject o = some u ∧ u.onceKey = b := by
  induction ls generalizing Λ with
  | nil => exact Or.inl hm
  | cons o ls ih =>
    rcases ih (safetyRecordStep S Λ o) hm with hold | ⟨o', hm, u, hd, he⟩
    · unfold safetyRecordStep at hold
      cases hd : S.decodeObject o with
      | none => rw [hd] at hold; exact Or.inl hold
      | some u =>
        rw [hd] at hold
        rcases List.mem_cons.mp hold with he | hold
        · exact Or.inr ⟨o, List.mem_cons_self, u, hd, he.symm⟩
        · exact Or.inl hold
    · exact Or.inr ⟨o', List.mem_cons_of_mem _ hm, u, hd, he⟩

include J hown in
private theorem d7r_prior_origin (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (b : NamedHeightPair × Option FinalityPair)
    (hb : b ∈ (S.record (V2.D.Run.stateBefore E rho i x)).sent) :
    ∃ j r a, j < i ∧ HonestRowAt S E rho T j x r a ∧
      namedEntry (D.heightPair a) = namedEntry b.1 := by
  rw [d7r_record_fold J] at hb
  rcases d7r_sent_origin _ RecordOnce.initial b hb with hb | ⟨o, ho, u, hd, he⟩
  · cases hb
  obtain ⟨j, r, a, hji, ha, hdecode⟩ := d7r_own_origin hown i x o u hx ho hd
  refine ⟨j, r, a, hji, ha, ?_⟩
  rw [D.decode_height a u hdecode]
  exact congrArg namedEntry (congrArg Prod.fst he)

variable {valid : Wire → Bool}
variable (complete : ∀ j x r a, HonestRowAt S E rho T j x r a →
  ∃ u, S.decode a = some u ∧ RowComplete S rho D.signer valid x a)
variable (wireLaws : FGRowPermissionWireLaws S (fun a => namedEntry (D.heightPair a)))
variable (e : Fin n ≃ V) (he : ∀ k, rho.seatOf S.fgLabel (S.fgSeats k) = e k)
variable (hT : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
variable (enabled : ∀ r, S.enabled (T.action r) = true)

include hh cert hreflect hqc hhead hsrc hheight J emission hown hnames complete
  wireLaws e he hT hs enabled in
/-- The d2 current/prior split constructs a complete target with its original send index. -/
theorem high_target_row_covered (x : V) (hx : x ∈ rho.honest) (r : Nat)
    (C : FGBlock (Fin n)) (hsource : actionSourceFG R E rho T x r = some (some C))
    (hhigh : high R O pt.reset C) (hawake : E.awake x (T.action r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      RowComplete S rho D.signer valid x a ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false := by
  have he' : safetyHolder S rho = e := funext he
  have client : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    rw [he']
    exact ordinary_FGHolderClientLaws S Ef cfg E rho J e he
  have trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    apply (ordinary_FGHolderClientTrace_iff S Ef cfg E rho _).mpr
    intro i _ k
    simpa only [he', Equiv.symm_apply_apply] using safety_client_trace S Ef cfg E rho J e he (e i) k
  have hseat : safetyHolder S rho (e.symm x) = x :=
    (he (e.symm x)).trans (e.apply_symm_apply x)
  rw [← hseat] at hx hsource hawake ⊢
  exact high_target_row_covered_holder (highRecordEntry R O T E rho) (d7r_entry_source hh cert
    hreflect) (d7r_all hh cert hreflect hqc hhead J emission hown hnames) (d7r_finality_source hh
    cert hreflect hqc hhead) (d7r_prior_origin (D := D) J hown) hsrc hheight J client trace
    emission complete wireLaws hT hs enabled (e.symm x) hx r C hsource hhigh hawake

include hh cert hreflect hqc hhead hsrc hheight J emission hown hnames complete
  wireLaws e he hT hs enabled in
/-- A strict old-row cap excludes the prior-send branch at the first high action. -/
theorem high_target_first_row (x : V) (hx : x ∈ rho.honest) (r : Nat)
    (C : FGBlock (Fin n)) (hsource : actionSourceFG R E rho T x r = some (some C))
    (hhigh : high R O pt.reset C) (hawake : E.awake x (T.action r) = true)
    (hbefore : ∀ j q a h, q < r → HonestRowAt S E rho T j x q a →
      historyRowHeight S D a = some h → h < (O.height C).h) :
    ∃ j a, HonestRowAt S E rho T j x r a ∧ RowComplete S rho D.signer valid x a ∧
      D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false := by
  have he' : safetyHolder S rho = e := funext he
  have client : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    rw [he']
    exact ordinary_FGHolderClientLaws S Ef cfg E rho J e he
  have trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    apply (ordinary_FGHolderClientTrace_iff S Ef cfg E rho _).mpr
    intro i _ k
    simpa only [he', Equiv.symm_apply_apply] using safety_client_trace S Ef cfg E rho J e he (e i) k
  have hseat : safetyHolder S rho (e.symm x) = x :=
    (he (e.symm x)).trans (e.apply_symm_apply x)
  rw [← hseat] at hx hsource hawake hbefore ⊢
  exact high_target_first_row_holder (highRecordEntry R O T E rho) (d7r_entry_source hh cert
    hreflect) (d7r_all hh cert hreflect hqc hhead J emission hown hnames) (d7r_finality_source hh
    cert hreflect hqc hhead) (d7r_prior_origin (D := D) J hown) hsrc hheight J client trace
    emission complete wireLaws hT hs enabled (e.symm x) hx r C hsource hhigh hawake hbefore

include e he in
/-- Unit FG seats transport the honest count without identifying arbitrary populations. -/
theorem high_target_honest_quorum [Fintype V] (unit : FGSafetyUnitLaws Ef)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3) :
    Ef.IsQuorum ((Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest))) := by
  classical
  have he' : ∀ j : Fin n, safetyHolder S rho j = e j := he
  have hmem (i : Fin n) :
      i ∈ (Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest)) ↔
        safetyHolder S rho i ∈ rho.honest := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have himage :
      ((Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest))).image
        (safetyHolder S rho) = rho.honest := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (hmem i).mp hi
    · intro hx
      refine Finset.mem_image.mpr ⟨e.symm x, ?_, ?_⟩
      · apply (hmem _).mpr
        rw [he', Equiv.apply_symm_apply]; exact hx
      · exact (he' _).trans (e.apply_symm_apply x)
  have hinj : Function.Injective (safetyHolder S rho) := by
    intro k l h
    exact e.injective ((he' k).symm.trans (h.trans (he' l)))
  have hcard :
      ((Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest))).card =
        rho.honest.card := by
    exact (Finset.card_image_of_injective _ hinj).symm.trans (congrArg Finset.card himage)
  have hn : Fintype.card V = n := by rw [← Fintype.card_congr e, Fintype.card_fin]
  have hbound := Finset.card_le_univ rho.honest
  rw [hn] at hbound
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    omega
  change Ef.q ≤ Ef.weightOf ((Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest)))
  rw [unit.quorum, unit.weight, hcard, Gen.Pure.qF_def]
  have := unit.n_pos
  omega

include hh cert hreflect hqc hhead hsrc hheight J emission hown hnames complete
  wireLaws e he hT hs enabled in
/-- Construct all honest quorum rows and retain each original strict receipt deadline. -/
theorem high_target_quorum_covered [Fintype V] (unit : FGSafetyUnitLaws Ef)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3)
    (blockWireRows : P.State → List Wire) (deltaF : Time) (hdeltaF : 0 ≤ deltaF)
    (receipt : TRowsReceipt R S E rho T blockWireRows deltaF)
    (awake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true)
    (r : Nat) (C : FGBlock (Fin n)) (hhigh : high R O pt.reset C)
    (hsource : ∀ x ∈ rho.honest, actionSourceFG R E rho T x r = some (some C))
    (hGST : E.t_GST ≤ T.action r) (hhor : T.action r + deltaF ≤ rho.horizon) :
    let honest := Finset.univ.filter (fun k => safetyHolder S rho k ∈ rho.honest)
    Ef.IsQuorum honest ∧ ∃ rows : Fin n → Wire, ∀ i ∈ honest, ∃ j rSent,
      rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent (rows i) ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) (rows i) ∧
      D.signer (rows i) = some i ∧
      D.heightPair (rows i) = .vote (O.height C).h (O.height C).T_h.root false ∧
      ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x (rows i)
        (max (T.action rSent) E.t_GST + deltaF) := by
  have he' : safetyHolder S rho = e := funext he
  have client : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    rw [he']
    exact ordinary_FGHolderClientLaws S Ef cfg E rho J e he
  have trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho) := by
    apply (ordinary_FGHolderClientTrace_iff S Ef cfg E rho _).mpr
    intro i _ k
    simpa only [he', Equiv.symm_apply_apply] using safety_client_trace S Ef cfg E rho J e he (e i) k
  classical
  have hQ := high_target_honest_quorum_holder S rho Ef unit
    (by rw [fg_fault_count_eq_nodes_of_equiv S rho e he]; exact hf)
  have hpos : 0 < Ef.q := by
    rw [unit.quorum, Gen.Pure.qF_def]
    have := unit.n_pos
    omega
  have hn := fgHonestSeats_nonempty_of_quorum S rho Ef hpos hQ
  exact high_target_quorum_covered_holder (highRecordEntry R O T E rho) (d7r_entry_source hh cert
    hreflect) (d7r_all hh cert hreflect hqc hhead J emission hown hnames) (d7r_finality_source hh
    cert hreflect hqc hhead) (d7r_prior_origin (D := D) J hown) hsrc hheight J client trace
    emission complete wireLaws hT hs enabled (FGHonestSeats S rho) (Finset.Subset.refl _) hn hQ
    blockWireRows deltaF hdeltaF receipt awake r C hhigh (fun i hi => hsource _
    (Finset.mem_filter.mp hi).2) hGST hhor

end AvailableChain.FGCompose
end
