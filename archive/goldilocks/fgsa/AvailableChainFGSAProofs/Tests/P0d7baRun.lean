module
public import AvailableChainFGSAProofs.Proofs.Assembly.Healing
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality
public meta import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (cached prefix checks)

set_option linter.privateModule false

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

-- Each test is complete on its own. The layer rules forbid test-to-test imports.
/-! P0d7b-a bounded whole-kernel G0. The fixture and prefix proofs through `nvHealingInput`
are copied verbatim from Tests/NonVacuity/HealingClaims.lean (horizon 310, the smallest
fixture horizon that closes HealingInput; the kernel deadline used below is 97). Only the
namespace, this comment and module privacy change (no public section, so the copy adds
no inventory entries); the kernel section at the end is new. -/
namespace AvailableChain.FGSA.Run.Tests.P0d7baRun

/-- S5 NV6: S5 fixture: one honest node, positive horizon, and unchanged SA clocks.
DC: SAME canonical fixture and cached prefix proof. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 310

theorem params_delta : params.Δ = 1 := rfl
theorem params_n : params.n = 1 := rfl
theorem params_k : params.k = 2 := rfl
theorem params_eta : params.η = 0 := rfl
theorem params_R : params.R = 3 := rfl
theorem params_timeout : params.δt = 6 := rfl
theorem params_window : params.K_W = 2 := rfl
theorem env_delta : env.Δ = params.Δ := rfl
theorem env_gst : env.t_GST = 0 := rfl
theorem env_awake (v : Fin 1) (t : Time) : env.awake v t = true := rfl
theorem deltaF_value : deltaF = 3 := rfl
theorem gap_value : gap = 4 := rfl
theorem horizon_value : horizon = 310 := rfl
theorem horizon_pos : 0 < horizon := by decide
theorem deltaF_lower : env.Δ ≤ deltaF := by decide
theorem gap_lower : 4 * params.Δ ≤ gap := by decide

theorem kappaF_value : kappaF params deltaF = 3 := by decide
theorem betaF_value : betaF params deltaF = 12 := by decide
theorem epsF_value : epsF params deltaF = 4 := by decide
theorem period_value : P params = 12 := by decide
theorem gamma_value : Γ params gap = 4 := by decide
theorem lease_value : L params = 7 := by decide
theorem rhoGamma_value : ρΓ params gap = 26 := by decide
theorem rhoOne_value : ρ₁ params gap = 21 := by decide
theorem short_k : params.k ≤ 2 * params.R + 1 := by decide
theorem Eg_two_value : E_gF params deltaF gap (ρΓ params gap) = 53 := by decide
theorem Eg_one_value : E_gF params deltaF gap (ρ₁ params gap) = 48 := by decide
theorem Ej_two_value : E_jF params deltaF gap (ρΓ params gap) = 49 := by decide
theorem Ej_one_value : E_jF params deltaF gap (ρ₁ params gap) = 44 := by decide
theorem Bc_two_value : B_cF params deltaF gap (ρΓ params gap) = 48 := by decide
theorem Bc_one_value : B_cF params deltaF gap (ρ₁ params gap) = 43 := by decide
theorem Dc_two_value : D_cF params (ρΓ params gap) = 37 := by decide
theorem Dc_one_value : D_cF params (ρ₁ params gap) = 32 := by decide
theorem reset_two_value : B_resetF params deltaF gap (ρΓ params gap) = 325 := by decide
theorem reset_one_value : B_resetF params deltaF gap (ρ₁ params gap) = 295 := by decide
theorem reset_value : B'_resetF params deltaF gap = 295 := by decide
theorem healing_two_value : B_H2F params deltaF gap = 333 := by decide
theorem healing_one_value : B_H1F params deltaF gap = 303 := by decide
theorem healing_value : B_HF params deltaF gap = 303 := by decide

theorem healing_strict_horizon : B_HF params deltaF gap < horizon := by decide
theorem healing_horizon : recoveryStart params env + B_HF params deltaF gap ≤ horizon := by decide
theorem reset_horizon :
    recoveryStart params env + B'_resetF params deltaF gap ≤ horizon := by decide
theorem reset_full_horizon :
    recoveryStart params env + B'_resetF params deltaF gap +
        Γ params gap + 4 * params.Δ ≤ horizon := by
  decide
theorem reset_full_budget : B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ = 303 := by
  decide
theorem action_three_value : params.actionTime 3 = 42 := by decide
theorem renewed_three_budget :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ = 66 := by decide
theorem renewed_three_horizon :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ ≤ horizon := by decide

theorem livenessBound : LivenessBoundW params deltaF := ⟨by decide⟩

section EmissionHelpers
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

theorem nv_rows_clock (st : State p.n) (t : Time)
    (h : EmissionRowsValid st) : EmissionRowsValid (FGSA.clock p st t) := by
  constructor
  · rw [clock_rowPool]; exact h.1
  · rw [clock_proposals]; exact h.2

theorem nv_rows_admit (st : State p.n) (a : RowWire p.n)
    (h : EmissionRowsValid st) (ha : a.valid = true) :
    EmissionRowsValid (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem nv_rows_fold (rows : List (RowWire p.n)) (st : State p.n)
    (h : EmissionRowsValid st) (hr : ∀ a ∈ rows, a.valid = true) :
    EmissionRowsValid (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (nv_rows_admit st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem nv_rows_process (st : State p.n) (o : Obj p)
    (h : EmissionRowsValid st) (hw : (fgsa p c).wellFormed o = true) :
    EmissionRowsValid (FGSA.process p st (toWire p o)) := by
  change FGSA.wellFormed p (toWire p o) = true at hw
  unfold FGSA.process
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row i body =>
      have he := decode_eq_row.mp hd
      rw [he] at hw ⊢
      exact nv_rows_admit _ _ h hw
    | block s N =>
      have hr : ∀ a ∈ N.rows, a.valid = true := by
        unfold FGSA.wellFormed at hw
        rw [hd] at hw
        intro a ha
        exact List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 a ha
      change EmissionRowsValid (admitBlock p st s N)
      unfold admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply nv_rows_fold _ _ _ hr
            have hs : EmissionRowsValid
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } := by
              refine ⟨h.1, ?_⟩
              intro w hw s' M hd'
              rcases List.mem_append.mp hw with hm | hm
              · exact h.2 w hm s' M hd'
              · have hew := List.mem_singleton.mp hm
                subst w
                change some (Input.block s N) = some (Input.block s' M) at hd'
                cases hd'
                exact hr
            split
            · exact hs
            · constructor
              · rw [(reconcile_frame _).2.2.1]; exact hs.1
              · rw [(reconcile_frame _).2.1]; exact hs.2
          · exact h

theorem nv_attest_valid (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (body : RowPayload) (hbody : (attest p st Λ j).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh := congrArg Prod.fst hc
  change (derive p.E p.cfg C).h = h at heh
  have hpos : 1 ≤ h := heh ▸ KitFG.one_le_h p.E p.cfg C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < h))
      |>.map (fun fp => decide (fp.height < h))).getD true) = true
  cases hfp : finality_pair Λ.toRecord (fgInputs p st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

theorem nv_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, N, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s N hd a hm

theorem nv_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

theorem nv_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  simp only [FGSA.wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, NamedProposal.raw, NamedProposal.support, NamedProposal.rows]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := nv_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (nv_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

theorem nv_proposal_shape (st : State p.n) (s : Slot) (app : Nat)
    (N : NamedProposal p.n)
    (ha : (propose p st s).map (withApp p app) = some (.proposal N)) :
    N.erase = proposalBlock p
      (getHead p st (proposerVotes st s) (proposerSupport st s)) s app
      N.raw N.support N.rows ∧
      N.raw = (proposerVotes st s).filterMap liftHead? ∧
      N.support = (proposerSupport st s).filterMap liftHead? ∧
      N.rows = proposalRows p st
        (getHead p st (proposerVotes st s) (proposerSupport st s)) := by
  unfold propose at ha
  split at ha
  · cases ha
  · simp only [Option.map_map] at ha
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp ha
    have hN := Msg.proposal.inj he
    subst N
    have heP := (namedByErase?_sound st _ P hP).2
    refine ⟨?_, rfl, rfl, rfl⟩
    rw [namedProposal_erase, heP]
    rfl

theorem nv_wire_cases (o : Obj p) (hw : (fgsa p c).wellFormed o = true) :
    (∃ s j b, o = ofHead p ⟨.seat (.head s) j, b⟩) ∨
    (∃ j body, o = ofRow p ⟨.seat .fg j, body⟩) ∨
    (∃ s N, o = (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p)) := by
  cases hd : (toWire p o).decode with
  | none => change FGSA.wellFormed p (toWire p o) = true at hw
            simp only [FGSA.wellFormed, hd] at hw
            cases hw
  | some m =>
    have hinj := (toWireEquiv p).injective
    have he (w : Wire p.n) (h : toWire p o = w) : o = ofWire p w := by
      apply hinj
      exact h.trans ((toWireEquiv p).right_inv w).symm
    cases m with
    | vote s j b => exact Or.inl ⟨s, j, b, he _ (decode_eq_vote.mp hd)⟩
    | row j body => exact Or.inr (Or.inl ⟨j, body, he _ (decode_eq_row.mp hd)⟩)
    | block s N => exact Or.inr (Or.inr ⟨s, N, he _ (decode_eq_block.mp hd)⟩)

theorem nv_liftHead (w : GridCO.Wire p.n .root) (a : HeadWire p.n) (ha : liftHead? w = some a) :
    baseVote a = w ∧ ∃ s j b, a = ⟨.seat (.head s) j, b⟩ := by
  obtain ⟨auth, m⟩ := w
  cases auth with
  | seat s j =>
    cases m with
    | head b =>
      change some (⟨.seat (.head s) j, b⟩ : HeadWire p.n) = some a at ha
      cases ha
      exact ⟨rfl, s, j, b, rfl⟩
    | proposal => change none = some a at ha; cases ha
  | proposer => cases m <;> change none = some a at ha <;> cases ha
  | none => cases m <;> change none = some a at ha <;> cases ha

theorem nv_handles_carries (st : State p.n) (o o' : Obj p) (hh : handlesS p st o o') :
    o = o' ∨ carriesS p o o' := by
  rcases hh with he | hh
  · exact Or.inl he
  · right
    cases hd : (toWire p o).decode with
    | none => simp only [hd] at hh
    | some m =>
      cases m with
      | vote | row => simp only [hd] at hh
      | block s N =>
        rw [hd] at hh
        have he := congrArg Signed.payload (decode_eq_block.mp hd)
        change o.payload = .proposal N at he
        rw [carriesS, he]
        exact hh.2.imp_right (fun h => Or.inr h)

theorem nv_carries_payload (o o' : Obj p) (N : NamedProposal p.n)
    (he : o.payload = .proposal N)
    (hc : o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.support.map (ofHead p) ∨
      o' ∈ N.rows.map (ofRow p)) : carriesS p o o' := by
  rw [carriesS, he]
  exact hc
end EmissionHelpers

open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine

abbrev Object := (fgsa params unitCodec).Object
abbrev Event := V2.Event (Fin 1) Object
abbrev FixtureNode := (fgsa params unitCodec).State

def mkRun (es : List Event) : V2.D.Run (Fin 1) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- One tick, then one delivery of each released object, in release order. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- The cached node avoids a repeated fold of all preceding events. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 311).1

theorem runPrefix_zero : runPrefix 0 = ([], (fgsa params unitCodec).init) := rfl

theorem runPrefix_succ (n : Nat) : runPrefix (n + 1) = batch (runPrefix n) n := by
  simp [runPrefix, List.range_succ, List.foldl_append]

theorem duties_length (t : Time) : (duties params t).length ≤ 1 := by
  have hp : SA.proposalTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) := rfl
  have hv : SA.voteTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) + 1 := rfl
  have ha : params.actionTime ((params.slotOf t - 1) / params.R) =
      12 * (((params.slotOf t - 1) / params.R : Nat) : Time) + 6 := by
    change 4 * ((((params.slotOf t - 1) / params.R) * 3 : Nat) : Time) + 6 = _
    push_cast
    ring
  have hpa (a b : Time) : 4 * a ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  have hva (a b : Time) : 4 * a + 1 ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  simp only [duties, hp, hv, ha]
  split_ifs <;> simp_all
  · exact hpa (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)
  · exact hva (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)

theorem ownSeats_single (d : RunDuty) :
    (mkRun []).ownSeats (RunDuty.signLabel d) 0 = [⟨0, by cases d <;> exact Nat.one_pos⟩] := by
  cases d <;> change (List.finRange 1).filter (fun _ => decide ((0 : Fin 1) = 0)) = [0]
  all_goals decide

theorem released_length (nd : FixtureNode) (t : Time) :
    (V2.D.tick env (mkRun []) nd 0 t).2.length ≤ 1 := by
  change (((duties params t).flatMap (fun d =>
    ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun i =>
      ((fgsa params unitCodec).act ((fgsa params unitCodec).clock nd t) d ()).map
        (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Object))))) ++ []).length ≤ 1
  rw [List.append_nil]
  have h := duties_length t
  cases he : duties params t with
  | nil => simp
  | cons d ds =>
    have hds : ds = [] := by simpa [he] using h
    rw [hds]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ownSeats_single,
      List.filterMap_cons, List.filterMap_nil]
    split <;> simp

theorem prefix_events_time (n : Nat) :
    ∀ e ∈ (runPrefix n).1, ∃ m < n, e.time = (m : Time) ∧
      (e = .tick 0 (m : Time) ∨ ∃ o, e = .deliver 0 o (m : Time)) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    intro e he
    simp only [batch, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (he | he) | ⟨o, _, he⟩
    · obtain ⟨m, hm, ht, he⟩ := ih e he
      exact ⟨m, by omega, ht, he⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inl rfl⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inr ⟨o, rfl⟩⟩

theorem prefix_ticks (n m : Nat) (hm : m < n) : .tick 0 (m : Time) ∈ (runPrefix n).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [runPrefix_succ]
    by_cases hmn : m < n
    · exact List.mem_append_left _ (List.mem_append_left _ (ih hmn))
    · have he : m = n := by omega
      subst m
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem prefix_mono {n m : Nat} (h : n ≤ m) :
    (runPrefix n).1.IsPrefix (runPrefix m).1 := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact List.prefix_refl _
  | succ m ih =>
    by_cases hn : n ≤ m
    · apply (ih hn).trans
      rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.append_assoc]
      exact List.prefix_append _ _
    · have : n = m + 1 := by omega
      subst n; exact List.prefix_refl _

theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ t => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd) t
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  cases e with
  | restart w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | tick w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | deliver w o t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl

theorem fold_deliveries (os : List Object) (nd : FixtureNode) (t : Time) :
    (os.map (fun o => (.deliver 0 o t : Event))).foldl
        (V2.D.World.step env (mkRun [])) (fun _ => nd) =
      fun _ => os.foldl (fgsa params unitCodec).process nd := by
  induction os generalizing nd with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_constant]
    exact ih _

/-- The cached node equals the engine fold, for every prefix length. -/
theorem prefix_cached (n : Nat) :
    (runPrefix n).1.foldl (V2.D.World.step env (mkRun [])) V2.D.World.init =
      fun _ => (runPrefix n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runPrefix_succ]
    simp only [batch, List.foldl_append, ih]
    rw [List.foldl_cons, List.foldl_nil, step_constant, fold_deliveries]

def batchEvents (n : Nat) : List Event :=
  [.tick 0 (n : Time)] ++
    (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2.map
      (fun o => .deliver 0 o (n : Time))

theorem prefix_flat (n : Nat) :
    (runPrefix n).1 = (List.range n).flatMap batchEvents := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runPrefix_succ, batch, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, batchEvents]
    rw [← ih, List.append_assoc]

theorem tick_at (n : Nat) (hn : n < 311) :
    run.events[(runPrefix n).1.length]? = some (.tick 0 (n : Time)) := by
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 311 by omega)
  change (runPrefix 311).1[(runPrefix n).1.length]? = _
  rw [← he, runPrefix_succ]
  simp [batch, List.append_assoc]

theorem state_before_tick (n : Nat) (hn : n < 311) :
    V2.D.Run.stateBefore env run (runPrefix n).1.length = fun _ => (runPrefix n).2 := by
  obtain ⟨tail, he⟩ := prefix_mono (show n ≤ 311 by omega)
  unfold V2.D.Run.stateBefore
  change ((runPrefix 311).1.take (runPrefix n).1.length).foldl
      (V2.D.World.step env run) V2.D.World.init = _
  rw [← he]
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact prefix_cached n

theorem emits_at_tick (n : Nat) (hn : n < 311) :
    V2.D.Run.emitsAt env run (runPrefix n).1.length =
      (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  rw [V2.D.Run.emitsAt, tick_at n hn, state_before_tick n hn]
  rfl

theorem immediate_delivery (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    run.events[(runPrefix n).1.length + 1]? = some (.deliver 0 o (n : Time)) := by
  have hos : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = [o] := by
    have hl := released_length (runPrefix n).2 (n : Time)
    cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
    | nil => simp [he] at ho
    | cons a as =>
      have has : as = [] := by simpa [he] using hl
      rw [he, has] at ho
      rw [has]
      exact (List.mem_singleton.mp ho) ▸ rfl
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 311 by omega)
  change (runPrefix 311).1[(runPrefix n).1.length + 1]? = _
  rw [← he, runPrefix_succ]
  simp [batch, hos, List.append_assoc]

theorem prefix_strict (n : Nat) :
    (runPrefix n).1.Pairwise (fun e f => e.key < f.key) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    dsimp only [batch]
    rw [List.append_assoc, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · have hl := released_length (runPrefix n).2 (n : Time)
      cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
      | nil => simp
      | cons o os =>
        have hos : os = [] := by simpa [he] using hl
        rw [hos]
        simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.lt_iff]
    · intro e he f hf
      obtain ⟨m, hm, ht, _⟩ := prefix_events_time n e he
      have hft : f.time = (n : Time) := by
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hf
        rcases hf with rfl | ⟨o, _, rfl⟩ <;> rfl
      apply Prod.Lex.lt_iff.mpr
      left
      change e.time < f.time
      rw [ht, hft]
      exact_mod_cast hm

theorem nvSchedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := le_of_lt horizon_pos
  sorted := (prefix_strict 311).imp (fun h => le_of_lt h)
  nodup := by
    have hne : run.events.Pairwise (fun e f => e ≠ f) :=
      (prefix_strict 311).imp (fun h he => by rw [he] at h; exact lt_irrefl _ h)
    exact hne
  in_horizon := by
    intro e he
    obtain ⟨m, hm, ht, _⟩ := prefix_events_time 311 e he
    rw [ht]
    change 0 ≤ (m : Time) ∧ (m : Time) ≤ 310
    exact ⟨Int.natCast_nonneg m, by dsimp only [Time] at *; omega⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    obtain ⟨m, _, ht, _⟩ := prefix_events_time 311 (.tick v t) he
    exact ⟨m, by simpa only [V2.Event.time, env, Int.mul_one] using ht⟩
  tick_total := by
    intro v _ t _ ht hh _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 310 at hh
    have he : t = (t.toNat : Time) := (Int.toNat_of_nonneg ht).symm
    rw [he]
    exact prefix_ticks 311 t.toNat (by dsimp only [Time] at *; omega)

theorem noRestart : V2.D.NoRestart run := by
  intro i v t hi
  obtain ⟨_, _, _, he⟩ := prefix_events_time 311 (.restart v t) (List.mem_of_getElem? hi)
  rcases he with he | ⟨o, he⟩ <;> cases he

set_option maxHeartbeats 2000000 in
-- Index uniqueness uses the symbolic prefix proof through the concrete run type.
theorem delivery_source {i : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) :
    ∃ n : Nat, n < 311 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length + 1 ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  have hm := List.mem_of_getElem? hi
  rw [show run.events = (runPrefix 311).1 from rfl, prefix_flat] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 311 := List.mem_range.mp hn
  simp only [batchEvents, List.mem_append, List.mem_singleton, List.mem_map] at hm
  rcases hm with he | ⟨a, ha, he⟩
  · cases he
  · cases he
    have hd := immediate_delivery n hn' o ha
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
    have hij : i = (runPrefix n).1.length + 1 :=
      (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
    exact ⟨n, hn', rfl, hij, ha⟩

theorem tick_source {i : Nat} {v : Fin 1} {t : Time}
    (hi : run.events[i]? = some (.tick v t)) :
    ∃ n : Nat, n < 311 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length := by
  obtain ⟨n, hn, ht, _⟩ := prefix_events_time 311 (.tick v t) (List.mem_of_getElem? hi)
  change t = (n : Time) at ht
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hd := tick_at n hn
  rw [← ht] at hd
  obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
  exact ⟨n, hn, ht,
    (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)⟩

theorem emitted_wire (n : Nat) (hn : n < 311)
    (hr : EmissionRowsValid (runPrefix n).2.st) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    (fgsa params unitCodec).wellFormed o = true := by
  have hi := tick_at n hn
  have hc := state_before_tick n hn
  obtain ⟨auth, m⟩ := o
  cases auth with
  | none =>
    change (⟨.none, m⟩ : Object) ∈
      (duties params (n : Time)).flatMap (fun d =>
        ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun j =>
          ((fgsa params unitCodec).act ((fgsa params unitCodec).clock (runPrefix n).2
            (n : Time)) d ()).map (fun m => ⟨.seat (RunDuty.signLabel d) j, m⟩))) ++ [] at ho
    rw [List.append_nil] at ho
    obtain ⟨d, _, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨j, _, ho⟩ := List.mem_filterMap.mp ho
    obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp ho
    cases he
  | seat l j =>
    obtain ⟨_, _, d, hl, ht, ha⟩ :=
      (mem_tick_seat_iff env (mkRun []) (runPrefix n).2 0 (n : Time) l j m).mp ho
    change RunDuty.signLabel d = l at hl
    cases d with
    | headAction s =>
      change RunLabel.base (.head s) = l at hl
      subst l
      have he : .head (headVote params
          (FGSA.clock params (runPrefix n).2.st (n : Time)) s).root = m :=
        by
          change (if joinedNow params (clock params (runPrefix n).2.st (n : Time)) then
            some (.head (headVote params
              (clock params (runPrefix n).2.st (n : Time)) s).root) else none) = some m at ha
          split at ha
          · exact Option.some.inj ha
          · cases ha
      subst m
      rfl
    | fgAction r =>
      change RunLabel.base .fg = l at hl
      subst l
      change (attest params (FGSA.clock params (runPrefix n).2.st (n : Time))
        (runPrefix n).2.record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact nv_attest_valid _ _ _ _ hb
    | propAction s =>
      change RunLabel.prop s = l at hl
      subst l
      change SA.proposalTime params.toParams s = (n : Time) at ht
      change (if joinedNow params (clock params (runPrefix n).2.st (n : Time)) then
        (propose params (clock params (runPrefix n).2.st (n : Time)) s).map
          (withApp params 0) else none) = some m at ha
      have ha : (propose params (clock params (runPrefix n).2.st (n : Time)) s).map
          (withApp params 0) = some m := by
        split at ha
        · exact ha
        · cases ha
      have hs0 : 0 < s := by
        by_contra hh
        have hs : s = 0 := Nat.eq_zero_of_not_pos hh
        subst s
        change none = some m at ha
        cases ha
      have hp := fgsa_propose_parent_lt env run nvSchedule (ht.symm ▸ hi) hs0
      rw [hc] at hp
      rw [ht] at hp
      exact nv_proposal_wf _ s 0 (nv_rows_clock _ _ hr) hp ha

theorem prefix_rows (n : Nat) (hn : n ≤ 311) : EmissionRowsValid (runPrefix n).2.st := by
  induction n with
  | zero => exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim⟩
  | succ n ih =>
    have hn' : n < 311 := by omega
    have hr := ih (by omega)
    have hw := emitted_wire n hn' hr
    rw [runPrefix_succ]
    dsimp only [batch]
    have hclock : EmissionRowsValid
        (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1.st := by
      exact (tick_st (c := unitCodec) env (mkRun []) (runPrefix n).2 0 (n : Time)).symm ▸
        nv_rows_clock _ _ hr
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1 = nd at *
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = os at *
    induction os generalizing nd with
    | nil => exact hclock
    | cons a os ih =>
      rw [List.foldl_cons]
      exact ih _ (nv_rows_process nd.st a hclock (hw a (List.mem_cons_self ..)))
        (fun o ho => hw o (List.mem_cons_of_mem a ho))

theorem wire : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).wellFormed o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  exact emitted_wire n hn (prefix_rows n (by omega)) o ho

/-- A delivered proposal is the exact release at its cached tick. -/
theorem nv_delivery_origin {x : Fin 1} {o : Object} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    ∃ n : Nat, n < 311 ∧ ∃ s : Slot,
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 ∧
      o = ofWire params ⟨.proposer s, .proposal N⟩ ∧
      N.slot = s ∧ SA.proposalTime params.toParams s = (n : Time) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  rcases nv_wire_cases o (wire i x o t hi) with ⟨s, j, B, he⟩ | ⟨j, body, he⟩ |
    ⟨s, B, he⟩
  · rw [he] at hp; cases hp
  · rw [he] at hp; cases hp
  · rw [he] at hp
    cases Msg.proposal.inj hp
    subst o
    have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    refine ⟨n, hn, s, ho, rfl, ?_, ha.2.1⟩
    rw [← named_erase_slot, hb]
    rfl

/-- W2's emission equation supplies the small delivered root. -/
theorem nv_delivery_root {x : Fin 1} {o : Object} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    N.root = ⟨N.slot + 1⟩ := by
  obtain ⟨n, hn, s, ho, rfl, _, _⟩ := nv_delivery_origin hd hp
  exact emitted_proposal_slot_root env run (fun _ => rfl)
    (runPrefix n).1.length 0 (n : Time) s N (tick_at n hn)
    ((emits_at_tick n hn).symm ▸ ho)

/-- Equal slots give equal cached ticks, objects, and recursive named proposals. -/
theorem nv_delivery_unique {x y : Fin 1} {o o' : Object} {t u : Time}
    {N M : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N)
    (hd' : V2.Event.deliver y o' u ∈ run.events) (hp' : o'.payload = .proposal M)
    (hs : N.slot = M.slot) : N = M := by
  obtain ⟨n, hn, s, ho, _, hb, ht⟩ := nv_delivery_origin hd hp
  obtain ⟨m, _, s', ho', _, hB, ht'⟩ := nv_delivery_origin hd' hp'
  have hss : s = s' := hb.symm.trans (hs.trans hB)
  have hnm : n = m := by
    have hh := ht.symm.trans (hss ▸ ht')
    exact_mod_cast hh
  subst m
  have hl := released_length (runPrefix n).2 (n : Time)
  have he : o = o' := by
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = os at *
    cases os with
    | nil => cases ho
    | cons a as =>
      have hnil : as = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hl
        omega
      subst as
      exact (List.mem_singleton.mp ho).trans (List.mem_singleton.mp ho').symm
  rw [he, hp'] at hp
  exact (Msg.proposal.inj hp).symm

/-- Each exact delivered parent was held before its actual emission. -/
theorem nvParents : ∀ x o t N,
    V2.Event.deliver x o t ∈ run.events → o.payload = .proposal N →
    ∃ i y, N.parent ∈ (V2.D.Run.stateBefore env run i y).st.namedBodies := by
  intro x o t N hd hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  obtain ⟨j, hj⟩ := emitted_payload_parent_stored env run
    ⟨(runPrefix n).1.length, tick_at n hn, (emits_at_tick n hn).symm ▸ ho⟩ hp
  exact ⟨j, 0, hj⟩

/-- Named origin and exact payload uniqueness prove the premise before Base₂. -/
theorem nvRoots : NamedRootCollisionFree params unitCodec env run where
  root_injective := by
    intro B C hB hC A D hA hD he
    have hAs : NamedProposalInRun params unitCodec env run A := by
      rcases hA with hA | hA
      · exact namedScope_ancestor env run hB hA
      · exact namedScope_ancestor env run hC hA
    have hDs : NamedProposalInRun params unitCodec env run D := by
      rcases hD with hD | hD
      · exact namedScope_ancestor env run hB hD
      · exact namedScope_ancestor env run hC hD
    rcases namedProposalInRun_genesis_or_delivered env run nvParents hAs with rfl | hA
    · rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · rfl
      · obtain ⟨x, o, t, hd, hp⟩ := hD
        have hr := nv_delivery_root hd hp
        have hh := congrArg BlockId.value (he.trans hr)
        change 0 = D.slot + 1 at hh
        exact (Nat.succ_ne_zero _ hh.symm).elim
    · obtain ⟨x, o, t, hd, hp⟩ := hA
      have hr := nv_delivery_root hd hp
      rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · have hh := congrArg BlockId.value (hr.symm.trans he)
        change A.slot + 1 = 0 at hh
        exact (Nat.succ_ne_zero _ hh).elim
      · obtain ⟨y, o', u, hd', hp'⟩ := hD
        have hr' := nv_delivery_root hd' hp'
        apply nv_delivery_unique hd hp hd' hp'
        have hh := congrArg BlockId.value (hr.symm.trans (he.trans hr'))
        change A.slot + 1 = D.slot + 1 at hh
        exact Nat.add_right_cancel hh

theorem state_delivery_store (n : Nat) (hn : n < 311) :
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st =
      FGSA.clock params (runPrefix n).2.st (n : Time) := by
  have hs := (V2.D.Run.step_tick_eq env run (tick_at n hn)).1
  rw [state_before_tick n hn] at hs
  exact (congrArg Node.st hs).trans
    (tick_st (c := unitCodec) env run (runPrefix n).2 0 (n : Time))

theorem emitted_deps (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    depsS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = true := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ | ⟨s, N, rfl⟩
  · rfl
  · rfl
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    have hm := ha.2.2.2.2
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    unfold propose at hm
    split at hm
    · cases hm
    · simp only [Option.map_map] at hm
      obtain ⟨P, hP, heN⟩ := Option.map_eq_some_iff.mp hm
      have hN := Msg.proposal.inj heN
      subst N
      have hs := namedByErase?_sound st _ P hP
      have hc := (storeBundle_postClock env run (runPrefix n).1.length 0 (n : Time)).cstore
      rw [state_before_tick n hn] at hc
      let H := getHead params st (proposerVotes st s) (proposerSupport st s)
      obtain ⟨B, hB, he⟩ := (hc.baseTree H).mp (getHead_stored params st hc _ _)
      have hl := (fgBlockOf_spec params st hc H B).mpr ⟨hB, he⟩
      change (decide (P ∈ st.namedBodies) && (fgBlockOf st P.erase).isSome) = true
      rw [hs.2, hl]
      simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
      exact hs.1

theorem deps : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore env run i v) o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change depsS params _ o = true
  rw [state_delivery_store n hn]
  exact emitted_deps n hn o ho

theorem earlier_batch {i n : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) (hin : i < (runPrefix n).1.length) :
    ∃ m : Nat, m < n ∧ m < 311 ∧ t = (m : Time) ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 := by
  obtain ⟨m, hm, ht, he, ho⟩ := delivery_source hi
  refine ⟨m, ?_, hm, ht, ho⟩
  by_contra hh
  have hl := (prefix_mono (Nat.le_of_not_gt hh)).length_le
  omega

theorem carried_from_state (n : Nat) (hn : n < 311) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') :
    (∃ s j b, o' = ofHead params ⟨.seat (.head s) j, b⟩ ∧
      (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes) ∨
    (∃ a : RowWire params.n, o' = ofRow params a ∧
      (a ∈ (runPrefix n).2.st.rowPool ∨
        ∃ w ∈ (runPrefix n).2.st.proposals, ∃ s N,
          w.decode = some (.block s N) ∧ a ∈ N.rows)) := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, N, rfl⟩
  · exact hc.elim
  · exact hc.elim
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨_, hraw, hsup, hrows⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    have heads (xs : List (HeadWire params.n))
        (hxs : ∀ a ∈ xs, a ∈ (proposerVotes st s).filterMap liftHead?)
        (hc' : o' ∈ xs.map (ofHead params)) :
        ∃ r j B, o' = ofHead params ⟨.seat (.head r) j, B⟩ ∧
          (⟨.seat r j, .head B⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes := by
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp (hxs a hm)
      obtain ⟨he, r, j, B, rfl⟩ := nv_liftHead w a hl
      have hpool : w ∈ st.base.votes := (List.mem_filter.mp hw).1
      rw [← he] at hpool
      change (⟨.seat r j, .head B⟩ : GridCO.Wire params.n .root) ∈
        (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes at hpool
      rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hpool
      exact ⟨r, j, B, rfl, hpool⟩
    rcases hc with hc | hc | hc
    · left
      rw [hraw] at hc
      exact heads _ (fun _ h => h) hc
    · left
      rw [hsup] at hc
      exact heads _ (nv_proposal_votes st s).2 hc
    · right
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc
      rw [hrows, proposalRows_eq_proposalRowsFor] at hm
      have horigin := proposalRowsFor_origin params st (st.slot params) _ a hm
      rcases horigin with hm | ⟨w, hw, r, M, hd, hm⟩
      · rw [clock_rowPool] at hm
        exact ⟨a, rfl, Or.inl hm⟩
      · rw [clock_proposals] at hw
        exact ⟨a, rfl, Or.inr ⟨w, hw, r, M, hd, hm⟩⟩

def EarlierEmitted (n : Nat) (o : Object) : Prop :=
  ∃ m : Nat, m < n ∧ m < 311 ∧
    o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2

theorem handled_before (n : Nat)
    (past : ∀ m : Nat, m < n → m < 311 → ∀ o o' : Object,
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 →
      carriesS params o o' → EarlierEmitted m o')
    (j : Nat) (hj : j < (runPrefix n).1.length) (o : Object) (t : Time)
    (hh : V2.D.Run.handlesAt env run j 0 o t) : EarlierEmitted n o := by
  obtain ⟨parent, he, hh⟩ := hh
  obtain ⟨m, hmn, hm, _, ho⟩ := earlier_batch he hj
  rcases nv_handles_carries _ parent o hh with rfl | hc
  · exact ⟨m, hmn, hm, ho⟩
  · obtain ⟨k, hkm, hk, ho'⟩ := past m hmn hm parent o ho hc
    exact ⟨k, hkm.trans hmn, hk, ho'⟩

theorem carried_authentic (n : Nat) (hn : n < 311) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') : EarlierEmitted n o' := by
  induction n using Nat.strong_induction_on generalizing o o' with
  | h n ih =>
    have past := fun m hm => ih m hm
    have hbefore := handled_before n past
    rcases carried_from_state n hn o o' ho hc with ⟨s, j, b, rfl, hm⟩ |
      ⟨a, rfl, hm | ⟨w, hw, s, N, hd, hm⟩⟩
    · have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
          (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
        rw [state_before_tick n hn]
        exact hm
      rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
      obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
      dsimp only at he
      subst v
      obtain ⟨i, hi, t, ha, _⟩ := fgsa_vote_stamp_source env run noRestart (runPrefix n).1.length
        0 s j b stamp hstamp
      exact hbefore i hi _ t ha.1
    · have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
        rw [state_before_tick n hn]
        exact hm
      obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
      exact hbefore i hi _ t hh
    · have hp : w ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.proposals := by
        rw [state_before_tick n hn]
        exact hw
      obtain ⟨i, parent, t, hi, he, hwire, _, _⟩ :=
        stored_proposal_delivered env run (runPrefix n).1.length 0 w hp
      have hpay := congrArg Signed.payload (hwire.trans (decode_eq_block.mp hd))
      change parent.payload = .proposal N at hpay
      have hcarry : carriesS params parent (ofRow params a) := by
        exact nv_carries_payload parent _ N hpay
          (Or.inr (Or.inr (List.mem_map.mpr ⟨a, hm, rfl⟩)))
      obtain ⟨m, hmn, hmb, _, hem⟩ := earlier_batch he hi
      obtain ⟨k, hkm, hkb, hek⟩ := past m hmn hmb parent (ofRow params a) hem hcarry
      exact ⟨k, hkm.trans hmn, hkb, hek⟩

theorem head_pool_authentic (n : Nat) (hn : n < 311) (s : Slot) (j : Fin params.n) (b : BlockId)
    (hm : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes) :
    EarlierEmitted n (ofHead params ⟨.seat (.head s) j, b⟩) := by
  have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
      (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
    rw [state_before_tick n hn]
    exact hm
  rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
  obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
  dsimp only at he
  subst v
  obtain ⟨i, hi, t, ha, _⟩ :=
    fgsa_vote_stamp_source env run noRestart (runPrefix n).1.length 0 s j b stamp hstamp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t ha.1

theorem row_pool_authentic (n : Nat) (hn : n < 311) (a : RowWire params.n)
    (hm : a ∈ (runPrefix n).2.st.rowPool) : EarlierEmitted n (ofRow params a) := by
  have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
    rw [state_before_tick n hn]
    exact hm
  obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t hh

theorem prefix_length_strict {m n : Nat} (h : m < n) :
    (runPrefix m).1.length < (runPrefix n).1.length := by
  have hs : (runPrefix m).1.length < (runPrefix (m + 1)).1.length := by
    rw [runPrefix_succ]
    simp only [batch, List.length_append, List.length_singleton, List.length_map]
    omega
  exact hs.trans_le (prefix_mono (show m + 1 ≤ n by omega)).length_le

theorem emitted_fresh (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    processedS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = false := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, N, rfl⟩
  · change decide ((⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes) = false
    apply decide_eq_false
    intro hm
    rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := head_pool_authentic n hn s j b hm
    have ht := ((fgsa_emits_head env (mkRun []) (runPrefix n).2 0 (n : Time) s j b).mp ho).2.1
    have hm' := ((fgsa_emits_head env (mkRun []) (runPrefix m).2 0 (m : Time) s j b).mp hem).2.1
    have he : (m : Time) = (n : Time) := hm'.symm.trans ht
    have hne : m = n := by exact_mod_cast he
    omega
  · change decide ((⟨.seat .fg j, body⟩ : RowWire params.n) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).rowPool) = false
    apply decide_eq_false
    intro hm
    rw [clock_rowPool] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := row_pool_authentic n hn ⟨.seat .fg j, body⟩ hm
    obtain ⟨_, _, r, _, ha⟩ := (fgsa_emits_row env (mkRun []) (runPrefix n).2
      0 (n : Time) j body).mp ho
    have hsent := fgsa_row_sent_before env run 0 j body (prefix_length_strict hmn)
      (m : Time) (tick_at m hmb) ((emits_at_tick m hmb).symm ▸ hem)
    rw [state_before_tick n hn] at hsent
    exact attest_some_fresh _ _ _ _ ha hsent
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    have hs0 : 0 < s := by
      by_contra hh
      have he : s = 0 := Nat.eq_zero_of_not_pos hh
      subst s
      have hnone := ha.2.2.2.2
      change (none : Option (Msg params.n)) = some (Msg.proposal N) at hnone
      cases hnone
    have ht := ha.2.1
    have hg := (fgsa_stored_block_slots env run nvSchedule (ht.symm ▸ tick_at n hn) hs0).2.2.2
    rw [state_before_tick n hn, ht] at hg
    change decide (∃ B ∈ (FGSA.clock params (runPrefix n).2.st (n : Time)).fg.TF,
      B.root = N.root) = false
    apply decide_eq_false
    rintro ⟨B, hB, hroot⟩
    have hc := cstoreInv_stateBefore env run (runPrefix n).1.length 0
    have hm : B ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.fg.TF := by
      rw [state_before_tick n hn]
      simpa only [clock_fg] using hB
    have hBs := rootBlockInRun_held env run (Finset.mem_univ 0)
      (runPrefix n).1.length ((hc.baseTree _).mpr ⟨B, hm, rfl⟩)
    have hbs := rootBlockInRun_delivered env run
      (List.mem_of_getElem? (immediate_delivery n hn _ ho)) rfl
    have he : eraseFG B = N.erase := rootBlockInRun_eq env run nvRoots hBs hbs
      ((eraseFG_root B).trans (hroot.trans (named_erase_root N).symm))
    have hslot : B.slot = s := (eraseFG_slot B).symm.trans
      ((congrArg Block.slot he).trans (by rw [hb]; rfl))
    have hh := hg B hB
    rw [hslot] at hh
    exact lt_irrefl s hh

theorem fgp_fresh : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore env run i v) o = false := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change processedS params _ o = false
  rw [state_delivery_store n hn]
  exact emitted_fresh n hn o ho

theorem nvExecution : V2.D.ExecutionValid env run where
  tick_awake := by intros; rfl
  deliver_awake := by intros; rfl
  restart_awake := by intros; rfl
  wake_restart := by intro v hv t ht hh hw; cases hw.2
  toScheduleWellFormed := nvSchedule
  wire := wire
  deps := deps
  fresh := fgp_fresh
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(n : Time), le_rfl, (runPrefix n).1.length, tick_at n hn,
      (emits_at_tick n hn).symm ▸ ho⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    obtain ⟨m, hmn, hm, hem⟩ := carried_authentic n hn o o' ho hc
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(m : Time), by exact_mod_cast hmn.le, (runPrefix m).1.length, tick_at m hm,
      (emits_at_tick m hm).symm ▸ hem⟩

/-- Every honest emission is delivered immediately in this concrete run. -/
theorem nvReceiptRoots : NamedReceiptRootCollisionFree params unitCodec env run := by
  have scope (A : NamedProposal params.n)
      (h : NamedProposalReceiptScope params unitCodec env run A) :
      NamedProposalInRun params unitCodec env run A := by
    rcases h with h | ⟨v, hv, o, t, N, ⟨i, hi, ho⟩, hp, hAN⟩
    · exact h
    · obtain ⟨n, hn, rfl, rfl⟩ := tick_source hi
      rw [emits_at_tick n hn] at ho
      exact ⟨N, Or.inl ⟨0, o, (n : Time),
        List.mem_of_getElem? (immediate_delivery n hn o ho), hp⟩, hAN⟩
  intro A B hA hB he
  exact nvRoots.root_injective A B (scope A hA) (scope B hB)
    A B (Or.inl ((named_preceq_refl _))) (Or.inr ((named_preceq_refl _))) he

theorem base : Base₂ params unitCodec env run where
  valid := nvExecution
  receiptIdealization := nvReceiptRoots
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    rcases l with (_ | _) | _
    · exact hl.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hl.elim
  cstar := by
    intro l hl
    rcases l with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hl.elim
    · exact hl.elim
  restartsAtWakes := by
    intro v t h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact (noRestart i v t hi).elim
  delta := env_delta

theorem honest_slot {s : Slot} (hs : 0 < s) :
    Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  rw [Gen.V2.Duty.HonestSlot_def]
  exact ⟨hs, Finset.mem_univ _⟩

theorem proposer_gap (t : Time) (ht : env.t_GST ≤ t) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + gap ∧
      Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  change 0 ≤ t at ht
  dsimp only [Time] at *
  have he : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  refine ⟨t.toNat / 4 + 1, ?_, ?_, honest_slot (by dsimp only [Slot]; omega)⟩
  · change t < 4 * ((t.toNat / 4 + 1 : Nat) : Time)
    dsimp only [Time] at *
    omega
  · change 4 * ((t.toNat / 4 + 1 : Nat) : Time) ≤ t + 4
    dsimp only [Time] at *
    omega

theorem fault_value : (Gen.V2.Duty.faulty run).card = 0 := by
  rw [Gen.V2.Duty.faulty_def]
  change (Finset.univ \ Finset.univ : Finset (Fin 1)).card = 0
  simp

/-- An honest emission has reached its own admission clock. -/
theorem emitted_admission (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    fgsaAdmissionTime params o ≤ (n : Time) := by
  rcases nv_wire_cases o (emitted_wire n hn (prefix_rows n (by omega)) o ho) with
    ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ | ⟨s, N, rfl⟩
  · have ht := ((fgsa_emits_head env (mkRun []) (runPrefix n).2 0
      (n : Time) s j b).mp ho).2.1
    change 4 * (s : Time) + 1 = (n : Time) at ht
    change 4 * (s : Time) ≤ (n : Time)
    dsimp [Time] at *
    omega
  · change (0 : Time) ≤ (n : Time)
    positivity
  · have ht := ((fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0
      (n : Time) s (.proposal N)).mp ho).2.1
    exact ht.le

/-- Immediate self-delivery processes or permanently excludes the emitted object. -/
theorem emitted_settled (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    (fgsa params unitCodec).processed
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 2) 0) o = true ∨
    (fgsa params unitCodec).excludes
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 2) 0) o = true := by
  have hd := immediate_delivery n hn o ho
  have ht : fgsaTimely params
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0) o := by
    change fgsaAdmissionTime params o ≤
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st.base.now
    rw [state_delivery_store n hn]
    rw [(clock_vn (runPrefix n).2.st (n : Time)).2]
    exact emitted_admission n hn o ho
  have hp := (fgsaAcceptance params unitCodec).accepts
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0) o o
    (cstoreInv_stateBefore env run _ 0) (Or.inl rfl)
    (wire _ 0 o (n : Time) hd) (deps _ 0 o (n : Time) hd) ht
  rw [V2.D.Run.stateBefore_succ env run hd]
  exact hp

theorem sync : Gen.V2.Duty.PartialSynchronyBy env run (fgsaDelay env.Δ deltaF) where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, ho⟩ w _ a hta _ had _ _ _ hExcl
    obtain ⟨n, hn, rfl, rfl⟩ := tick_source hi
    rw [emits_at_tick n hn] at ho
    have hw : w = 0 := Subsingleton.elim _ _
    subst w
    by_cases he : (n : Time) = a
    · right
      exact ⟨(n : Time), he.symm.le, he ▸ had, (runPrefix n).1.length + 1,
        o, immediate_delivery n hn o ho, Or.inl rfl⟩
    · left
      obtain hp | hx := emitted_settled n hn o ho
      · refine ⟨(runPrefix n).1.length + 2, ?_, hp⟩
        have hk := (index_lt_actionCut_iff nvSchedule
        (immediate_delivery n hn o ho) a).mpr (Or.inl (lt_of_le_of_ne hta he))
        omega
      · have hidx := (Gen.V2.Duty.index_lt_idxBefore_iff nvSchedule
          (immediate_delivery n hn o ho) _).mpr (hta.trans_lt had)
        change (runPrefix n).1.length + 1 <
          V2.D.Run.idxBefore run (max a env.t_GST + fgsaDelay env.Δ deltaF o) at hidx
        have hx' := (fgsaHooks params unitCodec).excludes_stable env run nvSchedule 0 o
          ((runPrefix n).1.length + 2)
          (V2.D.Run.idxBefore run (max a env.t_GST + fgsaDelay env.Δ deltaF o))
          (by omega)
          (noRestart.restartFree 0 _ _) hx
        rw [Gen.V2.Duty.stateBefore_idxBefore env run _ nvSchedule] at hx'
        exact Bool.noConfusion (hx'.symm.trans hExcl)
  relay_accepted := by
    intro v _ i o t ha w _ a hta _ had _ _ _ _
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    by_cases he : t = a
    · right
      exact ⟨t, he.symm.le, he ▸ had, i, ha.1⟩
    · left
      refine ⟨i + 1, ?_, ha.2.2⟩
      obtain ⟨o', hi, _⟩ := ha.1
      have hk := (index_lt_actionCut_iff nvSchedule hi a).mpr
        (Or.inl (lt_of_le_of_ne hta he))
      omega

theorem nvRecovery : RecoverySleep₂ params unitCodec env run gap deltaF where
  sync := sync
  deltaF := deltaF_lower
  gap := by intro t ht _; exact proposer_gap t ht
  base := base
  fault := by rw [fault_value]; decide
  awake := by intros; rfl
  gapPos := gap_lower
  suffixNoRestart := by intro x hx i t hi; exact (noRestart i x t hi).elim
  joinedGap := by
    intro t ht hh
    obtain ⟨s, hts, hst, hs⟩ := proposer_gap t (by
      change (0 : Time) ≤ t
      change (6 : Time) ≤ t at ht
      dsimp only [Time] at *
      omega)
    refine ⟨s, hts, hst, hs, ?_⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro u _ _ hw; cases hw.2
    · intro u _ _ hu
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
      exact (noRestart i _ u hi).elim

theorem healingSet : HealingSet params unitCodec env run gap deltaF := nvRecovery

theorem healingPrem {Pt : Type} (pt : Pt) :
    HealingPrem params unitCodec gap deltaF env run pt := ⟨healingSet, livenessBound⟩

theorem healingTimePrem : HealingTimePrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), healing_horizon⟩

theorem resetArrivalPrem : ResetArrivalPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_horizon⟩

theorem resetArrivalFullPrem : ResetArrivalFullPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_full_horizon⟩

theorem renewedPromotionPrem : RenewedPromotionPrem params unitCodec gap deltaF env run ⟨3⟩ :=
  ⟨healingPrem (⟨3⟩ : PtR), renewed_three_horizon⟩

-- NV4 uses the same fixture and the prefix invariants above.
def actionNode (r : Nat) : FixtureNode :=
  (fgsa params unitCodec).clock (runPrefix (params.actionTime r).toNat).2
    (params.actionTime r)

def rowAtAction (r : Nat) : Option RowPayload :=
  (attest params (actionNode r).st (actionNode r).record ⟨0, params.nPos⟩).1

def sourceAtAction (r : Nat) : Option (FGBlock (Fin params.n)) :=
  (fgInputs params (actionNode r).st).1

def rowEntry (r : Nat) : Option (Nat × BlockId) :=
  (rowAtAction r).bind (fun a => namedEntry a.height_pair)

-- These evaluations use at most 43 ticks, through cached nodes.

/-- S5 NV6: The time filter of any longer prefix gives the same shorter prefix.
DC: SAME canonical fixture and cached prefix proof. -/
theorem prefix_cut (n m : Nat) (hn : n ≤ m) :
    (runPrefix m).1.filter (fun e => decide (e.time < (n : Time))) = (runPrefix n).1 := by
  induction m generalizing n with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.filter_append, List.filter_append, ih n hnm]
      have ht : decide ((m : Time) < (n : Time)) = false := by
        apply decide_eq_false
        exact not_lt.mpr (by exact_mod_cast hnm)
      have hd : ((V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2.map
          (fun o => (.deliver 0 o (m : Time) : Event))).filter
            (fun e => decide (e.time < (n : Time))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
        change ¬ decide ((m : Time) < (n : Time)) = true
        rw [ht]
        decide
      rw [hd]
      simp only [List.filter_cons, List.filter_nil]
      change ((runPrefix n).1 ++
        (if decide ((m : Time) < (n : Time)) = true then [.tick 0 (m : Time)] else [])) ++ [] = _
      rw [ht]
      simp
    · have he : n = m + 1 := by omega
      subst n
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨k, hk, ht, _⟩ := prefix_events_time (m + 1) e he
      rw [ht]
      exact decide_eq_true (by exact_mod_cast hk)

/-- S5 NV6: The inclusive read at tick n is the cached node after tick n.
DC: SAME canonical fixture and cached prefix proof. -/
theorem read_prefix (n : Nat) (hn : n < 311) :
    V2.D.Run.readAt env run (n : Time) = fun _ => (runPrefix (n + 1)).2 := by
  have hp : run.events.filter (fun e => decide (e.time ≤ (n : Time))) =
      (runPrefix (n + 1)).1 := by
    have he : (fun e : Event => decide (e.time ≤ (n : Time))) =
        (fun e : Event => decide (e.time < ((n + 1 : Nat) : Time))) := by
      funext e
      have hp : e.time ≤ (n : Time) ↔ e.time < ((n + 1 : Nat) : Time) := by
        dsimp only [Time]
        push_cast
        omega
      exact decide_eq_decide.mpr hp
    rw [he]
    exact prefix_cut (n + 1) 311 (by omega)
  unfold V2.D.Run.readAt
  rw [hp]
  exact prefix_cached (n + 1)

theorem frontier_cached (n : Nat) (hn : n < 311) :
    honestFrontier params unitCodec env run (n : Time) = (runPrefix (n + 1)).2.st.fg.h_max := by
  unfold honestFrontier
  rw [read_prefix n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix (n + 1)).2.st.fg.h_max) = _
  simp

theorem frontier_idx_cached (n : Nat) (hn : n < 311) :
    frontierAtIdx params unitCodec env run (runPrefix n).1.length =
      (runPrefix n).2.st.fg.h_max := by
  unfold frontierAtIdx storeAt
  rw [state_before_tick n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix n).2.st.fg.h_max) = _
  simp

set_option maxHeartbeats 2000000 in
-- The kernel checks the cached state after the first 31 ticks.
theorem nvCachedFrontier : (runPrefix 31).2.st.fg.h_max = 2 := by decide +kernel

theorem nvFrontier : honestFrontier params unitCodec env run 30 = 2 :=
  (frontier_cached 30 (by decide)).trans nvCachedFrontier

theorem nvFrontierAtIdx : frontierAtIdx params unitCodec env run (runPrefix 31).1.length = 2 :=
  (frontier_idx_cached 31 (by decide)).trans nvCachedFrontier

theorem action_read (r : Nat) (hr : (params.actionTime r).toNat < 311) :
    postClock env run 0 (params.actionTime r) = some (actionNode r) := by
  have ht : ((params.actionTime r).toNat : Time) = params.actionTime r := by
    apply Int.toNat_of_nonneg
    change 0 ≤ 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1
    omega
  have he := tick_at (params.actionTime r).toNat hr
  rw [ht] at he
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event params unitCodec env run nvSchedule he,
    Option.map_some, state_before_tick (params.actionTime r).toNat hr]
  rfl

theorem source_read (r : Nat) (hr : (params.actionTime r).toNat < 311) :
    actionSourceFG params unitCodec env run 0 r = some (sourceAtAction r) := by
  rw [actionSourceFG_def, action_read r hr]
  rfl

-- The reset source and wire come from the round-3 action itself.
def resetSource : FGBlock (Fin params.n) := (sourceAtAction 3).getD .genesis
def resetRow : RowWire params.n :=
  ⟨.seat .fg ⟨0, params.nPos⟩, (rowAtAction 3).getD (.vote ⟨.empty, none⟩)⟩

def w : HealingWitness :=
  ⟨0, 30, 2, 3, 9, eraseFG resetSource, 0, .genesis⟩

set_option maxHeartbeats 2000000 in
-- The kernel checks the source at tick 42, using its cached prefix.
theorem nvSourceHeight : (sourceAtAction 3).map (fun C => (heightView params C).h) = some 3 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete source slot at tick 42.
theorem nvSourceSlot : resetSource.slot = 9 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete row and source entry at tick 42.
theorem nvResetRowFields :
    namedEntry resetRow.payload.height_pair =
      some (3, (heightView params resetSource).T_h.root) := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete wire emission at tick 42.
theorem nvResetEmissionWire :
    toWire params (ofRow params resetRow) ∈
      (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2.map (toWire params) := by
  decide +kernel

theorem nvResetEmission :
    ofRow params resetRow ∈ (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2 := by
  obtain ⟨o, ho, he⟩ := List.mem_map.mp nvResetEmissionWire
  have heq : o = ofRow params resetRow := (toWireEquiv params).injective he
  exact heq ▸ ho

theorem nvSource : sourceAtAction 3 = some resetSource := by
  have h := nvSourceHeight
  cases he : sourceAtAction 3 with
  | none => rw [he] at h; cases h
  | some C => simp only [resetSource, he, Option.getD_some]

theorem nvResetHeight : (heightView params resetSource).h = 3 := by
  have h := nvSourceHeight
  rw [nvSource] at h
  exact Option.some.inj h

theorem nvHonestResetRow :
    HonestRowAt params unitCodec env run (runPrefix 42).1.length 0 3 resetRow := by
  refine ⟨Finset.mem_univ _, tick_at 42 (by decide), ?_⟩
  rw [emits_at_tick 42 (by decide)]
  exact nvResetEmission

set_option maxHeartbeats 2000000 in
-- The kernel checks only the first three action prefixes.
theorem nvEarlySourceHeights :
    ((sourceAtAction 0).map (fun C => (heightView params C).h),
     (sourceAtAction 1).map (fun C => (heightView params C).h),
     (sourceAtAction 2).map (fun C => (heightView params C).h)) =
      (none, some 1, some 2) := by decide +kernel

/-- S5 NV6: Every named honest row in rounds 0--2 has height at most 2.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvEarlyRowCap {j : Nat} {y : Fin 1} {r h : Nat} {a : RowWire params.n} {e : BlockId}
    (ha : HonestRowAt params unitCodec env run j y r a)
    (he : namedEntry a.payload.height_pair = some (h, e)) (hr : r < 3) : h ≤ 2 := by
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : (params.actionTime r).toNat < 311 := by
    change (4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1).toNat < 311
    push_cast
    omega
  obtain ⟨C, _, hC, hh, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read r hb] at hC
  have hs : (sourceAtAction r).map (fun C => (heightView params C).h) = some h := by
    rw [Option.some.inj hC]
    exact congrArg some hh.symm
  have h0 : (sourceAtAction 0).map (fun C => (heightView params C).h) = none :=
    congrArg Prod.fst nvEarlySourceHeights
  have h1 : (sourceAtAction 1).map (fun C => (heightView params C).h) = some 1 :=
    congrArg (fun z => z.2.1) nvEarlySourceHeights
  have h2 : (sourceAtAction 2).map (fun C => (heightView params C).h) = some 2 :=
    congrArg (fun z => z.2.2) nvEarlySourceHeights
  have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [h0] at hs
    cases hs
  · rw [h1] at hs
    have hh' : h = 1 := (Option.some.inj hs).symm
    omega
  · rw [h2] at hs
    have hh' : h = 2 := (Option.some.inj hs).symm
    omega

theorem nvRowCap : ∀ j y r a h e t,
    HonestRowAt params unitCodec env run j y r a →
    run.events[j]? = some (.tick y t) → t ≤ 30 →
    namedEntry a.payload.height_pair = some (h, e) → h ≤ 2 := by
  intro j y r a h e t ha ht hcut he
  have heq : params.actionTime r = t :=
    (V2.Event.tick.inj (Option.some.inj (ha.2.1.symm.trans ht))).2
  have hr : r < 3 := by
    rw [← heq] at hcut
    change 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1 ≤ 30 at hcut
    push_cast at hcut
    omega
  exact nvEarlyRowCap ha he hr

/-- S5 NV6: With GST zero, no source vote is strictly before GST.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvOldRowsEmpty : oldRowHeights params unitCodec env run = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro h ⟨j, y, r, a, e, ha, he, ht⟩
  change 4 * 1 * ((r * 3 : Nat) : Int) + 1 < 6 at ht
  have hr : r = 0 := by push_cast at ht; omega
  subst r
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  obtain ⟨C, _, hC, _, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read 0 (by decide)] at hC
  have hn : sourceAtAction 0 = none := by decide +kernel
  rw [hn] at hC
  cases hC

theorem nvMu : muOf params unitCodec env run = 1 := by
  rw [muOf_def, nvOldRowsEmpty]
  simp

theorem nvHeightRow : HeightRow params unitCodec env run 3 3 :=
  ⟨(runPrefix 42).1.length, 0, resetRow, (heightView params resetSource).T_h.root,
    nvHonestResetRow, nvResetRowFields⟩

theorem nvResetFirst : ∀ r, HeightRow params unitCodec env run r 3 → 3 ≤ r := by
  rintro r ⟨j, y, a, e, ha, he⟩
  by_contra hn
  have h := nvEarlyRowCap ha he (by omega)
  omega

-- Keep the concrete witness terms closed during the final structure assembly.
attribute [irreducible] resetSource resetRow

theorem nvFresh : ∃ j y, ∃ (a : RowWire params.n) (C : FGBlock (Fin params.n)),
    HonestRowAt params unitCodec env run j y 3 a ∧
    namedEntry a.payload.height_pair = some (3, (heightView params C).T_h.root) ∧
    actionSourceFG params unitCodec env run y 3 = some (some C) ∧
    eraseFG C = eraseFG resetSource ∧ (heightView params C).h = 3 := by
  have hs : actionSourceFG params unitCodec env run 0 3 = some (some resetSource) :=
    (source_read 3 (by decide)).trans (congrArg some nvSource)
  exact ⟨(runPrefix 42).1.length, 0, resetRow, resetSource, nvHonestResetRow,
    nvResetRowFields, hs, Eq.refl _, nvResetHeight⟩

set_option maxHeartbeats 2000000 in
-- The assembly checks the concrete witness after the short-prefix source proof.
/-- S5 NV6: All 13 reset fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset : H0Reset params unitCodec env run w where
  rG_after := by decide
  rG_first := by intro r _; exact Nat.zero_le r
  cut := by decide
  frontier := nvFrontier.symm
  rowCap := nvRowCap
  mu_le := by change muOf params unitCodec env run ≤ 2; rw [nvMu]; decide
  cut_lower := by decide
  cut_upper := by decide
  reset_row := nvHeightRow
  reset_first := nvResetFirst
  label := rfl
  fresh := nvFresh
  synchronous := by decide

-- NV5 evaluates only proposal prefixes through tick 52.
def proposalObjects (s : Slot) : List Object :=
  (V2.D.tick env (mkRun []) (runPrefix (4 * s)).2 0 (4 * (s : Time))).2

def proposalBlocks (s : Slot) : List Block :=
  (proposalObjects s).filterMap (fun o => (fgsaInterface params unitCodec).block o.payload)

/-- S5 NV6: The chain is in child-to-parent order; each node records its slot and body.
DC: SAME canonical fixture and cached prefix proof. -/
def parentChain : Block → List (Slot × Nat)
  | .genesis => [(0, 0)]
  | .node B s _ x => (s, x) :: parentChain B

def firstProposal : Block := (proposalBlocks 11).headD .genesis

def w' : HealingWitness := { w with u := 11, QStar := firstProposal }

set_option maxHeartbeats 2000000 in
-- The kernel compares the cached proposal and reset-source prefixes.
/-- S5 NV6: The block of the first proposal has C* as its second parent.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvFirstParents : firstProposal.parent.parent = eraseFG resetSource := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks ancestry through the cached prefixes at ticks 42 and 44.
theorem nvSourcePrefix : Block.Preceq (eraseFG resetSource) firstProposal := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the block emitted from the cached state at tick 44.
theorem nvFirstMember : firstProposal ∈ proposalBlocks 11 := by decide +kernel

/-- S5 NV6: A cached block emission is an honest proposal of the complete run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem honestProposal_of_cached {s : Slot} {B : Block} (hs : 0 < s)
    (hn : 4 * s < 311) (hB : B ∈ proposalBlocks s) :
    HonestProposal env run (fgsaInterface params unitCodec) s B := by
  obtain ⟨o, ho, hb⟩ := List.mem_filterMap.mp hB
  refine ⟨⟨hs, Finset.mem_univ _⟩, o, ?_, hb⟩
  refine ⟨(runPrefix (4 * s)).1.length, ?_, ?_⟩
  · change run.events[(runPrefix (4 * s)).1.length]? = some (.tick 0 (4 * (s : Time)))
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using tick_at (4 * s) hn
  · rw [emits_at_tick (4 * s) hn]
    simpa only [proposalObjects, Nat.cast_mul, Nat.cast_ofNat] using ho

/-- S5 NV6: w' changes only the proposal slot and block in the copied NV4 witness.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset' : H0Reset params unitCodec env run w' where
  rG_after := nvH0Reset.rG_after
  rG_first := nvH0Reset.rG_first
  cut := nvH0Reset.cut
  frontier := nvH0Reset.frontier
  rowCap := nvH0Reset.rowCap
  mu_le := nvH0Reset.mu_le
  cut_lower := nvH0Reset.cut_lower
  cut_upper := nvH0Reset.cut_upper
  reset_row := nvH0Reset.reset_row
  reset_first := nvH0Reset.reset_first
  label := nvH0Reset.label
  fresh := nvH0Reset.fresh
  synchronous := nvH0Reset.synchronous

theorem nvProposalLower : w'.sStar + 2 ≤ w'.u := by decide

-- Keep the evaluated block closed during proposal and H0 assembly.
attribute [irreducible] firstProposal

theorem nvProposal : HonestProposal env run (fgsaInterface params unitCodec) w'.u w'.QStar := by
  change HonestProposal env run (fgsaInterface params unitCodec) 11 firstProposal
  exact honestProposal_of_cached (by decide) (by decide) nvFirstMember

theorem nvProposalFirst : ∀ v Q, w'.sStar + 2 ≤ v →
    HonestProposal env run (fgsaInterface params unitCodec) v Q → w'.u ≤ v := by
  intro v Q hv _
  exact hv

theorem nvAfterGST : env.t_GST ≤ tstar params w' := by decide

/-- S5 NV6: All H0 fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0 : H0 params unitCodec env run w' where
  toH0Reset := nvH0Reset'
  proposal_lower := nvProposalLower
  proposal := nvProposal
  proposal_first := nvProposalFirst
  after_gst := nvAfterGST
  source_prefix := nvSourcePrefix

theorem nvClock : params.δt = 2 * params.R := by decide
theorem nvTstarValue : tstar params w' = 50 := by decide
theorem nvResetActionValue : params.actionTime w'.rStar = 42 := by decide
theorem nvTimeBudgetValue : params.actionTime w'.rStar + Γ params gap + 4 * params.Δ = 50 := by
  decide

-- Equality is allowed in the first H-time bound: 50 ≤ 42 + 4 + 4.
theorem nvTstarBound :
    tstar params w' ≤ params.actionTime w'.rStar + Γ params gap + 4 * params.Δ := by
  decide

theorem nvResetTimeStrict :
    params.actionTime w'.rStar < recoveryStart params env + B'_resetF params deltaF gap := by
  decide

-- Both horizon forms hold at 303 ≤ 310 on this run.
theorem nvFullHorizon :
    recoveryStart params env + B'_resetF params deltaF gap +
        Γ params gap + 4 * params.Δ ≤ run.horizon :=
  healing_resetFull_horizon params gap deltaF (recoveryStart params env) run.horizon healing_horizon

theorem nvTimeStrict :
    params.actionTime w'.rStar + Γ params gap + 4 * params.Δ <
      recoveryStart params env + B_HF params deltaF gap :=
  healing_time_strict_of_reset params gap deltaF (recoveryStart params env)
    (params.actionTime w'.rStar) nvResetTimeStrict


/-- S5 NV6 N1: apply the closed row permission producer to the NV3 package.
DC: SAME canonical run, action source, and row entry. -/
theorem nvRowPermission : RowPermissionAt params unitCodec env run :=
  fgsa_rowPermissionClaim params gap deltaF nvClock unitCodec env run () (healingPrem ())

/-- S5 NV6 N1: apply the closed renewed promotion producer to round 3.
DC: SAME canonical run and the proved 66 <= 310 horizon. -/
theorem nvRenewedPromotion : RenewedPromotionConcl params unitCodec env run gap 3 :=
  fgsa_renewedPromotionClaim params gap deltaF nvClock unitCodec env run ⟨3⟩
    renewedPromotionPrem

/-- S5 NV6 N1: adapt the closed reset-only statement to its claim.
DC: SAME reset-only conclusion; full H0 is a separate item. -/
theorem nvResetArrivalClaim : ResetArrivalClaim params := by
  intro G ΔF hδ V _ _ In c E rho pt h
  exact healing_resetArrivalStatement params G ΔF hδ c E rho h.set h.bound h.hhor

/-- S5 NV6 N1: apply the reset-only claim to the NV3 package.
DC: SAME canonical run and the proved 295 <= 310 horizon. -/
theorem nvResetArrival : ResetArrivalConcl params unitCodec env run gap deltaF :=
  nvResetArrivalClaim gap deltaF nvClock unitCodec env run () resetArrivalPrem

/-- S5 NV6 N1: the NV5 full witness supplies the healing input package.
DC: SAME full H0 and tstar = 50; this package is closed. -/
theorem nvHealingInputPrem : HealingInputPrem params unitCodec gap deltaF env run ⟨w'⟩ :=
  ⟨⟨healingPrem (⟨w'⟩ : PtW), nvH0⟩, by change (50 : Time) ≤ 310; decide⟩

/-- Blueprint 21 H.18–H.22; plan S5 NV7 N2: apply the closed full reset statement.
DC: SAME canonical run and the proved full reset horizon. -/
theorem nvResetArrivalFull : ∃ witness, H0 params unitCodec env run witness ∧
    params.actionTime witness.rStar < recoveryStart params env + B'_resetF params deltaF gap :=
  healing_resetArrivalFull params gap deltaF nvClock unitCodec env run
    healingSet livenessBound nvFullHorizon

/-- Blueprint 21 H.18–H.22; plan S5 NV7 N2: apply the closed HealingInputClaim.
DC: SAME canonical run and the full NV5 witness with tstar = 50. -/
theorem nvHealingInput : HealingInput params unitCodec env run w' deltaF :=
  healing_healingInputClaim params gap deltaF nvClock unitCodec env run ⟨w'⟩ nvHealingInputPrem


/-! P0d7b-a: the FG-SA finality kernel applied on this exact run. Opening round r = 5
(slot 15, time 60 ≥ tstar = 50), same witness w', ΔF = 3, deadline 97 ≤ 310. -/

open Gen.Pure

/-- Copied from Tests/NonVacuity/FinalityClaims.lean: every positive slot is honest. -/
theorem nvGood (r : Nat) (hr : 1 ≤ r) :
    FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      params.R (kappaF params deltaF) r := by
  rw [FGoodE_W_def]
  refine ⟨honest_slot (by change 0 < r * 3; omega),
    honest_slot (by change 0 < (r + 1) * 3; omega),
    ⟨(r + 2) * 3, ?_, ?_, honest_slot (by change 0 < (r + 2) * 3; omega)⟩, ?_⟩
  · change (r + 1) * 3 + 3 ≤ (r + 2) * 3
    omega
  · exact le_rfl
  · apply honest_slot
    change 0 < (r + 2) * 3 + 3
    omega

/-- Copied from Tests/NonVacuity/FinalityClaims.lean: the block the proposer computes. -/
def nvProposalBlock (s : Slot) : Block :=
  let st := FGSA.clock params (runPrefix (4 * s)).2.st (4 * (s : Time))
  let H := getHead params st (proposerVotes st s) (proposerSupport st s)
  Block.node H s ⟨s + 1⟩ (packBody 0 (proposalRows params st H))

/-- Copied from Tests/NonVacuity/FinalityClaims.lean (prefix bound 311 here). -/
theorem nvProposalBlock_honest (s : Slot) (hs : 0 < s) (hn : 4 * s < 311) :
    HonestProposal env run (fgsaInterface params unitCodec) s (nvProposalBlock s) := by
  apply honestProposal_of_cached hs hn
  let st := FGSA.clock params (runPrefix (4 * s)).2.st (4 * (s : Time))
  let raw := proposerVotes st s
  let sup := proposerSupport st s
  let H := getHead params st raw sup
  let rows := proposalRows params st H
  have hr := Reachable.tick (4 * (s : Time))
    (namedOrigin_reachable env run (runPrefix (4 * s)).1.length 0)
  rw [state_before_tick (4 * s) hn] at hr
  obtain ⟨P, hP, _, hPH⟩ := propose_parent_lookup params hr s
  let m := Msg.proposal (namedProposal params P s 0
    (raw.filterMap liftHead?) (sup.filterMap liftHead?) rows)
  let o : Object := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩
  have hm : o ∈ proposalObjects s := by
    apply (fgsa_emits_proposal env (mkRun []) (runPrefix (4 * s)).2
      0 (4 * (s : Time)) s m).mpr
    have hg := fgsa_joinedNow_of_joinedEnv env run nvSchedule (tick_at (4 * s) hn) (by
      intro u _ _ hu
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
      exact (noRestart i 0 u hi).elim)
    rw [state_before_tick (4 * s) hn] at hg
    refine ⟨rfl, rfl, rfl, hg, ?_⟩
    delta propose
    simp only [Nat.ne_of_gt hs, ↓reduceIte, hP, Option.map_some]
    rfl
  apply List.mem_filterMap.mpr
  refine ⟨o, hm, ?_⟩
  change some (namedProposal params P s 0
    (raw.filterMap liftHead?) (sup.filterMap liftHead?) rows).erase = some (nvProposalBlock s)
  rw [namedProposal_erase, hPH]
  rfl

/-- The kernel deadline of round 5 (action round 7) and the opening time. -/
theorem kernelDeadlineValue : kernelDeadlineW params deltaF (5 + 2) = 97 ∧
    (5 : Time) * P params = 60 := by decide

/-- premises_sat: every field of the FG-SA kernel premise on this exact run, with the same
witness w' that closes HealingInput, start 50 ≤ 60 and horizon 310 ≥ deadline 97. -/
theorem kernelPrem_premises_sat : KernelPrem_W params unitCodec gap deltaF env run ⟨w', 5⟩ where
  set := nvRecovery.toRecovery₂
  bound := livenessBound
  window := nvGood 5 (by decide)
  start := by rw [nvTstarValue]; decide
  hhor := by rw [kernelDeadlineValue.1]; decide
  input := nvHealingInput
  services := fgsa_coreServices env run nvRecovery.base w'
    (finality_vote_receipts nvRecovery.toRecovery₂)

/-- POSITIVE: the closed FG-SA kernel (`fgsa_finalityKernel_W`, which applies
`finality_kernel_W_of`) on this run. -/
theorem kernelConclusion : KernelConclusion_W params unitCodec env run deltaF 5 :=
  fgsa_finalityKernel_W params gap deltaF nvClock unitCodec env run ⟨w', 5⟩
    kernelPrem_premises_sat

/-- The returned witness for the actual slot-15 opening: its carrier erases to the computed
proposal, and a strict fresh extension U one height above it is accepted by the honest node
strictly before the deadline 97. (Retention of the carrier at the end is the third
conjunct of `kernelConclusion` itself.) -/
theorem kernelWitnessInspected :
    HonestProposal env run (fgsaInterface params unitCodec) 15 (nvProposalBlock 15) ∧
    ∃ Afg U : FGBlock (Fin params.n), eraseFG Afg = nvProposalBlock 15 ∧
    FGBlock.Preceq Afg U ∧ Afg ≠ U ∧
    (heightView params U).h = (heightView params Afg).h + 1 ∧
    AcceptsFinalBefore params unitCodec env run 0 U 97 := by
  have hA := nvProposalBlock_honest 15 (by decide) (by decide)
  obtain ⟨Afg, he, _, _, U, hAU, hne, hh, hacc⟩ :=
    (KernelConclusion_W_def params unitCodec env run deltaF 5).mp kernelConclusion
      (nvProposalBlock 15) hA
  refine ⟨hA, Afg, U, he, hAU, hne, hh, ?_⟩
  have := hacc 0 (Finset.mem_univ _)
  rwa [kernelDeadlineValue.1] at this

#print axioms kernelPrem_premises_sat
#print axioms kernelConclusion
#print axioms kernelWitnessInspected

end AvailableChain.FGSA.Run.Tests.P0d7baRun
