module
public import AvailableChainFGCompose.Statements.HistoricalReads
public import AvailableChainGeneric.Proofs.Pure.CommonAncestor

public section

namespace AvailableChain.FGCompose

private theorem historical_lookup_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact historical_lookup_nodup (xs.filter (fun b => !b == a))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A lookup resolves exactly one full body at the requested root. -/
theorem historicalLookup_spec {Body : Type} [DecidableEq Body]
    (root : Body → BlockId) (tree : List Body) (r : BlockId) (B : Body) :
    historicalLookup root tree r = some B ↔
      B ∈ tree ∧ root B = r ∧ ∀ C ∈ tree, root C = r → C = B := by
  let xs := (tree.filter (fun C => root C == r)).eraseDups
  have lookup_eq : historicalLookup root tree r = some B ↔ xs = [B] := by
    rw [historicalLookup_def]
    change (match xs with | [b] => some b | _ => none) = some B ↔ xs = [B]
    cases xs with
    | nil => constructor <;> intro h <;> cases h
    | cons C cs =>
      cases cs with
      | nil =>
        constructor
        · intro h
          cases h
          rfl
        · intro h
          exact congrArg some (List.cons.inj h).1
      | cons D ds => constructor <;> intro h <;> cases h
  have hm (C : Body) : C ∈ xs ↔ C ∈ tree ∧ root C = r := by
    simp [xs]
  have hn : xs.Nodup := historical_lookup_nodup _
  rw [lookup_eq]
  constructor
  · intro he
    have hB := (hm B).mp (by simp [he])
    refine ⟨hB.1, hB.2, ?_⟩
    intro C hC hr
    have := (hm C).mpr ⟨hC, hr⟩
    simpa [he] using this
  · rintro ⟨hB, hr, hu⟩
    have hb : B ∈ xs := (hm B).mpr ⟨hB, hr⟩
    have hall : ∀ C ∈ xs, C = B := fun C hC =>
      hu C ((hm C).mp hC).1 ((hm C).mp hC).2
    have he : xs = [B] := by
      cases hxs : xs with
      | nil => simp [hxs] at hb
      | cons C cs =>
          rw [hxs] at hn hall
          have hc : C = B := hall C (by simp)
          subst C
          have hempty : cs = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro C hC
            have he := hall C (by simp [hC])
            subst C
            exact (List.nodup_cons.mp hn).1 hC
          simp [hempty]
    exact he

variable {In Body : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire}
variable {H : FGHistoricalReads P.State Body} {Good : P.State → Prop}
variable (L : FGHistoricalLaws R H Good)
include L

theorem historical_read_sound {st : P.State} {r : BlockId} {b : Body}
    (hr : H.readBlock st r = some b) : b ∈ H.acceptedBodies st ∧ H.root b = r :=
  let h := (L.read_iff st r b).mp hr
  ⟨h.1, h.2.1⟩

theorem historical_read_complete {st : P.State} (hg : Good st) {b : Body}
    (hb : b ∈ H.acceptedBodies st) : H.readBlock st (H.root b) = some b :=
  (L.read_iff st _ b).mpr ⟨hb, rfl, fun c hc hr => L.reachable_unique st hg c hc b hb hr⟩

theorem historical_read_ambiguous {st : P.State} {b c : Body}
    (hb : b ∈ H.acceptedBodies st) (hc : c ∈ H.acceptedBodies st)
    (hr : H.root b = H.root c) (hne : b ≠ c) : H.readBlock st (H.root b) = none := by
  cases he : H.readBlock st (H.root b) with
  | none => rfl
  | some d =>
    have hu := ((L.read_iff st _ d).mp he).2.2
    exact (hne ((hu b hb rfl).trans (hu c hc hr.symm).symm)).elim

theorem historical_parent_held {st : P.State} (hg : Good st) {b : Body}
    (hb : b ∈ H.acceptedBodies st) :
    H.parent b ∈ H.acceptedBodies st ∧
      H.readBlock st (H.root (H.parent b)) = some (H.parent b) :=
  ⟨L.parent_closed st hg b hb,
    historical_read_complete L hg (L.parent_closed st hg b hb)⟩

omit L in
private theorem historical_prefix_mem (tree : Finset Block)
    (closed : ∀ B ∈ tree, B.parent ∈ tree) {B C : Block}
    (hc : C ∈ tree) (hp : Block.Preceq B C) : B ∈ tree := by
  induction C with
  | genesis =>
    have he : B = .genesis := of_decide_eq_true hp
    exact he ▸ hc
  | node p s r x ih =>
    rcases Bool.or_eq_true_iff.mp hp with he | hp
    · exact (of_decide_eq_true he : B = .node p s r x) ▸ hc
    · exact ih (closed _ hc) hp

theorem historical_lca_held {st : P.State} (hg : Good st) {b c : Body}
    (hb : b ∈ H.acceptedBodies st) (_hc : c ∈ H.acceptedBodies st) :
    ∃ d ∈ H.acceptedBodies st, H.erase d = H.lca b c ∧
      H.readBlock st (H.root d) = some d := by
  have closed : ∀ B ∈ H.acceptedBlocks st, B.parent ∈ H.acceptedBlocks st := by
    intro B hB
    obtain ⟨d, hd, rfl⟩ := (L.bodies_eq st hg B).mp hB
    exact (L.bodies_eq st hg _).mpr
      ⟨H.parent d, L.parent_closed st hg d hd, L.parent_eq d⟩
  have hm := historical_prefix_mem (H.acceptedBlocks st) closed
    ((L.bodies_eq st hg _).mpr ⟨b, hb, rfl⟩)
    (Gen.Pure.meet_preceq_left (H.erase b) (H.erase c))
  rw [← L.geometry_eq.2.2 b c] at hm
  obtain ⟨d, hd, he⟩ := (L.bodies_eq st hg _).mp hm
  exact ⟨d, hd, he, historical_read_complete L hg hd⟩

/-- Membership retention needs later uniqueness to preserve a successful lookup. -/
theorem historical_read_step {st st' : P.State} (step : FGHistoryStep P st st')
    (later : Good st') {r : BlockId} {b : Body} (hr : H.readBlock st r = some b) :
    H.readBlock st' r = some b := by
  obtain ⟨hb, he⟩ := historical_read_sound L hr
  rw [← he]
  exact historical_read_complete L later (L.step_keep st st' step b hb)

theorem historical_read_frame_eq {st st' : P.State}
    (he : H.acceptedBodies st = H.acceptedBodies st') (r : BlockId) :
    H.readBlock st r = H.readBlock st' r := L.frame_independent st st' he r

theorem historical_read_restore_eq (st : P.State) (t : Time) (r : BlockId) :
    H.readBlock (P.restore (P.durable st) t) r = H.readBlock st r :=
  L.frame_independent _ st (L.restore_eq st t).1 r

theorem historical_geometry_restore_eq (st : P.State) (t : Time) :
    H.acceptedBodies (P.restore (P.durable st) t) = H.acceptedBodies st ∧
      H.acceptedBlocks (P.restore (P.durable st) t) = H.acceptedBlocks st :=
  L.restore_eq st t

end AvailableChain.FGCompose
end
