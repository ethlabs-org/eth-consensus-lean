module
public import ConsensusLean.Lemmas.Model.Canonical.InjectFilter

public section

/-! # Where the signed parts of a run's objects come from (L1)

* `part_released`, `part_released_of_receives`: in a valid run, a part `d` signed by key `k` of an
  object released or received at `t`, with `k`'s validator honest at `t`, was released at top level
  by `k`'s validator at a time `≤ t` (honest code passes on only what it has seen, and unforgeable
  signatures trace every received honest signature to its signer's release).
* `injfRun_part_injected`: in a scheduled run with injections (`Canonical/Inject`), a part signed
  by a key whose validator is never honest, of an object an honest node receives at `t`, is a part
  of an object injected at a time `≤ t`, and that injection is received. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

omit [DecidableEq V] in
/-- An object signed by key `k` is signed by `k`'s validator. -/
private theorem signerOf_of_auth {d : (protoOf F E).Object} {k : Fin (Fintype.card V)}
    {r : (protoOf F E).Role} (hs : d.auth = .signed k r) : rho.signerOf d = some (rho.key k) := by
  simp only [signerOf, Obj.signer?, hs, Option.map_some]

/-- **A signed part of a release was released by its signer first**: in a valid run, a part `d`
signed by key `k` of an object released at `t`, with `k`'s validator honest at `t`, was released
at top level by `k`'s validator at a time `≤ t`. -/
theorem part_released (hv : rho.ExecutionValid) {u : V} {o : (protoOf F E).Object} {t : Time}
    (hr : rho.releases u o t) {d : (protoOf F E).Object} (hd : Obj.Contains o d)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (hs : d.auth = .signed k r)
    (hk : rho.point.HonestAt (rho.key k) t) :
    ∃ t', t' ≤ t ∧ rho.releases (rho.key k) d t' := by
  obtain ⟨i, hi, ho⟩ := hr
  have hk' : rho.key k ∉ rho.faultyAt t := hk
  let G : Nat → Prop := fun j => ∃ e, rho.events[j]? = some e ∧ e.time ≤ t
  let P : Nat → (protoOf F E).Object → Prop := fun j d => ∀ x, rho.signerOf d = some x →
    x ∉ rho.faultyAt t → ∃ l t', l < j ∧ t' ≤ t ∧ rho.SendsAt x l t' ∧ d ∈ rho.releasesAt l
  have hcl := rho.closed_of_sources P G
    (fun hle h x hsg hx => let ⟨l, t', hl, h1, h2, h3⟩ := h x hsg hx; ⟨l, t', by omega, h1, h2, h3⟩)
    (by
      rintro j l ej el ⟨e, he, het⟩ hlj hj hl -
      rw [he] at hj; cases hj
      exact ⟨el, hl, (rho.time_le_of_lt hv.sorted hlj he hl).trans het⟩)
    (by
      rintro j ⟨e, he, het⟩ o ho x hsg _
      cases e with
      | tick v τ =>
        simp only [releasesAt, he] at ho
        rcases rho.tick_signerOf _ v τ ho with hn | hx
        · rw [hn] at hsg; cases hsg
        · obtain rfl := Option.some.inj (hsg.symm.trans hx)
          exact ⟨j, τ, Nat.lt_succ_self j, het, Or.inl he, by simpa only [releasesAt, he] using ho⟩
      | deliver v p τ =>
        simp only [releasesAt, he] at ho
        rcases rho.deliver_signerOf _ v p τ ho with hn | hx
        · rw [hn] at hsg; cases hsg
        · obtain rfl := Option.some.inj (hsg.symm.trans hx)
          exact ⟨j, τ, Nat.lt_succ_self j, het, Or.inr ⟨p, he⟩,
            by simpa only [releasesAt, he] using ho⟩
      | restart v τ => simp [releasesAt, he] at ho)
    (by
      rintro j w' p τ ⟨e, he, het⟩ hj
      rw [hj] at he; cases he
      left
      intro d hd x hsg hx
      obtain ⟨l, t', hl, hS, hdl⟩ := hv.unforgeable j w' p τ hj d hd x hsg
        (fun h => hx (rho.faultyAt_mono het h))
      obtain ⟨el, hel, -, helt⟩ := hS.exists_event
      exact ⟨l, t', hl, (helt ▸ rho.time_le_of_lt hv.sorted hl hj hel).trans het, hS, hdl⟩)
  obtain ⟨e, he, -, het⟩ := hi.exists_event
  obtain ⟨l, t', -, ht', hS, hdl⟩ := hcl i ⟨e, he, het.le⟩ o ho d hd (rho.key k)
    (rho.signerOf_of_auth hs) hk'
  exact ⟨t', ht', l, hS, hdl⟩

/-- **A signed part of a receipt was released by its signer first**: in a valid run, a part `d`
signed by key `k` of an object received at `t`, with `k`'s validator honest at `t`, was released
at top level by `k`'s validator at a time `≤ t`. -/
theorem part_released_of_receives (hv : rho.ExecutionValid) {w : V} {o : (protoOf F E).Object}
    {t : Time} (hr : rho.receives w o t) {d : (protoOf F E).Object} (hd : Obj.Contains o d)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (hs : d.auth = .signed k r)
    (hk : rho.point.HonestAt (rho.key k) t) :
    ∃ t', t' ≤ t ∧ rho.releases (rho.key k) d t' := by
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, t', hj, hS, hdj⟩ :=
    hv.unforgeable i w o t hi d hd (rho.key k) (rho.signerOf_of_auth hs) hk
  obtain ⟨e, he, -, het⟩ := hS.exists_event
  exact ⟨t', het ▸ rho.time_le_of_lt hv.sorted hj hi he, j, hS, hdj⟩

variable (delay : Event V (protoOf F E).Object → Time)
  (inj : Time → V → List (protoOf F E).Object)
  (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)

/-- **A part signed by a never-honest key comes from an injection**: in the scheduled run with
injections, a part `d` signed by key `k`, whose validator is compromised at every time, of an
object received at `t` is a part of an object `o'` injected to a node `v` at a time `t' ≤ t`, and
`v` receives `o'` at `t'`. -/
theorem injfRun_part_injected (hdelay : ∀ e, 0 ≤ delay e)
    {k : Fin (Fintype.card V)} (hk : ∀ t, rho.key k ∈ rho.faultyAt t) {w : V}
    {o : (protoOf F E).Object} {t : Time} (hr : (rho.injfRun delay inj pol).receives w o t)
    {d : (protoOf F E).Object} (hd : Obj.Contains o d) {r : (protoOf F E).Role}
    (hs : d.auth = .signed k r) :
    ∃ t' v o', t' ≤ t ∧ o' ∈ inj t' v ∧ Obj.Contains o' d ∧
      (rho.injfRun delay inj pol).receives v o' t' := by
  let ir := rho.injfRun delay inj pol
  have hev : ir.events = rho.injfEvents delay inj pol := withEvents_events _ _
  have hsort : ir.events.Pairwise Event.keyLe := by
    rw [hev, injfEvents_eq]
    exact rho.injfStages_sorted delay inj pol _
  let G : Nat → Prop := fun j => ∃ e, ir.events[j]? = some e ∧ e.time ≤ t
  let P : Nat → (protoOf F E).Object → Prop := fun _ d => ∀ ρ, d.auth = .signed k ρ →
    ∃ t' v o', t' ≤ t ∧ o' ∈ inj t' v ∧ Obj.Contains o' d ∧ ir.receives v o' t'
  have hdel : ∀ j w' p τ, G j → ir.events[j]? = some (.deliver w' p τ) →
      (∀ d, Obj.Contains p d → P j d) ∨ ∃ l < j, G l ∧ p ∈ ir.releasesAt l := by
    rintro j w' p τ ⟨e, he, het⟩ hj
    rw [hj] at he; cases he
    rcases rho.injfEvents_source delay inj pol hj with hp | ⟨l, hl, el, hel, helt, hlr⟩
    · exact Or.inl fun d hd _ _ => ⟨τ, w', p, het, hp, hd, j, hj⟩
    · exact Or.inr ⟨l, hl, ⟨el, hel,
        ((le_add_of_nonneg_right (hdelay el)).trans helt).trans het⟩, hlr⟩
  have hcl := ir.closed_of_sources P G (fun _ h => h)
    (by
      rintro j l ej el ⟨e, he, het⟩ hlj hj hl -
      rw [he] at hj; cases hj
      exact ⟨el, hl, (ir.time_le_of_lt hsort hlj he hl).trans het⟩)
    (by
      rintro j - o ho ρ hsg
      have hsig := ir.signerOf_of_auth hsg
      cases he : ir.events[j]? with
      | none => simp [releasesAt, he] at ho
      | some e =>
        have hhon : e.node ∉ rho.faultyAt e.time := by
          have hm := List.mem_of_getElem? he
          rw [hev, injfEvents_eq] at hm
          obtain ⟨n, -, hn⟩ := (rho.mem_injfStages delay inj pol _ _).mp hm
          exact rho.injfLayer_honest delay inj pol _ _ hn
        cases e with
        | tick v τ =>
          simp only [releasesAt, he] at ho
          rcases ir.tick_signerOf _ v τ ho with hn | hx
          · rw [hn] at hsig; cases hsig
          · obtain rfl := Option.some.inj (hsig.symm.trans hx)
            have hx : rho.key k ∉ rho.faultyAt τ := by
              simp only [ir, injfRun, withEvents_key] at hhon
              exact hhon
            exact absurd (hk τ) hx
        | deliver v p τ =>
          simp only [releasesAt, he] at ho
          rcases ir.deliver_signerOf _ v p τ ho with hn | hx
          · rw [hn] at hsig; cases hsig
          · obtain rfl := Option.some.inj (hsig.symm.trans hx)
            have hx : rho.key k ∉ rho.faultyAt τ := by
              simp only [ir, injfRun, withEvents_key] at hhon
              exact hhon
            exact absurd (hk τ) hx
        | restart v τ => simp [releasesAt, he] at ho)
    hdel
  obtain ⟨i, hi⟩ := hr
  rcases hdel i w o t ⟨_, hi, le_rfl⟩ hi with h | ⟨l, -, hG, hlr⟩
  · exact h d hd r hs
  · exact hcl l hG o hlr d hd r hs

end Run

end Consensus.Model

end
