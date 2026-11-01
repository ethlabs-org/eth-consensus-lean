module
public import AvailableChainFGSA.Model.Spec.Codec
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.NamedProposal

public section

namespace AvailableChain.FGSA.Spec

variable {n : Nat}

@[simp] theorem embed_root (B : Block n) : B.embed.root = B.root := by
  cases B <;> rfl

@[simp] theorem embed_slot (B : Block n) : B.embed.slot = B.slot := by
  cases B <;> rfl

@[simp] theorem embed_parent (B : Block n) : B.embed.parent = B.parent.embed := by
  cases B <;> rfl

/-- All identities, including those on invalid ancestors, are required for injectivity. -/
theorem embed_injective : Function.Injective (@Block.representation n) := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [Block.representation, Block.embed]
  | node P s i r rows raw support ih =>
      intro B h
      cases B with
      | genesis => simp [Block.representation, Block.embed] at h
      | node Q t j u rs vs ss =>
          simp only [Block.representation, Block.embed, Block.identities,
            Prod.mk.injEq, NamedProposal.node.injEq, List.cons.injEq] at h
          rcases h with ⟨⟨hP, rfl, rfl, _, rfl, rfl, rfl⟩, rfl, hids⟩
          have hPQ := ih (Prod.ext hP hids)
          cases hPQ
          rfl

/-- The relation has exactly one spec block for a complete representation. -/
theorem blockCorresponds_unique (A B : Block n) (N : NamedProposal n) (ids : List (Fin n))
    (hA : BlockCorresponds A N ids) (hB : BlockCorresponds B N ids) : A = B :=
  embed_injective (hA.trans hB.symm)

/-- Assigned identities can be recovered from slots, including every ancestor. -/
theorem assigned_embed_injective (assigned : Slot → Fin n) (A B : Block n)
    (hA : A.Assigned assigned) (hB : B.Assigned assigned) (h : A.embed = B.embed) :
    A = B := by
  induction A generalizing B with
  | genesis => cases B <;> simp_all [Block.embed]
  | node P s i r rows raw support ih =>
      cases B with
      | genesis => simp [Block.embed] at h
      | node Q t j u rs vs ss =>
          simp only [Block.embed, NamedProposal.node.injEq] at h
          rcases h with ⟨hP, rfl, rfl, _, rfl, rfl, rfl⟩
          obtain ⟨hi, hP'⟩ := hA
          obtain ⟨hj, hQ'⟩ := hB
          rw [ih Q hP' hQ' hP, hi, hj]

/-- Plain Lean ancestry is exact when every ancestor has its assigned identity. -/
theorem embed_preceq (assigned : Slot → Fin n) (A B : Block n)
    (hA : A.Assigned assigned) (hB : B.Assigned assigned) :
    NamedProposal.preceq A.embed B.embed = Block.preceq A B := by
  have heq (C : Block n) (hC : C.Assigned assigned) :
      (A.embed = C.embed) ↔ A = C :=
    ⟨assigned_embed_injective assigned A C hA hC, congrArg Block.embed⟩
  induction B with
  | genesis =>
      change decide (A.embed = Block.embed .genesis) = decide (A = .genesis)
      simp only [heq .genesis trivial]
  | node P s i r rows raw support ih =>
      change (decide (A.embed = (Block.node P s i r rows raw support).embed) ||
        NamedProposal.preceq A.embed P.embed) = _
      simp only [heq _ hB, ih hB.2, Block.preceq]

/-- The FG carrier and named carrier have the same geometry. -/
theorem carrier_embedding (B : Block n) : eraseFG B.toFG = B.embed.erase := by
  induction B with
  | genesis => rfl
  | node P s i r rows raw support ih =>
      simp only [Block.toFG, Block.embed, eraseFG, NamedProposal.erase, packBody, ih]

/-- Root order is unchanged; no hash injectivity premise is needed. -/
theorem embed_root_order (A B : Block n) :
    A.embed.root < B.embed.root ↔ A.root < B.root := by simp

/-- Signed carried lists remain byte-for-byte data, in the same order. -/
theorem embed_lists (P : Block n) (s : Slot) (i : Fin n) (r : BlockId)
    (rows : List (RowWire n)) (raw support : List (HeadWire n)) :
    let N := (Block.node P s i r rows raw support).embed
    N.rows = rows ∧ N.raw = raw ∧ N.support = support := ⟨rfl, rfl, rfl⟩

theorem digest_embedding (p : Params) (P : BlockId) (s : Slot)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) :
    digestSpec p P s rows raw support = p.digest ⟨P, s, 0, rows, raw, support⟩ := rfl

/-- A supplied wrong digest is still wrong after embedding. -/
theorem content_check_embedding (p : Params) (P : Block p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) :
    namedContentOk p (Block.node P s i r rows raw support).embed =
      (r == digestSpec p P.root s rows raw support) := by
  have hrows : rowsOk (Block.node P s i r rows raw support).embed.erase rows = true := by
    simp [rowsOk, Block.embed, NamedProposal.erase, AvailableChain.Block.body]
  unfold namedContentOk contentOk
  change (rowsOk (Block.node P s i r rows raw support).embed.erase rows && _) = _
  rw [hrows, Bool.true_and]
  change (r == p.digest ⟨P.embed.erase.root, s, appOf (packBody 0 rows),
    rows, raw, support⟩) = _
  rw [appOf_packBody, named_erase_root, embed_root]
  rfl


@[simp] theorem wire_embed_auth (o : Wire n) : o.embed.auth = o.auth := rfl

/-- Decoding commutes on every wire, not only well-formed wires. -/
theorem decode_embedding (o : Wire n) :
    o.embed.decode = o.decode.map Input.embed := by
  rcases o with ⟨a, m⟩
  cases a with
  | none => cases m <;> rfl
  | proposer s => cases m <;> rfl
  | seat l i => cases l <;> cases m <;> rfl

/-- The complete wire representation retains the proposer at every ancestor. -/
theorem wire_embed_injective :
    Function.Injective (fun o : Wire n => (o.embed, o.identities)) := by
  intro a b h
  rcases a with ⟨aa, am⟩
  rcases b with ⟨ba, bm⟩
  have ha := congrArg (fun x => x.1.auth) h
  have hm := congrArg (fun x => x.1.payload) h
  have hi := congrArg Prod.snd h
  simp only [wire_embed_auth] at ha
  cases ha
  cases am <;> cases bm <;> simp_all [Wire.embed, Wire.identities]
  rename_i A B
  exact embed_injective (Prod.ext h.1 h.2)

/-- Lean combines the paper wire check with its parent-slot admission assertion. -/
theorem wellFormed_embedding (p : Params) (o : Wire p.n) :
    FGSA.wellFormed p o.embed = (wellFormed p o && parentSlotValid o) := by
  delta FGSA.wellFormed
  unfold wellFormed parentSlotValid
  rw [decode_embedding]
  cases h : o.decode with
  | none => rfl
  | some i =>
      cases i with
      | vote s i r => rfl
      | row i a => exact (Bool.and_true a.valid).symm
      | block s B =>
          cases B with
          | genesis =>
              have refuse (a b c d e f : Bool) :
                  (false && a && b && c && d && e && f) = false := rfl
              exact refuse _ _ _ _ _ _
          | node P t j r rows raw support =>
              change (_ && _ && _ && _ && _ && _ &&
                namedContentOk p (Block.node P t j r rows raw support).embed) = _
              rw [content_check_embedding]
              have hs : P.embed.erase.slot = P.slot := by
                rw [named_erase_slot, embed_slot]
              change ((P.embed.erase.node t r (packBody 0 rows) != .genesis) &&
                (s == t) && decide (P.embed.erase.slot < t) && _ && _ && _ && _) = _
              rw [hs]
              have hn : (P.embed.erase.node t r (packBody 0 rows) != .genesis) = true := by
                rfl
              rw [hn, Bool.true_and]
              have rearrange (a b c d e f : Bool) :
                  (a && b && c && d && e && f) = (a && (c && d) && e && f && b) := by
                simp only [Bool.and_left_comm, Bool.and_comm]
              refine (rearrange _ _ _ _ _ _).trans ?_
              apply congrArg (fun z : Bool => (s == t) && z && rows.all RowWire.valid &&
                (r == digestSpec p P.root t rows raw support) && decide (P.slot < t))
              delta validPayload
              apply congrArg (fun z : Bool => z && support.all (fun v => decide (v ∈ raw)))
              apply congrArg (fun f => raw.all f)
              funext v
              cases v.decode? <;> rfl



theorem refusal_embedding (p : Params) (o : Wire p.n) :
    FGSA.wellFormed p o.embed = false ↔
      wellFormed p o = false ∨ parentSlotValid o = false := by
  rw [wellFormed_embedding, Bool.and_eq_false_iff]

/-- The adapter adds the assigned-proposer assertion without moving it into the wire check. -/
theorem delivery_check_embedding (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    FGSA.wellFormed p (deliveryWire assigned o) =
      (wellFormed p o && admissionValid assigned o) := by
  unfold deliveryWire admissionValid
  split
  · simp_all only [wellFormed_embedding, Bool.true_and]
  · change false = _
    simp_all only [Bool.not_eq_true, Bool.false_and, Bool.and_false]

/-- Both placements of the pure checks have the same state effect for every continuation. -/
theorem checkedDelivery_embedding {σ : Type} (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (next : σ → σ) (state : σ) :
    checkedDelivery p assigned o next state =
      (if FGSA.wellFormed p (deliveryWire assigned o) then next state else state) := by
  rw [delivery_check_embedding]
  simp only [checkedDelivery, Bool.and_eq_true, ite_and]

/-- A paper wire rejection has no effect under Lean's combined check. -/
theorem wire_rejection_effect {σ : Type} (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (next : σ → σ) (state : σ) (h : wellFormed p o = false) :
    checkedDelivery p assigned o next state = state ∧
      (if FGSA.wellFormed p (deliveryWire assigned o) then next state else state) = state := by
  simp [checkedDelivery, delivery_check_embedding, h]

/-- A paper admission rejection also has no effect, even after a successful wire check. -/
theorem admission_rejection_effect {σ : Type} (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (next : σ → σ) (state : σ)
    (h : admissionValid assigned o = false) :
    checkedDelivery p assigned o next state = state ∧
      (if FGSA.wellFormed p (deliveryWire assigned o) then next state else state) = state := by
  simp [checkedDelivery, delivery_check_embedding, h]

end AvailableChain.FGSA.Spec
end
