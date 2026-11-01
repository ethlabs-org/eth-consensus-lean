module
public import Mathlib.Data.Nat.Size

@[expose] public section

namespace AvailableChain

/-! A length-delimited pairing of natural numbers.

`epair a b` puts the bits of `b` below the bits of `a`, and codes the bit
length of `b` in a delimiter. The code grows by the lengths of `a` and `b`
and a small term for the length of `b`, so nested pairs stay small.

The definitions use only `+`, `-`, `*`, `/`, `%`, `2 ^ ·` and `>>>`, with
structural recursion on a fuel. The kernel has fast paths for these
operations, so `decide +kernel` can evaluate codes with many bits. The fast
path for `2 ^ k` holds only for `k < 2 ^ 24`, so each component must have
fewer than `2 ^ 24` bits. `Nat.log2` has no fast path, so the definitions do
not use it. -/

/-- Phase 1 of `bitLen`: double `w` until `n >>> w = 0`. -/
def bitLenDouble : Nat → Nat → Nat → Nat
  | 0, _, w => w
  | fuel + 1, n, w => if n >>> w = 0 then w else bitLenDouble fuel n (2 * w)

/-- Phase 2 of `bitLen`: a binary search for the bit length inside
`(lo, hi]`. -/
def bitLenSearch : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, hi => hi
  | fuel + 1, n, lo, hi =>
    if hi ≤ lo + 1 then hi
    else
      let mid := (lo + hi) / 2
      if n >>> mid = 0 then bitLenSearch fuel n lo mid
      else bitLenSearch fuel n mid hi

/-- The bit length of `n`: the least `k` with `n < 2 ^ k`. -/
def bitLen (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let w := bitLenDouble (n + 1) n 1
    bitLenSearch (n + 1) n (w / 2) w

/-- Step of `tz`: the number of factors 2 in `m`, with a fuel. -/
def tzAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, m =>
    if m = 0 then 0
    else if m % 2 = 0 then tzAux fuel (m / 2) + 1
    else 0

/-- The number of trailing zero bits of `m` (`0` for `m = 0`). -/
def tz (m : Nat) : Nat := tzAux (m + 1) m

/-- A pair with a delimiter: `lpair a b + 1 = 2 ^ k * odd`, where
`k = bitLen b`. The odd factor holds `a` above the `k` bits of `b`. -/
def lpair (a b : Nat) : Nat :=
  2 ^ bitLen b * (2 * (a * 2 ^ bitLen b + b) + 1) - 1

/-- The first component of `lpair`. -/
def lfst (z : Nat) : Nat :=
  (z + 1) / 2 ^ tz (z + 1) / 2 / 2 ^ tz (z + 1)

/-- The second component of `lpair`. -/
def lsnd (z : Nat) : Nat :=
  (z + 1) / 2 ^ tz (z + 1) / 2 % 2 ^ tz (z + 1)

/-- The length-delimited pairing: the bits of `b` below the bits of `a`, and
`lpair` codes the bit length of `b`, not `b`. -/
def epair (a b : Nat) : Nat :=
  lpair (a * 2 ^ bitLen b + b) (bitLen b)

/-- The first component of `epair`. -/
def efst (e : Nat) : Nat := lfst e / 2 ^ lsnd e

/-- The second component of `epair`. -/
def esnd (e : Nat) : Nat := lfst e % 2 ^ lsnd e

/-- A list code: `0` ends the list, and each element adds one `epair` level.
The code keeps the order and the duplicates of the list. -/
def encList {α : Type} (enc : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => epair (enc x) (encList enc xs) + 1

/-- An option code: `0` for `none`. -/
def encOption {α : Type} (enc : α → Nat) : Option α → Nat
  | none => 0
  | some x => enc x + 1

/-- A Boolean code. -/
def encBool : Bool → Nat
  | false => 0
  | true => 1

/-! ### Bit length -/

private theorem shiftRight_eq_zero_iff (n w : Nat) : n >>> w = 0 ↔ n < 2 ^ w := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos w)]

private theorem bitLenDouble_spec (fuel n w : Nat) (hw : 1 ≤ w)
    (hlo : w / 2 < Nat.size n) (hfuel : Nat.size n ≤ w + fuel) :
    (bitLenDouble fuel n w) / 2 < Nat.size n ∧
      Nat.size n ≤ bitLenDouble fuel n w := by
  induction fuel generalizing w with
  | zero => exact ⟨hlo, by simpa using! hfuel⟩
  | succ fuel ih =>
    simp only [bitLenDouble]
    split
    next h => exact ⟨hlo, Nat.size_le.2 ((shiftRight_eq_zero_iff n w).1 h)⟩
    next h =>
      have hw' : w < Nat.size n :=
        Nat.lt_size.2 (Nat.le_of_not_lt fun h' => h ((shiftRight_eq_zero_iff n w).2 h'))
      exact ih (2 * w) (by omega) (by omega) (by omega)

private theorem bitLenSearch_spec (fuel n lo hi : Nat) (hlo : lo < Nat.size n)
    (hhi : Nat.size n ≤ hi) (hfuel : hi ≤ lo + 1 + fuel) :
    bitLenSearch fuel n lo hi = Nat.size n := by
  induction fuel generalizing lo hi with
  | zero => simp only [bitLenSearch]; omega
  | succ fuel ih =>
    simp only [bitLenSearch]
    split
    next => omega
    split
    next h₁ h₂ =>
      exact ih _ _ hlo (Nat.size_le.2 ((shiftRight_eq_zero_iff n _).1 h₂)) (by omega)
    next h₁ h₂ =>
      have hmid : (lo + hi) / 2 < Nat.size n :=
        Nat.lt_size.2 (Nat.le_of_not_lt fun h' => h₂ ((shiftRight_eq_zero_iff n _).2 h'))
      exact ih _ _ hmid hhi (by omega)

/-- `bitLen` is `Nat.size`. The fuel `n + 1` is enough for both phases. -/
theorem bitLen_eq_size (n : Nat) : bitLen n = Nat.size n := by
  unfold bitLen
  split
  next h => simp [h, Nat.size_zero]
  next h =>
    have hpos : 0 < Nat.size n := Nat.size_pos.2 (Nat.pos_of_ne_zero h)
    have hself : Nat.size n ≤ n := Nat.size_le.2 n.lt_two_pow_self
    obtain ⟨hlo, hhi⟩ := bitLenDouble_spec (n + 1) n 1 (Nat.le_refl 1) (by omega) (by omega)
    exact bitLenSearch_spec _ _ _ _ hlo hhi (by omega)

/-- The bit length of `0` is `0`. -/
theorem bitLen_zero : bitLen 0 = 0 := by simp [bitLen_eq_size, Nat.size_zero]

/-- Every `n` is below `2 ^ bitLen n`. -/
theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := by
  rw [bitLen_eq_size]; exact Nat.lt_size_self n

/-- A nonzero `n` has its top bit at `bitLen n - 1`. -/
theorem two_pow_bitLen_sub_one_le {n : Nat} (h : n ≠ 0) : 2 ^ (bitLen n - 1) ≤ n := by
  rw [bitLen_eq_size]
  have : 0 < Nat.size n := Nat.size_pos.2 (Nat.pos_of_ne_zero h)
  exact Nat.lt_size.1 (by omega)

/-- The same bit length in terms of `Nat.log2`, for proofs only. -/
theorem bitLen_eq_log2 (n : Nat) : bitLen n = if n = 0 then 0 else Nat.log2 n + 1 := by
  split
  next h => rw [h, bitLen_zero]
  next h =>
    apply Nat.le_antisymm
    · rw [bitLen_eq_size]; exact Nat.size_le.2 (Nat.lt_log2_self)
    · have := two_pow_bitLen_sub_one_le h
      have := (Nat.log2_lt h).2 (lt_two_pow_bitLen n)
      omega

/-- `bitLen n ≤ k` exactly when `n < 2 ^ k`. -/
theorem bitLen_le_iff {n k : Nat} : bitLen n ≤ k ↔ n < 2 ^ k := by
  rw [bitLen_eq_size]; exact Nat.size_le

/-! ### Trailing zeros -/

private theorem tzAux_two_pow_mul (r : Nat) (hr : r % 2 = 1) :
    ∀ k fuel, k < fuel → tzAux fuel (2 ^ k * r) = k := by
  intro k
  induction k with
  | zero =>
    intro fuel hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [tzAux, hr]
  | succ k ih =>
    intro fuel hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hne : 2 ^ (k + 1) * r ≠ 0 :=
      Nat.mul_ne_zero (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)) (by omega)
    have hdiv : 2 ^ (k + 1) * r / 2 = 2 ^ k * r := by
      rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide)]
    have hmod : 2 ^ (k + 1) * r % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_mod_left]
    simp only [tzAux, hne, hmod, hdiv, ite_false, ite_true]
    rw [ih fuel (by omega)]

/-- `tz` finds the exact power of two in `2 ^ k * r` for an odd `r`. -/
theorem tz_two_pow_mul {k r : Nat} (hr : r % 2 = 1) : tz (2 ^ k * r) = k := by
  unfold tz
  apply tzAux_two_pow_mul r hr
  have : 2 ^ k ≤ 2 ^ k * r := Nat.le_mul_of_pos_right _ (by omega)
  have := k.lt_two_pow_self
  omega

private theorem exists_two_pow_mul_odd :
    ∀ fuel m, m ≠ 0 → m ≤ fuel → ∃ k r, r % 2 = 1 ∧ m = 2 ^ k * r := by
  intro fuel
  induction fuel with
  | zero => intro m h₁ h₂; omega
  | succ fuel ih =>
    intro m h₁ h₂
    by_cases h : m % 2 = 0
    · obtain ⟨k, r, hr, hm⟩ := ih (m / 2) (by omega) (by omega)
      exact ⟨k + 1, r, hr, by rw [Nat.pow_succ, Nat.mul_right_comm, ← hm]; omega⟩
    · exact ⟨0, m, by omega, by simp⟩

/-- `tz` is exact: every nonzero `m` is `2 ^ tz m` times an odd number. -/
theorem tz_spec {m : Nat} (h : m ≠ 0) : ∃ r, r % 2 = 1 ∧ m = 2 ^ tz m * r := by
  obtain ⟨k, r, hr, rfl⟩ := exists_two_pow_mul_odd _ m h (Nat.le_refl m)
  exact ⟨r, hr, by rw [tz_two_pow_mul hr]⟩

/-! ### Pairing laws -/

private theorem two_pow_mul_add_div {a b k : Nat} (hb : b < 2 ^ k) :
    (a * 2 ^ k + b) / 2 ^ k = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hb,
    Nat.zero_add]

private theorem two_pow_mul_add_mod {a b k : Nat} (hb : b < 2 ^ k) :
    (a * 2 ^ k + b) % 2 ^ k = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The factorisation of `lpair`. -/
theorem lpair_add_one (a b : Nat) :
    lpair a b + 1 = 2 ^ bitLen b * (2 * (a * 2 ^ bitLen b + b) + 1) := by
  unfold lpair
  have : 0 < 2 ^ bitLen b * (2 * (a * 2 ^ bitLen b + b) + 1) :=
    Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  omega

private theorem lpair_decode (a b : Nat) :
    (lpair a b + 1) / 2 ^ tz (lpair a b + 1) / 2 = a * 2 ^ bitLen b + b := by
  rw [lpair_add_one, tz_two_pow_mul (by omega),
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  omega

/-- `lfst` inverts `lpair` in the first argument. -/
theorem lfst_lpair (a b : Nat) : lfst (lpair a b) = a := by
  unfold lfst
  rw [lpair_decode, lpair_add_one, tz_two_pow_mul (by omega)]
  exact two_pow_mul_add_div (lt_two_pow_bitLen b)

/-- `lsnd` inverts `lpair` in the second argument. -/
theorem lsnd_lpair (a b : Nat) : lsnd (lpair a b) = b := by
  unfold lsnd
  rw [lpair_decode, lpair_add_one, tz_two_pow_mul (by omega)]
  exact two_pow_mul_add_mod (lt_two_pow_bitLen b)

/-- `efst` inverts `epair` in the first argument, for every input. -/
@[simp] theorem efst_epair (a b : Nat) : efst (epair a b) = a := by
  unfold efst epair
  rw [lfst_lpair, lsnd_lpair]
  exact two_pow_mul_add_div (lt_two_pow_bitLen b)

/-- `esnd` inverts `epair` in the second argument, for every input. -/
@[simp] theorem esnd_epair (a b : Nat) : esnd (epair a b) = b := by
  unfold esnd epair
  rw [lfst_lpair, lsnd_lpair]
  exact two_pow_mul_add_mod (lt_two_pow_bitLen b)

/-- `epair` is injective in the pair. -/
theorem epair_inj {a b c d : Nat} (h : epair a b = epair c d) : a = c ∧ b = d :=
  ⟨by rw [← efst_epair a b, h, efst_epair], by rw [← esnd_epair a b, h, esnd_epair]⟩

private theorem mul_two_pow_add_lt {x y p q : Nat} (hx : x < 2 ^ p) (hy : y < 2 ^ q) :
    x * 2 ^ q + y < 2 ^ (p + q) := by
  rw [Nat.pow_add]
  calc x * 2 ^ q + y < (x + 1) * 2 ^ q := by rw [Nat.succ_mul]; omega
    _ ≤ 2 ^ p * 2 ^ q := Nat.mul_le_mul_right _ hx

/-- The size law: nesting in the second argument adds the lengths. -/
theorem bitLen_epair_le (a b : Nat) :
    bitLen (epair a b) ≤ bitLen a + bitLen b + 2 * bitLen (bitLen b) + 1 := by
  rw [bitLen_le_iff]
  have hc := mul_two_pow_add_lt (lt_two_pow_bitLen a) (lt_two_pow_bitLen b)
  have hu := mul_two_pow_add_lt hc (lt_two_pow_bitLen (bitLen b))
  have he := lpair_add_one (a * 2 ^ bitLen b + b) (bitLen b)
  unfold epair
  generalize a * 2 ^ bitLen b + b = c at hc hu he
  generalize bitLen a + bitLen b = p at hc hu
  generalize bitLen (bitLen b) = k at hu he ⊢
  have h2 : 2 * (c * 2 ^ k + bitLen b) + 1 ≤ 2 ^ (p + k + 1) := by
    rw [Nat.pow_succ]; omega
  have h3 : 2 ^ k * (2 * (c * 2 ^ k + bitLen b) + 1) ≤ 2 ^ k * 2 ^ (p + k + 1) :=
    Nat.mul_le_mul_left _ h2
  rw [← Nat.pow_add] at h3
  have : k + (p + k + 1) = p + 2 * k + 1 := by omega
  rw [this] at h3
  omega

/-! ### Container codes -/

/-- An injective element code gives an injective list code. -/
theorem encList_inj {α : Type} {enc : α → Nat} (h : Function.Injective enc) :
    Function.Injective (encList enc) := by
  intro xs
  induction xs with
  | nil => intro ys hys; cases ys with
    | nil => rfl
    | cons y ys => simp [encList] at hys
  | cons x xs ih => intro ys hys; cases ys with
    | nil => simp [encList] at hys
    | cons y ys =>
      simp only [encList, Nat.add_right_cancel_iff] at hys
      obtain ⟨hxy, hrest⟩ := epair_inj hys
      rw [h hxy, ih hrest]

/-- An injective element code gives an injective option code. -/
theorem encOption_inj {α : Type} {enc : α → Nat} (h : Function.Injective enc) :
    Function.Injective (encOption enc) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [encOption, h.eq_iff]

/-- The Boolean code is injective. -/
theorem encBool_inj : Function.Injective encBool := by
  intro x y h
  cases x <;> cases y <;> simp_all [encBool]

end AvailableChain
end
