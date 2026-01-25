import Mathlib.Algebra.Ring.Nat
import Mathlib.Order.Basic
import Mathlib.Tactic

variable
  -- M is the wrapping point of the unsigned integer representation. So if we're
  -- dealing with uint32, then M is 1 more than the maximum representable value
  -- in uint32.
  (M : ℕ)
  -- Since all integer types are non-trivial (uint8, uint16, uint32, ..., but we
  -- never see a uint0), it is safe to assume that M is positive.
  (hM₀ : 0 < M)

-- Let (a b : uint32). This theorem tells us that we can check if there will be
-- multiplcation overflow upon `a * b` by simply checking if `0 < a`, and that
-- `a * b / a != b`. (note that the modulo-M operation will be the part of the
-- overflow).
include hM₀ in
theorem UintMultplicationOverflow (a b : ℕ) :
  M ≤ a * b -- multiplication overflow
  ↔ 0 < a ∧ a * b % M / a ≠ b := by
  rcases Nat.eq_zero_or_pos b with hb₀ | hb₀
  · -- b = 0
    subst hb₀
    rw [mul_zero]
    constructor
    · intro h
      exact False.elim (h.not_gt hM₀)
    · intro ⟨_, h⟩
      refine False.elim ?_
      rw [Nat.zero_mod, Nat.zero_div] at h
      exact false_of_ne h
  · -- b > 0
    constructor
    · intro hab
      have hab₀ : 0 < a * b := Nat.lt_of_lt_of_le hM₀ hab
      have ha₀ : 0 < a := Nat.pos_of_mul_pos_right hab₀
      have : a * b % M / a ≤ (a * b - M) / a := by
        refine Nat.div_le_div_right ?_
        rw [Nat.mod_eq_sub]
        refine Nat.sub_le_sub_left ?_ (a * b)
        refine Nat.le_mul_of_pos_right M ?_
        exact Nat.div_pos_iff.mpr ⟨hM₀, hab⟩
      refine ⟨ha₀, ?_⟩
      refine Nat.ne_of_lt ?_
      refine this.trans_lt ?_
      rw [Nat.div_lt_iff_lt_mul ha₀, mul_comm]
      exact Nat.sub_lt (Nat.mul_pos hb₀ ha₀) hM₀
    · intro ⟨ha₀, hne⟩
      refine Nat.le_of_not_lt ?_
      by_contra hab
      have : a * b % M = a * b := Nat.mod_eq_of_lt hab
      rw [this, Nat.mul_div_cancel_left b ha₀] at hne
      exact false_of_ne hne
