import Mathlib

theorem CancellationLaw [CommRing α] [NoZeroDivisors α] (a b c : α) :
  (c*a = c*b) ∧ (c ≠ 0) → a = b := by
  . intro ⟨ca_eq_cb, c_n0⟩;
    rw [← sub_eq_zero, sub_eq_add_neg, neg_mul_eq_mul_neg, ← left_distrib] at ca_eq_cb;
    have a_plus_neg_b_0 := Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero ca_eq_cb) c_n0.elim;
    rwa [add_neg_eq_zero] at a_plus_neg_b_0;
