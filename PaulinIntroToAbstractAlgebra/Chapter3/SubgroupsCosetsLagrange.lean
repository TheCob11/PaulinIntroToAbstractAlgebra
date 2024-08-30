import Mathlib
open Nat (card)

noncomputable def G_equiv_G_quo_S_prod_S [Group G] (S: Subgroup G) : G ≃ (G⧸S) × S :=
  let s_exists (x: G) := QuotientGroup.mk_out'_eq_mul S x
  let f (x: G) : (G⧸S) × S := ⟨⟦x⟧, (s_exists x).choose, SetLike.coe_mem _⟩
  let f_inv : (G⧸S) × S → G := fun (xS, s) ↦ xS.out' * s⁻¹
  have left_inv : Function.LeftInverse f_inv f := fun x ↦
    mul_inv_eq_iff_eq_mul.mpr (s_exists x).choose_spec
  have right_inv : Function.RightInverse f_inv f := fun (xS, ⟨s, hs⟩) ↦
    let x := xS.out';
    have left : ↑(x * s⁻¹) = xS := calc (x * s⁻¹ : G⧸S)
      _ = ↑(x * s⁻¹ * s) := (QuotientGroup.mk_mul_of_mem _ hs).symm
      _ = ↑x := inv_mul_cancel_right _ s ▸ rfl
      _ = xS := xS.out_eq'

    have right : (s_exists (x * s⁻¹)).choose = ⟨s, hs⟩ := by
      have h := (s_exists (x * s⁻¹)).choose_spec;
      simp_rw [left] at h ⊢
      rw [← mul_inv_eq_iff_eq_mul,
          mul_left_cancel_iff,
          inv_inj] at h
      exact SetCoe.ext h
    (Prod.mk.injEq _ _ _ _).mpr ⟨left, right⟩
  ⟨f, f_inv, left_inv, right_inv⟩

theorem lagranges_theorem [Group G] (S: Subgroup G) : card S ∣ card G :=
  let k := card (G⧸S);
  have hk : card G = card S * k := calc card G
    _ = card ((G⧸S)×S) := Nat.card_congr (G_equiv_G_quo_S_prod_S S)
    _ = k * card S := Nat.card_prod _ _
    _ = _ := mul_comm _ _
  ⟨k, hk⟩

-- example corollary listed below the thm
theorem prime_order_subgroups_bot_top [Group G] [hG : Fact (card G).Prime] {S: Subgroup G} :
  S = ⊥ ∨ S = ⊤ :=
  have _G_Finite := Nat.finite_of_card_ne_zero hG.out.ne_zero -- necessary for eq_top_of_card_eq
  have card_eq_1_or_p : card S = 1 ∨ card S = card G := (Nat.dvd_prime hG.out).mp (lagranges_theorem S)
  Or.imp (Subgroup.eq_bot_of_card_eq S) (Subgroup.eq_top_of_card_eq S) card_eq_1_or_p
