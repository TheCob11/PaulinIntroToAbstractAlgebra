import Mathlib

section SubgroupsCosetsLagrange
open Nat (card)

noncomputable def G_equiv_G_quo_S_prod_S [Group G] (S: Subgroup G) : G ≃ (G⧸S) × S :=
  let s_exists (x: G) := QuotientGroup.mk_out'_eq_mul S x
  let f (x: G) : (G⧸S) × S := ⟨⟦x⟧, (s_exists x).choose, SetLike.coe_mem _⟩
  let f_inv : (G⧸S) × S → G := fun (xS, s) ↦ xS.out' * s⁻¹
  have left_inv : Function.LeftInverse f_inv f := fun x ↦
    mul_inv_eq_iff_eq_mul.mpr (s_exists x).choose_spec
  have right_inv : Function.RightInverse f_inv f := fun (xS, ⟨s, hs⟩) ↦
    let x := xS.out';
    have left : ↑(x * s⁻¹) = xS := calc
      (x * s⁻¹ : G⧸S) = ↑(x * s⁻¹ * s) := (QuotientGroup.mk_mul_of_mem _ hs).symm
      _ = ↑x := congrArg (⟦·⟧) (inv_mul_cancel_right _ s)
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
  have hk : card G = card S * k := calc
    card G = card ((G⧸S)×S) := Nat.card_congr (G_equiv_G_quo_S_prod_S S)
    _ = k * card S := Nat.card_prod _ _
    _ = _ := mul_comm _ _
  ⟨k, hk⟩

end SubgroupsCosetsLagrange

section OrbitStabilizerSylow
open MulAction
open Function (Injective Surjective Bijective)

theorem orbit_stabilizer (G : Type u) {S : Type v} [Group G] [MulAction G S] (s: S) :
  Subgroup.index (stabilizer G s) = Nat.card (orbit G s) :=

  let G_quo_stab := G ⧸ stabilizer G s;
  let φ (xStab : G_quo_stab) : orbit G s :=
    ⟨xStab.exists_rep.choose • s, mem_orbit _ _⟩
  have φ_Bij : Bijective φ :=
    -- turns out defining these two functions allows for a lot of automatic proving
    have smul_s_eq_iff_coset_eq {x: G} {y: G} : (x•s = y•s) ↔ (@Eq G_quo_stab ⟦x⟧ ⟦y⟧) := by
      rw [smul_eq_iff_eq_inv_smul, Eq.comm, smul_smul]
      rw [← mem_stabilizer_iff]
      rw [← QuotientGroup.leftRel_apply, ← @Quotient.eq', @Quotient.mk'_eq_mk]
    have rep_choose_spec (xStab: G_quo_stab) := xStab.exists_rep.choose_spec;

    have φ_Surj : Surjective φ := by
      rw [Surjective, Subtype.forall]
      intro _ hs'
      obtain ⟨_, hx⟩ := Set.mem_range.mpr hs'
      subst hx
      simp_all only [φ, Subtype.mk.injEq, exists_eq]

    have φ_Inj : Injective φ := by
      rw [Injective]
      intros
      simp_all only [φ, Subtype.mk.injEq]
    ⟨φ_Inj, φ_Surj⟩
  Nat.card_eq_of_bijective φ φ_Bij

end OrbitStabilizerSylow
