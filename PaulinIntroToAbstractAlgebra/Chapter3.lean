import Mathlib

section SubgroupsCosetsLagrange
open scoped Pointwise
open Function (Injective Surjective Bijective)

-- set_option trace.Meta.Tactic.simp.rewrite true
theorem lagranges_theorem [Group G] (S: Subgroup G) : Nat.card S ∣ Nat.card G := by
  -- #check (λ (x: G⧸S) ↦ (Quotient.out' x•S : Set G)) _
  -- have xS_equiv_S {x: G} : (x•S : Set G) ≃ S :=
  --   let φ (s: S) : (x • S : Set G) := ⟨x * s, mem_leftCoset x (Subtype.coe_prop s)⟩
  --   have φ_Bij : Bijective φ :=
  --     have φ_Inj : Injective φ := by
  --       intros _ _ _;
  --       simp_all only [Subtype.mk.injEq, mul_right_inj, SetLike.coe_eq_coe, φ]

  --     have φ_Surj : Surjective φ := by
  --       intro ⟨_, prop⟩
  --       simp_all only [Subtype.exists, φ, Subtype.mk.injEq, exists_prop]
  --       exact prop
  --     ⟨φ_Inj, φ_Surj⟩;
  --   (Equiv.ofBijective φ φ_Bij).symm

  -- -- have card_xS_eq_card_S {x: G} : Nat.card (x • S : Set G) = Nat.card S :=
  -- --   Nat.card_congr xS_equiv_S;
  -- -- #check Quotient.out_injective
  -- have card_xS_eq_card_S {xS: G⧸S} : Nat.card (Quotient.out' xS • S : Set G) = Nat.card S :=
  --   Nat.card_congr (@xS_equiv_S (Quotient.out' xS))

  -- use Nat.card (G⧸S)
  have G_equiv_G_quo_S_prod_S : G ≃ (G⧸S) × S :=
    -- #reduce λ x ↦ ⟦x⟧
    -- #check λ x ↦ Quotient.mk (QuotientGroup.leftRel S) x
    -- #check λ (x: G) ↦ (x • (Quotient.mk (QuotientGroup.leftRel S) x) : S)
    -- #check Quotient.out
    let s_exists (x: G) := QuotientGroup.mk_out'_eq_mul S x
    let f (x: G) : (G⧸S) × S := ⟨⟦x⟧, (s_exists x).choose, SetLike.coe_mem _⟩
    let f_inv : (G⧸S) × S → G | (xS, s) => xS.out' * s⁻¹
    have left_inv : Function.LeftInverse f_inv f
    | x => mul_inv_eq_iff_eq_mul.mpr (s_exists x).choose_spec
    let right_inv : Function.RightInverse f_inv f
    | (xS, ⟨s, hs⟩) =>
      let x := xS.out';
      have left : ↑(x * s⁻¹) = xS := calc
        (x * s⁻¹ : G⧸S) = ↑(x * s⁻¹ * s) := (QuotientGroup.mk_mul_of_mem _ hs).symm
        _ = ↑x := congrArg (⟦·⟧) (inv_mul_cancel_right _ s)
        _ = xS := QuotientGroup.out_eq' xS

      let right : (s_exists (x * s⁻¹)).choose = ⟨s, hs⟩ := by
        have h := (s_exists (x * s⁻¹)).choose_spec;
        simp_rw [left] at h
        rw [← @mul_inv_eq_iff_eq_mul] at h
        rw [@mul_left_cancel_iff] at h
        simp_all only [inv_inj]
        exact SetCoe.ext h

      (Prod.mk.injEq _ _ _ _).mpr ⟨left, right⟩

    ⟨f, f_inv, left_inv, right_inv⟩

    -- have f_inj : Injective f := by
    --   unfold Injective
    --   intros x1 x2 hx
    --   simp [f] at hx
    --   obtain ⟨h_GS, h_S⟩ := hx
    --   have ⟨s1, hs1⟩ := (QuotientGroup.mk_out'_eq_mul S x1)
    --   have ⟨s2, hs2⟩ := (QuotientGroup.mk_out'_eq_mul S x2)
    --   replace h_GS : (x1: G⧸S) = (x2: G⧸S) := h_GS
    --   rw [h_GS] at hs1
    --   sorry

    -- have f_surj : Surjective f := sorry
  have h : Nat.card G = Nat.card S * Nat.card (G⧸S) := calc
    Nat.card G = Nat.card ((G⧸S)×S) := Nat.card_congr G_equiv_G_quo_S_prod_S
    _ = Nat.card (G⧸S) * Nat.card S := Nat.card_prod _ _
    _ = _ := mul_comm _ _
  exact ⟨Nat.card (G⧸S), h⟩

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
