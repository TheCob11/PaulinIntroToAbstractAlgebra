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

-- example corollary listed below the thm
theorem prime_order_subgroups_bot_top [Group G] [hG : Fact (card G).Prime] {S: Subgroup G} :
  S = ⊥ ∨ S = ⊤ :=
  have _G_Finite := Nat.finite_of_card_ne_zero hG.out.ne_zero -- necessary for eq_top_of_card_eq
  have card_eq_1_or_p : card S = 1 ∨ card S = card G := (Nat.dvd_prime hG.out).mp (lagranges_theorem S)
  Or.imp (Subgroup.eq_bot_of_card_eq S) (Subgroup.eq_top_of_card_eq S) card_eq_1_or_p

end SubgroupsCosetsLagrange

section FinitelyGeneratedGroups

theorem prime_order_cyclic [Group G] [h: Fact (Nat.card G).Prime] : IsCyclic G :=
  have _G_Finite : Finite G := Nat.finite_of_card_ne_zero h.out.ne_zero
  have _G_Fintype : Fintype G := Fintype.ofFinite G
  have _G_FintypeG_Nontrivial : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp
    (Fintype.card_eq_nat_card ▸ h.out.one_lt)
  have ⟨x, hx⟩ := exists_ne (1: G)
  let gp_x := Subgroup.zpowers x
  have gp_x_not_bot: gp_x ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx
  have gp_x_top: gp_x = ⊤ :=
    Or.resolve_left prime_order_subgroups_bot_top gp_x_not_bot
  ⟨x, (Subgroup.eq_top_iff' gp_x).mp gp_x_top⟩

def cyclic_abelian [Group G] [h: IsCyclic G] : CommGroup G := .mk <| fun a b ↦
  have ⟨x, hx⟩ := h.exists_generator;
  have ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hx a)
  have ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hx b)
  calc a * b = x^r * x^s := hs ▸ hr ▸ rfl
       _ = x ^ (r + s) := (zpow_add _ _ _).symm
       _ = x ^ (s + r) := congrArg _ (add_comm _ _)
       _ = x ^ s * x ^ r := zpow_add _ _ _
       _ = b * a := hr ▸ hs ▸ rfl

noncomputable def cyclic_infinite_Z [Group G] [Infinite G] [hG: IsCyclic G] :
  G ≃* Multiplicative ℤ :=
  -- for some reason ∃ can't be unboxed like ⟨x, hx⟩ in def (not theorem)
  let x := hG.exists_generator.choose;
  have hx : (g: G) → g ∈ Subgroup.zpowers x := hG.exists_generator.choose_spec;
  have order_x_0 : orderOf x = 0 := Infinite.orderOf_eq_zero_of_forall_mem_zpowers hx
  have not_isOfFinOrder_x : ¬IsOfFinOrder x := orderOf_eq_zero_iff.mp order_x_0
  have h_pow (g: G) : ∃(k: ℤ), x ^ k = g := Subgroup.mem_zpowers_iff.mp (hx g);
  let φ (g: G) : Multiplicative ℤ := (h_pow g).choose;
  have φ_pow {n: ℤ} : φ (x ^ n) = n :=
    have h_spec := (h_pow (x^n)).choose_spec
    injective_zpow_iff_not_isOfFinOrder.mpr not_isOfFinOrder_x h_spec
  let φ_inv (n: ℤ) : G := x ^ n;
  have left_inv : Function.LeftInverse φ_inv φ := fun g => (h_pow g).choose_spec
  have right_inv : Function.RightInverse φ_inv φ := @φ_pow
  let φ_equiv : G ≃ Multiplicative ℤ := ⟨φ, φ_inv, left_inv, right_inv⟩
  have map_mul' (g₁ g₂ : G) : φ (g₁ * g₂) = φ g₁ * φ g₂ :=
    have ⟨a, ha⟩ := h_pow g₁;
    have ⟨b, hb⟩ := h_pow g₂;
    calc φ (g₁ * g₂) = φ (x ^ a * x ^ b) := ha ▸ hb ▸ rfl
         _ = φ (x ^ (a + b)) := congrArg φ (zpow_add _ _ _).symm
         _ = a + b := φ_pow
         _ = φ (x ^ a) * φ (x ^ b) := φ_pow.symm ▸ φ_pow.symm ▸ rfl
         _ = φ g₁ * φ g₂ := ha ▸ hb ▸ rfl
  MulEquiv.mk φ_equiv map_mul'

noncomputable def cyclic_finite_ZMod [Group G] [Fintype G] [hG: IsCyclic G] :
  G ≃* Multiplicative (ZMod (Fintype.card G)) :=
  let m := Fintype.card G;
  let ZM := ZMod m;
  have card_eq : m = Fintype.card (Multiplicative ZM) :=
    (Fintype.card_multiplicative ZM ▸ ZMod.card m).symm;
  -- for some reason ∃ can't be unboxed like ⟨x, hx⟩ in def (not theorem)
  let x := hG.exists_generator.choose;
  have hx : (g: G) → g ∈ Subgroup.zpowers x := hG.exists_generator.choose_spec;
  have order_x_eq_m : orderOf x = m := orderOf_eq_card_of_forall_mem_zpowers hx
  have _m_NeZero : NeZero m := NeZero.of_pos (order_x_eq_m ▸ orderOf_pos x)
  have h_pow (g: G) : ∃(k: ℤ), x ^ k = g := Subgroup.mem_zpowers_iff.mp (hx g);
  let φ (g: G) : Multiplicative ZM := ((h_pow g).choose: ZM);
  let φ_inv (n: ZM) := x ^ (n.val: ℤ)
  have zpow_zmpow_eq (a: ℤ) (b: ZM) : (x ^ a = x ^ (b.val: ℤ)) ↔ (a = b) := by
    rw [zpow_eq_zpow_iff_modEq,
        ← ZMod.intCast_eq_intCast_iff, order_x_eq_m,
        ← ZMod.cast_eq_val, ZMod.intCast_zmod_cast b]
  have right_inv : Function.RightInverse φ_inv φ := fun n =>
    have ex := h_pow (φ_inv n)
    (zpow_zmpow_eq ex.choose n).mp ex.choose_spec
  let φ_Equiv : G ≃ Multiplicative ZM :=
    Equiv.ofRightInverseOfCardLE (Nat.le_of_eq card_eq) φ φ_inv right_inv
  have left_inv := φ_Equiv.left_inv
  have map_mul' (g₁ g₂ : G) : φ (g₁ * g₂) = φ g₁ * φ g₂ :=
    let a := φ g₁
    let b := φ g₂
    let ha := left_inv g₁
    let hb := left_inv g₂
    calc φ (g₁ * g₂) = φ (x ^ (a.val: ℤ) * x ^ (b.val: ℤ)) := ha ▸ hb ▸ rfl
         _ = φ (x ^ ((a.val: ℤ) + (b.val: ℤ))) := congrArg φ (zpow_add _ _ _).symm
         _ = φ (x ^ ((a * b).val : ℤ)) :=
          -- yikes
          have : x ^ ((a.val: ℤ) + (b.val: ℤ)) = x ^ ((a*b).val: ℤ) := by
            unfold_let a b φ ZM
            simp_all only [ZMod.natCast_val, Int.cast_add, ZMod.intCast_cast, ZMod.cast_intCast']
            rfl
          congrArg φ this
         _ = a * b := right_inv _
         _ = φ (x ^ (a.val: ℤ)) * φ (x ^ (b.val: ℤ)) := right_inv _ ▸ right_inv _ ▸ rfl
         _ = φ g₁ * φ g₂ := ha ▸ hb ▸ rfl
  MulEquiv.mk φ_Equiv map_mul'

end FinitelyGeneratedGroups

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
