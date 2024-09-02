import Mathlib
open MulAction
open Function (Injective Surjective Bijective)

lemma mem_subgroup_iff_quotient_eq [Group G] {S: Subgroup G} {x y : G} :
  x⁻¹*y ∈ S ↔ @Eq (G ⧸ S) ⟦x⟧ ⟦y⟧ :=
  by rw [← QuotientGroup.leftRel_apply, ← @Quotient.eq']; rfl

theorem orbit_stabilizer (G : Type u) {S : Type v} [Group G] [MulAction G S] (s: S) :
  Subgroup.index (stabilizer G s) = Nat.card (orbit G s) :=

  let stab_s := stabilizer G s
  let φ (xStab : G⧸stab_s) : orbit G s :=
    ⟨xStab.exists_rep.choose • s, mem_orbit _ _⟩
  have φ_Bij : Bijective φ :=
    -- turns out defining these two functions allows for a lot of automatic proving
    have smul_s_eq_iff_coset_eq {x y: G} : x•s = y•s ↔ ⟦x⟧ = ⟦y⟧ := calc
      _ ↔ s = x⁻¹•y•s := smul_eq_iff_eq_inv_smul x
      _ ↔ s = (x⁻¹ * y)•s := smul_smul x⁻¹ y s ▸ Iff.rfl
      _ ↔ (x⁻¹ * y) ∈ stab_s := comm
      _ ↔ ⟦x⟧ = ⟦y⟧ := mem_subgroup_iff_quotient_eq
    have rep_choose_spec (xStab: G⧸stab_s) := xStab.exists_rep.choose_spec;

    have φ_Surj : Surjective φ := fun ⟨_, hs'⟩ ↦ by
      have ⟨_, hx⟩ := Set.mem_range.mpr hs'
      subst hx
      simp_all only [φ, Subtype.mk.injEq]
      exact exists_eq

    have φ_Inj : Injective φ := fun _ _ _ ↦ by simp_all only [φ, Subtype.mk.injEq]
    ⟨φ_Inj, φ_Surj⟩
  Nat.card_eq_of_bijective φ φ_Bij
