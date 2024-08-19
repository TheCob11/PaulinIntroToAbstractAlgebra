import Mathlib

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
