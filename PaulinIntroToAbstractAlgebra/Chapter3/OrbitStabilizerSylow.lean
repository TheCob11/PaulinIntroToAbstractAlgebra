import Mathlib
open MulAction
open Function (Injective Surjective Bijective)

lemma mem_subgroup_iff_quotient_eq [Group G] {S: Subgroup G} {x y : G} :
  x⁻¹*y ∈ S ↔ @Eq (G ⧸ S) ⟦x⟧ ⟦y⟧ :=
  by rw [← QuotientGroup.leftRel_apply, ← @Quotient.eq']; rfl

theorem orbit_stabilizer (G: Type*) [Group G] [MulAction G S] (s: S) :
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

-- corollary listed in the book
theorem card_eq_card_orbit_times_card_stabilizer [Group G] [MulAction G S] (s: S) :
  Nat.card G = Nat.card (orbit G s) * Nat.card (stabilizer G s) := Trans.trans
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer G s))
    (orbit_stabilizer G s ▸ rfl)

lemma singleton_conj_iff_mem_center [Group G] (g: G):
  g ∈ Subgroup.center G ↔ (orbit (ConjAct G) g) = {g} :=
  let Cg := orbit (ConjAct G) g
  have mp (h: g ∈ Subgroup.center G) : Cg = {g} :=
    have g_mem : g ∈ Cg := orbit_eq_iff.mp rfl
    have : g ∈ MulAction.fixedPoints (ConjAct G) G :=
      ConjAct.fixedPoints_eq_center (G := G) ▸ h
    have : ∀a' ∈ Cg, a' = g := MulAction.mem_fixedPoints'.mp this
    have : Cg.Subsingleton := Set.subsingleton_of_forall_eq g this
    Set.ext fun _ ↦ ⟨(this · g_mem), (· ▸ g_mem)⟩
  have mpr (h: Cg = {g}) : g ∈ Subgroup.center G :=
    have : ∀a' ∈ Cg, a' = g := fun _ ha ↦ Set.mem_singleton_iff.mp (h ▸ ha)
    have : g ∈ MulAction.fixedPoints (ConjAct G) G :=
      MulAction.mem_fixedPoints'.mpr this
    ConjAct.fixedPoints_eq_center.subst this
  ⟨mp, mpr⟩

theorem center_ne_bot_of_prime_pow_order
  [Group G] [Fintype G] (hG: IsPrimePow (Fintype.card G)):
  Subgroup.center G ≠ ⊥ := fun h ↦
  have _ := Classical.dec
  let Conj := ConjAct G
  have ⟨p, n, ⟨hp, n_pos, hpn⟩⟩ := hG
  have p_prime := hp.nat_prime
  have sum_card_conj : ∑x: ConjClasses G, Fintype.card x.carrier = p ^ n := hpn ▸
    Finset.sum_congr
      rfl
      (fun x _ ↦ @Set.toFinset_card G (ConjClasses.carrier x) _)
    ▸ sum_conjClasses_card_eq_card G
  have card_conj1_eq_1 : Fintype.card (@ConjClasses.carrier G _ 1) = 1 := by
    have : ConjClasses.carrier 1 = (ConjClasses.mk (1: G)).carrier := rfl
    simp_rw [this, ← ConjAct.orbit_eq_carrier_conjClasses]
    have : orbit Conj (1: G) = {1} := Set.ext fun x ↦
      (@ConjAct.mem_orbit_conjAct G _ x 1).trans isConj_one_left
    exact this ▸ @Fintype.card_unique _ _ (_)
  let sum_diff_one_card := ∑ x ∈ @Finset.univ (ConjClasses G) _ \ {1},
    Fintype.card x.carrier
  have p_dvd_sum_diff_one_card :
    p ∣ sum_diff_one_card := Finset.dvd_sum fun conjCl_g hconjCl_g ↦
    have ⟨g, hg⟩ := ConjClasses.exists_rep conjCl_g
    let Cg := orbit Conj g
    have Cg_eq : Cg = conjCl_g.carrier := hg ▸
      ConjAct.orbit_eq_carrier_conjClasses g
    have g_ne_one : g ≠ 1 := fun g_eq_one ↦
      have : conjCl_g ≠ 1 := Finset.not_mem_singleton.mp <|
          Finset.not_mem_sdiff_of_mem_right.mt (not_not.mpr hconjCl_g)
      this.symm <| (g_eq_one ▸ ConjClasses.one_eq_mk_one).trans hg
    have Cg_nontrivial : Cg.Nontrivial := by_contra fun hnot_nontrivial ↦
      have g_mem_Cg : g ∈ Cg := orbit_eq_iff.mp rfl
      have g_not_mem_ZG := h ▸ Subgroup.mem_bot.not.mpr g_ne_one
      have Cg_not_sing : Cg ≠ {g} :=
        (singleton_conj_iff_mem_center g).not.mp g_not_mem_ZG
      have subsingleton := Set.not_nontrivial_iff.mp hnot_nontrivial
      Cg_not_sing ((Set.subsingleton_iff_singleton g_mem_Cg).mp subsingleton)
    have card_Cg_dvd_p_n : Fintype.card Cg ∣ p ^ n := hpn ▸ Exists.intro
      (Fintype.card (stabilizer Conj g))
      (card_orbit_mul_card_stabilizer_eq_card_group Conj g).symm
    have p_dvd_card_Cg : p ∣ Fintype.card Cg :=
      have ⟨k, ⟨_, hk⟩⟩ := (Nat.dvd_prime_pow p_prime).mp card_Cg_dvd_p_n
      have k_nz : k ≠ 0 := fun k_eq_zero ↦
        have : Fintype.card Cg = 1 := k_eq_zero ▸ hk |>.trans p.pow_zero
        Fintype.one_lt_card_iff_nontrivial.not.mp this.symm.not_lt <|
          Cg_nontrivial.coe_sort
      hk ▸ dvd_pow_self p k_nz
    Fintype.card_congr' (congrArg (↑·) Cg_eq) ▸ p_dvd_card_Cg

  have : 1 + sum_diff_one_card = p ^ n := card_conj1_eq_1 ▸
    Finset.sum_eq_add_sum_diff_singleton
      (Finset.mem_univ (1: ConjClasses G))
        (Fintype.card ·.carrier) ▸
    sum_card_conj
  have p_dvd_p_n : p ∣ p ^ n := dvd_pow_self p n_pos.ne.symm
  this ▸ Nat.dvd_add_left p_dvd_sum_diff_one_card |>.not.mpr
    p_prime.not_dvd_one <| p_dvd_p_n

-- version in the book
theorem center_nontrivial_of_prime_pow_order
  [Group G] [Fintype G] (hG: IsPrimePow (Fintype.card G)) :
  Nontrivial (Subgroup.center G) :=
  Subgroup.nontrivial_iff_ne_bot (Subgroup.center G) |>.mpr <|
    center_ne_bot_of_prime_pow_order hG
