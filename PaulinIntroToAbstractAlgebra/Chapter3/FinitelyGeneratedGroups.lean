import Mathlib
import PaulinIntroToAbstractAlgebra.Chapter3.SubgroupsCosetsLagrange

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

def cyclic_abelian [Group G] [h: IsCyclic G] : CommGroup G := .mk fun a b ↦
  have ⟨x, hx⟩ := h.exists_generator;
  have ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hx a)
  have ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hx b)
  calc a * b = x^r * x^s := hs ▸ hr ▸ rfl
       _ = x ^ (r + s) := (zpow_add _ _ _).symm
       _ = x ^ (s + r) := (add_comm s r) ▸ rfl
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
         _ = φ (x ^ (a + b)) := zpow_add x _ _ ▸ rfl
         _ = a + b := φ_pow
         _ = φ (x ^ a) * φ (x ^ b) := φ_pow ▸ φ_pow ▸ rfl
         _ = φ g₁ * φ g₂ := ha ▸ hb ▸ rfl
  MulEquiv.mk φ_equiv map_mul'

noncomputable def cyclic_finite_ZMod [Group G] [Fintype G] [hG: IsCyclic G] :
  G ≃* Multiplicative (ZMod (Fintype.card G)) :=
  let m := Fintype.card G;
  let ZM := ZMod m;
  -- for some reason ∃ can't be unboxed like ⟨x, hx⟩ in this case
  let x := hG.exists_generator.choose;
  have hx : (g: G) → g ∈ Subgroup.zpowers x := hG.exists_generator.choose_spec;
  have h_pow (g: G) : ∃(k: ℤ), x ^ k = g := Subgroup.mem_zpowers_iff.mp (hx g);
  let φ (g: G) : Multiplicative ZM := ((h_pow g).choose: ZM);
  let φ_inv (n: ZM) := x ^ (n.val: ℤ)
  have zpow_zmpow_eq (a: ℤ) (b: ZM) : (x ^ a = x ^ (b.val: ℤ)) ↔ (a = b) := by
    have order_x_eq_m : orderOf x = m := orderOf_eq_card_of_forall_mem_zpowers hx
    rw [zpow_eq_zpow_iff_modEq,
        ← ZMod.intCast_eq_intCast_iff, order_x_eq_m,
        ← ZMod.cast_eq_val, ZMod.intCast_zmod_cast b]
  have right_inv : Function.RightInverse φ_inv φ := fun n =>
    have ex := h_pow (φ_inv n)
    (zpow_zmpow_eq ex.choose n).mp ex.choose_spec
  let φ_Equiv : G ≃ Multiplicative ZM :=
    have card_eq : m = Fintype.card (Multiplicative ZM) :=
      (Fintype.card_multiplicative ZM ▸ ZMod.card m).symm;
    Equiv.ofRightInverseOfCardLE (Nat.le_of_eq card_eq) φ φ_inv right_inv
  have map_mul' (g₁ g₂ : G) : φ (g₁ * g₂) = φ g₁ * φ g₂ :=
    let a := φ g₁
    let b := φ g₂
    let ha := φ_Equiv.left_inv g₁
    let hb := φ_Equiv.left_inv g₂
    have zmpow_add : x ^ ((a.val: ℤ) + (b.val: ℤ)) = x ^ ((a*b).val: ℤ) := by
      -- yikes
      unfold_let a b φ ZM
      simp_all only [ZMod.natCast_val, Int.cast_add,
                     ZMod.intCast_cast, ZMod.cast_intCast']
      rfl
    let aZ: ℤ := a.val; let bZ: ℤ := b.val
    calc φ (g₁ * g₂) = φ (x ^ aZ * x ^ bZ) := ha ▸ hb ▸ rfl
         _ = φ (x ^ (aZ + bZ)) := zpow_add x _ _ ▸ rfl
         _ = φ (x ^ ((a * b).val : ℤ)) := zmpow_add ▸ rfl
         _ = a * b := right_inv _
         _ = φ (x ^ aZ) * φ (x ^ bZ) := right_inv _ ▸ right_inv _ ▸ rfl
         _ = φ g₁ * φ g₂ := ha ▸ hb ▸ rfl
  MulEquiv.mk φ_Equiv map_mul'

noncomputable def cyclic_equiv_ZMod [Group G] [IsCyclic G] :
  (G ≃* Multiplicative (ZMod (Nat.card G))) :=
  have inf_case (_: Infinite G) : G ≃* Multiplicative (ZMod (Nat.card G)) :=
    @Nat.card_eq_zero_of_infinite G _ ▸ cyclic_infinite_Z
  have fin_case (h: ¬Infinite G) : G ≃* Multiplicative (ZMod (Nat.card G)) :=
    have _G_Fintype : Fintype G := fintypeOfNotInfinite h
    @Nat.card_eq_fintype_card G _ ▸ cyclic_finite_ZMod
  have _ := Classical.dec;
  dite (Infinite G) inf_case fin_case

theorem cyclic_subgroup_cyclic [Group G] [hG: IsCyclic G] (S: Subgroup G): IsCyclic S :=
  have _ := Classical.dec;
  -- trivial case, not indenting the else bc its more like an early return
  if h: ¬Nontrivial S then
    @isCyclic_of_subsingleton S _ (not_nontrivial_iff_subsingleton.mp h)
  else have _ : Nontrivial S := not_not.mp h; clear% h;
  have ⟨a, ha⟩ := IsCyclic.exists_generator (α := G);
  have ex_m : ∃ m, 0 < m ∧ a ^ m ∈ S :=
    have ⟨s, _s_ne_1⟩ := (nontrivial_iff_exists_ne 1).mp ‹Nontrivial S›
    have ⟨nZ, hnZ⟩ := Subgroup.mem_zpowers_iff.mp (ha s)
    have a_nZ_mem : (a ^ nZ) ∈ S := (congrArg (· ∈ S) hnZ).mpr (SetLike.coe_mem s);
    let n := nZ.natAbs
    have n_pos : 0 < n :=
      have nZ_nz : nZ ≠ 0 := by
        by_contra _h
        obtain ⟨_sG, _s_mem⟩ := s
        simp_all only [ne_eq, Submonoid.mk_eq_one, zpow_zero]
      Int.natAbs_pos.mpr nZ_nz
    have a_n_mem : (a ^ n) ∈ S :=
      match (Int.natAbs_eq_iff (n := n)).mp rfl with
      | .inl eq_pos =>
        by rwa [eq_pos, zpow_natCast] at a_nZ_mem
      | .inr eq_neg =>
        by rwa [eq_neg, zpow_neg a ↑n, Subgroup.inv_mem_iff S, zpow_natCast] at a_nZ_mem
    ⟨n, ⟨n_pos, a_n_mem⟩⟩
  let m := Nat.find ex_m
  have ⟨m_pos, a_m_mem⟩ := Nat.find_spec ex_m
  let s: S := ⟨a ^ m, a_m_mem⟩
  have s_gen (s': S) : s' ∈ Subgroup.zpowers s :=
    let ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha s')
    let q := k.ediv m;
    let r := k.emod m;
    have s_q_eq : s ^ q = s' :=
      have h : (s': G) = s ^ q * a ^ r := calc (s': G)
        _ = a ^ k := hk.symm
        _ = a ^ (m * q + r) := Int.ediv_add_emod k ↑m ▸ rfl
        _ = a ^ (m * q) * a ^ r := zpow_add a (↑m * q) r
        _ = (a ^ m) ^ q * a ^ r := zpow_mul a (↑m) q ▸ zpow_natCast a m ▸ rfl
        _ = s ^ q * a ^ r := rfl
      have r_eq_zero : r = 0 :=
        have r_nonneg : 0 ≤ r :=
          have m_nz : m ≠ 0 := Nat.not_eq_zero_of_lt m_pos;
          Int.emod_nonneg k (Int.ofNat_ne_zero.mpr m_nz)
        let rN := r.toNat
        have r_eq_rN : r = ↑rN := (Int.toNat_of_nonneg r_nonneg).symm;
        have rN_zero : rN = 0 :=
          have rN_lt_m : rN < m :=
            have r_lt_m : r < m := Int.emod_lt_of_pos k (Int.ofNat_pos.mpr m_pos)
            (Int.toNat_lt r_nonneg).mpr r_lt_m
          have r_fails_ex_m := Nat.find_min ex_m rN_lt_m
          have a_r_mem : a ^ r ∈ S := by
            rw_mod_cast [← inv_mul_eq_iff_eq_mul, Subtype.coe_eq_iff] at h
            exact h.choose
          have a_rN_mem : a ^ rN ∈ S := by rwa [r_eq_rN, zpow_natCast] at a_r_mem
          by simp_all only [and_true, not_lt, nonpos_iff_eq_zero]
        r_eq_rN ▸ congrArg Nat.cast rN_zero
      SetCoe.ext <| Eq.symm <| calc (s': G)
        _ = s ^ q * a ^ r := h
        _ = s ^ q * 1 := r_eq_zero ▸ zpow_zero a ▸ rfl
        _ = s ^ q := mul_one _
    Subgroup.mem_zpowers_iff.mpr ⟨q, s_q_eq⟩
  ⟨s, s_gen⟩

theorem cyclic_dvd_subgroup
  [Group G] [Fintype G] [hG: IsCyclic G] (m: ℕ) (hm: m ∣ Nat.card G) :
  ∃! S: Subgroup G, Nat.card S = m ∧ IsCyclic S :=
  have ⟨n, hn⟩ := hm
  have ⟨g, hg⟩ := hG.exists_generator;
  let S := Subgroup.zpowers (g ^ n);
  let s: S := ⟨g ^ n, Subgroup.mem_zpowers (g ^ n)⟩
  have s_gen (x: S): x ∈ Subgroup.zpowers s  :=
    have ⟨k, hk⟩ := x.property
    ⟨k, SetCoe.ext hk⟩
  have IsCyclic_S : IsCyclic S := cyclic_subgroup_cyclic S
  have orderOf_g_eq_mn : orderOf g = m * n := (orderOf_generator_eq_natCard hg) ▸ hn
  have n_nz : n ≠ 0 := fun h ↦ Nat.card_pos.ne' (h ▸ hn)
  have n_dvd_orderOf_g : n ∣ orderOf g := orderOf_g_eq_mn ▸ dvd_mul_left n m
  have card_S : Nat.card S = m :=
    calc Nat.card S
      _ = orderOf s := (orderOf_generator_eq_natCard s_gen).symm
      _ = orderOf (g ^ n) := Subgroup.orderOf_mk s.val s.prop
      _ = orderOf g / n := orderOf_pow_of_dvd n_nz n_dvd_orderOf_g
      _ = m * n / n := orderOf_g_eq_mn ▸ rfl
      _ = m := (Nat.eq_div_of_mul_eq_left n_nz rfl).symm
  let cyclic_order_m (K: Subgroup G) := Nat.card K = m ∧ IsCyclic K
  let cyclic_order_m_zpow (d: ℕ) := cyclic_order_m (Subgroup.zpowers (g ^ d))
  have S_unique (K: Subgroup G) (hK: cyclic_order_m K) : K = S := by
    -- #check Nat.find ⟨S, And.intro card_S IsCyclic_S⟩
    let ⟨k, hk⟩ := hK.right.exists_generator
    have ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg k)
    -- have K_eq_zpowers_k : K = Subgroup.zpowers ↑k :=
    --   have elems_eq (x: G) : x ∈ K ↔ x ∈ Subgroup.zpowers ↑k :=
    --     have mp (h: x ∈ K) : x ∈ Subgroup.zpowers ↑k :=
    --       have ⟨i, hi⟩ := hk ⟨x, h⟩
    --       have : ↑k ^ i = x := SubgroupClass.coe_zpow ↑k i ▸ SetCoe.ext_iff.mpr hi
    --       ⟨i, this⟩
    --     have mpr : x ∈ Subgroup.zpowers ↑k → x ∈ K
    --       | ⟨i, hi⟩ => hi ▸ Subgroup.zpow_mem K (SetLike.coe_mem k) i
    --     ⟨mp, mpr⟩
    --   Subgroup.ext elems_eq;
    -- have k_ex: ∃k, cyclic_order_m (Subgroup.zpowers (g ^ k)) := ⟨n, ⟨card_S, IsCyclic_S⟩⟩
    -- have b_satisfies : cyclic_order_m (Subgroup.zpowers (g ^ b)) := hb ▸ K_eq_zpowers_k ▸ hK
    have k_mem_S : ↑k ∈ S :=
      let c := b / n
      have n_dvd_b : ↑n ∣ b := by
        -- #check zpow_eq_zpow_emod
        sorry
      have s_c_eq_k : (s ^ c: G) = (k: G) := calc (s ^ c: G)
        _ = (g ^ (n: ℤ)) ^ c := zpow_natCast g n ▸ rfl
        _ = g ^ (n * c) := (zpow_mul g n c).symm
        _ = g ^ b := (Int.mul_ediv_cancel' n_dvd_b) ▸ rfl
        _ = _ := hb
      ⟨c, s_c_eq_k⟩
    have elems_eq (x: G) : x ∈ K ↔ x ∈ S :=
      have mp (h: x ∈ K) : x ∈ S :=
        have ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hk ⟨x, h⟩)
        let c := b * a / n
        have g_n_c_eq : (g ^ n) ^ c = x :=
          have n_dvd_ai : ↑n ∣ b * a := by
            -- #check dvd_trans
            have : ↑n ∣ b := by
              have n_dvd_card : n ∣ Nat.card G := hn ▸ dvd_mul_left n m
              have a_dvd_card : b ∣ Nat.card G := by
                sorry

              sorry
            exact Dvd.dvd.mul_right this a
          calc (g ^ n) ^ c
            _ = (g ^ (n: ℤ)) ^ c := zpow_natCast g _ ▸ rfl
            _ = g ^ ((n: ℤ) * c) := (zpow_mul g _ _).symm
            _ = g ^ (b * a) := (Int.mul_ediv_cancel' n_dvd_ai) ▸ rfl
            _ = (g ^ b) ^ a := zpow_mul g b a
            _ = x := hb ▸ Subtype.ext_iff.mp ha
        ⟨c, g_n_c_eq⟩
      have mpr : x ∈ S → x ∈ K
      | ⟨a, ha⟩ => by
        -- simp_all?
        let c := n * a / b
        have g_b_c_eq : (g ^ b) ^ c = x := sorry
        -- exact ⟨c, g_b_c_eq⟩
        have := Subgroup.mem_zpowers_iff.mpr ⟨c, g_b_c_eq⟩
        -- simp_all?
        sorry
      ⟨mp, mpr⟩
    exact Subgroup.ext elems_eq
  -- exact ExistsUnique.intro S ⟨card_S, IsCyclic_S⟩ S_unique
  ⟨S, ⟨card_S, IsCyclic_S⟩, S_unique⟩
