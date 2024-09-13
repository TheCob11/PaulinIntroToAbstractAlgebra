import Mathlib

-- this is a pretty trivial definition but the entire chapter is defs and
-- cayleys thm (through this proof) so i figured id put it in
def perm_hom (G S : Type*) [Group G] [MulAction G S] : G →* Equiv.Perm S := .mk'
  (fun g ↦ ⟨SMul.smul g, SMul.smul g⁻¹, inv_smul_smul g, smul_inv_smul g⟩)
  (fun a b ↦ Equiv.Perm.ext (mul_smul a b))

noncomputable
def cayleys_theorem [Group G] [MulAction G S] [faithful : FaithfulSMul G S] :
  G ≃* (perm_hom G S).range :=
  MonoidHom.ofInjective fun _ _ s ↦
    faithful.eq_of_smul_eq_smul (congrFun ((Equiv.mk.injEq ..).mp s).left)

-- the version from the book
noncomputable example [Group G] : G ≃* (perm_hom G G).range := cayleys_theorem
