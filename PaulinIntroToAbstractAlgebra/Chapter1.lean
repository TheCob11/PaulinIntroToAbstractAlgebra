import mathlib
import Paperproof -- just for visualizations
open Function
open Classical
-- Bottom of page 5
theorem Exercise1 {S T : Type} {SNonempty : Nonempty S} (f: S → T):
  Bijective f ↔ ∃ (g: T → S), f∘g=id ∧ g∘f=id := by
  constructor;
  · intro ⟨finj, fsurj⟩;
    let inv_exists t := ∃ s, f s = t;
    have S_default := SNonempty.some;
    let g t := if inv_ex_t : inv_exists t then inv_ex_t.choose else S_default;
    use g;

    have inv_t_f_g_t_eq_t {t: T} (inv_ex_t: inv_exists t = True): f (g t) = t := by
      · simp_rw [g, dite_cond_eq_true inv_ex_t];
        simp [eq_iff_iff, iff_true] at inv_ex_t;
        apply choose_spec inv_ex_t;

    constructor <;> funext;
    · unfold Surjective at fsurj;
      exact inv_t_f_g_t_eq_t (by simp [inv_exists, fsurj]);

    · have eq_iff_f_eq x y : (x = y) ↔ (f x = f y) := by
        · constructor;
          · intro x_eq_y; rw [x_eq_y];
          · apply finj;
      rw [comp, eq_iff_f_eq (g (f _))];
      exact inv_t_f_g_t_eq_t (by simp [inv_exists]);

  · intro ⟨g, hg⟩;
    constructor;
    · intros x y f_eq;
      have gfx_eq_gfy : g (f x) = g (f y) := by rw [f_eq];
      repeat rw [← @comp_apply T S S g f] at gfx_eq_gfy;
      rwa [hg.right] at gfx_eq_gfy;

    · intro t;
      use g t;
      rw [← @comp_apply S T T f g, hg.left, id];
