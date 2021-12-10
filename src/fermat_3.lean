import data.nat.basic
import data.int.nat_prime
import data.complex.basic
import tactic
import data.nat.prime
import ring_theory.principal_ideal_domain
import ring_theory.roots_of_unity
import algebra.ring 
import algebra.euclidean_domain
import algebra.associated
import Eisenstein_Int

open int_cubic_root
/- if norm = 1 -/
lemma norm_eq_one_2(a b : ℤ): a^2 - a * b + b^2 = 1 → 
(abs a = 1 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1) ∨ (abs a = 1 ∧ abs b = 1):=
begin
     intro h,
     have h1 : (2*a - b)^2 + 3*b^2 = 4, 
     calc (2*a - b)^2 + 3*b^2 = 4 * (a^2 - a * b + b^2) : by ring 
                      ...     = 4 * 1                   : by rw h 
                      ...     = 4                       : by norm_num,   
     /-first we show that abs b ≤ 1 and abs a ≤ 1-/
     /-abs b ≤ 1-/
     have h2: abs b ≤ 1, 
     {contrapose! h1,
     have h3 : abs b >= 2, by exact lt_le_succ 1 (abs b) h1,
     have a1: 0 ≤ (3 : ℤ), by norm_num,
     have a2: 0 ≤ (4 : ℤ), by norm_num,
     have t2: 4 ≤ (abs b)^2 , by nlinarith,
     have t1: (2*a - b)^2 + 3*b^2 >= 12,
     calc (2*a - b)^2 + 3*b^2 >= 3*b^2   :  by exact left_add_nonneg ((2*a - b)^2) (3*b^2) (pow_two_nonneg (2*a - b))
                ...           = 3 * (abs b)^2 : by rw pow_two_abs b
                ...           = 3 * ((abs b)^2)  : by ring
                ...           ≥ 3 * 4         : by exact mul_le_mul (le_refl 3) t2 a2 a1
                ...           = 12            : by norm_num,
     linarith,},
     have b1: (2*b - a)^2 + 3*a^2 = 4, 
     calc (2*b - a)^2 + 3*a^2 = 4 * (a^2 - a * b + b^2) : by ring 
                      ...     = 4 * 1                   : by rw h 
                      ...     = 4                       : by norm_num,   
     /-abs a ≤ 1, the same as the previous part-/
     have h3: abs a <= 1, {contrapose! b1,
     have h3 : abs a >= 2, by exact lt_le_succ 1 (abs a) b1,
     have a1: 0 ≤ (3 : ℤ), by norm_num,
     have a2: 0 ≤ (4 : ℤ), by norm_num,
     have t2: 4 ≤ (abs a)^2 , by nlinarith,
     have t1: (2*b - a)^2 + 3*a^2 >= 12,
     calc (2*b - a)^2 + 3*a^2 >= 3*a^2   :  by exact left_add_nonneg ((2*b - a)^2) (3*a^2) (pow_two_nonneg (2*b - a))
                ...           = 3 * (abs a)^2 : by rw pow_two_abs a
                ...           = 3 * ((abs a)^2)  : by ring
                ...           ≥ 3 * 4         : by exact mul_le_mul (le_refl 3) t2 a2 a1
                ...           = 12            : by norm_num,
     linarith,},
     /-our conclusions-/
     have h4: abs a = 0 ∨ abs a = 1, 
     by exact smaller_1 (abs a) ⟨h3, abs_nonneg a⟩,
     have h5: abs b = 0 ∨ abs b = 1, 
     by exact smaller_1 (abs b) ⟨h2, abs_nonneg b⟩,
     have h6: (abs a = 0 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1)∨ (abs a = 1 ∧ abs b = 0) ∨ (abs a = 1 ∧ abs b = 1),
     by tauto, 
     have h7: ¬(abs a = 0 ∧ abs b = 0),
     {contrapose! h,
      have t1: a = 0, by exact abs_eq_zero.mp h.1,
      have t2: b = 0, by exact abs_eq_zero.mp h.2,
      have t3: a^2 - a*b + b^2 ≠ 1,
      {rw[t1, t2], ring, norm_num,}, 
      exact t3, },
     have h8: ¬(abs a = 0 ∧ abs b = 0) ∧ ((abs a = 0 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1)∨ (abs a = 1 ∧ abs b = 0) ∨ (abs a = 1 ∧ abs b = 1)),
     by exact ⟨h7, h6⟩,
     tauto,
end 

lemma abs_either: ∀ x : ℤ, x = abs x ∨ x = -abs x :=
begin
     intro x,
     have h: abs x = x ∨ abs x = -x,  by exact abs_choice x,
     cases h,
     left, rw h,
     right, rw h, ring,
end

lemma norm_eq_one_3(a b : ℤ) : 
(a^2 - a * b + b^2 = 1) ∧ ((abs a = 1 ∧ abs b = 1)) → 
(a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) :=
begin
     intro h;
     have e: a^2 -a*b + b^2 = 1, by exact h.1,
     have h1: abs a = 1, by exact (h.2).1,
     have h2: abs b = 1, by exact (h.2).2,
     have h3: a = 1 ∨ a = -1, 
     {have t1: a = abs a ∨ a = - abs a, by exact abs_either a,
     cases t1,
     {rw [t1, h1], left, norm_num,},
     {rw [t1, h1], right, norm_num,}},
     have h4: b = 1∨ b = -1,
     {have t1: b = abs b ∨ b = - abs b, by exact abs_either b,
     cases t1,
     {rw [t1, h2], left, norm_num, },
     {rw [t1, h2], right, norm_num,}},
     have h5: (a = 1 ∧  b = 1) ∨ (a = -1 ∨ b = 1) ∨ (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = -1), by tauto,
     have h6: ¬(a = 1 ∧ b = -1), {
     contrapose! e,
     calc a^2 - a*b + b^2 = 1^2 - 1*(-1) + (-1)^2  : by rw [e.1, e.2]
                  ...     ≠ 1                      : by norm_num,},
     have h7: ¬(a = -1 ∧ b = 1), {
     contrapose! e,
     calc a^2 - a*b + b^2 = (-1)^2 - (-1)*1 + 1^2  : by rw [e.1, e.2]
                  ...     ≠ 1                      : by norm_num,},
     tauto,
end

lemma norm_eq_one_1 {x : ℤ_ζ}: (x.a^2 - x.a * x.b + x.b^2 = 1) → 
(abs x.a = 1 ∧ abs x.b = 0) ∨ (abs x.a = 0 ∧ abs x.b = 1) ∨ (x = ⟨1, 1⟩ 
∨ (x = ⟨-1, -1⟩)) := 
begin
     intro h,
     have h1: (abs x.a = 1 ∧ abs x.b = 0) ∨ (abs x.a = 0 ∧ abs x.b = 1) 
  ∨ (abs x.a = 1 ∧ abs x.b = 1), by apply norm_eq_one_2 x.a x.b h,
     cases h1, 
     {have h2: abs x.a = 1 ∧ abs x.b = 0, tauto, by tauto,},
     {cases h1,
     {have h2: abs x.a = 0 ∧ abs x.b = 1, tauto, by tauto,},
     {have h2: (x.a = 1 ∧ x.b = 1) ∨ (x.a = -1 ∧  x.b = -1), 
      by exact norm_eq_one_3 x.a x.b ⟨h, h1⟩,
     cases h2,
     {have h3: x = ⟨1, 1⟩, {simp[ext], exact h2,}, tauto,
     },
     {have h3: x = ⟨-1, -1⟩, {simp[ext], exact h2,}, tauto,},}},
end


lemma not1 (a : ℤ) : 0 < a ∧ a ≠ 1 → 1 < a := by omega

lemma norm_eq_zero_iff (z : ℤ_ζ) : z.norm = 0 ↔ z = 0 :=
begin
  split,
  { intro h,
    rw [ext, zero_a, zero_b],
    have h1 : z.a * z.a - z.a * z.b + z.b * z.b = 0, by exact h,
    have h2: (2* z.a - z.b)^2 + 3*z.b^2 = 0,
    {ring, linarith[h1],},
    have h3: z.b = 0, by nlinarith,
    have h4: (2*z.b - z.a)^2 + 3 * z.a ^2 = 0,
    {ring, linarith[h1],},
    have h5: z.a = 0, by nlinarith,
    exact ⟨h5, h3⟩,
   },
  { rintro rfl, exact norm_zero }
end

lemma gt_if_ge_ne(a b : ℤ) : b ≤ a ∧ a ≠ b → b < a := by omega

lemma abs_pow_two(a : ℤ): a^2 = (abs a)^2 := 
begin
     have h: abs a = a ∨ abs a = -a, by exact abs_choice a,
     cases h, rw h,
     {rw h, ring,},
end

lemma abs_ge_zero (a : ℤ) : 0 ≤ a → abs a = a :=
by exact abs_eq_self.mpr

@[simp] lemma norm_eq_one_iff {x : ℤ_ζ} : x.norm.nat_abs = 1 ↔ is_unit x :=
begin
split,
{intro h,
have h0: x.norm = 1, 
calc x.norm  = abs x.norm                :  by rw abs_ge_zero x.norm (norm_nonneg x) 
        ...  = ((x.norm).nat_abs :ℤ)     : by exact int.abs_eq_nat_abs x.norm 
        ...  =  (1 : ℤ)                  : by linarith [h],
have h0_1: x.a^2 - x.a * x.b + x.b^2 = 1, 
calc x.a^2 - x.a * x.b + x.b^2 = x.a * x.a - x.a * x.b + x.b * x.b  : by ring
                       ...     = 1                                  : by exact h0,
have h1: (abs x.a = 1 ∧ abs x.b = 0) ∨ (abs x.a = 0 ∧ abs x.b = 1) ∨  (x = ⟨1, 1⟩ ∨ (x = ⟨-1, -1⟩)), 
by exact norm_eq_one_1 h0_1,
 cases h1,
 {have h2: ∃ y : ℤ_ζ,  x * y = 1, 
 { have t1: x.a * x.a = 1, 
 calc x.a * x.a = x.a ^ 2     : by ring 
          ...   = 1^2         : by rw [abs_pow_two x.a, h1.1]
          ...   = 1           : by norm_num,
 use ⟨x.a, 0⟩, 
 have a: x.b = 0, by exact abs_eq_zero.mp h1.2,
 rw[eql x, a], simp, rw t1, simp[ext], },
 cases h2 with y ty,
 have h3: is_unit x, by exact is_unit_of_mul_eq_one x y ty, tauto,},
 {cases h1,
 {have e1: x.b^2 = x.b * x.b, by ring,
 have a : x.a = 0, by exact abs_eq_zero.mp h1.1,
 have f1: x * ⟨-x.b, -x.b⟩  = 1,
 calc x* ⟨-x.b, -x.b⟩ = ⟨0, x.b⟩ * ⟨-x.b, -x.b⟩  :  by rw [eql x, a]
       ...           = ⟨(abs x.b)^2, 0⟩        :  by {simp, rw e1,}
       ...            = 1                      : by {rw h1.2, simp[ext],}, 
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨-x.b, -x.b⟩ f1,
 tauto,},
 {cases h1,
 {have f: x * ⟨0, -1⟩ = 1, {rw h1, simp[ext],},
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨0, -1⟩ f,
 tauto,},
 {have f: x * ⟨0, 1⟩ = 1, {rw h1, simp[ext],},
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨0, 1⟩ f,
 tauto,},}}
},
{intro h,
have h1: ∃ y, x*y = 1, by exact is_unit.exists_right_inv h,
cases h1 with y h1',
have h2: norm x * norm y = 1, 
{rw[←norm_mul, h1'], try{refl},},
have a1: norm x ≠ 0, {contrapose! h2, 
calc x.norm * y.norm = 0           : by {rw h2, norm_num}
                 ... ≠ 1           : by linarith,},
have a2: norm y ≠ 0, {contrapose! h2,
calc x.norm * y.norm =  0          : by {rw h2, norm_num} 
                ...  ≠  1          : by linarith,},
have h3: norm x = 1, 
{contrapose! h2,
 have t1: norm x > 0, by exact gt_if_ge_ne (norm x) 0 ⟨norm_nonneg x, a1⟩,
 have t3: norm y > 0, by exact gt_if_ge_ne (norm y) 0 ⟨norm_nonneg y, a2⟩,
 have t2: norm x > 1, by omega,
 have t4: norm y ≥ 1, by omega,
 have t5: norm x * norm y > 1,
 calc norm x * norm y > 1 * 1  : by exact mul_lt_mul t2 t4 zero_lt_one (norm_nonneg x)
                ...   = 1      : by norm_num,
 linarith,
},
calc x.norm.nat_abs = (norm x).nat_abs   : rfl 
              ...   =  int.nat_abs (norm x)  : rfl 
              ...   =  int.nat_abs (1 : ℤ)   : by rw h3 
              ...   =  1                     : by exact int.nat_abs_one,     
},
end

lemma is_unit_iff_norm_is_unit (z : ℤ_ζ) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs_eq, norm_eq_one_iff]

lemma norm_eq_one_iff'  (z : ℤ_ζ) : z.norm = 1 ↔ is_unit z :=
by rw [←norm_eq_one_iff, ←int.coe_nat_inj', int.nat_abs_of_nonneg (norm_nonneg z),
  int.coe_nat_one]

lemma norm_eq_of_associated {x y : ℤ_ζ} (h : associated x y) :
  x.norm = y.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  rw [norm_mul, (norm_eq_one_iff' _).mpr u.is_unit],
  ring,
end

/-- arithmetic properties of (1 - ζ)  -/
theorem divide_3 : ∀ a b : ℤ, 1 - ζ ∣ (a + b * ζ) ↔ 3 ∣ a + b :=
begin
     intros a b,
     split,
     {intro h,
     have h1 : ∃ z : ℤ_ζ, (a + b * ζ : ℤ_ζ) = (1 - ζ) * z, by tauto,  /-? Curious-/
     cases h1 with z hz,
     have h2: (⟨1, 0⟩ - ⟨0, 1⟩ : ℤ_ζ) = ⟨1, -1⟩, by refl,
     have h3: (a + b * ζ : ℤ_ζ) = ⟨z.a + z.b, 2 * z.b - z.a⟩,
     calc (a + b * ζ : ℤ_ζ) = (1 - ζ) * z         : by exact hz
                 ...        = (1 - ζ) * ⟨z.a, z.b⟩ : by rw eql z 
                 ...        = (⟨1, 0⟩ - ⟨0, 1⟩) * ⟨z.a, z.b⟩  :  by try {refl}
                 ...        = ⟨1, -1⟩ * ⟨z.a, z.b⟩           :  by simp*
                 ...        = ⟨1 * z.a - (-1) * z.b, 1 * z.b + (-1) * z.a - (-1) * z.b⟩ : rfl 
                 ...        = ⟨z.a + z.b, 2 * z.b - z.a⟩       : by {simp, ring},
     have h4: (a + b * ζ : ℤ_ζ) = ⟨a, b⟩,
     calc (a + b * ζ : ℤ_ζ) = coe a + coe b * ⟨0, 1⟩  :  by try{refl}
                  ...       = ⟨a, b⟩                  :  by simp*,
     have h5: a + b = 3 * z.b, 
     calc a + b = (⟨a, b⟩ : ℤ_ζ).a + (⟨a, b⟩ : ℤ_ζ).b                                            :  by simp 
           ...  = (a + b * ζ : ℤ_ζ).a + (a + b * ζ : ℤ_ζ).b                                     :  by rw h4 
           ...  = (⟨z.a + z.b, 2 * z.b - z.a⟩ : ℤ_ζ).a + (⟨z.a + z.b, 2 * z.b - z.a⟩ : ℤ_ζ).b    :  by rw h3 
           ...  = (z.a + z.b) + (2 * z.b - z.a)                                                 :  rfl 
           ...  = 3 * z.b                                                                       :  by ring,
     use ⟨z.b, h5⟩,
     },
     {intro h,
     have h1 : ∃ w : ℤ, a + b = 3 * w, by tauto,
     cases h1 with w hw,
     let x := a - w,
     have h3: (⟨1, 0⟩ - ⟨0, 1⟩ : ℤ_ζ) = ⟨1, -1⟩, by refl,
     have h4: 1 * w + (-1) * x - (-1) * w = 2 * w - x, by ring,
     have h5:  (a + b * ζ : ℤ_ζ) = ⟨a, b⟩,
     calc (a + b * ζ : ℤ_ζ) = coe a + coe b * ⟨0, 1⟩  :  by try{refl}
                  ...       = ⟨a, b⟩                  :  by simp*,
     have h2 : (1 - ζ) * ⟨x, w⟩ = (a + b * ζ : ℤ_ζ),
     calc (1 - ζ) * ⟨x, w⟩ = (⟨1, 0⟩ - ⟨0, 1⟩) * ⟨x, w⟩  :  by try {refl}
               ...        = ⟨1, -1⟩ * ⟨x, w⟩           :  by rw h3
               ...        = ⟨1 * x - (-1) * w, 1 * w + (-1) * x - (-1) * w⟩  : rfl
               ...        = ⟨x + w, 2 * w - x⟩        :  by {rw h4, simp}
               ...        = ⟨x + w, 3 * w - (w + x)⟩  :  by {simp*, ring}
               ...        = ⟨a, a + b - a⟩            :  by simp* 
               ...        = ⟨a, b⟩                    :  by simp
               ...        = a + b * ζ                :  by rw h5,
     let y : ℤ_ζ := ⟨x, w⟩, 
     have hy: (a + b * ζ : ℤ_ζ) = (1 - ζ) * y, 
     calc         (a + b * ζ : ℤ_ζ) = (1 - ζ) * ⟨x, w⟩  : by rw h2 
                        ...         = (1 - ζ) * y       : by refl,
     use ⟨y, hy⟩,},
end

/-- give a function of mod-/
def mod : ℤ_ζ → ℤ_ζ → ℤ_ζ → Prop
| d a b := ∃ c : ℤ_ζ, a - b = c * d 
theorem mod_def : ∀ d a b : ℤ_ζ, mod d a b → ∃ c : ℤ_ζ, a - b = c * d :=
begin
      intros d a b h, exact h,
end

/-- given d, mod is an equivalent relation-/
theorem mod_self : ∀ d a: ℤ_ζ, mod d a a :=
begin
      intros d a, use 0, ring,
end
theorem mod_symm: ∀ d a b : ℤ_ζ, mod d a b → mod d b a :=
begin
      intros d a b, 
      intro h, cases h with c hc, use -c, simp, rw ←hc, ring,
end
theorem mod_trans: ∀ d a b c : ℤ_ζ, mod d a b ∧ mod d b c → 
mod d a c :=
begin
      intros d a b c h,
      cases h.1 with x hx,  cases h.2 with y hy,
      use x + y,
      calc a - c = a - b + (b - c) :  by ring 
            ...  = x * d + y * d   :  by rw[hx, hy]
            ...  = (x + y) * d     :  by ring,
end
theorem mod_0_dvd : ∀ d a : ℤ_ζ, mod d a 0 → d ∣ a :=
begin
      intros d a h, cases h with c hc,
      use c, 
      calc a = a - 0  : by ring
         ... = d * c  : by {rw hc, ring},
end

/-
theorem mod_9 {a b : ℤ} : ¬(1 - ζ ∣ a + b * ζ) → 
mod 9 ((a + b * ζ)^3) 1 ∨ mod 9 ((a + b * ζ)^3) (-1) :=
begin
      intro h,
      have h₁ : ¬(3 ∣ (a + b)), 
      {contrapose! h, exact (divide_3 a b).mpr h,},
      have h₂ : 3 ∣ a ∨ ¬ (3 ∣ a), by exact em (3 ∣ a),
      have h₃ : 3 ∣ b ∨ ¬ (3 ∣ b), by exact em (3 ∣ b),
      cases h₂,
      {have hb1 : ¬ (3 ∣ b), 
      {contrapose! h₁, 
      cases h₂ with k hk, cases h₁ with l hl,
      use (k + l), 
      simp only[hk, hl], ring,},

      },
end -/

#lint