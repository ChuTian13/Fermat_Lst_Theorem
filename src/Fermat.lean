import data.nat.basic
import data.int.nat_prime
import tactic
import data.nat.prime
import number_theory.fermat4


lemma pow_nonzero {x y z: ℤ} {k: ℕ} : x * y * z ≠ 0 →  (x^k) * (y^k) * (z^k) ≠ 0
:= 
begin
  intro h,
  have h1: x ≠ 0, 
  {intro h1,
  contrapose! h,
  calc x * y * z = 0 * y * z    : by rw h1
          ...    = 0 * (y * z)  : by exact mul_assoc 0 y z
          ...    = 0            : by exact zero_mul (y*z),},
  have h2: y ≠ 0, 
  {intro h2,
  contrapose! h,
  calc x * y * z = x * 0 * z    : by rw h2
          ...    = x * (0 * z)  : by ring
          ...    = x * 0        : by rw zero_mul z
          ...    = 0            : by exact mul_zero x,},
  have h3: z ≠ 0, 
  {intro h3,
  contrapose! h,
  calc x * y * z = x * y * 0    : by rw h3
          ...    = (x * y) * 0  : by ring
          ...    = 0            : by exact mul_zero (x * y)},
  have h4: (x * y * z)^k ≠ 0, 
  {exact pow_ne_zero k h,},
  calc (x^k) * (y^k) * (z^k) = (x * y)^k * z^k  : by rw mul_pow x y k 
                        ...  =  (x * y * z)^k   : by rw mul_pow (x*y) z k 
                        ...  ≠ 0                : by exact h4,
end

theorem pow_assoc(x: ℤ)(m n:ℕ) : x^(m*n) = (x^m)^n 
:= 
begin
  exact pow_mul x m n,
end

theorem fermat_last_theorem_p :
 ∀ x y z:ℤ, ∀ n : ℕ, n > 2 ∧ nat.prime n ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n
:= sorry

theorem fermat_last_theorem_4 :
∀ x y z : ℤ, x * y * z ≠ 0 → x^4 + y^4 ≠ z^4
:= 
begin
  intros x y z h,
  have h4x: x ≠ 0, 
  {intro h1,
  contrapose! h,
  calc x * y * z = 0 * y * z    : by rw h1
          ...    = 0 * (y * z)  : by exact mul_assoc 0 y z
          ...    = 0            : by exact zero_mul (y*z)},
  have h4y: y ≠ 0,
  {intro h2,
  contrapose! h,
  calc x * y * z = x * 0 * z    : by rw h2
          ...    = x * (0 * z)  : by ring
          ...    = x * 0        : by rw zero_mul z
          ...    = 0            : by exact mul_zero x,},
  apply not_fermat_4 h4x h4y,
end


theorem fermat_last_theorem :
  ∀ x y z: ℤ, ∀ n: ℕ ,n > 2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n
:=
begin
  intros x y z n h,
  have h1: (4 ∣ n) ∨ ¬ (4 ∣ n), by exact em (4 ∣ n),
  rcases h1 with ⟨ k, rfl ⟩,
  have h2: (x^k) * (y^k) * (z^k) ≠ 0, by exact pow_nonzero h.2,
  calc x^(4 * k) + y^(4 * k) = x^(k * 4) + y^(4 * k) : by rw mul_comm 4 k 
       ... = x^(k * 4) + y^(k * 4)                   : by rw mul_comm 4 k
       ... =(x^k)^4 + y^(k*4)                        : by rw pow_assoc x k 4
       ... = (x^k)^4 + (y^k)^4                       : by rw pow_assoc y k 4
       ... ≠ (z^k)^4                                 : by exact fermat_last_theorem_4 (x^k) (y^k) (z^k) h2
       ... = z^(k*4)                                 : by rw pow_assoc z k 4
       ... = z^(4*k)                                 : by ring_nf,
    
  have h3: (2 ∣ n) ∨ ¬ (2 ∣ n), by exact em (2 ∣ n),
  rcases h3 with ⟨ k, rfl ⟩,
  { have hk: 1 < k, 
    {have hk1: 2 * 1 < 2 * k, by exact h.1,
     exact lt_of_mul_lt_mul_left' hk1},
    let p: ℕ := k.min_fac,
    have h4 : p ∣ k, by exact nat.min_fac_dvd k,
    cases h4 with l hl,
    have h5: p ≠ 2,
    {intro h5,
    contrapose! h1,
    calc   4 ∣ 4 * l         :  by exact dvd_mul_right 4 l
         ... = 2 * (2 * l)    :  by linarith
         ... = 2 * (p * l)    :  by rw h5
         ... = 2 * k          :  by rw hl,},
    have h6: (x^(2 * l))^p + (y^(2 * l))^p ≠ (z^(2 * l))^p, 
    {have t1: x^(2 * l)*(y^(2 * l))*(z^(2 * l))≠ 0, by exact pow_nonzero h.2,
     have t2: k ≠ 1, {exact ne_comm.mp (ne_of_lt hk),},
     have t3: nat.prime p, {exact nat.min_fac_prime t2,},
     have t5: p > 2, {exact lt_iff_le_and_ne.mpr⟨nat.prime.two_le t3, ne_comm.mp h5⟩},
     have t4: p > 2 ∧ nat.prime p ∧ x^(2 * l)*(y^(2 * l))*(z^(2 * l))≠ 0, by exact ⟨t5, t3, t1⟩, 
     exact fermat_last_theorem_p (x^(2 * l)) (y^(2 * l)) (z^(2 * l)) p t4,
    },
    calc x^(2 * k) + y^(2 * k) = x^(2 * (p * l)) + y^(2 * k)        : by rw hl
                         ...   = x^(2 * (p * l)) + y^(2 * (p * l))  : by rw hl 
                         ...   = x^(2 * (l * p)) + y^(2 * (l * p))  : by rw mul_comm p l
                         ...   = x^(2 * l * p) + y^(2 * l * p)      : by rw mul_assoc 2 l p
                         ...   = (x^(2 * l))^p + y^(2 * l * p)      : by rw pow_assoc x (2 * l) p
                         ...   = (x^(2 * l))^p + (y^(2 * l))^p      : by rw pow_assoc y (2 * l) p
                         ...   ≠ (z^(2 * l))^p                      : by exact h6
                         ...   = z^(2 * l * p)                      : by rw pow_assoc z (2 * l) p 
                         ...   = z^(2 * (p * l))                    : by ring_nf
                         ...   = z^(2 * k)                          : by rw hl,
  },
  let p: ℕ := n.min_fac,
  have hp1 : p ≠ 2, 
  begin
    contrapose! h3,
    calc 2 = p   : by exact eq.symm h3
       ... ∣ n  : by exact nat.min_fac_dvd n,
  end,
  have hp21 : n ≠ 1, 
  {have hp211: n > 1, {exact gt_trans h.1 one_lt_two}, exact ne_of_gt hp211},
  have hp2 : nat.prime p, by exact nat.min_fac_prime hp21,
  have hp3 : p > 2, {exact lt_iff_le_and_ne.mpr⟨nat.prime.two_le hp2, ne_comm.mp hp1⟩},
  have hp4 : p ∣ n, by exact nat.min_fac_dvd n,
  cases hp4 with k hkp,
  have hp5: (x^k)*(y^k)*(z^k) ≠ 0, by exact pow_nonzero h.2,
  have hp6: p>2 ∧ nat.prime p ∧ (x^k)*(y^k)*(z^k) ≠ 0, by exact⟨hp3, hp2, hp5⟩,
  calc x^n + y^n = x^(p*k) + y^(p*k)  : by rw hkp 
           ...   = x^(k*p) + y^(p*k)  : by rw mul_comm
           ...   = x^(k*p) + y^(k*p)  : by rw mul_comm 
           ...   = (x^k)^p + y^(k*p)  : by rw pow_assoc x k p 
           ...   = (x^k)^p + (y^k)^p  : by rw pow_assoc y k p 
           ...   ≠ (z^k)^p            : by exact fermat_last_theorem_p (x^k) (y^k) (z^k) p hp6
           ...   = z^(k*p)            : by rw pow_assoc z k p
           ...   = z^(p*k)            : by rw mul_comm p k
           ...   = z^n                : by rw hkp,
end

#lint
