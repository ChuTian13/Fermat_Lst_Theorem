import data.nat.basic
import data.int.nat_prime
import data.complex.basic
import tactic
import data.nat.prime
import ring_theory.principal_ideal_domain
import ring_theory.roots_of_unity
import algebra.ring 

namespace my_ring 
variables {R : Type*} [ring R]
theorem add_zero (a : R) : a + 0 = a := 
by rw [add_comm, zero_add]
theorem add_right_neg (a : R) : a + -a = 0 := 
by rw [add_comm, add_left_neg] end my_ring

lemma h1_lt_3 : 1 < 3 
:= by norm_num

structure int_cubic_root (d : ℤ) :=
(a : ℤ)
(b : ℤ)

constant ζ : ℂ 
constant hζ : is_primitive_root ζ 3

lemma prop_3_1  : ζ^3 = 1
:= by exact hζ.pow_eq_one 
lemma prop_3_2  : 1 + ζ + ζ^2 = 0
:= 
begin
  have h1: (ζ - 1)*(1 + ζ + ζ^2) = (ζ - 1) * 0,
  {calc (ζ - 1)*(1 + ζ + ζ^2) = ζ^3 - 1     : by ring
                       ...    = 1 - 1       : by rw prop_3_1 
                       ...    = (ζ - 1) * 0 : by ring,
  },
  have h2: ζ - 1 ≠ 0, 
  {have h3: ζ ≠ 1, 
  {calc ζ = ζ^1  : by ring 
        ... ≠ 1 : by exact is_primitive_root.pow_ne_one_of_pos_of_lt hζ zero_lt_one h1_lt_3,},
  exact sub_ne_zero.mpr h3},
  exact mul_left_cancel' h2 h1
end

lemma fac_3{x y :ℤ}: 
((coe x) + (coe y)) * ((coe x) + ζ * (coe y)) * ((coe x) + ζ^2 * (coe y)) = (coe x)^3 + (coe y)^3
:=
begin
  calc ((coe x) + (coe y)) * ((coe x) + ζ * (coe y)) * ((coe x) + ζ^2 * (coe y)) 
          = (coe x)^3 + (coe y) * (coe x)^2 + ζ * (coe x)^2 * (coe y) + ζ * (coe y)^2 * (coe x)
           + ζ^2 * (coe y) * (coe x)^2 + ζ^2 * (coe y)^2 * (coe x) + ζ^3*(coe y)^2 * (coe x) + ζ^3 * (coe y)^3     
           : by ring
      ... = (coe x)^3 + (coe y) * (coe x)^2 + ζ * (coe x)^2 * (coe y) + ζ * (coe y)^2 * (coe x)
           + ζ^2 * (coe y) * (coe x)^2 + ζ^2 * (coe y)^2 * (coe x) + 1 *(coe y)^2 * (coe x) + 1 * (coe y)^3 
           : by rw prop_3_1
      ... = (coe x)^3 + (1 + ζ + ζ^2) * (coe x)^2 * (coe y) + (1 + ζ + ζ^2) * (coe y)^2 * (coe x)
           + 1 * (coe y)^3  : by ring 
      ... = (coe x)^3 + 0 * (coe x)^2 * (coe y) + 0 * (coe y)^2 * (coe x) + 1 * (coe y)^3 : by rw (prop_3_2 ζ h)
      ... = (coe x)^3 + (coe y)^3 : by ring
 end

theorem fac_3_1{x y :ℤ}: 
(coe x)^3 + (coe y)^3 = ((coe x) + (coe y)) * ((coe x) + ζ * (coe y)) * ((coe x) + ζ^2 * (coe y))
:= 
begin
  exact eq.symm fac_3,
end

theorem fermat_last_theorem_3' :
∀ x y z: ℤ, ∀ n : ℕ, x * y * z ≠ 0 → 
((coe x) + (coe y)) * ((coe x) + ζ * (coe y)) * ((coe x) + ζ^2 * (coe y)) ≠ (coe z)^3
:= sorry

theorem fermat_last_theorem_3 :
 ∀ x y z: ℤ, ∀ n : ℕ, x * y * z ≠ 0 → (coe x)^3 + (coe y)^3 ≠ (coe z : ℂ)^3 
:= 
begin
  intros x y z n h, 
  calc (coe x)^3 + (coe y)^3 = ((coe x) + (coe y)) * ((coe x) + ζ * (coe y)) * ((coe x) + ζ^2 * (coe y))
                        : by exact eq.symm fac_3
       ...  ≠ (coe z)^3 : by exact fermat_last_theorem_3' x y z n h,
end


