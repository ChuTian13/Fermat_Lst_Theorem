import data.nat.basic
import data.int.nat_prime
import data.rat.basic
import data.complex.basic
import tactic
import data.real.basic
import data.nat.prime
import ring_theory.principal_ideal_domain
import ring_theory.roots_of_unity
import algebra.ring 
import algebra.euclidean_domain
import algebra.associated
import algebra.algebra.ordered

lemma h1_lt_3 : 1 < 3 
:= by norm_num

/-Construction of Z[ζ] primitive root of x^3 = 1. The whole process just copies the definitions
of those of zsqrt, by the construction, hope to show that Z[ζ] is an euclidean domain-/
structure int_cubic_root :=
(a : ℤ)
(b : ℤ)

notation `ℤ_ζ`  := int_cubic_root

namespace int_cubic_root
section

instance : decidable_eq ℤ_ζ:=
by tactic.mk_dec_eq_instance 

theorem ext : ∀ {z w : ℤ_ζ }, z = w ↔ z.a = w.a ∧ z.b = w.b
| ⟨x, y⟩ ⟨x', y'⟩ := 
⟨λ h, by injection h; split; assumption,
                      λ ⟨h₁, h₂⟩, by congr; assumption⟩

/-Convert an integer to a Z_ζ n -/
def of_int(m : ℤ) : ℤ_ζ := ⟨m,0⟩
theorem of_int_a(m : ℤ) : (of_int m).a = m := rfl 
theorem of_int_b(m : ℤ) : (of_int m).b = 0 := rfl

/-zero-/
def zero : ℤ_ζ  := of_int 0
instance : has_zero ℤ_ζ := ⟨int_cubic_root.zero⟩
theorem zero_a : (0 : ℤ_ζ ).a = 0 := rfl 
theorem zero_b : (0 : ℤ_ζ ).b = 0 := rfl

instance : inhabited (ℤ_ζ) := ⟨0⟩ 

/-one-/
def one : ℤ_ζ := of_int 1
instance : has_one (ℤ_ζ) := ⟨int_cubic_root.one⟩ 
@[simp] theorem one_a : (1 : (ℤ_ζ)).a = 1 := rfl
@[simp] theorem one_b : (1 : (ℤ_ζ)).b = 0 := rfl
lemma one_eq: (1 : (ℤ_ζ)) = ⟨1, 0⟩  := by simp[ext]

/-representative of ζ in the ring-/
def ζ : ℤ_ζ := ⟨0, 1⟩ 
@[simp] theorem ζ_a : (ζ : (ℤ_ζ)).a = 0 := rfl
@[simp] theorem ζ_b : (ζ : (ℤ_ζ)).b = 1 := rfl

/-addition-/
def add: (ℤ_ζ) → (ℤ_ζ) → (ℤ_ζ)
|⟨x, y⟩ ⟨x', y'⟩ := ⟨x + x', y + y'⟩
instance : has_add ℤ_ζ := ⟨int_cubic_root.add⟩
@[simp] theorem add_def(x y x' y' : ℤ) :
   (⟨x, y⟩ + ⟨x', y'⟩ : ℤ_ζ) = ⟨x + x', y + y'⟩ := rfl 
@[simp] theorem add_a : ∀ z w : ℤ_ζ, (z + w).a = z.a + w.a 
|⟨x, y⟩⟨x', y'⟩ := rfl 
@[simp] theorem add_b : ∀ z w : ℤ_ζ, (z + w).b = z.b + w.b
|⟨x, y⟩⟨x', y'⟩ := rfl 

@[simp] theorem bit0_a(z) : (bit0 z: ℤ_ζ).a = bit0 z.a := add_a _ _ 
@[simp] theorem bit0_b(z) : (bit0 z: ℤ_ζ).b = bit0 z.b := add_b _ _ 

@[simp] theorem bit1_re (z) : (bit1 z : ℤ_ζ).a = bit1 z.a := by simp [bit1]
@[simp] theorem bit1_im (z) : (bit1 z : ℤ_ζ).b = bit0 z.b := by simp [bit1]

/-negation-/
def neg : ℤ_ζ → ℤ_ζ
|⟨x, y⟩ := ⟨-x, -y⟩
instance : has_neg ℤ_ζ := ⟨int_cubic_root.neg⟩
@[simp] theorem neg_a : ∀ z : ℤ_ζ, (-z).a = - z.a 
|⟨x, y⟩ := rfl 
@[simp] theorem neg_b : ∀ z : ℤ_ζ, (-z).b = - z.b 
|⟨x, y⟩ := rfl 

/-mul-/
def mul : ℤ_ζ → ℤ_ζ → ℤ_ζ
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩
instance : has_mul ℤ_ζ := ⟨int_cubic_root.mul⟩
@[simp] theorem mul_def(x y x' y' : ℤ) : 
   (⟨x, y⟩ * ⟨x', y'⟩ : ℤ_ζ) = ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩ := rfl 
@[simp] theorem mul_a : ∀ z w : ℤ_ζ, (z * w).a = z.a * w.a - z.b * w.b
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem mul_b : ∀ z w : ℤ_ζ, (z * w).b = z.a * w.b + z.b * w.a - z.b * w.b
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem zero_prop : (0 : ℤ_ζ).a = 0 ∧ (0 : ℤ_ζ).b = 0 := by exact ⟨zero_a, zero_b⟩

@[simp] theorem zero_add (a : ℤ_ζ) : 0 + a = a := by simp [ext]

/- z = ⟨z.a, z.b⟩; notations-/
theorem eql(z : ℤ_ζ) : z = ⟨z.a, z.b⟩ :=
begin 
     have h1 : z.a = (⟨z.a, z.b⟩ : ℤ_ζ).a, refl,
     have h2 : z.b = (⟨z.a, z.b⟩ : ℤ_ζ).b, refl,
     exact ext.mpr ⟨h1, h2⟩,
end

theorem eql'(z : ℤ_ζ)(m n : ℤ)(h : z.a = m)(h': z.b = n) : z = ⟨m, n⟩ :=
begin
     have h1: z.a = (⟨m, n⟩ : ℤ_ζ).a, by rw h,
     have h2: z.b = (⟨m, n⟩ : ℤ_ζ).b, by rw h',
     exact ext.mpr ⟨h1, h2⟩,
end

/-some theorems, may not be necessary to prove it's a commutative ring-/
@[simp] theorem mul_assoc (a b c: ℤ_ζ) : a * b * c = a * (b * c):= 
begin 
     have h1 : (a * b * c).a = (a * (b * c)).a, 
     calc (a * b * c).a = (⟨a.a, a.b⟩ * ⟨b.a, b.b⟩ * ⟨c.a, c.b⟩ : ℤ_ζ ).a    : by rw [eql a, eql b, eql c] 
                ...     = (a.a * b.a - a.b * b.b) * c.a - (a.a * b.b + a.b * b.a - a.b * b.b) * c.b  
                                                                           : by simp [ext] 
                ...     = a.a * (b.a * c.a - b.b * c.b) - a.b *(b.a * c.b + b.b * c.a - b.b * c.b)
                                                                           : by ring                                                                                                                 
                ...     = (a * (b * c)).a                                  : by simp [ext],
     have h2 : (a * b * c).b = (a * (b * c)).b, 
     calc (a * b * c).b = (⟨a.a, a.b⟩ * ⟨b.a, b.b⟩ * ⟨c.a, c.b⟩ : ℤ_ζ ).b    : by rw [eql a, eql b, eql c] 
                ...     = (a.a * b.a - a.b * b.b) * c.b + (a.a * b.b + a.b * b.a - a.b * b.b) * c.a 
                          - (a.a * b.b + a.b * b.a - a.b * b.b) * c.b      : by simp[ext] 
                ...     = a.a * (b.a * c.b + b.b * c.a - b.b * c.b) + a.b * (b.a * c.a - b.b * c.b) 
                          - a.b * (b.a * c.b + b.b * c.a - b.b * c.b)      : by ring 
                ...     = (a * (b * c)).b                                  : by simp [ext],
     exact ext.mpr ⟨h1, h2⟩,
end

@[simp] theorem left_distrib (a b c : ℤ_ζ) : a.a * b.a + a.a * c.a - (a.b * b.b + a.b * c.b) = a.a * b.a - a.b * b.b + (a.a * c.a - a.b * c.b) 
      ∧a.a * b.b + (a.a * c.b + (b.a * a.b + c.a * a.b)) - (a.b * b.b + a.b * c.b) =
      a.a * b.b + b.a * a.b - a.b * b.b + (a.a * c.b + c.a * a.b - a.b * c.b)
      := 
begin
     have h1:  a.a * b.a + a.a * c.a - (a.b * b.b + a.b * c.b) = a.a * b.a - a.b * b.b + (a.a * c.a - a.b * c.b), by ring, 
     have h2: a.a * b.b + (a.a * c.b + (b.a * a.b + c.a * a.b)) - (a.b * b.b + a.b * c.b) =
      a.a * b.b + b.a * a.b - a.b * b.b + (a.a * c.b + c.a * a.b - a.b * c.b), by ring,
     exact ⟨h1, h2⟩,
end
@[simp] theorem right_distrib(a b c : ℤ_ζ) :a.a * c.a + b.a * c.a - (a.b * c.b + b.b * c.b) = a.a * c.a - a.b * c.b + (b.a * c.a - b.b * c.b) 
    ∧a.a * c.b + (b.a * c.b + (c.a * a.b + c.a * b.b)) - (a.b * c.b + b.b * c.b) =
      a.a * c.b + c.a * a.b - a.b * c.b + (b.a * c.b + c.a * b.b - b.b * c.b)
      := 
begin
     have h1: a.a * c.a + b.a * c.a - (a.b * c.b + b.b * c.b) = a.a * c.a - a.b * c.b + (b.a * c.a - b.b * c.b), by ring,
     have h2: a.a * c.b + (b.a * c.b + (c.a * a.b + c.a * b.b)) - (a.b * c.b + b.b * c.b) =
      a.a * c.b + c.a * a.b - a.b * c.b + (b.a * c.b + c.a * b.b - b.b * c.b), by ring,
     exact ⟨h1, h2⟩,
end
/-commutative ring-/
/-can't just copy codes here, don't know why it can't works, seems the same, so I state some theorems above-/
instance : comm_ring ℤ_ζ :=
by refine_struct
{ add            := (+),
  zero           := (0 : ℤ_ζ),
  neg            := has_neg.neg,
  mul            := (*),
  sub            := λ a b, a + -b,
  one            := (1 : ℤ_ζ),
  npow           := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  nsmul          := @nsmul_rec _ ⟨0⟩ ⟨(+)⟩,
  gsmul          := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨int_cubic_root.neg⟩ };
{intros; try { refl }; 
simp [ext, zero_add, add_mul, mul_add, add_comm, add_left_comm, 
  left_distrib, mul_comm, mul_left_comm, mul_assoc, right_distrib],}

instance : add_comm_monoid ℤ_ζ    := by apply_instance
instance : add_monoid ℤ_ζ         := by apply_instance
instance : monoid ℤ_ζ             := by apply_instance
instance : comm_monoid ℤ_ζ        := by apply_instance
instance : comm_semigroup ℤ_ζ     := by apply_instance
instance : semigroup ℤ_ζ          := by apply_instance
instance : add_comm_semigroup ℤ_ζ := by apply_instance
instance : add_semigroup ℤ_ζ      := by apply_instance
instance : comm_semiring ℤ_ζ      := by apply_instance
instance : semiring ℤ_ζ           := by apply_instance
instance : ring ℤ_ζ               := by apply_instance
instance : distrib ℤ_ζ            := by apply_instance

instance : nontrivial ℤ_ζ :=
⟨⟨0, 1, dec_trivial⟩⟩

/-  ∃ lifts ℕ, ℤ → ℤ_ζ  -/
@[simp] theorem coe_nat_a(m : ℕ) : (m : ℤ_ζ).a = m :=
begin
induction m; simp *,
end
@[simp] theorem coe_nat_b(m : ℕ) : (m : ℤ_ζ).b = 0 :=
begin
induction m; simp *,
end
@[simp] theorem coe_nat_val(m : ℕ): (m : ℤ_ζ) = ⟨m, 0⟩ := 
by simp [ext] 

@[simp] theorem coe_int_a(m : ℤ) : (m : ℤ_ζ).a = m :=
begin 
     cases m; simp[*, int.of_nat_eq_coe, int.neg_succ_of_nat_eq],
end
@[simp] theorem coe_int_im (n : ℤ) : (n : ℤ_ζ).b = 0 :=
by cases n; simp *
@[simp] theorem coe_int_val (n : ℤ) : (n : ℤ_ζ) = ⟨n, 0⟩ :=
by simp [ext]

/-char = 0-/
instance : char_zero ℤ_ζ :=
{ cast_injective := λ m n, by simp [ext]}

/-ℕ coe-/

@[simp] theorem of_int_eq_coe (n : ℤ) : (of_int n : ℤ_ζ) = n :=
by simp [ext, of_int_a, of_int_b]

@[simp] theorem smul_val (n x y : ℤ) : (n : ℤ_ζ) * ⟨x, y⟩ = ⟨n * x, n * y⟩ :=
by simp [ext]

/- zeta in Z_ζ-/
theorem prop_3_3: ζ^3 = ⟨1, 0⟩        :=            by ring

theorem prop_3_4: 1 + ζ + ζ^2 = 0    :=            by ring

/-surprised how powerful simp[ext] can be-/
@[simp] theorem muld_val (x y : ℤ) : ζ * ⟨x, y⟩ = ⟨-y, x - y⟩ :=
by simp[ext]

@[simp] theorem ζmulζ : ζ * ζ = - 1 - ζ :=
calc ζ * ζ  = ζ ^ 2 - 0                                   : by ring
     ...    = ζ ^ 2 - (1 + ζ + ζ^2)                       : by rw[←prop_3_4]
     ...    = -1 - ζ                                      : by ring

@[simp] theorem smuld_val (n x y : ℤ) : ζ * (n : ℤ_ζ) * ⟨x, y⟩ = ⟨-n * y, n * x - n * y⟩ :=
by simp [ext]

theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ_ζ) = x + ζ * y :=
by simp [ext]

/-ζ is the primitive root-/
theorem primitive_ζ : is_primitive_root ζ 3 := 
begin
     have h1: ζ^3 = 1,
     calc ζ^3   = ⟨1, 0⟩       : by exact prop_3_3 
            ... = 1 + ζ * 0   : by exact decompose
            ... = 1           : by ring,
     have h2 : ∀ l : ℕ, (0 < l) → (l < 3) → ζ^l ≠ 1, 
     {intros l h' h'',
     have h2_1: l = 1 ∨ l = 2, by omega,
     cases h2_1,
     calc ζ^l = ζ^1           : by rw h2_1 
          ... = ⟨0, 1⟩         : by simp [ext]
          ... ≠ ⟨1, 0⟩         : by simp [ext]
          ... = 1 + ζ * 0     : by exact decompose
          ... = 1             : by ring,
     calc ζ^l = ζ^2           : by rw h2_1
           ...= ζ * ζ         : by ring 
           ...= -1 - ζ        : by exact ζmulζ
           ... = -(1 + ζ)     : by ring 
           ... = -(⟨1, 0⟩  + ⟨0, 1⟩)   : rfl
           ... = -(⟨1, 1⟩)     : by ring
          ... ≠ ⟨1, 0⟩         : by simp [ext],
     },
     have h3: 0 < 3, by norm_num,
     exact is_primitive_root.mk_of_lt ζ h3 h1 h2,
end

@[simp] theorem add_left_neg(a : ℤ_ζ): -a + a = 0 := by ring

@[simp] theorem exists_pair_ne : ∃ (x y : ℤ_ζ), x ≠ y := 
begin
     have h: (0 : ℤ_ζ) ≠ (1 : ℤ_ζ), by simp[ext],
     exact ⟨0, 1, h⟩,
end

/-conjugation-/
def conj : ℤ_ζ → ℤ_ζ 
| ⟨x, y⟩ := ⟨x-y, -y⟩
@[simp] theorem conj_a: ∀ z : ℤ_ζ, (conj z).a = z.a - z.b
| ⟨x, y⟩ := rfl 
@[simp] theorem conj_b: ∀ z : ℤ_ζ, (conj z).b = - z.b
| ⟨x, y⟩ := rfl 

@[simp] lemma hom_1(a ai b bi: ℤ): 
(⟨a, ai⟩ + ⟨b, bi⟩ : ℤ_ζ).conj.a = ((⟨a, ai⟩ : ℤ_ζ).conj + (⟨b, bi⟩ : ℤ_ζ).conj).a := 
begin
     have h1 :    (⟨a, ai⟩ + ⟨b, bi⟩ : ℤ_ζ).conj.a = a + b - (ai + bi),
     calc         (⟨a, ai⟩ + ⟨b, bi⟩ : ℤ_ζ).conj.a = (⟨a + b, ai + bi⟩ : ℤ_ζ).conj.a   : rfl 
                                ...         = (⟨a + b - (ai + bi), -(ai + bi)⟩ : ℤ_ζ).a  : rfl
                                ...         = a + b - (ai + bi)        : rfl,
     have h2 :    ((⟨a, ai⟩ : ℤ_ζ).conj + (⟨b, bi⟩ : ℤ_ζ).conj).a = a + b - (ai + bi),
     calc         ((⟨a, ai⟩ : ℤ_ζ).conj + (⟨b, bi⟩ : ℤ_ζ).conj).a = (⟨a -ai, -ai⟩ + ⟨b -bi, -bi⟩ : ℤ_ζ).a  : rfl
                                               ...               = (⟨a -ai + (b-bi), -ai + -bi⟩ : ℤ_ζ).a         : rfl 
                                               ...               = a - ai + (b-bi)     : rfl
                                               ...               = a + b - (ai + bi)   : by ring,
     calc (⟨a, ai⟩ + ⟨b, bi⟩ : ℤ_ζ).conj.a = a + b - (ai + bi) : by rw h1 
                               ...       = ((⟨a, ai⟩ : ℤ_ζ).conj + (⟨b, bi⟩ : ℤ_ζ).conj).a : by rw h2,
end

/-- `conj` as an `add_monoid_hom`. -/
def conj_hom : ℤ_ζ →+ ℤ_ζ :=
{ to_fun := conj,
  map_add' := λ ⟨a, ai⟩ ⟨b, bi⟩, ext.mpr ⟨hom_1 a ai b bi, neg_add _ _⟩,
  map_zero' := ext.mpr ⟨rfl, neg_zero⟩ }

@[simp] lemma conj_zero : conj (0 : ℤ_ζ) = 0 :=
conj_hom.map_zero

@[simp] lemma conj_one : conj (1 : ℤ_ζ) = 1 :=
calc conj(1 : ℤ_ζ) = conj(⟨1, 0⟩)            : rfl 
             ...   = ⟨1, 0⟩                  : rfl 
             ...   = 1                      : rfl

@[simp] lemma conj_neg (x : ℤ_ζ) : (-x).conj = -x.conj :=
conj_hom.map_neg x
@[simp] lemma conj_add (x y : ℤ_ζ) : (x + y).conj = x.conj + y.conj :=
conj_hom.map_add x y
@[simp] lemma conj_sub (x y : ℤ_ζ) : (x - y).conj = x.conj - y.conj :=
conj_hom.map_sub x y

@[simp] lemma conj_conj_1 (x y : ℤ):  x - y - -y = x := by ring
@[simp] lemma conj_conj (x : ℤ_ζ) : x.conj.conj = x :=
by simp only [ext, true_and, conj_a, conj_conj_1, eq_self_iff_true, 
neg_neg, conj_b]

theorem mul_conj (x y : ℤ) : (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ_ζ) = (x^2 - x * y + y^2 : ℤ_ζ):=
begin
have h1: x * -y + y * (x - y) - y * -y = 0, by ring,
have h2: x * (x-y) - y* (-y) = x^2 - x * y + y^2, by ring,
let z : ℤ := x^2 - x * y + y^2, 
have h3: z = x^2 - x * y + y^2, refl,
have h6 : x * x - 0 * 0 = x^2 ∧ x * 0 + 0 * x - 0 * 0 = 0, {split,{ring,}, {ring},},
have h7 : x * y - 0 * 0 = x * y ∧ x * 0 + 0 * y - 0 * 0 = 0, {split,{ring,}, {ring},},
have h8 : y * y - 0 * 0 = y^2 ∧ y * 0 + 0 * y - 0 * 0 = 0, {split,{ring,}, {ring},},
have h5: (⟨x, 0⟩ * ⟨x, 0⟩ - ⟨x, 0⟩ * ⟨y, 0⟩ + ⟨y, 0⟩ * ⟨y, 0⟩ : ℤ_ζ) = ⟨x^2, 0⟩ - ⟨x*y, 0⟩ + ⟨y^2, 0⟩,
     calc (⟨x, 0⟩ * ⟨x, 0⟩ - ⟨x, 0⟩ * ⟨y, 0⟩ + ⟨y, 0⟩ * ⟨y, 0⟩ : ℤ_ζ) = ⟨x * x - 0 * 0, x * 0 + 0 * x - 0 * 0⟩ 
     - ⟨x * y - 0 * 0, x * 0 + 0 * y - 0 * 0⟩ + ⟨y * y - 0 * 0, y * 0 + 0 * y - 0 * 0⟩  : rfl 
     ... = ⟨x^2, 0⟩ -  ⟨x*y, 0⟩ + ⟨y^2, 0⟩ : by rw[h6.1, h6.2, h7.1, h7.2, h8.1, h8.2],
have h4: (z : ℤ_ζ) = (x^2 - x * y + y^2 : ℤ_ζ), 
calc (z : ℤ_ζ) = ⟨z, 0⟩                      : by exact coe_int_val z
         ...   = ⟨x^2 - x * y + y^2, 0⟩      : by rw h3
         ...   = ⟨x^2, 0⟩ - ⟨x*y, 0⟩ + ⟨y^2, 0⟩   : rfl
         ...   = ⟨x, 0⟩ * ⟨x, 0⟩ - ⟨x, 0⟩ * ⟨y, 0⟩ + ⟨y, 0⟩ * ⟨y, 0⟩ : by rw h5
         ...   = (x * x - x * y + y * y : ℤ_ζ)       : by rw [coe_int_val x, coe_int_val y]
         ...   = (x^2 - x * y + y^2 : ℤ_ζ)           : by ring,
calc (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ_ζ) = (⟨x, y⟩ * ⟨x- y, -y⟩  : ℤ_ζ)  : rfl 
                         ...     = ⟨x * (x-y) - y* (-y),  x * -y + y * (x - y) - y * -y⟩ 
                                                 : by exact mul_def x y (x-y) (-y)
                         ...     = ⟨(x * (x-y) - y* (-y)),  0⟩     : by rw h1 
                         ...     = ⟨x^2 - x * y + y^2, 0⟩          : by rw h2
                         ...     = ⟨z, 0⟩                          : rfl
                         ...     = z + ζ * 0                      : by exact decompose
                         ...     = (z : ℤ_ζ)                      : by ring 
                         ...     = x^2 - x * y + y^2              : by rw h4,
end

theorem conj_mul {a b : ℤ_ζ} : conj (a * b) = conj a * conj b :=
begin
     have h1 : (conj (a * b)).a = (conj a * conj b).a, 
     calc (conj (a * b)).a = (conj(⟨a.a, a.b⟩ * ⟨b.a, b.b⟩)).a    : by rw [eql a, eql b]
                 ...       = (conj(⟨a.a * b.a - a.b * b.b, a.a * b.b + a.b * b.a - a.b * b.b⟩)).a : rfl 
                 ...       = (⟨a.a * b.a - a.b * b.b - (a.a * b.b + a.b * b.a - a.b * b.b), -(a.a * b.b + a.b * b.a - a.b * b.b)⟩ : ℤ_ζ).a : rfl 
                 ...       = a.a * b.a - a.b * b.b - (a.a * b.b + a.b * b.a - a.b * b.b) : rfl 
                 ...       = (a.a - a.b) * (b.a - b.b) - (-a.b) * (-b.b) : by ring 
                 ...       = (⟨a.a - a.b, -a.b⟩ * ⟨b.a - b.b, -b.b⟩ : ℤ_ζ).a     : by simp[ext]
                 ...       = (conj(⟨a.a, a.b⟩) * conj(⟨b.a, b.b⟩)).a     : rfl 
                 ...       = (conj a * conj b).a                 : by rw [eql a, eql b],
     have h2 : (conj (a * b)).b = (conj a * conj b).b, 
     calc (conj (a * b)).b = (conj(⟨a.a, a.b⟩ * ⟨b.a, b.b⟩)).b   : by rw [eql a, eql b]
                 ...       = (conj(⟨a.a * b.a - a.b * b.b, a.a * b.b + a.b * b.a - a.b * b.b⟩)).b : rfl 
                 ...       = (⟨a.a * b.a - a.b * b.b - (a.a * b.b + a.b * b.a - a.b * b.b), -(a.a * b.b + a.b * b.a - a.b * b.b)⟩ : ℤ_ζ).b : rfl 
                 ...       = -(a.a * b.b + a.b * b.a - a.b * b.b) : rfl 
                 ...       = (a.a -a.b) * (-b.b) + (-a.b)*(b.a- b.b) -(-a.b) * (-b.b) : by ring 
                 ...       = (⟨a.a - a.b, -a.b⟩ * ⟨b.a - b.b, -b.b⟩ : ℤ_ζ).b     : by simp[ext]
                 ...       = (conj(⟨a.a, a.b⟩) * conj(⟨b.a, b.b⟩)).b     : rfl 
                 ...       = (conj a * conj b).b                 : by rw [eql a, eql b],
     exact ext.mpr⟨h1, h2⟩,
end
theorem conj_mul_0 : ∀ (x y : ℤ_ζ), conj(x * y) = conj x * conj y :=
begin 
     intros x y,
     exact conj_mul,
end

/-- `conj` as a `monoid_hom`. -/
def conj_monoid_hom : ℤ_ζ →* ℤ_ζ :=
{ to_fun := conj,
  map_mul' := conj_mul_0,
  map_one' := conj_one }

/-norm-/
def norm (n : ℤ_ζ) : ℤ := n.a * n.a - n.a * n.b + n.b * n.b
lemma norm_def (n : ℤ_ζ) : n.norm = n.a * n.a - n.a * n.b + n.b * n.b := rfl

@[simp] theorem norm_nonneg : ∀ x : ℤ_ζ, norm x ≥ 0 :=
begin
     intro x,
     calc norm x  = x.a * x.a - x.a * x.b + x.b * x.b  : by exact norm_def x
           ...   ≥ 0                                   : by nlinarith,
end

@[simp] theorem norm_mul_0 : ∀ x y : ℤ_ζ, x.norm * y.norm = (x * y).norm :=
begin
intros x y,
have h1: x.norm = (x.a)^2 - x.a * x.b + (x.b)^2, 
calc x.norm = x.a * x.a - x.a * x.b + x.b * x.b  : rfl
        ... =  (x.a)^2 - x.a * x.b + (x.b)^2     : by ring,
have h2: y.norm = (y.a)^2 - y.a * y.b + (y.b)^2, 
calc y.norm = y.a * y.a - y.a * y.b + y.b * y.b  : rfl
        ... =  (y.a)^2 - y.a * y.b + (y.b)^2     : by ring,
have h3: (x*y).norm = (x.a * y.a - x.b * y.b)^2 - (x.a * y.a - x.b* y.b) * (x.a * y.b + x.b * y.a - x.b * y.b)
                       + (x.a * y.b + x.b * y.a - x.b * y.b)^2,
calc (x*y).norm = (⟨x.a, x.b⟩ * ⟨y.a, y.b⟩ : ℤ_ζ).norm                                    : by rw [eql x, eql y]
          ...   = (⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩ : ℤ_ζ).norm : rfl 
          ...   = ((x.a * y.a - x.b * y.b) * (x.a * y.a - x.b * y.b)  - (x.a * y.a - x.b* y.b) * (x.a * y.b + x.b * y.a - x.b * y.b)
                       + (x.a * y.b + x.b * y.a - x.b * y.b) * (x.a * y.b + x.b * y.a - x.b * y.b))    : rfl
          ...   = ((x.a * y.a - x.b * y.b)^2  - (x.a * y.a - x.b* y.b) * (x.a * y.b + x.b * y.a - x.b * y.b)
                       + (x.a * y.b + x.b * y.a - x.b * y.b)^2)                         : by ring,
calc x.norm * y.norm = ((x.a)^2 - x.a * x.b + (x.b)^2)* ((y.a)^2 - y.a * y.b + (y.b)^2) : by rw [h1, h2]
             ...     = ((x.a * y.a - x.b * y.b)^2 - (x.a * y.a - x.b* y.b) * (x.a * y.b + x.b * y.a - x.b * y.b)
                       + (x.a * y.b + x.b * y.a - x.b * y.b)^2)                         : by ring 
             ...     = (x * y).norm                                                     : by rw ←h3,
end

@[simp] lemma norm_zero : norm 0 = 0 := by simp [norm]
@[simp] lemma norm_one : norm 1 = 1 := by simp [norm]
@[simp] lemma norm_int_cast (n : ℤ) : norm n = n * n := by simp [norm]
@[simp] lemma norm_nat_cast (n : ℕ) : norm n = n * n := norm_int_cast n

@[simp] lemma norm_mul (n m : ℤ_ζ) : norm (n * m) = norm n * norm m :=
by exact eq.symm(norm_mul_0 n m)

/-- `norm` as a `monoid_hom`. -/
def norm_monoid_hom : ℤ_ζ →* ℤ :=
{ to_fun := norm,
  map_mul' := norm_mul,
  map_one' := norm_one }

@[simp] lemma norm_eq_mul_conj (n : ℤ_ζ) : (norm n : ℤ_ζ) = n * n.conj :=
begin
     have h1: (norm n : ℤ_ζ) = ⟨n.a * n.a - n.a * n.b + n.b * n.b, 0⟩,
     calc (norm n : ℤ_ζ) = ⟨norm n, 0⟩  : by exact coe_int_val (norm n) 
               ...       = ⟨n.a * n.a - n.a * n.b + n.b * n.b, 0⟩   : rfl,
     have t1: n.a * (n.a - n.b) - n.b * (-n.b) = n.a * n.a - n.a * n.b + n.b * n.b, by ring,
     have t2: n.a * (-n.b) + n.b * (n.a - n.b) - n.b * (-n.b) = 0, by ring,
     have h2: n * n.conj = ⟨n.a * n.a - n.a * n.b + n.b * n.b, 0⟩,
     calc n * n.conj = ⟨n.a, n.b⟩ * conj⟨n.a, n.b⟩  : by rw eql n 
            ...      = ⟨n.a, n.b⟩ * ⟨n.a - n.b, -n.b⟩  : rfl 
            ...      = ⟨n.a * (n.a - n.b) - n.b * (-n.b), n.a * (-n.b) + n.b * (n.a - n.b) - n.b * (-n.b)⟩ : rfl 
            ...      = ⟨n.a * n.a - n.a * n.b + n.b * n.b, 0⟩  :  by rw[t1,t2],
     rw[h1,h2],
end

@[simp] lemma norm_neg (x : ℤ_ζ) : (-x).norm = x.norm :=
calc (-x).norm = (⟨(-x).a, (-x).b⟩ : ℤ_ζ).norm  : by rw eql (-x)
           ... = (-x).a*(-x).a - (-x).a * (-x).b + (-x).b * (-x).b      : rfl 
           ... = (-x.a) * (-x.a) - (-x.a) * (-x.b) + (-x.b) * (-x.b)    : by rw [neg_a x, neg_b x]
           ... = (x.a) * (x.a) - (x.a) * (x.b) + (x.b) * (x.b)          : by ring 
           ... = x.norm                                                 : rfl

@[simp] lemma norm_conj (x : ℤ_ζ) : x.conj.norm = x.norm :=
calc x.conj.norm = (⟨x.a, x.b⟩ : ℤ_ζ).conj.norm                                           : by rw eql x 
             ... = (⟨x.a - x.b, -x.b⟩ : ℤ_ζ).norm                                         : rfl 
             ... = (x.a - x.b) * (x.a - x.b) - (x.a - x.b) * (-x.b) + (-x.b)* (-x.b)     : rfl
             ... = x.a * x.a - x.a * x.b + x.b * x.b                                     : by ring 
             ... = x.norm                                                                : rfl

@[simp] lemma norm_nat: ∀ n : ℤ, ∀ x : ℤ_ζ, (of_int n * x).norm = n^2 * x.norm :=
begin
     intros n x,
     have h1: of_int n * x = ⟨n * x.a, n * x.b⟩, by simp[ext],
     calc (of_int n * x).norm = (⟨n * x.a, n * x.b⟩ : ℤ_ζ).norm  :  by rw h1 
                        ...   = (n * x.a)*(n * x.a) - (n * x.a * (n * x.b)) 
                              + (n * x.b)*(n * x.b)   : rfl 
                        ...   = n^2 * (x.a * x.a - x.a * x.b + x.b * x.b)  : by ring 
                        ...   = n^2 * x.norm       : rfl,
end

@[simp] lemma norm_nonneg_0 (n : ℤ_ζ) : 0 ≤ n.norm :=
by exact norm_nonneg n

lemma norm_eq_one_0(a : ℤ) : a ≥ 0 ∧ a ≠ 0 → a > 0 := 
begin
     intro h,
     contrapose! h,
     finish,
end

/-unit-/
lemma lt_le_succ(a b : ℤ) : b > a → b ≥ a.succ :=
by tauto

lemma left_add_nonneg(a b : ℤ):  a ≥ 0 → a + b ≥ b  := by omega

lemma pow_two_abs(b : ℤ) : b^2 = (abs b)^2 := 
begin
     have h1: abs b = b ∨ abs b = -b, by exact abs_choice b,
     cases h1,
     {by rw h1,},
     {calc b^2 = (-b)^2  : by ring 
          ...  = (abs b)^2 : by rw h1,},
end

lemma little_1(n : ℤ) : n ≤ 1 ∧ n ≥ 0 → n = 0 ∨ n = 1 :=
by omega

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
     by exact little_1 (abs a) ⟨h3, abs_nonneg a⟩,
     have h5: abs b = 0 ∨ abs b = 1, 
     by exact little_1 (abs b) ⟨h2, abs_nonneg b⟩,
     have h6: (abs a = 0 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1)∨ (abs a = 1 ∧ abs b = 0) ∨ (abs a = 1 ∧ abs b = 1),
     by tauto, /-amazing tactic!-/
     have h7: ¬(abs a = 0 ∧ abs b = 0),
     {contrapose! h,
      have t1: a = 0, by exact abs_eq_zero.mp h.1,
      have t2: b = 0, by exact abs_eq_zero.mp h.2,
      have t3: a^2 - a*b + b^2 ≠ 1,
      calc a^2 - a * b + b^2 = 0^2 - 0 * 0 + 0^2 : by rw [t1,t2] 
      ...                   = 0                 : by ring 
      ...                   ≠ 1                 : by norm_num,
      exact t3,
     },
     have h8: ¬(abs a = 0 ∧ abs b = 0) ∧ ((abs a = 0 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1)∨ (abs a = 1 ∧ abs b = 0) ∨ (abs a = 1 ∧ abs b = 1)),
     by exact ⟨h7, h6⟩,
     tauto,
end 

lemma abs_either: ∀ x : ℤ, x = abs x ∨ x = -abs x :=
begin
     intro x;
     have h: abs x = x ∨ abs x = -x,  by exact abs_choice x,
     cases h,
     {tauto},
     {have h1 : x = -abs x, 
     calc x = -(-x)  : by ring 
         ...= -(abs x) : by rw h 
         ...= -abs x   : by ring,
     tauto,},
end

@[simp] lemma norm_eq_one_3(a b :ℤ) : (a^2 - a * b + b^2 = 1) ∧ ((abs a = 1 ∧ abs b = 1)) → 
(a = 1 ∧ b = 1) ∨ (a = -1 ∧  b = -1) :=
begin
     intro h;
     have e: a^2 -a*b + b^2 = 1, by exact h.1,
     have h1: abs a = 1, by exact (h.2).1,
     have h2: abs b = 1, by exact (h.2).2,
     have h3: a = 1 ∨ a = -1, 
     {have t1: a = abs a ∨ a = - abs a, by exact abs_either a,
     cases t1,
     {have t2: a = 1, 
          calc a  = abs a  : by exact t1 
          ... = 1      : by rw h1, 
     tauto,
     },
     {have t3: a = -1,
          calc a = -abs a : by exact t1 
            ...  = -1     : by rw h1 ,
     tauto,}},
     have h4: b = 1∨ b = -1,
     {have t1: b = abs b ∨ b = - abs b, by exact abs_either b,
     cases t1,
     {have t2: b = 1, 
          calc b  = abs b  : by exact t1 
          ... = 1      : by rw h2, 
     tauto,
     },
     {have t3: b = -1,
          calc b = -abs b : by exact t1 
            ...  = -1     : by rw h2 ,
     tauto,}},
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

@[simp] lemma norm_eq_one_1 {x : ℤ_ζ}: (x.a^2 - x.a * x.b + x.b^2 = 1) → 
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
     {have h3: x = ⟨-1, -1⟩, {simp[ext], exact h2,},tauto,},}},
end


lemma not1 (a : ℤ) : a > 0 ∧ a ≠ 1 → a > 1 :=
by omega


lemma norm_eq_zero_iff (z : ℤ_ζ) : z.norm = 0 ↔ z = 0 :=
begin
  split,
  { intro h,
    rw [ext, zero_a, zero_b],
    have h1 : z.a * z.a - z.a * z.b + z.b * z.b = 0, by exact h,
    have h2: (2* z.a - z.b)^2 + 3*z.b^2 = 0,
    calc (2* z.a - z.b)^2 + 3*z.b^2 = 4 * (z.a * z.a - z.a * z.b + z.b * z.b) 
                                   : by ring 
                   ...              = 4 * 0               : by rw h1 
                   ...              = 0                   : by norm_num,
    have h3: z.b = 0, by nlinarith,
    have h4: (2*z.b - z.a)^2 + 3 * z.a ^2 =0,
    calc (2*z.b - z.a)^2 + 3 * z.a ^2 = 4 * (z.a* z.a - z.a * z.b + z.b * z.b) 
                                   : by ring 
                              ...     = 4 * 0             : by rw h1 
                              ...     = 0                 : by norm_num,
    have h5: z.a = 0, by nlinarith,
    exact ⟨h5, h3⟩,
   },
  { rintro rfl, exact norm_zero }
end

lemma gt_if_ge_ne(a b : ℤ) : a ≥ b ∧ a ≠ b → a > b := by omega 
lemma abs_pow_two(a : ℤ): a^2 = (abs a)^2 := 
begin
     have h: abs a = a ∨ abs a = -a, by exact abs_choice a,
     cases h,
     {rw h,},
     {calc a^2 = (-a)^2 : by ring 
          ...  = (abs a)^2  : by rw h,},
end

lemma abs_eq_zero (a : ℤ) : abs a = 0 → a = 0  :=
begin
     have h : abs a = a ∨ abs a = -a, by exact abs_choice a,
     cases h,
     {omega,},
     {omega,},
end

lemma abs_ge_zero (a : ℤ) : a ≥ 0 → abs a = a :=
begin
     intro h,
     have h1: a ≥ -a, by linarith,
     have h2: max a (-a) = a, by exact max_eq_left h1,
     tauto,
end

@[simp] lemma norm_eq_one_iff {x : ℤ_ζ} : x.norm.nat_abs = 1 ↔ is_unit x :=
begin
split,
{
intro h,
have h0: x.norm = 1, 
calc x.norm  = abs x.norm               :  by rw abs_ge_zero x.norm (norm_nonneg x) 
        ...  = ((x.norm).nat_abs :ℤ)   : by exact int.abs_eq_nat_abs x.norm 
        ...  =  (1 : ℤ)                  : by linarith [h],
have h0_1: x.a^2 - x.a * x.b + x.b^2 = 1, 
calc x.a^2 - x.a * x.b + x.b^2 = x.a * x.a - x.a * x.b + x.b * x.b  : by ring
                       ...     = 1                                  : by exact h0,
have h1: (abs x.a = 1 ∧ abs x.b = 0) ∨ (abs x.a = 0 ∧ abs x.b = 1) ∨  (x = ⟨1, 1⟩ ∨ (x = ⟨-1, -1⟩)), 
by exact norm_eq_one_1 h0_1,
 cases h1,
 {have h2: ∃ y : ℤ_ζ,  x * y = 1, 
 { have t1: x.a * x.a = 1, 
 calc x.a * x.a = x.a ^ 2 : by ring 
          ...   = (abs x.a)^2         : by exact abs_pow_two x.a
          ...   = 1^2                 : by rw h1.1 
          ...   = 1                   : by norm_num,
 use ⟨x.a, 0⟩, 
 have a: x.b = 0, by exact abs_eq_zero x.b h1.2,
 calc x * ⟨x.a, 0⟩ = ⟨x.a, x.b⟩ * ⟨x.a, 0⟩   :  by rw eql x 
           ...  = ⟨x.a, 0⟩ * ⟨x.a, 0⟩       :  by rw a 
           ...  = ⟨x.a * x.a - 0 * 0, x.a * 0 + 0 * x.a - 0 * 0⟩  : rfl 
           ...  = ⟨x.a * x.a, 0⟩           : by norm_num
           ...  = ⟨1, 0⟩                   : by rw t1 
           ...  = 1                       : rfl,
 },
 cases h2 with y ty,
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x y ty,
 tauto,},
 {cases h1,
 {have e1: x.b^2 = x.b * x.b, by ring,
 have a : x.a = 0, by exact abs_eq_zero x.a h1.1,
 have f1: x * ⟨-x.b, -x.b⟩  = 1,
 calc x* ⟨-x.b, -x.b⟩ = ⟨x.a, x.b⟩* ⟨-x.b, -x.b⟩ : by rw eql x
       ...          = ⟨0, x.b⟩ * ⟨-x.b, -x.b⟩  :  by rw a
       ...          = ⟨0 * (-x.b) - x.b * (-x.b), 0 * (-x.b) + x.b * (-x.b) - x.b * (-x.b)⟩  :  rfl 
       ...          = ⟨x.b * x.b, 0⟩            : by norm_num 
       ...          = ⟨x.b^2, 0⟩              : by rw e1
       ...          = ⟨(abs x.b)^2, 0⟩        : by rw abs_pow_two x.b 
       ...          = ⟨1^2, 0⟩                : by rw h1.2 
       ...          = ⟨1, 0⟩                  : by norm_num 
       ...          =  1                     : rfl, 
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨-x.b, -x.b⟩ f1,
 tauto,},
 {cases h1,
 {have f: x * ⟨0, -1⟩ = 1, 
 calc x * ⟨0, -1⟩  = ⟨1, 1⟩ * ⟨0, -1⟩       : by rw h1
          ...  = ⟨1 * 0 - 1 * (-1), 1 * (-1) + 1 * 0 - 1 * (-1)⟩   : rfl 
          ...  = ⟨1, 0⟩                    : by norm_num
          ...  =  1                       : rfl,
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨0, -1⟩ f,
 tauto,},
 {have f: x * ⟨0, 1⟩ = 1, 
 calc x * ⟨0, 1⟩  = ⟨-1, -1⟩ * ⟨0, 1⟩       : by rw h1
          ...  = ⟨(-1) * 0 - (-1) * 1, (-1) * 1 + (-1) * 0 - (-1) * 1⟩   : rfl 
          ...  = ⟨1, 0⟩                    : by norm_num
          ...  =  1                       : rfl,
 have h3: is_unit x,
 by exact is_unit_of_mul_eq_one x ⟨0, 1⟩ f,
 tauto,},}}
},
{intro h,
have h1: ∃ y, x*y = 1, by exact is_unit.exists_right_inv h,
cases h1 with y h1',
have h2: norm x * norm y = 1, 
calc norm x * norm y = norm (x*y)  : by rw norm_mul x y 
                ...  = norm  1     : by rw h1' 
                ...  = 1           : by try{refl'},
have a1: norm x ≠ 0, {contrapose! h2, 
calc x.norm * y.norm = 0 * y.norm  : by rw h2 
                 ... = 0           : by norm_num
                 ... ≠ 1           : by linarith,},
have a2: norm y ≠ 0, {contrapose! h2,
calc x.norm * y.norm = x.norm * 0  : by rw h2 
                ...  =  0          : by norm_num 
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

lemma is_unit_iff_norm_is_unit {d : ℤ} (z : ℤ_ζ) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs_eq, norm_eq_one_iff]

lemma norm_eq_one_iff'  (z : ℤ_ζ) : z.norm = 1 ↔ is_unit z :=
by rw [←norm_eq_one_iff, ←int.coe_nat_inj', int.nat_abs_of_nonneg (norm_nonneg_0 z),
  int.coe_nat_one]



lemma norm_eq_of_associated {d : ℤ} {x y : ℤ_ζ} (h : associated x y) :
  x.norm = y.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  rw [norm_mul, (norm_eq_one_iff' _).mpr u.is_unit, mul_one],
end

/-quotient-/
def quotient: ℤ_ζ → ℤ_ζ → ℤ_ζ | ⟨x, y⟩ ⟨x', y'⟩ 
       := ⟨round ((x * x' - x * y' + y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
          round ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩ 
lemma quotient_def (x y x' y': ℤ) : quotient ⟨x, y⟩ ⟨x', y'⟩  = 
          ⟨round ((x * x' - x * y' + y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
          round ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩  := rfl

lemma div_zero (n : ℤ_ζ): quotient n 0 = 0 := 
begin 
have h1: round ((n.a * 0 - n.a * 0 + n.b * 0 : ℚ)/(0^2 - 0 * 0 + 0^2 : ℚ)) = 0,
calc round ((n.a * 0 - n.a * 0 + n.b * 0 : ℚ)/(0^2 - 0 * 0 + 0^2 : ℚ)) 
                    = round ((0 : ℚ)/(0 : ℚ))  : by norm_num 
       ...          = 0                         : by norm_num,
have h2: round ((-n.a * 0 + 0 * n.b : ℚ)/(0^2 - 0 * 0 + 0 ^2 : ℚ)) = 0,
calc round ((-n.a * 0 + 0 * n.b : ℚ)/(0^2 - 0 * 0 + 0 ^2 : ℚ)) 
     = round ((0 : ℚ)/(0 : ℚ))  : by norm_num 
     ...          = 0             : by norm_num,
calc quotient n 0 = quotient ⟨n.a, n.b⟩ 0  : by rw eql n 
            ...   = quotient ⟨n.a, n.b⟩ ⟨0, 0⟩  : rfl 
            ...   = ⟨round ((n.a * 0 - n.a * 0 + n.b * 0 : ℚ)/(0^2 - 0 * 0 + 0^2 : ℚ)), 
                    round ((-n.a * 0 + 0 * n.b : ℚ)/(0^2 - 0 * 0 + 0 ^2 : ℚ))⟩  : by exact quotient_def n.a n.b 0 0
            ...   = ⟨0, 0⟩          : by rw [h1,h2]
            ...   = (0: ℤ_ζ)       : rfl,
end 

@[simp] theorem add_assoc : ∀ (a b c : ℤ_ζ), a + b + c = a + (b + c) :=
begin
     intros a b c,
     have h1: (a + b + c).a = (a + (b + c)).a, by ring_nf,
     have h2: (a + b + c).b = (a + (b + c)).b, by ring_nf,
     exact ext.mpr⟨h1, h2⟩,
end
@[simp] theorem nsmul_zero' : ∀ (x : ℤ_ζ), nsmul 0 x = 0 :=
begin
     intro x,
     calc nsmul 0 x = nsmul 0 ⟨x.a, x.b⟩   : by rw eql x
               ...  = ⟨0 * x.a, 0 * x.b⟩   : by ring_nf
               ...  = ⟨0, 0⟩               : by norm_num 
               ...  = 0                    : rfl,
end

@[simp] theorem nsmul_succ' : ∀ (n : ℕ) (x : ℤ_ζ), nsmul n.succ x = x + nsmul n x :=
begin
     intros;
     try{refl'},
end

@[simp] theorem sub_eq_add_neg :  ∀ (a b : ℤ_ζ), a - b = a + -b := 
begin
     intros a b,
     calc a - b = ⟨a.a, a.b⟩ - ⟨b.a, b.b⟩        : by rw[eql a, eql b]
           ...  = ⟨a.a - b.a, a.b - b.b⟩        : by ring_nf
           ...  = ⟨a.a + (-b.a), a.b + (-b.b)⟩  : by ring 
           ...  = ⟨a.a + (-b).a, a.b + (-b).b⟩  : by rw[←neg_a b, ←neg_b b]
           ...  = ⟨a.a, a.b⟩ + ⟨(-b).a, (-b).b⟩  : by ring_nf
           ...  = a + (-b)                     : by rw[← eql a, ← eql (-b)]
           ...  = a + -b                       : rfl,
end

@[simp] theorem gsmul_zero' : ∀ (a : ℤ_ζ), gsmul_rec 0 a = 0 :=
 begin
     intro x,
     calc nsmul 0 x = nsmul 0 ⟨x.a, x.b⟩   : by rw eql x
               ...  = ⟨0 * x.a, 0 * x.b⟩   : by ring_nf
               ...  = ⟨0, 0⟩               : by norm_num 
               ...  = 0                    : rfl,
end

@[simp] theorem gsmul_succ': ∀ (n : ℕ) (a : ℤ_ζ), gsmul_rec (int.of_nat n.succ) a = a + gsmul_rec (int.of_nat n) a :=
begin
     intros;
     try{refl},
end

@[simp] theorem gsmul_neg' : ∀ (n : ℕ) (a : ℤ_ζ), gsmul_rec -[1+ n] a = -gsmul_rec ↑(n.succ) a :=
begin
     intros;
     try{refl},
end

@[simp] theorem add_comm :  ∀ (a b : ℤ_ζ), a + b = b + a :=
begin
intros a b,
have h1 : a.a + b.a = b.a + a.a, by ring,
have h2 : a.b + b.b = b.b + a.b, by ring,
calc a + b = (⟨a.a, a.b⟩  + ⟨b.a, b.b⟩  :ℤ_ζ)  : by rw[eql a, eql b]
        ...= ⟨a.a + b.a, a.b + b.b⟩             : rfl 
        ...= ⟨b.a + a.a, b.b + a.b⟩            : by rw [h1,h2]
        ...= ⟨b.a, b.b⟩ + ⟨a.a, a.b⟩            : rfl 
        ...= b + a                            : by rw[eql a, eql b],
end

@[simp] theorem one_mul : ∀ (a : ℤ_ζ), 1 * a = a :=
begin
     intros a,
     have h1: 1 * a.a - 0 * a.b = a.a, by ring,
     have h2: 1 * a.b + 0 * a.a - 0 * a.b = a.b, by ring,
     calc 1 * a = ⟨1, 0⟩ * a                   : by refl'
         ...    = ⟨1, 0⟩ * ⟨a.a, a.b⟩           : by rw eql a
         ...    = ⟨1 * a.a - 0 * a.b, 1 * a.b + 0 * a.a - 0 * a.b⟩   : rfl
         ...    = ⟨a.a, a.b⟩                   : by  rw [h1,h2]
         ...    = a                           :  by rw eql a,
end

@[simp] theorem mul_one : ∀ (a : ℤ_ζ), a * 1 = a := 
begin
     intro a,
     have h1: a.a * 1 - a.b * 0 = a.a, by ring,
     have h2: a.a * 0 + a.b * 1 - a.b * 0 = a.b, by ring,
     calc a * 1 = a * ⟨1, 0⟩           : by refl'
          ...   = ⟨a.a, a.b⟩ * ⟨1, 0⟩   : by rw eql a
          ...   = ⟨a.a * 1 - a.b * 0,  a.a * 0 + a.b * 1 - a.b * 0⟩    : rfl
          ...   = ⟨a.a, a.b⟩                   : by rw [h1,h2]
          ...   = a                           : by rw eql a,
end

@[simp] theorem npow_zero' :  ∀ (x : ℤ_ζ), npow_rec 0 x = 1 :=
begin
intros; 
try {refl},
end

@[simp] theorem npow_succ' :  ∀ (n : ℕ) (x : ℤ_ζ), npow_rec n.succ x = x * npow_rec n x :=
begin
intros;
try{refl},
end

@[simp] theorem left_distrib_0 : ∀ (a b c : ℤ_ζ), a * (b + c) = a * b + a * c :=
begin
     intros a b c,
     have h1 : a.a * (b.a + c.a) - a.b * (b.b + c.b) = a.a * b.a - a.b * b.b + (a.a * c.a - a.b * c.b), by ring,
     have h2:  a.a * (b.b + c.b) + a.b * (b.a + c.a) - a.b * (b.b + c.b) = a.a * b.b + a.b * b.a - a.b * b.b + (a.a * c.b + a.b * c.a - a.b * c.b), by ring,
     calc a * (b + c) = ⟨a.a, a.b⟩ * (⟨b.a, b.b⟩  + ⟨c.a, c.b⟩ : ℤ_ζ)   : by rw[eql a, eql b, eql c]
               ...    = ⟨a.a, a.b⟩ * ⟨b.a + c.a, b.b + c.b⟩            : rfl
               ...    = ⟨a.a * (b.a + c.a) - a.b * (b.b + c.b), a.a * (b.b + c.b) + a.b * (b.a + c.a) - a.b * (b.b + c.b)⟩ : rfl
               ...    = ⟨a.a * b.a - a.b * b.b + (a.a * c.a - a.b * c.b), a.a * b.b + a.b * b.a - a.b * b.b + (a.a * c.b + a.b * c.a - a.b * c.b)⟩  : by rw[h1,h2]
               ...    = ⟨a.a, a.b⟩ * ⟨b.a, b.b⟩ + ⟨a.a, a.b⟩ * ⟨c.a, c.b⟩    : rfl
               ...    = a * b + a * c    : by rw[eql a, eql b, eql c],
end

@[simp] theorem right_distrib_0 : ∀ (a b c : ℤ_ζ), (a + b) * c = a * c + b * c :=
begin
     intros a b c,
     have h1: (a.a + b.a)* c.a - (a.b + b.b) * c.b = a.a * c.a - a.b * c.b + (b.a* c.a - b.b * c.b), by ring,
     have h2: (a.a + b.a)* c.b + (a.b + b.b)* c.a - (a.b + b.b) * c.b = 
               a.a * c.b + a.b * c.a - a.b * c.b + (b.a * c.b + b.b * c.a - b.b * c.b), by ring,
     calc (a + b) * c = (⟨a.a, a.b⟩ + ⟨b.a, b.b⟩) * ⟨c.a, c.b⟩    : by rw[eql a, eql b, eql c]
               ...    = ⟨a.a + b.a, a.b + b.b⟩ * ⟨c.a, c.b⟩      : rfl 
               ...    = ⟨(a.a + b.a)* c.a - (a.b + b.b) * c.b, (a.a + b.a)* c.b + (a.b + b.b)* c.a - (a.b + b.b) * c.b⟩  : rfl
               ...    = ⟨a.a * c.a - a.b * c.b + (b.a* c.a - b.b * c.b), a.a * c.b + a.b * c.a - a.b * c.b + (b.a * c.b + b.b * c.a - b.b * c.b)⟩  : by rw[h1,h2]
               ...    = ⟨a.a, a.b⟩ * ⟨c.a, c.b⟩ + ⟨b.a, b.b⟩ * ⟨c.a, c.b⟩    : rfl
               ...    = a * c + b * c             : by rw[eql a, eql b, eql c],
end

@[simp] theorem mul_comm:  ∀ (a b : ℤ_ζ), a * b = b * a :=
begin
     intros a b,
     have h1 : a.a * b.a - a.b * b.b = b.a * a.a - b.b * a.b, by ring,
     have h2: a.a * b.b + a.b * b.a - a.b * b.b = b.a * a.b + b.b * a.a - b.b * a.b, by ring,
     calc a * b = ⟨a.a, a.b⟩ * ⟨b.a, b.b⟩        : by rw [eql a, eql b]
             ...= ⟨a.a * b.a - a.b * b.b, a.a * b.b + a.b * b.a - a.b * b.b⟩  : rfl
             ...= ⟨b.a * a.a - b.b * a.b, b.a * a.b + b.b * a.a - b.b * a.b⟩  : by rw[h1,h2]
             ...= ⟨b.a, b.b⟩ * ⟨a.a, a.b⟩    : rfl
             ... = b * a                    : by rw[eql a, eql b],
end

def remainder : ℤ_ζ → ℤ_ζ → ℤ_ζ |  a b := a - b * (quotient a b) 
@[simp] theorem remiander_def (a b: ℤ_ζ):  remainder a b = a - b * (quotient a b)  := rfl 
@[simp] theorem quotient_mul_add_remainder_eq :∀ (a b : ℤ_ζ), b * quotient a b + (remainder a b) = a :=
begin
     intros a b,
     calc b * a.quotient b + (remainder a b) = b * quotient a b + (a - b * (quotient a b))  : by rw remiander_def 
                                         ... = a           : by ring,
end

lemma nat_abs_ge0(a b : ℤ) : a ≥ 0 ∧ b ≥ 0 ∧ a ≥ b → a.nat_abs ≥ b.nat_abs :=
begin
     intro h,
     have h1 : a * a ≥ b * b, by nlinarith[h.1, h.2.1, h.2.2],
     exact int.nat_abs_le_iff_mul_self_le.mpr h1,
end

lemma nat_abs_lt(a b: ℤ): a ≥ 0 ∧ b ≥ 0 ∧ a < b → a.nat_abs < b.nat_abs :=
begin
     intro h,
     exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt h.1 h.2.2,
end

def f := λ (a : ℤ_ζ), a.norm.nat_abs
def r := inv_image nat.lt f

@[simp] theorem r_well_founded : well_founded r :=
begin
     have h : well_founded nat.lt, by exact nat.lt_wf,
     exact inv_image.wf f h,
end
end
end int_cubic_root

/-define ℚ_ζ-/
structure ra_cubic_root := 
(c : ℚ)
(d : ℚ)

notation `ℚ_ζ`  := ra_cubic_root

namespace ra_cubic_root
section

instance : decidable_eq ℚ_ζ:=
by tactic.mk_dec_eq_instance 

theorem ext : ∀ {z w : ℚ_ζ }, z = w ↔ z.c = w.c ∧ z.d = w.d
| ⟨x, y⟩ ⟨x', y'⟩ := 
⟨λ h, by injection h; split; assumption,
                      λ ⟨h₁, h₂⟩, by congr; assumption⟩


def of_eisen_int(x : ℤ_ζ) : ℚ_ζ := ⟨(x.a : ℚ), (x.b : ℚ)⟩ 
theorem of_eisen_int_def: ∀ x y : ℤ, of_eisen_int ⟨x, y⟩ = ⟨(x : ℚ), (y : ℚ)⟩ := 
begin
     intros x y,
     try{refl},
end

/-zero-/
def zero : ℚ_ζ  := of_eisen_int 0
instance : has_zero ℚ_ζ := ⟨ra_cubic_root.zero⟩
theorem zero_c : (0 : ℚ_ζ).c = (0 : ℚ) := rfl 
theorem zero_d : (0 : ℚ_ζ).d = (0 : ℚ) := rfl
instance : inhabited (ℚ_ζ) := ⟨0⟩ 

/-one-/
def one : ℚ_ζ := of_eisen_int 1
instance : has_one (ℚ_ζ) := ⟨ra_cubic_root.one⟩ 
@[simp] theorem one_c : (1 : (ℚ_ζ)).c = 1 := 
begin
have h1 : (1 : ℚ) = (1 : ℤ), by norm_num,
have h0 : (0 : ℚ) = (0 : ℤ), by norm_num,
calc (1 : (ℚ_ζ)).c = (of_eisen_int (1 : ℤ_ζ)).c : rfl 
               ... =  (of_eisen_int⟨1, 0⟩ : ℚ_ζ).c           : by try {refl}
               ... =  (⟨1, 0⟩ : ℚ_ζ).c                       : by rw[of_eisen_int_def 1 0, h0, h1]
               ... =  1                                      : rfl,
end
@[simp] theorem one_d : (1 : (ℚ_ζ)).d = 0 := rfl

/-representative of ζ in the ring-/
def ζ0 : ℚ_ζ := ⟨0, 1⟩  
@[simp] theorem ζ_c : (ζ0 : (ℚ_ζ)).c = 0 := rfl
@[simp] theorem ζ_d : (ζ0 : (ℚ_ζ)).d = 1 := rfl

/-addition-/
def add: (ℚ_ζ) → (ℚ_ζ) → (ℚ_ζ)
|⟨x, y⟩ ⟨x', y'⟩ := ⟨x + x', y + y'⟩
instance : has_add ℚ_ζ := ⟨ra_cubic_root.add⟩
@[simp] theorem add_def(x y x' y' : ℚ) :
   (⟨x, y⟩ + ⟨x', y'⟩ : ℚ_ζ) = ⟨x + x', y + y'⟩ := rfl 

/-negation-/
def neg : ℚ_ζ → ℚ_ζ
|⟨x, y⟩ := ⟨-x, -y⟩
instance : has_neg ℚ_ζ := ⟨ra_cubic_root.neg⟩
@[simp] theorem neg_c : ∀ z : ℚ_ζ, (-z).c = - z.c 
|⟨x, y⟩ := rfl 
@[simp] theorem neg_d : ∀ z : ℚ_ζ, (-z).d = - z.d 
|⟨x, y⟩ := rfl 

/-sub-/
def sub: ℚ_ζ → (ℚ_ζ) → (ℚ_ζ) := λ a b, a + -b
instance : has_sub ℚ_ζ := ⟨ra_cubic_root.sub⟩

/-mul-/
def mul : ℚ_ζ → ℚ_ζ → ℚ_ζ
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩
instance : has_mul ℚ_ζ := ⟨ra_cubic_root.mul⟩
@[simp] theorem mul_def(x y x' y' : ℚ) : 
   (⟨x, y⟩ * ⟨x', y'⟩ : ℚ_ζ) = ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩ := rfl 
@[simp] theorem mul_c : ∀ z w : ℚ_ζ, (z * w).c = z.c * w.c - z.d * w.d
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem mul_d : ∀ z w : ℚ_ζ, (z * w).d = z.c * w.d + z.d * w.c - z.d * w.d
| ⟨x, y⟩ ⟨x', y'⟩ := rfl

/- z = ⟨z.a, z.b⟩; notations-/
theorem eql0(z : ℚ_ζ) : z = ⟨z.c, z.d⟩ :=
begin 
     have h1 : z.c = (⟨z.c, z.d⟩ : ℚ_ζ).c, refl,
     have h2 : z.d = (⟨z.c, z.d⟩ : ℚ_ζ).d, refl,
     exact ext.mpr ⟨h1, h2⟩,
end

example (a b c d e: ℚ) : a * (b / c) + d * (e / c) = (a * b + d * e)/ c :=
begin
     ring,
end

/-norm-/
def norm1 (a : ℚ_ζ) : ℚ := a.c * a.c - a.c * a.d + a.d * a.d
@[simp] lemma norm1_def (a b : ℚ) : (⟨a, b⟩ : ℚ_ζ).norm1 = a * a - a * b + b * b  := 
by try {refl}

@[simp] theorem norm1_nonneg : ∀ x : ℚ_ζ, norm1 x ≥ 0 :=
begin
     intro x,
     calc norm1 x  = x.c * x.c - x.c * x.d + x.d * x.d   : by refl
           ...   ≥ 0                                     : by nlinarith,
end
@[simp] theorem norm1_nezero : ∀ x : ℚ_ζ, x ≠ 0 → x.norm1 > 0 := 
begin
     intros x h,
     have h1 : 4 * x.norm1 > 0, 
     begin
     have h2 : x.c ≠ 0 ∨ x.d ≠ 0, by {contrapose! h, simp[ext], exact h,},
     cases h2,
     {have h3: x.c^2 > 0, by exact pow_two_pos_of_ne_zero x.c h2,
     calc 4 * x.norm1 = 4 * (x.c * x.c - x.c * x.d + x.d * x.d)  :  by refl 
              ...     = (2 * x.d - x.c)^2 + 3 * x.c^2            :  by ring 
              ...     > (2 * x.d - x.c)^2 + 3 * 0                :  by nlinarith[h3]
              ...     = (2 * x.d - x.c)^2                        :  by norm_num
              ...     ≥ 0                                        :  by nlinarith,},
     {have h3: x.d^2 > 0, by exact pow_two_pos_of_ne_zero x.d h2,
     calc 4 * x.norm1 = 4 * (x.c * x.c - x.c * x.d + x.d * x.d)  :  by refl 
              ...     = (2 * x.c - x.d)^2 + 3 * x.d^2            :  by ring 
              ...     > (2 * x.c - x.d)^2 + 3 * 0                :  by nlinarith[h3]
              ...     = (2 * x.c - x.d)^2                        :  by norm_num
              ...     ≥ 0                                        :  by nlinarith,},
     end,
     nlinarith[h1],
end

@[simp] lemma norm1_mul : ∀ x y : ℚ_ζ, (x * y).norm1 = x.norm1 * y.norm1 := 
begin
intros x y,
have h1: x.norm1 = (x.c)^2 - x.c * x.d + (x.d)^2, 
calc x.norm1 = x.c * x.c - x.c * x.d + x.d * x.d  : rfl
        ... =  (x.c)^2 - x.c * x.d + (x.d)^2     : by ring,
have h2: y.norm1 = (y.c)^2 - y.c * y.d + (y.d)^2, 
calc y.norm1 = y.c * y.c - y.c * y.d + y.d * y.d  : rfl
        ... =  (y.c)^2 - y.c * y.d + (y.d)^2     : by ring,
have h3: (x * y).norm1 = (x.c * y.c - x.d * y.d)^2 - (x.c * y.c - x.d* y.d) * (x.c * y.d + x.d * y.c - x.d * y.d)
                       + (x.c * y.d + x.d * y.c - x.d * y.d)^2,
calc (x * y : ℚ_ζ).norm1 = (⟨x.c, x.d⟩ * ⟨y.c, y.d⟩ : ℚ_ζ).norm1                                : by rw [eql0 x, eql0 y]
          ...   = (⟨x.c * y.c - x.d * y.d, x.c * y.d + x.d * y.c - x.d * y.d⟩ : ℚ_ζ).norm1 : rfl 
          ...   = ((x.c * y.c - x.d * y.d) * (x.c * y.c - x.d * y.d)  
                       - (x.c * y.c - x.d* y.d) * (x.c * y.d + x.d * y.c - x.d * y.d)
                       + (x.c * y.d + x.d * y.c - x.d * y.d) * (x.c * y.d + x.d * y.c - x.d * y.d))    : rfl
          ...   = ((x.c * y.c - x.d * y.d)^2  - (x.c * y.c - x.d * y.d) * (x.c * y.d + x.d * y.c - x.d * y.d)
                       + (x.c * y.d + x.d * y.c - x.d * y.d)^2)                         : by ring,
have t : x.norm1 * y.norm1 = (x * y).norm1,
calc x.norm1 * y.norm1 = ((x.c)^2 - x.c * x.d + (x.d)^2)* ((y.c)^2 - y.c * y.d + (y.d)^2) : by rw [h1, h2]
             ...     = ((x.c * y.c - x.d * y.d)^2 - (x.c * y.c - x.d * y.d) * (x.c * y.d + x.d * y.c - x.d * y.d)
                       + (x.c * y.d + x.d * y.c - x.d * y.d)^2)                         : by ring 
             ...     = (x * y).norm1                                                    : by rw h3,
rw t,
end

lemma norm_lt_1: ∀ x : ℚ_ζ, abs x.c ≤ 1/2 ∧ abs x.d ≤ 1/2 → x.norm1 < 1 :=
begin
     intros x h,
     have a0: (1/2 : ℚ) > 0,  by norm_num,
     have a01 : (1/2 : ℚ) ≥ 0, by norm_num,
     have a1: abs(abs x.c) ≤ abs (1/2), 
     calc abs(abs x.c) = abs (x.c)      : by exact abs_abs x.c
                 ...   ≤ (1/2 : ℚ)      : by exact h.1 
                 ...   = abs(1/2)       : by rw abs_of_pos a0,
     have a2 : abs(abs x.d) ≤ abs(1/2),
     calc abs(abs x.d) = abs(x.d)       :  by exact abs_abs x.d 
                 ...   ≤ (1/2 : ℚ)     :  by exact h.2 
                 ...   = abs(1/2)       : by rw abs_of_pos a0,
     have h1: x.c^2 + (-x.c * x.d + x.d^2) = x.c^2 - x.c * x.d + x.d^2, by ring,
     have h2: abs (x.c^2) ≤ 1/4, 
     calc abs (x.c^2) = (abs x.c)^2     :  by exact abs_pow x.c 2 
                ...   ≤ (1/2)^2         :  by exact sq_le_sq a1
                ...   = 1/4             :  by norm_num,
     have h3: abs (-x.c * x.d) ≤ 1/4, 
     calc abs (-x.c * x.d) = abs (x.c) * abs (x.d) : by rw [abs_mul, abs_neg]
                   ...     ≤  (1/2) * (1/2)  :  by exact mul_le_mul h.1 h.2 (abs_nonneg x.d) a01
                   ...     = 1/4         :  by norm_num,
     have h4: abs (x.d^2) ≤ 1/4,  
     calc abs(x.d^2) = (abs x.d)^2      :  by exact abs_pow x.d 2
                ...   ≤ (1/2)^2         :  by exact sq_le_sq a2 
                ...   = 1/4             :  by norm_num,
     calc x.norm1 = x.c * x.c - x.c * x.d + x.d * x.d       : rfl
             ... ≤ abs (x.c * x.c - x.c * x.d + x.d * x.d) : by exact le_abs_self (x.c * x.c - x.c * x.d + x.d * x.d)
             ... = abs (x.c^2 - x.c * x.d + x.d^2)         : by ring_nf 
             ... = abs (x.c^2 + (-x.c * x.d + x.d^2))      : by rw h1
             ... ≤ abs (x.c^2) + abs (-x.c * x.d + x.d^2)  : by exact abs_add (x.c^2) (-x.c * x.d + x.d^2)
             ... ≤ abs (x.c^2) + abs (-x.c * x.d) + abs (x.d^2) 
                 : by linarith[abs_add (- x.c * x.d) (x.d^2)]
             ... ≤ 1/4 + 1/4 + 1/4                         : by linarith[h2, h3, h4]
             ... < 1                                       : by norm_num,
end

/-division in ℚ_ζ-/
def div: ℚ_ζ → ℚ_ζ → ℚ_ζ
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨(x * x' - x * y' + y * y')/(x'^2 - x' * y' + y'^2), 
                    (-x * y' + x' * y)/(x'^2 - x' * y' + y'^2)⟩ 
instance : has_div ℚ_ζ := ⟨ra_cubic_root.div⟩
@[simp] theorem div_def(x y x' y' : ℚ) : 
   (⟨x, y⟩ / ⟨x', y'⟩ : ℚ_ζ) = ⟨(x * x' - x * y' + y * y')/(x'^2 - x' * y' + y'^2), 
                    (-x * y' + x' * y)/(x'^2 - x' * y' + y'^2)⟩ := rfl 
@[simp] theorem div_a : ∀ z w : ℚ_ζ, (z / w).c = (z.c * w.c - z.c * w.d + z.d * w.d)/(w.c^2 - w.c * w.d + w.d^2)
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem div_b : ∀ z w : ℚ_ζ, (z / w).d = (-z.c * w.d + w.c * z.d)/(w.c^2 - w.c * w.d + w.d^2)
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem div_mul : ∀ a b : ℚ_ζ, b ≠ 0 → b * (a / b) = a :=
begin
     intros a b h,
     have s: b.c^2 - b.c * b.d + b.d^2 ≠ 0, {
     have this : b.c^2 - b.c * b.d + b.d^2 > 0,
     calc b.c^2 - b.c * b.d + b.d^2 = b.c * b.c - b.c * b.d + b.d * b.d: by ring
                         ...        =  (⟨b.c, b.d⟩ : ℚ_ζ).norm1 : by rw norm1_def b.c b.d
                         ...        =  b.norm1                 : rfl
                         ...        > 0                        : by exact norm1_nezero b h,
     nlinarith[this],},
     have h1: b.c * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) = a.c, 
     calc b.c * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2))
              =  a.c * ((b.c^2 - b.c * b.d + b.d^2)/(b.c^2 - b.c * b.d + b.d^2)) : by ring 
          ... =  a.c * ((b.c^2 - b.c * b.d + b.d^2)* (b.c^2 - b.c * b.d + b.d^2)⁻¹) : by try{refl}
          ... =  a.c * 1: by rw mul_inv_cancel s
          ... =  a.c    : by ring,
     have h2: b.c * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       + b.d * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2))
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) = a.d, 
     calc b.c * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       + b.d * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2))
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) 
               = a.d * ((b.c^2 - b.c * b.d + b.d^2)/(b.c^2 - b.c * b.d + b.d^2))  : by ring
          ...  = a.d * ((b.c^2 - b.c * b.d + b.d^2) * (b.c^2 - b.c * b.d + b.d^2)⁻¹) : by try {refl}
          ...  = a.d * 1 : by rw mul_inv_cancel s
          ...  = a.d     : by ring,
     calc b * (a/b) = ⟨b.c, b.d⟩ * (⟨a.c, a.d⟩ / ⟨b.c, b.d⟩)    :  by rw [eql0 a, eql0 b] 
              ...   = ⟨b.c, b.d⟩ * ⟨(a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2),
                                   (-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)⟩  : rfl 
              ...   = ⟨b.c * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)),
                       b.c * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2)) 
                       + b.d * ((a.c * b.c - a.c * b.d + a.d * b.d)/(b.c^2 - b.c * b.d + b.d^2))
                       - b.d * ((-a.c * b.d + b.c * a.d)/(b.c^2 - b.c * b.d + b.d^2))⟩  : rfl 
              ...   = ⟨a.c, a.d⟩                               : by rw[h1, h2]
              ...   = a                                       : by rw ← eql0 a,
end
@[simp] theorem zero_prop : (0 : ℚ_ζ).c = 0 ∧ (0 : ℚ_ζ).d = 0 := by exact ⟨zero_c, zero_d⟩
@[simp] theorem zero_add (x : ℚ_ζ) : 0 + x = x := 
begin
     simp[ext],
     split,
     have h: 0 = (⟨0, 0⟩ : ℚ_ζ), by exact eql0 0,
     calc (0 + x).c = ((⟨0, 0⟩ : ℚ_ζ) + x).c         : by rw h
             ...    = ((⟨0, 0⟩ : ℚ_ζ) + ⟨x.c, x.d⟩).c : by rw (eql0 x)   
             ...    = (⟨0 + x.c, 0 + x.d⟩ : ℚ_ζ).c   : rfl 
             ...    = (⟨x.c, x.d⟩ : ℚ_ζ).c           : by norm_num  
             ...    = x.c                            : rfl,
     have h1: 0 = (⟨0, 0⟩ : ℚ_ζ), by exact eql0 0,
     calc (0 + x).d = ((⟨0, 0⟩ : ℚ_ζ) + x).d         : by rw h1
             ...    = ((⟨0, 0⟩ : ℚ_ζ) + ⟨x.c, x.d⟩).d : by rw (eql0 x)   
             ...    = (⟨0 + x.c, 0 + x.d⟩ : ℚ_ζ).d   : rfl 
             ...    = (⟨x.c, x.d⟩ : ℚ_ζ).d           : by norm_num  
             ...    = x.d                            : rfl,
end
@[simp] theorem add_zero (x : ℚ_ζ) : x + 0 = x := 
begin
     simp[ext],
     split,
     have h: 0 = (⟨0, 0⟩ : ℚ_ζ), by exact eql0 0,
     calc (x + 0).c = (x + (⟨0, 0⟩ : ℚ_ζ)).c         : by rw h
             ...    = ((⟨x.c, x.d⟩ + ⟨0, 0⟩ : ℚ_ζ)).c : by rw (eql0 x)   
             ...    = (⟨x.c + 0, x.d + 0⟩ : ℚ_ζ).c   : rfl 
             ...    = (⟨x.c, x.d⟩ : ℚ_ζ).c           : by norm_num  
             ...    = x.c                            : rfl,
     have h1: 0 = (⟨0, 0⟩ : ℚ_ζ), by exact eql0 0,
     calc (x + 0).d = ((x + ⟨0, 0⟩ : ℚ_ζ)).d         : by rw h1
             ...    = ((⟨x.c, x.d⟩ + ⟨0, 0⟩ : ℚ_ζ)).d : by rw (eql0 x)   
             ...    = (⟨x.c + 0, x.d + 0⟩ : ℚ_ζ).d   : rfl 
             ...    = (⟨x.c, x.d⟩ : ℚ_ζ).d           : by norm_num  
             ...    = x.d                            : rfl,
end

@[simp]lemma add_assoc : ∀ a b c : ℚ_ζ, (a + b + c) = (a + (b + c)) :=
begin
     intros a b c,
     simp[ext],
     split,
     calc (a + b + c).c = (⟨a.c, a.d⟩ + ⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).c   : by rw [eql0 a, eql0 b, eql0 c]
                   ...  = (⟨a.c + b.c, a.d + b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).c   : rfl 
                   ...  =  (⟨a.c + b.c + c.c, a.d + b.d + c.d⟩ : ℚ_ζ).c   : rfl 
                   ...  =  (a.c + b.c + c.c : ℚ)                         : rfl 
                   ...  =  (a.c : ℚ) + (b.c + c.c)                       : by ring
                   ...  =  (⟨a.c + (b.c + c.c), a.d + (b.d + c.d)⟩ : ℚ_ζ).c   :  rfl 
                   ...  =  (⟨a.c, a.d⟩ + ⟨b.c + c.c, b.d + c.d⟩ : ℚ_ζ).c   : rfl
                   ...  =  (⟨a.c, a.d⟩ + (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩) : ℚ_ζ).c : rfl
                   ...  =  (a + (b + c)).c                                : by {try{refl}, rw[←eql0 a, ←eql0 b, ← eql0 c]},
     calc (a + b + c).d = (⟨a.c, a.d⟩ + ⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).d   : by rw [eql0 a, eql0 b, eql0 c]
                   ...  = (⟨a.c + b.c, a.d + b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).d   : rfl 
                   ...  =  (⟨a.c + b.c + c.c, a.d + b.d + c.d⟩ : ℚ_ζ).d   : rfl 
                   ...  =  (a.d + b.d + c.d : ℚ)                         : rfl 
                   ...  =  (a.d : ℚ) + (b.d + c.d)                       : by ring
                   ...  =  (⟨a.c + (b.c + c.c), a.d + (b.d + c.d)⟩ : ℚ_ζ).d   :  rfl 
                   ...  =  (⟨a.c, a.d⟩ + ⟨b.c + c.c, b.d + c.d⟩ : ℚ_ζ).d   : rfl
                   ...  =  (⟨a.c, a.d⟩ + (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩) : ℚ_ζ).d : rfl
                   ...  =  (a + (b + c)).d                                : by {try{refl}, rw[←eql0 a, ←eql0 b, ← eql0 c]},
end
@[simp]lemma add_comm : ∀ x y: ℚ_ζ, x + y = y + x :=
begin
     intros x y,
     have h1: x.c + y.c = y.c + x.c ∧ x.d + y.d = y.d + x.d, by {split, ring, ring,},
     calc x + y = ⟨x.c, x.d⟩ + ⟨y.c, y.d⟩    :   by rw [eql0 x, eql0 y]
            ... = ⟨x.c + y.c, x.d + y.d⟩    :   rfl 
            ... = ⟨y.c + x.c, y.d + x.d⟩    :   by rw[h1.1, h1.2]
            ... = ⟨y.c, y.d⟩ + ⟨x.c, x.d⟩    :   rfl 
            ... = y + x                    :   by rw[←eql0 x, ←eql0 y],
end
@[simp]lemma add_assoc_0 : ∀ x y z : ℚ_ζ, x + (y + z) = z + (x + y)       :=
begin
     intros x y z,
     calc x + (y + z) = x + y + z        :  by rw ←add_assoc x y z 
                 ...  = (x + y) + z      :  by refl 
                 ...  = z + (x + y)      :  by rw add_comm z (x + y),
end
@[simp]lemma add_left_neg: ∀ x : ℚ_ζ, (-x) + x = 0 :=
begin
     intro x,
     simp[ext],
     have h : -x  = ⟨-x.c, -x.d⟩, by {simp[ext], try{refl}},
     split,
     calc (x + (-x)).c = (⟨x.c, x.d⟩ + (-x): ℚ_ζ).c  : by rw eql0 x 
              ...    = (⟨x.c, x.d⟩ + ⟨-x.c, -x.d⟩ : ℚ_ζ).c  : by rw h
              ...    = (⟨x.c + -x.c, x.d + -x.d⟩ : ℚ_ζ).c   : rfl 
              ...    = (⟨0, 0⟩ : ℚ_ζ).c                     : by norm_num
              ...    = 0                                : rfl,
     calc (x + (-x)).d = (⟨x.c, x.d⟩ + (-x): ℚ_ζ).d  : by rw eql0 x 
              ...    = (⟨x.c, x.d⟩ + ⟨-x.c, -x.d⟩ : ℚ_ζ).d  : by rw h
              ...    = (⟨x.c + -x.c, x.d + -x.d⟩ : ℚ_ζ).d   : rfl 
              ...    = (⟨0, 0⟩ : ℚ_ζ).d                     : by norm_num
              ...    = 0                                : rfl,
end
@[simp]lemma add_right_neg: ∀ x : ℚ_ζ, x + -x = 0 :=
begin
     intro x,
     simp[ext],
     have h : -x  = ⟨-x.c, -x.d⟩, by {simp[ext], try{refl}},
     split,
     calc (x + (-x)).c = (⟨x.c, x.d⟩ + (-x): ℚ_ζ).c  : by rw eql0 x 
              ...    = (⟨x.c, x.d⟩ + ⟨-x.c, -x.d⟩ : ℚ_ζ).c  : by rw h
              ...    = (⟨x.c + -x.c, x.d + -x.d⟩ : ℚ_ζ).c   : rfl 
              ...    = (⟨0, 0⟩ : ℚ_ζ).c                     : by norm_num
              ...    = 0                                : rfl,
     calc (x + (-x)).d = (⟨x.c, x.d⟩ + (-x): ℚ_ζ).d  : by rw eql0 x 
              ...    = (⟨x.c, x.d⟩ + ⟨-x.c, -x.d⟩ : ℚ_ζ).d  : by rw h
              ...    = (⟨x.c + -x.c, x.d + -x.d⟩ : ℚ_ζ).d   : rfl 
              ...    = (⟨0, 0⟩ : ℚ_ζ).d                     : by norm_num
              ...    = 0                                : rfl,
end
@[simp] theorem mul_assoc (a b c: ℚ_ζ) : a * b * c = a * (b * c):= 
begin 
     have h1 : (a * b * c).c = (a * (b * c)).c, 
     calc (a * b * c).c = (⟨a.c, a.d⟩ * ⟨b.c, b.d⟩ * ⟨c.c, c.d⟩ : ℚ_ζ).c    : by rw [eql0 a, eql0 b, eql0 c] 
                ...     = (a.c * b.c - a.d * b.d) * c.c - (a.c * b.d + a.d * b.c - a.d * b.d) * c.d  
                                                                           : by simp [ext] 
                ...     = a.c * (b.c * c.c - b.d * c.d) - a.d *(b.c * c.d + b.d * c.c - b.d * c.d)
                                                                           : by ring                                                                                                                 
                ...     = (a * (b * c)).c                                  : by simp [ext],
     have h2 : (a * b * c).d = (a * (b * c)).d, 
     calc (a * b * c).d = (⟨a.c, a.d⟩ * ⟨b.c, b.d⟩ * ⟨c.c, c.d⟩ : ℚ_ζ ).d    : by rw [eql0 a, eql0 b, eql0 c] 
                ...     = (a.c * b.c - a.d * b.d) * c.d + (a.c * b.d + a.d * b.c - a.d * b.d) * c.c 
                          - (a.c * b.d + a.d * b.c - a.d * b.d) * c.d      : by simp[ext] 
                ...     = a.c * (b.c * c.d + b.d * c.c - b.d * c.d) + a.d * (b.c * c.c - b.d * c.d) 
                          - a.d * (b.c * c.d + b.d * c.c - b.d * c.d)      : by ring 
                ...     = (a * (b * c)).d                                  : by simp [ext],
     exact ext.mpr ⟨h1, h2⟩,
end
@[simp] theorem left_distrib (a b c : ℚ_ζ) : a * (b + c) = a * b + a * c := 
begin
     simp[ext],
     split,
     calc a.c * (b + c).c - a.d * (b + c).d = a.c * (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).c 
                                             - a.d * (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).d : by rw [eql0 b, eql0 c]
                                   ...      = a.c * (b.c + c.c) - a.d * (b.d + c.d) : by refl
                                   ...      = a.c * b.c - a.d * b.d + (a.c * c.c - a.d * c.d) : by ring
                                   ...      = (⟨a.c * b.c - a.d * b.d, a.c * b.d + a.d * b.c - a.d * b.d⟩ 
                                            +  ⟨a.c * c.c - a.d * c.d, a.c * c.d + a.d * c.c - a.d * c.d⟩ : ℚ_ζ).c : by simp*
                                   ...      = (⟨a.c, a.d⟩ * ⟨b.c, b.d⟩ + ⟨a.c, a.d⟩ * ⟨c.c, c.d⟩: ℚ_ζ).c : by refl
                                   ...      = (a * b + a * c).c         : by rw [← eql0 a, ←eql0 b, ←eql0 c],
     calc a.c * (b + c).d + a.d * (b + c).c - a.d * (b + c).d = 
          a.c * (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).d + a.d * (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).c 
          - a.d * (⟨b.c, b.d⟩ + ⟨c.c, c.d⟩ : ℚ_ζ).d : by rw [eql0 b, eql0 c]
          ...  = a.c * (b.d + c.d) + a.d * (b.c + c.c) - a.d * (b.d + c.d) : by refl 
          ...  = (a.c * b.d + a.d * b.c - a.d * b.d) + (a.c * c.d + a.d * c.c - a.d * c.d) : by ring
          ...  = (⟨a.c * b.c - a.d * b.d, a.c * b.d + a.d * b.c - a.d * b.d⟩ 
               +  ⟨a.c * c.c - a.d * c.d, a.c * c.d + a.d * c.c - a.d * c.d⟩ : ℚ_ζ).d : by simp*
          ...  = (⟨a.c, a.d⟩ * ⟨b.c, b.d⟩ + ⟨a.c, a.d⟩ * ⟨c.c, c.d⟩: ℚ_ζ).d : by refl
          ...      = (a * b + a * c).d         : by rw [← eql0 a, ←eql0 b, ←eql0 c],
end
@[simp] theorem mul_comm (a b : ℚ_ζ) : a * b = b * a := 
begin
     calc a * b = ⟨a.c, a.d⟩ * ⟨b.c, b.d⟩    : by rw [eql0 a, eql0 b] 
         ...    = ⟨a.c * b.c - a.d * b.d, a.c * b.d + a.d * b.c - a.d * b.d⟩  : by refl 
         ...    = ⟨b.c * a.c - b.d * a.d, b.c * a.d + b.d * a.c - b.d * a.d⟩  : by {simp,split, ring,ring}
         ...    = ⟨b.c, b.d⟩ * ⟨a.c, a.d⟩    : by refl
         ...    = b * a                    : by rw [← eql0 a, ← eql0 b],
end
@[simp] theorem right_distrib (a b c : ℚ_ζ) : (a + b) * c = a * c + b * c :=
begin
     simp[ext],
end


instance : comm_ring ℚ_ζ :=
by refine_struct
{ add            := (+),
  zero           := (0 : ℚ_ζ),
  neg            := has_neg.neg,
  mul            := (*),
  sub            := λ a b, a + -b,
  one            := (1 : ℚ_ζ),
  npow           := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  nsmul          := @nsmul_rec _ ⟨0⟩ ⟨(+)⟩,
  gsmul          := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨ra_cubic_root.neg⟩,
  zero_add       := zero_add,
  add_zero       := add_zero,
  add_left_neg   := add_left_neg,
  add_comm       := add_comm,
  add_assoc      := add_assoc,
  mul_assoc      := mul_assoc,
  left_distrib   := left_distrib,
  right_distrib  := right_distrib,
  mul_comm       := mul_comm,};
{intros; try { refl }; 
simp [ext, add_mul, mul_add, add_comm, add_left_comm,
  left_distrib, mul_comm, mul_left_comm, mul_assoc, right_distrib],}



/-unique 'ring-hom' from ℤ_ζ to ℂ-/
open int_cubic_root 

@[simp] def lift0: ℤ_ζ →+* ℚ_ζ :=
{ 
  to_fun := λ x, ⟨(x.a : ℚ), (x.b : ℚ)⟩,
  map_zero' := by try{refl},
  map_add' := λ a b, by { simp, },
  map_one' := by try{refl},
  map_mul' := λ x y, by { simp[ext],},
}
instance : has_coe (ℤ_ζ) ℚ_ζ := ⟨lift0⟩

theorem coe_add : ∀ x y : ℤ_ζ, (x : ℚ_ζ) + (y : ℚ_ζ) = (coe(x + y) : ℚ_ζ) := 
begin
     intros x y,
     calc (x : ℚ_ζ) + (y : ℚ_ζ) = ⟨(x.a : ℚ), (x.b : ℚ)⟩ + ⟨(y.a : ℚ), (y.b : ℚ)⟩  : by try{refl}
                         ...     = ⟨(x.a + y.a : ℚ), (x.b + y.b : ℚ)⟩               : rfl 
                         ...     = ⟨(coe (x.a + y.a) : ℚ), (coe (x.b + y.b) : ℚ)⟩   : by simp* 
                         ...     = (coe(⟨x.a, x.b⟩ + ⟨y.a, y.b⟩ : ℤ_ζ) : ℚ_ζ)        : by try {refl}
                         ...     = (coe(x + y) : ℚ_ζ)                              : by rw [eql x, eql y],
end
theorem coe_sub : ∀ x y : ℤ_ζ, (x : ℚ_ζ) - (y : ℚ_ζ) = (coe(x - y) : ℚ_ζ)   :=
begin
     intros x y,
     calc (x : ℚ_ζ) - (y : ℚ_ζ) = ⟨(x.a : ℚ), (x.b : ℚ)⟩ - ⟨(y.a : ℚ), (y.b : ℚ)⟩  : by try{refl}
                         ...     = ⟨(x.a - y.a : ℚ), (x.b - y.b : ℚ)⟩               : rfl 
                         ...     = ⟨(coe (x.a - y.a) : ℚ), (coe (x.b - y.b) : ℚ)⟩   : by simp* 
                         ...     = (coe(⟨x.a, x.b⟩ - ⟨y.a, y.b⟩ : ℤ_ζ) : ℚ_ζ)        : by try {refl}
                         ...     = (coe(x - y) : ℚ_ζ)                              : by rw [eql x, eql y],
end
theorem coe_mul : ∀ x y : ℤ_ζ, (x : ℚ_ζ) * (y : ℚ_ζ) = (coe(x * y) : ℚ_ζ) := 
begin
     intros x y,
     calc (x : ℚ_ζ) * (y : ℚ_ζ) = ⟨(x.a : ℚ), (x.b : ℚ)⟩ * ⟨(y.a : ℚ), (y.b : ℚ)⟩  : by try{refl} 
                       ...       = ⟨(x.a * y.a - x.b * y.b : ℚ), (x.a * y.b + x.b * y.a - x.b * y.b : ℚ)⟩ : rfl 
                       ...       = ⟨(coe (x.a * y.a - x.b * y.b) : ℚ), (coe (x.a * y.b + x.b * y.a - x.b * y.b) : ℚ)⟩ : by simp* 
                       ...       = (coe (⟨x.a, x.b⟩ * ⟨y.a, y.b⟩ : ℤ_ζ) : ℚ_ζ)       : by try {refl} 
                       ...       = (coe (x * y) : ℚ_ζ)                              : by rw [eql x, eql y],
end
theorem coe_neg : ∀ x : ℤ_ζ, (-x : ℚ_ζ) = -(x : ℚ_ζ) := by simp*

@[simp] theorem int_rat_cubic_coe(x y: ℤ_ζ) : 
(x : ℚ_ζ).norm1 < (y : ℚ_ζ).norm1 → x.norm < y.norm :=
begin 
     intro h,
     have h1 : (x.norm : ℚ) = (x : ℚ_ζ).norm1,
     calc (x.norm : ℚ) = (coe (x.a * x.a - x.a * x.b + x.b * x.b) : ℚ)  : rfl
             ... = (x.a * x.a - x.a * x.b + x.b * x.b : ℚ)      : by norm_num 
             ... = (⟨x.a, x.b⟩ : ℚ_ζ).norm1                      : by refl
             ... = (⟨(x.a : ℚ), (x.b : ℚ)⟩ : ℚ_ζ).norm1         : by try {refl}
             ... = (x : ℚ_ζ).norm1                              : by try {refl},
     have h2 : (y.norm : ℚ) = (y : ℚ_ζ).norm1, 
     calc (y.norm : ℚ) = (coe (y.a * y.a - y.a * y.b + y.b * y.b) : ℚ)  : rfl
             ... = (y.a * y.a - y.a * y.b + y.b * y.b : ℚ)      : by norm_num 
             ... = (⟨y.a, y.b⟩ : ℚ_ζ).norm1                      : by refl
             ... = (⟨(y.a : ℚ), (y.b : ℚ)⟩ : ℚ_ζ).norm1         : by try {refl}
             ... = (y : ℚ_ζ).norm1                              : by try {refl},
     have h3 : (x.norm : ℚ) < (y.norm : ℚ), 
     calc (x.norm : ℚ)  = (x : ℚ_ζ).norm1 :  by rw h1 
           ...   < (y : ℚ_ζ).norm1         :  by exact h 
           ...   = (y.norm : ℚ)            :  by rw h2,
     have h4 : ∀ a b : ℤ, (a : ℚ) < (b : ℚ) → a < b, by norm_num,
     exact h4 x.norm y.norm h3,
end
end
end ra_cubic_root

theorem int_ne_zero(x : ℤ_ζ) : x ≠ 0 → x.a ≠ 0 ∨ x.b ≠ 0 := 
begin
     intro h,
     contrapose! h,
     simp[int_cubic_root.ext],
     exact h,
end
theorem ra_c_ne (x : ℚ_ζ) : x.c ≠ 0 → x ≠ 0 := 
begin
     intro h, contrapose! h, simp*,
end
theorem ra_d_ne (x : ℚ_ζ) : x.d ≠ 0 → x ≠ 0 := 
begin
     intro h, contrapose! h, simp*,
end

/-get back to ℤ_ζ-/
open int_cubic_root
open ra_cubic_root
section
theorem remainder_lt:  ∀ (a : ℤ_ζ) {b : ℤ_ζ}, b ≠ 0 → r (a - b * a.quotient b) b := 
begin
intros a b h,
let r0 := a - b * a.quotient b,
have t : (r0 : ℚ_ζ).norm1 < (b : ℚ_ζ).norm1, 
begin
     have hb: (b : ℚ_ζ) ≠ 0, 
     begin
          have b1 : b.a ≠ 0 ∨ b.b ≠ 0, by exact int_ne_zero b h,
          cases b1, 
          {have ba : (b.a : ℚ) ≠ 0, by simp*,
           calc (b : ℚ_ζ) = ⟨(b.a : ℚ), (b.b : ℚ)⟩  :  by try {refl}
                     ...  ≠ 0                        :  by exact ra_c_ne ⟨(b.a : ℚ), (b.b : ℚ)⟩ ba, },
          {have bb : (b.b : ℚ) ≠ 0, by simp*,
           calc (b : ℚ_ζ) = ⟨(b.a : ℚ), (b.b : ℚ)⟩  :  by try {refl}
                     ...  ≠ 0                        :  by exact ra_d_ne ⟨(b.a : ℚ), (b.b : ℚ)⟩ bb, },
     end,
     have s0 : (r0 : ℚ_ζ) = (a : ℚ_ζ) - (b : ℚ_ζ) * (coe(a.quotient b)), 
     calc (r0 : ℚ_ζ) = (coe (a - b * a.quotient b) : ℚ_ζ)                   : by try {refl} 
                ...   = (a : ℚ_ζ) - (coe(b * a.quotient b) : ℚ_ζ)           : by rw ←coe_sub a (b * a.quotient b)
                ...   = (a : ℚ_ζ) - (b : ℚ_ζ) * (coe(a.quotient b))         : by rw ←coe_mul b (a.quotient b),
     have s1 : (a : ℚ_ζ) = (b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ)), by rw div_mul (a : ℚ_ζ) (b : ℚ_ζ) hb,
     let r1 := (a : ℚ_ζ)/(b : ℚ_ζ) - (a.quotient b : ℚ_ζ),
     have s2 : (r0 : ℚ_ζ).norm1 = (b : ℚ_ζ).norm1 * r1.norm1,
     calc (r0 : ℚ_ζ).norm1 = ((a : ℚ_ζ) - (b : ℚ_ζ) * (coe(a.quotient b))).norm1  :  by rw s0 
                      ...   = ((b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ)) - (b : ℚ_ζ) * (coe(a.quotient b))).norm1    : by rw ←s1 
                      ...   = ((b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ)) + (b : ℚ_ζ) * -(coe(a.quotient b))).norm1   : by ring_nf
                      ...   = ((b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ) + -coe(a.quotient b))).norm1                 : by simp*
                      ...   = ((b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ) - coe(a.quotient b))).norm1                  : by ring_nf 
                      ...   = (coe b * r1).norm1                                                               : rfl
                      ...   = (b : ℚ_ζ).norm1 * r1.norm1                                   : by exact norm1_mul (coe b) r1,
     have s3: (b : ℚ_ζ).norm1 > 0, by exact norm1_nezero (b : ℚ_ζ) hb,
     let first := (a.a * b.a - a.a * b.b + a.b * b.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ),
     have hf : abs (first - round first : ℚ) ≤  1/2, by exact abs_sub_round first,
     let second := (-a.a * b.b + b.a * a.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ),
     have hs : abs (second - round second : ℚ) ≤  1/2, by exact abs_sub_round second,
     have s4: r1.norm1 < 1, 
     begin
          calc r1.norm1 = ((a : ℚ_ζ)/(b : ℚ_ζ) - (a.quotient b : ℚ_ζ)).norm1 : rfl 
                    ... = ((⟨(a.a : ℚ), (a.b : ℚ)⟩ : ℚ_ζ) / ⟨(b.a : ℚ), (b.b : ℚ)⟩ - (a.quotient b : ℚ_ζ)).norm1 : by try{refl}
                    ... = ((⟨(a.a * b.a - a.a * b.b + a.b * b.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ), 
                    (-a.a * b.b + b.a * a.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ)⟩ : ℚ_ζ) 
                    - (a.quotient b : ℚ_ζ)).norm1 : by try {refl}
                    ... =  ((⟨(a.a * b.a - a.a * b.b + a.b * b.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ), 
                    (-a.a * b.b + b.a * a.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ)⟩ : ℚ_ζ) 
                    - ((⟨a.a, a.b⟩ : ℤ_ζ) .quotient (⟨b.a, b.b⟩ : ℤ_ζ) : ℚ_ζ)).norm1 : by rw [eql a, eql b]
                    ... = ((⟨(a.a * b.a - a.a * b.b + a.b * b.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ), 
                    (-a.a * b.b + b.a * a.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ)⟩ : ℚ_ζ) 
                    - (coe(⟨round ((a.a * b.a - a.a * b.b + a.b * b.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ)), 
          round ((-a.a * b.b + b.a * a.b : ℚ)/(b.a^2 - b.a * b.b + b.b^2 : ℚ))⟩ : ℤ_ζ) : ℚ_ζ)).norm1 : by rw quotient_def
          ...  = ((⟨first, second⟩: ℚ_ζ) - (⟨(round first : ℚ), (round second : ℚ)⟩ : ℚ_ζ)).norm1      : by refl 
          ...  = (⟨(first - round first : ℚ), (second - round second : ℚ)⟩ : ℚ_ζ).norm1           : rfl 
          ...  < 1         : by exact norm_lt_1 (⟨(first - round first : ℚ), (second - round second : ℚ)⟩ : ℚ_ζ) 
                                ⟨hf, hs⟩,
     end,
     calc (r0 : ℚ_ζ).norm1 = (b : ℚ_ζ).norm1 * r1.norm1  : by rw s2 
           ...           = r1.norm1 * (b : ℚ_ζ).norm1  : by ring_nf 
           ...           < 1 * (b : ℚ_ζ).norm1         : by exact mul_lt_mul s4 (le_refl (b : ℚ_ζ).norm1) s3 zero_le_one
           ...           = (b : ℚ_ζ).norm1 * 1         : by ring 
           ...           = (b : ℚ_ζ).norm1             : by norm_num,
end,
have h0: (a - b * a.quotient b).norm < b.norm, 
by exact int_rat_cubic_coe (a - b * a.quotient b) b t,
have h1: (a - b * a.quotient b).norm.nat_abs < b.norm.nat_abs, 
begin
     apply nat_abs_lt ((a - b * a.quotient b).norm) (b.norm), 
     split,
     all_goals{try {split}},
     exact norm_nonneg (a - b * a.quotient b),
     exact norm_nonneg b,
     exact h0,
end,
exact h1,
end

@[simp] theorem mul_left_not_lt :  ∀ (a : ℤ_ζ) {b : ℤ_ζ}, b ≠ 0 → ¬ r (a * b) a
:=
begin
     intros a b h,
     have t: b.a ≠ 0 ∨ b.b ≠ 0, {contrapose! h, simp[int_cubic_root.ext], exact h,},
     have h1 : b.norm ≥  1, 
     {cases t,
     {have t1 : (2 * b.b - b.a)^2 ≥ 0, by exact pow_two_nonneg (2 * b.b - b.a),
     have t2 : 0 + 3 * b.a^2 ≤ (2 * b.b - b.a)^2 + 3 * b.a^2, by apply add_le_add_right t1 (3 * b.a^2),
     have h2: b.a^2 > 0, by exact pow_two_pos_of_ne_zero b.a t,
     have h3: 3 * b.a^2 ≥ 3, linarith,
     have h4: 4 * b.norm ≥ 3,
     calc 4 * b.norm = 4 * (b.a * b.a - b.a * b.b + b.b * b.b)    : rfl 
            ...   = (2 * b.b - b.a)^2 + 3 * b.a^2                 : by ring
            ...   ≥ 0 + 3 * b.a^2                                 : by exact t2
            ...   = 3 * b.a^2                                     : by ring 
            ...   ≥ 3 * 1                                         : by exact h3
            ...   = 3                                             : by ring,
     contrapose! h4,
     have h5: b.norm = 0, {have h6: b.norm ≥ 0 ∧ b.norm < 1, by exact⟨norm_nonneg b, h4⟩, linarith,},
     linarith,
     },
     {have t1 : (2 * b.a - b.b)^2 ≥ 0, by exact pow_two_nonneg (2 * b.a - b.b),
     have t2 : 0 + 3 * b.b^2 ≤ (2 * b.a - b.b)^2 + 3 * b.b^2, by apply add_le_add_right t1 (3 * b.b^2),
     have h2: b.b^2 > 0, by exact pow_two_pos_of_ne_zero b.b t,
     have h3: 3 * b.b^2 ≥ 3, linarith,
     have h4: 4 * b.norm ≥ 3,
     calc 4 * b.norm = 4 * (b.a * b.a - b.a * b.b + b.b * b.b)    : rfl 
            ...   = (2 * b.a - b.b)^2 + 3 * b.b^2                 : by ring
            ...   ≥ 0 + 3 * b.b^2                                 : by exact t2
            ...   = 3 * b.b^2                                     : by ring 
            ...   ≥ 3 * 1                                         : by exact h3
            ...   = 3                                             : by ring,
     contrapose! h4,
     have h5: b.norm = 0, {have h6: b.norm ≥ 0 ∧ b.norm < 1, by exact⟨norm_nonneg b, h4⟩, linarith,},
     linarith,
     }},
     have h3 : (a * b).norm ≥ a.norm,
     calc (a * b).norm = a.norm * b.norm        : by exact norm_mul a b
                ...    = b.norm * a.norm        : by ring 
                ...    ≥ 1 * a.norm             : by exact gsmul_le_gsmul (norm_nonneg a) h1
                ...    =   a.norm               : by ring,
     have h4_1 : (a * b).norm ≥ 0 ∧ a.norm ≥ 0 ∧ (a * b).norm ≥ a.norm, 
     begin
     split,
     all_goals{try {split}},
     exact norm_nonneg (a * b),
     exact norm_nonneg a,
     exact h3,
     end,
     have h4: (a * b).norm.nat_abs ≥ a.norm.nat_abs,
     by exact nat_abs_ge0 ((a * b).norm) (a.norm) h4_1,
     contrapose! h4,
     exact h4,
end

/-euclidean domain-/

instance int_cubic_root.euclidean_domain : euclidean_domain ℤ_ζ :=
by refine_struct
{ add := (+),
  mul := (*),
  one := (1 : ℤ_ζ),
  zero := (0 : ℤ_ζ),
  neg := has_neg.neg,
  zero_add := int_cubic_root.zero_add,
  add_zero := add_zero,
  nsmul := nsmul,
  sub := λ a b, a + -b,
  gsmul          := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨int_cubic_root.neg⟩,
  add_left_neg   := int_cubic_root.add_left_neg,
  npow           := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  exists_pair_ne := exists_pair_ne,
  quotient       := quotient,
  quotient_zero  := div_zero,
  remainder      := λ a b, a - b * (quotient a b),
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq,
  add_assoc      := int_cubic_root.add_assoc,
  nsmul_zero'    := nsmul_zero',
  nsmul_succ'    := nsmul_succ',
  sub_eq_add_neg := int_cubic_root.sub_eq_add_neg,
  gsmul_zero'    := gsmul_zero',
  add_comm       := int_cubic_root.add_comm,
  mul_assoc      := int_cubic_root.mul_assoc,
  one_mul        := int_cubic_root.one_mul,
  mul_one        := int_cubic_root.mul_one,
  npow_zero'     := npow_zero',
  npow_succ'     := npow_succ',
  left_distrib   := left_distrib_0,
  right_distrib  := right_distrib_0,
  gsmul_succ'    := gsmul_succ',
  gsmul_neg'     := gsmul_neg',
  mul_comm       := int_cubic_root.mul_comm,
  r              := r,
  r_well_founded := r_well_founded,
  remainder_lt   := remainder_lt,
  mul_left_not_lt  := mul_left_not_lt,
  }

end
#lint
