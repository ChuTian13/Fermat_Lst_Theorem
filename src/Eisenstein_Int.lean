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

lemma h1_lt_3 : 1 < 3 
:= by norm_num

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
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨λ h, by injection h; split; assumption,
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
{intros; try { refl }; simp [ext, zero_add, add_mul, mul_add, add_comm, add_left_comm, 
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
theorem coe_nat_val(m : ℕ): (m : ℤ_ζ) = ⟨m, 0⟩ := 
by simp [ext] 

@[simp] theorem coe_int_a(m : ℤ) : (m : ℤ_ζ).a = m :=
begin 
     cases m; simp[*, int.of_nat_eq_coe, int.neg_succ_of_nat_eq],
end
@[simp] theorem coe_int_im (n : ℤ) : (n : ℤ_ζ).b = 0 :=
by cases n; simp *
theorem coe_int_val (n : ℤ) : (n : ℤ_ζ) = ⟨n, 0⟩ :=
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
sorry

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
by simp only [ext, true_and, conj_a, conj_conj_1, eq_self_iff_true, neg_neg, conj_b]

theorem mul_conj (x y : ℤ) : (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ_ζ) = (x^2 - x * y + y^2 : ℤ_ζ):=
begin
have h1: x * -y + y * (x - y) - y * -y = 0, by ring,
have h2: x * (x-y) - y* (-y) = x^2 - x * y + y^2, by ring,
let z : ℤ := x^2 - x * y + y^2, 
have h3: z = x^2 - x * y + y^2, refl,
have h4: (z : ℤ_ζ) = (x^2 - x * y + y^2 : ℤ_ζ), 
calc (z : ℤ_ζ) = ⟨z, 0⟩                      : by exact coe_int_val z
         ...   = ⟨x^2 - x * y + y^2, 0⟩      : by rw h3
         ...   = coe(x^2 - x * y + y^2)     : by exact eq.symm(coe_int_val (x^2 - x * y + y^2))
         ...   = x^2 - x * y + y^2          : by sorry,
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
     have h1 : (conj (a * b)).a = (conj a * conj b).a, by sorry,
     have h2 : (conj (a * b)).b = (conj a * conj b).b, by sorry,
     exact ext.mpr⟨h1, h2⟩,
end

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

lemma norm_eq_mul_conj (n : ℤ_ζ) : (norm n : ℤ_ζ) = n * n.conj :=
sorry

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
begin
     tauto,
end

lemma norm_eq_one_2(a b : ℤ): a^2 - a * b + b^2 = 1 → (abs a = 1 ∧ abs b = 0) ∨ (abs a = 0 ∧ abs b = 1) :=
sorry

@[simp] lemma norm_eq_one_iff {x : ℤ_ζ} : x.norm.nat_abs = 1 ↔ is_unit x :=
begin
split,
{sorry},
{sorry}
end

lemma is_unit_iff_norm_is_unit {d : ℤ} (z : ℤ_ζ) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs_eq, norm_eq_one_iff]

lemma norm_eq_one_iff'  (z : ℤ_ζ) : z.norm = 1 ↔ is_unit z :=
by rw [←norm_eq_one_iff, ←int.coe_nat_inj', int.nat_abs_of_nonneg (norm_nonneg_0 z),
  int.coe_nat_one]

lemma norm_eq_zero_iff (z : ℤ_ζ) : z.norm = 0 ↔ z = 0 :=
begin
  split,
  { intro h,
    rw [ext, zero_a, zero_b],
    have h1 : z.a * z.a - z.a * z.b + z.b * z.b = 0, by exact h,
    sorry,
   },
  { rintro rfl, exact norm_zero }
end

lemma norm_eq_of_associated {d : ℤ} {x y : ℤ_ζ} (h : associated x y) :
  x.norm = y.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  rw [norm_mul, (norm_eq_one_iff' _).mpr u.is_unit, mul_one],
end

/-quotient-/
def quotient: ℤ_ζ → ℤ_ζ → ℤ_ζ
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨floor ((x * x' - x * y' - y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
                    floor ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩ 
lemma quotient_def (x y x' y': ℤ) : 
quotient ⟨x, y⟩ ⟨x', y'⟩  = ⟨floor ((x * x' - x * y' - y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
                    floor ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩  := rfl
lemma div_zero (n : ℤ_ζ): quotient n 0 = 0 := sorry

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
sorry

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
sorry

@[simp] theorem gsmul_neg' : ∀ (n : ℕ) (a : ℤ_ζ), gsmul_rec -[1+ n] a = -gsmul_rec ↑(n.succ) a :=
sorry

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

case euclidean_domain, left_distrib
⊢ ∀ (a b c : ℤ_ζ), a * (b + c) = a * b + a * c

case euclidean_domain, right_distrib
⊢ ∀ (a b c : ℤ_ζ), (a + b) * c = a * c + b * c

case euclidean_domain, mul_comm
⊢ ∀ (a b : ℤ_ζ), a * b = b * a

case euclidean_domain, r
⊢ ℤ_ζ → ℤ_ζ → Prop

case euclidean_domain, r_well_founded
⊢ well_founded ?m_1

case euclidean_domain, remainder_lt
⊢ ∀ (a : ℤ_ζ) {b : ℤ_ζ}, b ≠ 0 → ?m_16 (a - b * a.quotient b) b

case euclidean_domain, mul_left_not_lt
⊢ ∀ (a : ℤ_ζ) {b : ℤ_ζ}, b ≠ 0 → ¬?m_16 (a * b) a
/-euclidean domain-/
instance int_cubic_root.euclidean_domain : euclidean_domain ℤ_ζ :=
by refine_struct
{ add := (+),
  mul := (*),
  one := (1 : ℤ_ζ),
  zero := (0 : ℤ_ζ),
  neg := has_neg.neg,
  zero_add := zero_add,
  add_zero := add_zero,
  nsmul := nsmul,
  sub := λ a b, a + -b,
  gsmul          := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨int_cubic_root.neg⟩,
  add_left_neg := add_left_neg,
  npow           := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  exists_pair_ne := exists_pair_ne,
  quotient       := quotient,
  quotient_zero  := div_zero,
  remainder      := λ a b, a - b * (quotient a b),
  quotient_mul_add_remainder_eq := sorry,
  add_assoc      := add_assoc,
  nsmul_zero'    := nsmul_zero',
  nsmul_succ'    := nsmul_succ',
  sub_eq_add_neg := sub_eq_add_neg,
  gsmul_zero'    := gsmul_zero',
  add_comm       := add_comm,
  mul_assoc      := mul_assoc,
  one_mul        := one_mul,
  mul_one        := mul_one,
  npow_zero'     := npow_zero',
  npow_succ'     := npow_succ',

  }
