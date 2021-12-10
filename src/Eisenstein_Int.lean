import data.nat.basic data.int.nat_prime data.rat.basic data.complex.basic tactic
import data.real.basic data.nat.prime 
import ring_theory.principal_ideal_domain
import ring_theory.roots_of_unity
import algebra.ring algebra.euclidean_domain
import algebra.associated
import algebra.algebra.ordered

lemma h1_lt_3 : 1 < 3 
:= by norm_num

/-! Construction of Z[ζ] primitive root of x^3 = 1. The whole process just copies the definitions
of those of zsqrt, by the construction, hope to show that Z[ζ] is an euclidean domain-/

/-- basic structure definition of the Eisenstein Integers -/
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

/-- Convert an integer to a Z_ζ n -/
def of_int(m : ℤ) : ℤ_ζ := ⟨m,0⟩
theorem of_int_a(m : ℤ) : (of_int m).a = m := rfl 
theorem of_int_b(m : ℤ) : (of_int m).b = 0 := rfl

/-- zero-/
def zero : ℤ_ζ  := of_int 0
instance : has_zero ℤ_ζ := ⟨int_cubic_root.zero⟩
theorem zero_a : (0 : ℤ_ζ ).a = 0 := rfl 
theorem zero_b : (0 : ℤ_ζ ).b = 0 := rfl

instance : inhabited (ℤ_ζ) := ⟨0⟩ 

/-- one-/
def one : ℤ_ζ := of_int 1
instance : has_one (ℤ_ζ) := ⟨int_cubic_root.one⟩ 
@[simp] theorem one_a : (1 : (ℤ_ζ)).a = 1 := rfl
@[simp] theorem one_b : (1 : (ℤ_ζ)).b = 0 := rfl
lemma one_eq: (1 : (ℤ_ζ)) = ⟨1, 0⟩  := by simp[ext]

/-- representative of the primitive root of order 3 in the ring ℤ[ζ]-/
def ζ : ℤ_ζ := ⟨0, 1⟩ 
@[simp] theorem ζ_a : (ζ : (ℤ_ζ)).a = 0 := rfl
@[simp] theorem ζ_b : (ζ : (ℤ_ζ)).b = 1 := rfl

/-- addition-/
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

/-- negation-/
def neg : ℤ_ζ → ℤ_ζ
|⟨x, y⟩ := ⟨-x, -y⟩
instance : has_neg ℤ_ζ := ⟨int_cubic_root.neg⟩
@[simp] theorem neg_a : ∀ z : ℤ_ζ, (-z).a = - z.a 
|⟨x, y⟩ := rfl 
@[simp] theorem neg_b : ∀ z : ℤ_ζ, (-z).b = - z.b 
|⟨x, y⟩ := rfl 

/-- muliplication-/
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

@[simp] theorem zero_add (a : ℤ_ζ) : 0 + a = a := by simp[ext]

/-- z = ⟨z.a, z.b⟩; notations-/
theorem eql(z : ℤ_ζ) : z = ⟨z.a, z.b⟩ :=
begin 
     have h1 : z.a = (⟨z.a, z.b⟩ : ℤ_ζ).a, refl,
     have h2 : z.b = (⟨z.a, z.b⟩ : ℤ_ζ).b, refl,
     exact ext.mpr ⟨h1, h2⟩,
end

theorem eql'(z : ℤ_ζ)(m n : ℤ)(h : z.a = m)(h': z.b = n) : z = ⟨m, n⟩ :=
begin
     simp[ext], split, rw h, rw h',
end

/-- a * b * c = a * (b * c)-/
@[simp] theorem mul_assoc (a b c: ℤ_ζ) : a * b * c = a * (b * c):= 
begin 
     simp[ext], split, ring, ring,
end

/-- a * (b + c) = a * b + a * c-/
@[simp] theorem left_distrib (a b c : ℤ_ζ) : a.a * b.a + a.a * c.a - (a.b * b.b + a.b * c.b) = a.a * b.a - a.b * b.b + (a.a * c.a - a.b * c.b) 
      ∧a.a * b.b + (a.a * c.b + (b.a * a.b + c.a * a.b)) - (a.b * b.b + a.b * c.b) =
      a.a * b.b + b.a * a.b - a.b * b.b + (a.a * c.b + c.a * a.b - a.b * c.b)
      := 
begin
     split, ring, ring,
end
/-- (a + b) * c = a * c + b * c-/
@[simp] theorem right_distrib(a b c : ℤ_ζ) :a.a * c.a + b.a * c.a - (a.b * c.b + b.b * c.b) = a.a * c.a - a.b * c.b + (b.a * c.a - b.b * c.b) 
    ∧a.a * c.b + (b.a * c.b + (c.a * a.b + c.a * b.b)) - (a.b * c.b + b.b * c.b) =
      a.a * c.b + c.a * a.b - a.b * c.b + (b.a * c.b + c.a * b.b - b.b * c.b)
      := 
begin
     split, ring, ring,
end

/-- use the structure definition of commutative ring, fill in the properties needed to
prove that ℤ[ζ] is a commutative ring-/
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

/--  ∃ lifts ℕ, ℤ → ℤ_ζ  -/
@[simp] theorem coe_nat_val(m : ℕ): (m : ℤ_ζ) = ⟨m, 0⟩ := 
begin
     simp[ext], 
     induction m; simp*, 
end

@[simp] theorem coe_int_val (n : ℤ) : (n : ℤ_ζ) = ⟨n, 0⟩ :=
begin
     simp[ext],
     cases n; simp[*, int.of_nat_eq_coe, int.neg_succ_of_nat_eq],
end

/-- char(ℤ[ζ])= 0 -/
instance : char_zero ℤ_ζ :=
{ cast_injective := λ m n, by simp [ext]}

/-- ℕ coe : ℕ → ℤ_ζ-/
@[simp] theorem of_int_eq_coe (n : ℤ) : (of_int n : ℤ_ζ) = n :=
by simp [ext, of_int_a, of_int_b]

@[simp] theorem smul_val (n x y : ℤ) : (⟨x * n, y * n⟩ : ℤ_ζ) = ⟨n * x, n * y⟩ :=
begin
     simp[ext], split, ring, ring,
end

/-- ζ is a primitive root of order 3-/
theorem prop_3_3: ζ^3 = ⟨1, 0⟩        :=            by ring

theorem prop_3_4: 1 + ζ + ζ^2 = 0    :=            by ring

/-- surprised how powerful simp[ext] can be-/
@[simp] theorem muld_val (x y : ℤ) : ζ * ⟨x, y⟩ = ⟨-y, x - y⟩ :=
by simp[ext]

@[simp] theorem ζmulζ : ζ * ζ = - 1 - ζ :=
calc ζ * ζ  = ζ ^ 2 - 0                                   : by ring
     ...    = ζ ^ 2 - (1 + ζ + ζ^2)                       : by rw[←prop_3_4]
     ...    = -1 - ζ                                      : by ring


theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ_ζ) = x + ζ * y :=
by simp [ext]

/-- ζ is the primitive root-/
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

/-- conjugation of an Eisenstein Integer: 
the function conj turns an Eisenstein integer to its conjugation-/
def conj : ℤ_ζ → ℤ_ζ 
| ⟨x, y⟩ := ⟨x-y, -y⟩
@[simp] theorem conj_a: ∀ z : ℤ_ζ, (conj z).a = z.a - z.b
| ⟨x, y⟩ := rfl 
@[simp] theorem conj_b: ∀ z : ℤ_ζ, (conj z).b = - z.b
| ⟨x, y⟩ := rfl 

theorem hom_1(a ai b bi: ℤ): 
(⟨a, ai⟩ + ⟨b, bi⟩ : ℤ_ζ).conj.a = ((⟨a, ai⟩ : ℤ_ζ).conj + (⟨b, bi⟩ : ℤ_ζ).conj).a := 
begin
     simp*, ring,
end

/-- map `conj` is an `add_monoid_hom`. -/
def conj_hom : ℤ_ζ →+ ℤ_ζ :=
{ to_fun := conj,
  map_add' := λ ⟨a, ai⟩ ⟨b, bi⟩, ext.mpr ⟨hom_1 a ai b bi, neg_add _ _⟩,
  map_zero' := ext.mpr ⟨rfl, neg_zero⟩ }

@[simp] lemma conj_zero : conj (0 : ℤ_ζ) = 0 :=
conj_hom.map_zero

@[simp] lemma conj_one : conj (1 : ℤ_ζ) = 1 := rfl

@[simp] lemma conj_neg (x : ℤ_ζ) : (-x).conj = -x.conj :=
conj_hom.map_neg x
@[simp] lemma conj_add (x y : ℤ_ζ) : (x + y).conj = x.conj + y.conj :=
conj_hom.map_add x y

@[simp] lemma conj_conj_1 (x y : ℤ):  x - y - -y = x := by ring
@[simp] lemma conj_conj (x : ℤ_ζ) : x.conj.conj = x :=
by simp only [ext, true_and, conj_a, conj_conj_1, eq_self_iff_true, 
neg_neg, conj_b]

theorem mul_conj (x y : ℤ) : (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ_ζ) = (⟨x^2 - x * y + y^2, 0⟩ : ℤ_ζ):=
begin
     have h: conj ⟨x, y⟩ = ⟨x - y, -y⟩, refl,
     calc (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ_ζ) = ⟨x, y⟩ * ⟨x - y, -y⟩  :  by rw h
                       ...            = ⟨x^2 - x * y + y^2, 0⟩  : by {simp[ext], split, ring, ring,}
end

theorem conj_mul {a b : ℤ_ζ} : conj (a * b) = conj a * conj b :=
begin
     simp[ext], split, ring, ring,
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

/-- norm(x) represents the norm of x -/
def norm (n : ℤ_ζ) : ℤ := n.a * n.a - n.a * n.b + n.b * n.b
lemma norm_def (n : ℤ_ζ) : n.norm = n.a * n.a - n.a * n.b + n.b * n.b := rfl

@[simp] theorem norm_nonneg : ∀ x : ℤ_ζ, 0 ≤ x.norm :=
begin
     intro x,
     rw norm_def, nlinarith,
end

@[simp] lemma norm_mul (n m : ℤ_ζ) : norm (n * m) = norm n * norm m :=
begin
     rw [eql n, eql m, norm_def, norm_def, norm_def], 
     simp[ext], ring,
end

@[simp] lemma norm_zero : norm 0 = 0 := by simp [norm]
@[simp] lemma norm_one : norm 1 = 1 := by simp [norm]
theorem norm_int_cast (n : ℤ) : norm n = n * n := by simp [norm]
theorem norm_nat_cast (n : ℕ) : norm n = n * n := norm_int_cast n

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
     have h2: n * n.conj = ⟨n.a * n.a - n.a * n.b + n.b * n.b, 0⟩,
     {rw eql n, simp[ext], split, ring, ring,},
     rw[h1,h2],
end

@[simp] lemma norm_neg (x : ℤ_ζ) : (-x).norm = x.norm :=
begin
     rw norm_def (-x), rw norm_def x, simp[ext],
end

@[simp] lemma norm_conj (x : ℤ_ζ) : x.conj.norm = x.norm :=
begin
     rw norm_def, rw norm_def, simp[ext], ring, 
end                                                           

theorem norm_nat: ∀ n : ℤ, ∀ x : ℤ_ζ, (of_int n * x).norm = n^2 * x.norm :=
begin
     intros n x,
     have h1: of_int n * x = ⟨n * x.a, n * x.b⟩, by simp[ext],
     rw [h1, norm_def, norm_def],
     simp[ext], ring,
end

lemma norm_eq_one_0(a : ℤ) : 0 ≤ a ∧ a ≠ 0 → 0 < a := 
begin
     intro h, contrapose! h, finish,
end


lemma lt_le_succ(a b : ℤ) : a < b → a.succ ≤ b := by tauto
lemma left_add_nonneg(a b : ℤ):  0 ≤ a → b ≤ a + b := by omega

lemma pow_two_abs(b : ℤ) : b^2 = (abs b)^2 := 
begin
     have h1: abs b = b ∨ abs b = -b, by exact abs_choice b,
     cases h1, 
     rw h1,
     rw h1, ring, 
end

lemma smaller_1(n : ℤ) : n ≤ 1 ∧ 0 ≤ n → n = 0 ∨ n = 1 := by omega


/-- We prove that ℤ[ζ] is a Euclidean domain in this part. The main task is to show
∀ a b ∈ ℤ[ζ], ∃ q r ∈ ℤ[ζ], a = qb + r, with norm(r) < norm(b). ∀ a b, q is defined
by function quotient, and r by remainder.-/

def quotient: ℤ_ζ → ℤ_ζ → ℤ_ζ | ⟨x, y⟩ ⟨x', y'⟩ 
       := ⟨round ((x * x' - x * y' + y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
          round ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩ 
lemma quotient_def (x y x' y': ℤ) : quotient ⟨x, y⟩ ⟨x', y'⟩  = 
          ⟨round ((x * x' - x * y' + y * y' : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ)), 
          round ((-x * y' + x' * y : ℚ)/(x'^2 - x' * y' + y'^2 : ℚ))⟩  := rfl

lemma div_zero (n : ℤ_ζ): quotient n 0 = 0 := 
begin 
have h1: round ((n.a * 0 - n.a * 0 + n.b * 0 : ℚ)/(0^2 - 0 * 0 + 0^2 : ℚ)) = 0,
by norm_num,
have h2: round ((-n.a * 0 + 0 * n.b : ℚ)/(0^2 - 0 * 0 + 0^2 : ℚ)) = 0,
by norm_num,
rw [eql n, eql 0], rw quotient_def, simp[ext],
end 

@[simp] theorem add_assoc : ∀ (a b c : ℤ_ζ), a + b + c = a + (b + c) :=
begin
     intros a b c,
     simp[ext], split, ring, ring,
end

@[simp] theorem nsmul_zero' : ∀ (x : ℤ_ζ), nsmul 0 x = 0 :=
begin
     intro x,
     rw eql x, simp[ext],
end

@[simp] theorem nsmul_succ' : ∀ (n : ℕ) (x : ℤ_ζ), nsmul n.succ x = x + nsmul n x :=
begin
     intros;
     try{refl'},
end

@[simp] theorem sub_eq_add_neg :  ∀ (a b : ℤ_ζ), a - b = a + -b := 
begin
     intros a b,
     rw[eql a, eql b],
     simp[ext], split, ring, ring,
end

@[simp] theorem gsmul_zero' : ∀ (a : ℤ_ζ), gsmul_rec 0 a = 0 :=
 begin
     intro x, rw eql x, try{refl},
end

theorem gsmul_succ': ∀ (n : ℕ) (a : ℤ_ζ), gsmul_rec (int.of_nat n.succ) a = a + gsmul_rec (int.of_nat n) a :=
begin
     intros; try{refl},
end

@[simp] theorem gsmul_neg' : ∀ (n : ℕ) (a : ℤ_ζ), gsmul_rec -[1+ n] a = -gsmul_rec ↑(n.succ) a :=
begin
     intros;
     try{refl},
end

theorem add_comm :  ∀ (a b : ℤ_ζ), a + b = b + a :=
begin
intros a b,
rw[eql a, eql b],
simp[ext], split, ring, ring,
end

@[simp] theorem one_mul : ∀ (a : ℤ_ζ), 1 * a = a :=
begin
     intros a,
     rw [eql 1, eql a],
     simp[ext],
end

@[simp] theorem mul_one : ∀ (a : ℤ_ζ), a * 1 = a := 
begin
     intro a,
     rw [eql 1, eql a], simp[ext],
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
     simp[ext],
     split, ring, ring,
end

@[simp] theorem right_distrib_0 : ∀ (a b c : ℤ_ζ), (a + b) * c = a * c + b * c :=
begin
     intros a b c,
     simp[ext], split, ring, ring,
end

theorem mul_comm:  ∀ (a b : ℤ_ζ), a * b = b * a :=
begin
     intros a b,
     simp[ext], split, ring, ring,
end

/-- the definition of r in a = bq + r described above-/
def remainder : ℤ_ζ → ℤ_ζ → ℤ_ζ |  a b := a - b * (quotient a b) 

@[simp] theorem quotient_mul_add_remainder_eq :∀ (a b : ℤ_ζ), b * quotient a b + (remainder a b) = a :=
begin
     intros a b,
     calc b * a.quotient b + (remainder a b) = b * quotient a b + (a - b * (quotient a b))  : by refl
                                         ... = a           : by ring,
end

lemma nat_abs_ge0(a b : ℤ) : 0 ≤ a ∧ 0 ≤ b ∧ b ≤ a → b.nat_abs ≤ a.nat_abs:=
begin
     intro h,
     have h1 : a * a ≥ b * b, by nlinarith[h.1, h.2.1, h.2.2],
     exact int.nat_abs_le_iff_mul_self_le.mpr h1,
end

lemma nat_abs_lt(a b: ℤ): 0 ≤ a ∧ 0 ≤ b ∧ a < b → a.nat_abs < b.nat_abs :=
begin
     intro h,
     exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt h.1 h.2.2,
end

/-- Follow the structure definition of Euclidean domain we should define a 
well-founded relation r, s.t. r a b : |a| < |b|, and prove that r (remainder a b)
 b-/
def f := λ (a : ℤ_ζ), a.norm.nat_abs
/-- To make use of current results in mathlib, we define f, and use f to define r-/
def r := inv_image nat.lt f

@[simp] theorem r_well_founded : well_founded r :=
begin
     have h : well_founded nat.lt, by exact nat.lt_wf,
     exact inv_image.wf f h,
end
end
end int_cubic_root

/-- define ℚ_ζ-/
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

/-- lift an Eisenstein integer to ℚ[ζ]-/
def of_eisen_int(x : ℤ_ζ) : ℚ_ζ := ⟨(x.a : ℚ), (x.b : ℚ)⟩ 
theorem of_eisen_int_def: ∀ x y : ℤ, of_eisen_int ⟨x, y⟩ = ⟨(x : ℚ), (y : ℚ)⟩ := 
begin
     intros x y,
     try{refl},
end

/-- zero ∈ ℚ[ζ]-/
def zero : ℚ_ζ  := of_eisen_int 0
instance : has_zero ℚ_ζ := ⟨ra_cubic_root.zero⟩
theorem zero_c : (0 : ℚ_ζ).c = (0 : ℚ) := rfl 
theorem zero_d : (0 : ℚ_ζ).d = (0 : ℚ) := rfl
instance : inhabited (ℚ_ζ) := ⟨0⟩ 

/-- one ∈ ℚ[ζ]-/
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

/-- representative of ζ in ℚ[ζ], we use ζ0 to emphasize that ζ0 and ζ defined above
are two different elements of different types, ℤ[ζ] and ℚ[ζ], and avoid 
misunderstanding.-/
def ζ0 : ℚ_ζ := ⟨0, 1⟩  
@[simp] theorem ζ_c : (ζ0 : (ℚ_ζ)).c = 0 := rfl
@[simp] theorem ζ_d : (ζ0 : (ℚ_ζ)).d = 1 := rfl

/-- addition in ℚ[ζ]-/
def add: (ℚ_ζ) → (ℚ_ζ) → (ℚ_ζ)
|⟨x, y⟩ ⟨x', y'⟩ := ⟨x + x', y + y'⟩
instance : has_add ℚ_ζ := ⟨ra_cubic_root.add⟩
@[simp] theorem add_def(x y x' y' : ℚ) :
   (⟨x, y⟩ + ⟨x', y'⟩ : ℚ_ζ) = ⟨x + x', y + y'⟩ := rfl 

/-- negation in ℚ[ζ]-/
def neg : ℚ_ζ → ℚ_ζ
|⟨x, y⟩ := ⟨-x, -y⟩
instance : has_neg ℚ_ζ := ⟨ra_cubic_root.neg⟩
@[simp] theorem neg_c : ∀ z : ℚ_ζ, (-z).c = - z.c 
|⟨x, y⟩ := rfl 
@[simp] theorem neg_d : ∀ z : ℚ_ζ, (-z).d = - z.d 
|⟨x, y⟩ := rfl 

/-- subtraction in ℚ[ζ]-/
def sub: ℚ_ζ → (ℚ_ζ) → (ℚ_ζ) := λ a b, a + -b
instance : has_sub ℚ_ζ := ⟨ra_cubic_root.sub⟩

/-- multiplication in ℚ[ζ]-/
def mul : ℚ_ζ → ℚ_ζ → ℚ_ζ
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩
instance : has_mul ℚ_ζ := ⟨ra_cubic_root.mul⟩
@[simp] theorem mul_def(x y x' y' : ℚ) : 
   (⟨x, y⟩ * ⟨x', y'⟩ : ℚ_ζ) = ⟨x * x' - y * y', x * y' + y * x' - y * y'⟩ := rfl 
@[simp] theorem mul_c : ∀ z w : ℚ_ζ, (z * w).c = z.c * w.c - z.d * w.d
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem mul_d : ∀ z w : ℚ_ζ, (z * w).d = z.c * w.d + z.d * w.c - z.d * w.d
| ⟨x, y⟩ ⟨x', y'⟩ := rfl

/-- z = ⟨z.a, z.b⟩; notations-/
theorem eql0(z : ℚ_ζ) : z = ⟨z.c, z.d⟩ :=
begin 
     have h1 : z.c = (⟨z.c, z.d⟩ : ℚ_ζ).c, refl,
     have h2 : z.d = (⟨z.c, z.d⟩ : ℚ_ζ).d, refl,
     exact ext.mpr ⟨h1, h2⟩,
end

/-- norm of x ∈ ℚ[ζ], denoted by norm1-/
def norm1 (a : ℚ_ζ) : ℚ := a.c * a.c - a.c * a.d + a.d * a.d
@[simp] lemma norm1_def (a b : ℚ) : (⟨a, b⟩ : ℚ_ζ).norm1 = a * a - a * b + b * b  := 
by try {refl}

@[simp] theorem norm1_nonneg : ∀ x : ℚ_ζ, 0 ≤ norm1 x :=
begin
     intro x, rw eql0 x,
     simp, nlinarith,
end

@[simp] theorem norm1_nezero : ∀ x : ℚ_ζ, x ≠ 0 → 0 < x.norm1 := 
begin
     intros x h,
     have h1 : 4 * x.norm1 > 0, 
     begin
     have h2 : x.c ≠ 0 ∨ x.d ≠ 0, by {contrapose! h, simp[ext], exact h,},
     cases h2,
     {have h3: x.c^2 > 0, by exact pow_two_pos_of_ne_zero x.c h2,
     rw eql0 x, simp, nlinarith[h3]},
     {have h3: x.d^2 > 0, by exact pow_two_pos_of_ne_zero x.d h2,
     rw eql0 x, simp, nlinarith[h3]},
     end,
     nlinarith[h1],
end

@[simp] lemma norm1_mul : ∀ x y : ℚ_ζ, (x * y).norm1 = x.norm1 * y.norm1 := 
begin
intros x y,
have h1: x.norm1 = (x.c)^2 - x.c * x.d + (x.d)^2, 
{rw eql0 x, simp, ring,},
have h2: y.norm1 = (y.c)^2 - y.c * y.d + (y.d)^2, 
{rw eql0 y, simp, ring,},
have h3: (x * y).norm1 = (x.c * y.c - x.d * y.d)^2 - (x.c * y.c - x.d* y.d) * (x.c * y.d + x.d * y.c - x.d * y.d)
                       + (x.c * y.d + x.d * y.c - x.d * y.d)^2,
{rw [eql0 x, eql0 y], simp, ring,},
have t : x.norm1 * y.norm1 = (x * y).norm1,
{rw [h1, h2], rw h3, ring,},
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

/-- division in ℚ_ζ-/
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
     rw [eql0 0, eql0 x], simp, 
     rw [eql0 0, eql0 x], simp,
end
@[simp] theorem add_zero (x : ℚ_ζ) : x + 0 = x := 
begin
     simp[ext],
     split,
     rw [eql0 0, eql0 x], simp,
     rw [eql0 0, eql0 x], simp,
end

@[simp]lemma add_assoc : ∀ a b c : ℚ_ζ, (a + b + c) = (a + (b + c)) :=
begin
     intros a b c,
     simp[ext],
     split,
     rw [eql0 a, eql0 b, eql0 c], simp, ring, 
     rw [eql0 a, eql0 b, eql0 c], simp, ring,
end
lemma add_comm : ∀ x y: ℚ_ζ, x + y = y + x :=
begin
     intros x y,
     simp[ext], split, 
     rw[eql0 x, eql0 y], simp, ring,
     rw[eql0 x, eql0 y], simp, ring,
end

lemma add_assoc_0 : ∀ x y z : ℚ_ζ, x + (y + z) = z + (x + y)       :=
begin
     intros x y z,
     rw [← add_assoc x y z, add_comm (x + y) z],
end

@[simp]lemma add_left_neg: ∀ x : ℚ_ζ, (-x) + x = 0 :=
begin
     intro x,
     simp[ext],
     rw [eql0 (-x), eql0 x], split, simp, simp, 
end
@[simp]lemma add_right_neg: ∀ x : ℚ_ζ, x + -x = 0 :=
begin
     intro x,
     simp[ext],
     rw [eql0 (-x), eql0 x], split, simp, simp,
end

@[simp] theorem mul_assoc (a b c: ℚ_ζ) : a * b * c = a * (b * c):= 
begin 
     simp[ext],
     split, 
     ring, ring, 
end
@[simp] theorem left_distrib (a b c : ℚ_ζ) : a * (b + c) = a * b + a * c := 
begin
     rw[eql0 a, eql0 b, eql0 c],
     simp[ext],
     split,
     ring, ring,
end
@[simp] theorem right_distrib (a b c : ℚ_ζ) : (a + b) * c = a * c + b * c :=
begin
     rw[eql0 a, eql0 b, eql0 c],
     simp[ext],
     split,
     ring, ring,
end

theorem mul_comm (a b : ℚ_ζ) : a * b = b * a := 
begin
     rw [eql0 a, eql0 b],
     simp[ext], split, ring, ring,
end

/-- Combined the theorems above, we have ℚ[ζ] is a commmutative ring, and thus we 
are able to define a ring homomorphism from ℤ[ζ] to ℚ[ζ] in Lean.-/
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


open int_cubic_root 

/-- the ring homomorphism from ℤ[ζ] to ℚ[ζ] is defined as follows-/
@[simp] def lift0: ℤ_ζ →+* ℚ_ζ :=
{ 
  to_fun := λ x, ⟨(x.a : ℚ), (x.b : ℚ)⟩,
  map_zero' := by try{refl},
  map_add' := λ a b, by { simp, },
  map_one' := by try{refl},
  map_mul' := λ x y, by { simp[ext],},
}
instance : has_coe (ℤ_ζ) ℚ_ζ := ⟨lift0⟩

/-- The following properties facilitates later calculations.-/
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
             ... = (x : ℚ_ζ).norm1                              : by try {refl},
     have h2 : (y.norm : ℚ) = (y : ℚ_ζ).norm1, 
     calc (y.norm : ℚ) = (coe (y.a * y.a - y.a * y.b + y.b * y.b) : ℚ)  : rfl
             ... = (y.a * y.a - y.a * y.b + y.b * y.b : ℚ)      : by norm_num 
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

/- Now we begin to prove the Euclidean property-/
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
                      ...   = ((b : ℚ_ζ) * ((a : ℚ_ζ)/(b : ℚ_ζ)) + (b : ℚ_ζ) * -(coe(a.quotient b))).norm1   : by {rw ←s1, ring_nf}
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