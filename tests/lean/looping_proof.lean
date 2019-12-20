-- Lean's type theory allows looping proof terms. We test here that loops
-- are not observable outside of #reduce.
-- See https://leanprover-community.github.io/archive/113488general/41870Normalizationfailsinlean.html
-- and https://arxiv.org/abs/1911.08174

def top := ∀ p : Prop, p → p

def pext := ∀ (A B : Prop), A → B → A = B

def supercast (h : pext) (A B : Prop) (a : A) (b : B) : B
  := @cast A B (h A B a b) a

def omega : pext → top :=
  λ h A a, supercast h (top → top) A
    (λ z: top, z (top → top) (λ x, x) z) a

def Omega : pext → top :=
  λ h, omega h (top → top) (λ x, x) (omega h)

def Omega' : pext → top := λ h, (λ p x, x)

theorem loopy : Omega = Omega' := rfl

#print "No loops!"
