
A field $$k$$ is $$C_1$$ provided that any homogeneous polynomial $$f$$ of degree `d:ℕ` in `n:ℕ` variables with coefficients in $$k$$ has a solution $$v ∈ k^n$$ with $$f(v) = 0$$ and $$v ≠ 0$$ provided that $$d < n$$.

More generally, for a non-negative rational number $$r$$, the notion of a $$C_r$$ field is defined by

``` lean4
def IsCr (r : {q :ℚ // q≥0 }) : Prop :=
  (k : Type*) [Field k]
  ∀ (n : ℕ),
  ∀ f : MvPolynomial (Fin n) k,
  ∀ {d : ℕ},
  MvPolynomial.IsHomogeneous f d → (d:ℝ) ^ (r:ℝ) < (n:ℝ) →
  ∃ v  : Fin n → k, f.eval v = 0 ∧ v ≠ 0
```

This proposal suggests to include the notion of $$C_r$$ fields in `mathlib`, and to include (some of) the following results.

## results about "which fields are $$C_1$$"

1. algebraically closed fields are $$C_1$$ 
2. finite extension of $$C_1$$ fields are $$C_1$$
3. finite fields are $$C_1$$ (result of *Chevalley-Warning*)
4. the field of rational functions k(T) is $$C_1$$ when k is alg. closed ("Tsen's Theorem")
5. If $$K_{nr}$$ ​ is "the" maximal unramified extension of a field $$K$$ which is complete under a discrete valuation with perfect residue field, then $$K_{nr}$$ ​ is $$C_1$$ (a result of Lang).

## results about "applications of the $$C_1$$ condition

6. any quadratic form on a vector space of dimension $$≥3$$ over a $$C_1$$ fields is isotropic.
7. a central simple algebra over a $$C_1$$ field $$k$$ is split -- i.e. is isomorphic as $$k$$-algebras to the algebra of $$n × n$$ matrices $$Mat_n(k)$$ for some positive natural number $$n$$.
8. a $$C_1$$-field has cohomological dimension $$≤ 1$$   
   
## ancillary remarks

- some of the results -- especially 5. and 8. are probably aspirational at this point since they likely require development of a number of tools which aren't yet available.
  
- in particular, 7. requires introduction of the reduced norm of a central simple algebra (and so requires some sort of descent)
  
