# Formalising Wenger graphs in Lean

[![Lean Action CI](https://github.com/mitchell-horner/Wenger/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mitchell-horner/Wenger/actions/workflows/lean_action_ci.yml)

This repository contains a formalisation of Wenger graphs and the lower bounds for the extremal numbers of $C_4$, $C_6$ and $C_{10}$ in [Lean](https://lean-lang.org/). The statements of the results are as follows:

**Wenger's Lemma 1**

Suppose $p$ is a prime number and $m$ is a natural number. If $v_0 w_0 v_1 w_1 \cdots v_m w_m$ is a cycle of length $2(m+1)$ in the Wenger graph $H_{m+1}(p)$, with each $v_i$ in the first part, each $w_i$ in the second, and $v_i$ and $v_{i+1}$ both adjacent to $w_i$ cyclically, then every $w_{i_0}$ shares its last coordinate with some other $w_i$.

```lean
theorem WengerRel.exists_ne_last_eq (hp : p.Prime)
  {v w : ZMod (m + 1) → Fin (m + 1) → ZMod p}
  (hr : ∀ i, WengerRel p m (v i) (w i)) (hl : ∀ i, WengerRel p m (v (i + 1)) (w i))
  (hv : ∀ i, v (i + 1) ≠ v i) (i₀ : ZMod (m + 1)) :
  ∃ i, i ≠ i₀ ∧ w i (Fin.last m) = w i₀ (Fin.last m)
```

**Wenger's Lemma 2**

Suppose $p$ and $m$ are natural numbers, and $a$, $b$ and $b'$ are vertices of the Wenger graph $H_{m+1}(p)$ such that $b$ and $b'$ are both adjacent to $a$. If $b$ and $b'$ agree in the last coordinate, then $b = b'$.

```lean
lemma WengerRel.eq_of_last_eq {a b b' : Fin (m + 1) → ZMod p} (h : WengerRel p m a b)
  (h' : WengerRel p m a b') : b (Fin.last m) = b' (Fin.last m) → b = b'
```

**Wenger's theorem**

Suppose $p$ is a prime number and $m$ is a natural number such that $m+1$ is $2$, $3$ or $5$. Then the Wenger graph $H_{m+1}(p)$ contains no copy of the cycle $C_{2(m+1)}$.

```lean
theorem cycleGraph_free_wengerGraph (hp : p.Prime)
  (hm : m + 1 = 2 ∨ m + 1 = 3 ∨ m + 1 = 5) :
  (cycleGraph (2 * (m + 1))).Free (wengerGraph p m)
```

**Wenger's theorem ($C_4$, $C_6$ and $C_{10}$ versions)**

Suppose $p$ is a prime number. Then the Wenger graphs $H_2(p)$, $H_3(p)$ and $H_5(p)$ contain no copy of $C_4$, $C_6$ and $C_{10}$ respectively.

```lean
theorem cycleGraph_four_free_wengerGraph (hp : p.Prime) :
  (cycleGraph 4).Free (wengerGraph p 1)

theorem cycleGraph_six_free_wengerGraph (hp : p.Prime) :
  (cycleGraph 6).Free (wengerGraph p 2)

theorem cycleGraph_ten_free_wengerGraph (hp : p.Prime) :
  (cycleGraph 10).Free (wengerGraph p 4)
```

**The Wenger lower bound**

Suppose $m$ is a natural number. If the Wenger graphs $H_{m+1}(p)$ contain no copy of $C_{2(m+1)}$ for every prime $p$, then the extremal numbers of $C_{2(m+1)}$ satisfy

$$
\textrm{ex}\left(n, C_{2(m+1)}\right) = \Omega\left(n^{\frac{m+2}{m+1}}\right)
$$

as $n \rightarrow \infty$.

```lean
theorem isBigO_rpow_extremalNumber_cycleGraph_of_free {m : ℕ}
  (h : ∀ {p : ℕ}, p.Prime → (cycleGraph (2 * (m + 1))).Free (wengerGraph p m)) :
  (fun n : ℕ ↦ (n : ℝ) ^ (((m : ℝ) + 2) / ((m : ℝ) + 1))) =O[atTop]
    fun n : ℕ ↦ (extremalNumber n (cycleGraph (2 * (m + 1))) : ℝ)
```

**The $C_4$, $C_6$ and $C_{10}$ lower bounds**

The extremal numbers of $C_4$, $C_6$ and $C_{10}$ satisfy

$$
\textrm{ex}(n, C_4) = \Omega\left(n^{3/2}\right), \qquad
\textrm{ex}(n, C_6) = \Omega\left(n^{4/3}\right), \qquad
\textrm{ex}(n, C_{10}) = \Omega\left(n^{6/5}\right)
$$

as $n \rightarrow \infty$.

```lean
theorem isBigO_rpow_extremalNumber_cycleGraph_four :
  (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ)) =O[atTop]
    fun n : ℕ ↦ (extremalNumber n (cycleGraph 4) : ℝ)

theorem isBigO_rpow_extremalNumber_cycleGraph_six :
  (fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ)) =O[atTop]
    fun n : ℕ ↦ (extremalNumber n (cycleGraph 6) : ℝ)

theorem isBigO_rpow_extremalNumber_cycleGraph_ten :
  (fun n : ℕ ↦ (n : ℝ) ^ (6 / 5 : ℝ)) =O[atTop]
    fun n : ℕ ↦ (extremalNumber n (cycleGraph 10) : ℝ)
```

## Upstreaming to mathlib

The progress towards upstreaming these results to [mathlib](https://github.com/leanprover-community/mathlib4) is as follows:

- [ ] Wenger's lemma 1
- [ ] Wenger's lemma 2
- [ ] Wenger's theorem
- [ ] Wenger's theorem ($C_4$, $C_6$ and $C_{10}$)
- [ ] The Wenger lower bound
- [ ] The $C_4$, $C_6$ and $C_{10}$ lower bounds