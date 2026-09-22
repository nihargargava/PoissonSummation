# Blueprint

To prove the Poisson summation formula in $\mathbb{R}^{d}$, we will assume the formula for $\mathbb{R}$.
This is already present in `mathlib`. Hence, we know that for a Schwartz $f : \mathbb{R} \rightarrow  \mathbb{R}$ 
one has

$$
\sum_{n \in \mathbb{Z}}^{} f(n) = \sum_{\xi \in \mathbb{Z}}^{} \mathcal{F}(f)(\xi)
$$

One can then use the definition of the multidimensional Fourier transform for $f : \mathbb{R}^{d} \rightarrow  \mathbb{R}$:

$$
\mathcal{F}(f)(\xi_{1},\dots,\xi_{d}) = \int_{\mathbb{R}^{d}}^{} f(x_{1},\dots,x_{d}) e^{2 \pi i (x_{1} \xi_{1} + \dots + x_{d} \xi_{d})} \, \mathrm{d}x .
$$

Hence, this gives the Poisson summation formula for all variable-separable functions. What remains is to prove that this is enough.


One needs to show that variable-separable functions are dense in the Fréchet space of Schwartz functions and the Poisson summation formula is continuous with respect to limits in the Fréchet space. For this, we can take an explicit generating set of variable-separable bump functions to do this hopefully (still need to think about it).

