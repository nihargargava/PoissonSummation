# Poisson Summation


The goal of this repository is to formally verify the Poisson summation formula in $\mathbb{R}^n$ for all $n \geq 1$.

--------------------------------------------------

Consider a lattice $\Lambda \subseteq \mathbb{R}^{d}$. Let $\Lambda^{*}$ be the dual lattice defined as 

$$
\Lambda^{*} = \\{ \lambda \in \mathbb{R}^{d} \vert \langle \lambda,\Lambda\rangle \subseteq \mathbb{Z} \\}.
$$

On $\mathbb{R}^d$, we define the following map to be the Fourier transform.

$$
\mathcal{F}: \mathcal{S}(\mathbb{R}^{d})  \mapsto 
\mathcal{S}(\mathbb{R}^{d}) 
$$

Here $\mathcal{S}(\mathbb{R}^{d})$ is the space of Schwartz function on $\mathbb{R}^d$.

Let $\hat{f}= \mathcal{F}(f)$ for some Schwartz function $f \in \mathcal{S}(\mathbb{R}^{d})$. Then, we have the following formula

$$
\sum_{v \in \Lambda} f(v) = 
\frac{1}{\\mathrm{vol}(\mathbb{R}^{d}/\Lambda )} \sum_{\lambda \in \Lambda^{*}} \hat{f}(v).
$$

--------------------------------------------------



# AI Policy


The goal of this repository is for the author to become more proficient in Lean. No AI use is allowed or welcomed here.
LLMs may be used as a learning resource.
