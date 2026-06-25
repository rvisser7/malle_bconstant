# Computing the $b$-constant in Malle's conjecture

Let $G \subseteq S_d$ be a transitve permutation group of degree $d$.  A strong version of Malle's conjecture predicts that the number of number fields $K / Q$ with Galois group $G$ and of discriminant up to $X$ is $\sim c(G) X^{1/a(G)} (\log X)^{b(G) - 1}$ as $X \to \infty$, for some constants $a(G), b(G), c(G)$.

The code in this repository explicitly computes various conjectured values for the $b$-constant $b(G)$ in Malle's conjecture:

 - Malle's original conjectured, denoted as $b_M(G)$. 

 - Turkelli's modified $b_T(G)$, defined in https://arxiv.org/abs/0809.0951 .

 - Wang's constant $b_W(G)$, defined in https://arxiv.org/abs/2502.04261 .

Data is included for various transtive permutation groups up to degree 47, and data is stored both with respect to the discriminant ordering and with respect to the product of ramified primes ordering.
