# Singh Theorem: Lean 4 formalization

Jaskirat Singh, HIX Lab, founder@hixlab.si

## Statement

For $U\in U(N)$ Haar distributed, adjacent eigenangles $\theta_1<\theta_2$ with normalized gap
$s=\tfrac{N}{2\pi}(\theta_2-\theta_1)$ and $\Lambda(\theta)=\prod_k(1-e^{i(\theta_k-\theta)})$,

$$\operatorname{Var}\big(\log|\Lambda'(\theta_1)|-\log|\Lambda'(\theta_2)|\ \big|\ s\big)=c_N\,s^2\,(1+o(1)),\qquad s\to0,$$

$$c_N=\frac{\pi^2}{15}\Big(1-\frac{4}{N^2}\Big),\qquad c_N\to\frac{\pi^2}{15}.$$

## Structure

`Challenge.lean` is the statement a reader audits: the definitions and the two theorems
`Singh.singh_theorem` and `Singh.singh_theorem_isLittleO`, importing only Mathlib.
`Solution.lean` proves the same declarations from the library `Singh`, and
`comparator.json` lets `lake comparator` check that the two agree using only
`propext`, `Classical.choice` and `Quot.sound`. `formalization.yaml` records the
registry metadata.

| File | Content |
|---|---|
| `Singh/Algebra.lean` | pair identities, pointwise loop equations, $\mathbb E[(\sum u)^2]=\frac{n(n+2h)}{4h^2-1}$, closed form of $c_N$, $c_N\to\pi^2/15$ |
| `Singh/Hua.lean` | Hua ensemble $P_{n,2}(u)=Z^{-1}\prod_{j<k}(u_j-u_k)^2\prod_k(1+u_k^2)^{-(n+2)}$ on $\mathbb R^n$: $0<Z<\infty$, probability measure, distinct coordinates a.s., integrability of $(\sum u)^2$ and $\sum u^2$ |
| `Singh/Loop.lean` | loop equations for $P_{n,2}$ by integration by parts (`huaMeasure_loopA`, `huaMeasure_loopB`) |
| `Singh/Cayley.lean` | $\theta=\pi-2\arctan u$ maps the circle weight $\prod_{j<k}\sin^2\frac{\theta_j-\theta_k}{2}\prod_k\sin^4\frac{\theta_k}{2}$ to $P_{n,2}$; `circleE_eq_hua` |
| `Singh/Linear.lean` | conditional variance `palmVar` given an adjacent pair at gap $\delta$ under the Weyl density; `palmVar_tendsto`: $\operatorname{Var}/\delta^2\to\mathbb E_{w_0}[S^2]$ |
| `Singh/Analytic.lean` | `Singh.theorem_cN_CUE`, `Singh.theorem_cN_CUE_isLittleO` |

Key steps:

$$n+\mathbb E\Big[\sum u_k^2\Big]=2h\,\mathbb E\Big[\Big(\sum u_k\Big)^2\Big],\qquad n^2-2h\,\mathbb E\Big[\sum u_k^2\Big]+\mathbb E\Big[\Big(\sum u_k\Big)^2\Big]=0,$$

$$\mathbb E_{w_0}[S^2]=\tfrac14\,\mathbb E_{N-2,2}\Big[\Big(\sum u_k\Big)^2\Big]=\frac{N^2-4}{60},\qquad c_N=\Big(\frac{2\pi}{N}\Big)^2\frac{N^2-4}{60}.$$

## Conditioning

Given eigenangles at $\mp\delta/2$, $\delta=2\pi s/N$, the remaining $N-2$ angles have density proportional to
$\prod_{j<k}|e^{i\theta_j}-e^{i\theta_k}|^2\prod_k|e^{i\theta_k}-e^{-i\delta/2}|^2|e^{i\theta_k}-e^{i\delta/2}|^2$
restricted to $(\delta/2,2\pi-\delta/2)^{N-2}$ (adjacency). Under it
$x-y=\sum_k\big(\log|\sin\frac{\theta_k+\delta/2}{2}|-\log|\sin\frac{\theta_k-\delta/2}{2}|\big)$, its mean is $0$ by $\theta\mapsto2\pi-\theta$,
and dominated convergence gives the limit. `Singh.cueV N s` is this conditional variance; all inputs are proved.

## Build and check

```
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux with bubblewrap
```

Lean `v4.36.0-rc2`, Mathlib pinned in `lake-manifest.json`, Lean module system throughout.
No `sorry` outside the statement surface `Challenge.lean`; `#print axioms Singh.theorem_cN_CUE`
lists `propext`, `Classical.choice`, `Quot.sound`.

Registry submission: https://submit.palomar-registry.org/

## License

Apache-2.0, see `LICENSE`.
