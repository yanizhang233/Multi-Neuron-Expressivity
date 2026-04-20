# Multi-Neuron

This repository contains a Lean formalization of the results in the following paper

Yuhao Mao, Yani Zhang, and Martin Vechev, "Expressiveness of multi-neuron convex relaxations in neural network certification", International Conference on Learning Representations (ICLR), 2026.

https://arxiv.org/abs/2410.06816

## 0. Summary
The following notions are formalized:
convex polytopes in $\mathbb{R}^d$, feedforward ReLU neural networks, the layerwise convex relaxation $\mathcal{P}_1$, the cross-layer convex relaxation $\mathcal{P}_r$.


The following results in the paper, along with their proofs, are formalized:
Lemma 3.1, Lemma 3.2, Theorem 3.3, Lemma 4.1, Theorem 4.2. 


The central results in the paper are Theorem 3.3 and Theorem 4.2, which establish the incompleteness of layerwise relaxations and cross-layer relaxations, respectively. 
The argument in the paper is developed in the following structure:

```text
Lemma 3.1 -> Lemma 3.2 -> Theorem 3.3 ->|
                                        |--> Theorem 4.2
                            Lemma 4.1 ->|
```

During the development of the Lean code, we discovered an alternative way of proving Lemma 3.2, namely by way of Lemma 0 below instead of Lemma 3.1.

> **Lemma 3.0.**
> For a ReLU neural network $f = f₂ \circ f₁$, let $X$ be a convex input set.
> Then the feasible set induced by $\mathcal{P}_1$ for $f$ on $X$ is a superset of
> $f₂ (\texttt{convex hull} (f₁ (X)))$.


The lean formalization is built on the following structure. 

```text
Lemma 3.0 -> Lemma 3.2 -> Theorem 3.3 ->|
                                        |--> Theorem 4.2
                            Lemma 4.1 ->|
```
For the sake of completeness, we still formalized Lemma 3.1 into Lean. 


The following table contains the one-to-one correspondence between the lemmata and theorems mentioned above and the Lean theorems. 

| Paper statement | Lean theorem |
| --- | --- |
| Lemma 3.2 | `theorem lemma32` |
| Theorem 3.3 | `theorem theorem33` |
| Lemma 4.1 | `theorem lemma41` |
| Theorem 4.2 | `theorem theorem42` |
| Lemma 3.0 | `theorem reach_comp_convex_subset_P1OutputSet_comp` |
| Lemma 3.1 | `theorem lemma31` |




## 1. Basic
### 1.1 FunctionGraph.lean
| Lean | Definition or proof statement |
| --- | --- |
| `functionGraph` | Define function graph. |
|    `fst_image_functionGraph`        |   Prove that projecting a function graph onto the input coordinate recovers the domain.        |
|`snd_image_functionGraph` |Prove that projecting a function graph onto the output coordinate recovers the image.|
| `fst_image_convexHull_functionGraph`| Prove that projecting the convex hull of a function graph onto the input coordinate recovers the convex hull of the domain. |
|`snd_image_convexHull_functionGraph` |Prove that projecting the convex hull of a function graph onto the output coordinate recovers the convex hull of the image. |


### 1.2 Network.lean
| Lean | Definition or proof statement |
| --- | --- |
| `relu`| Define the coorindate-wise ReLU function.|
|`Net` |Define a ReLU neural network. |
|`eval` |Define the network function of a ReLU neural network. |
|`reach` |Define the exact reachable set of a network on an input set. |
|`continuous_relu` | Prove that the ReLU function is continuous.|
|`continuous_affinemap`|Prove that an affine layer is continuous.|
|`reach_nonempty`|Prove that if an input set is nonempty, then the exact reachable set is nonempty. |

### 1.3 Polytope.lean
| Lean | Definition or proof statement |
| --- | --- |
|`AffineInequality`|Define an affine inequality.|
|`halfspace`|Define the half space defined by an affine inequality.|
|`HPolyhedron`|Define an H-polyhedron.|
|`HPolyhedron.feasibleSet`|Define the set characterized by an H-polyhedron.|
|`Polytope`|Define  an H-polytope.|
|`Polytope.feasibleSet`|Define the set characterized by an H-polytope.|
|`convex_halfspace`|Prove that a half space is convex.|
|`HPolyhedron.convex_feasibleSet`|Prove that the set characterized by H-polyhedron is convex. |
|`HPolyhedron.convex_feasibleSet`|Prove that the set characterized by an H-polytope is convex. |
|`HPolyhedron.isBounded_feasibleSet`|Prove that the set characterized by an H-polytope is bounded.|

## 2. Relaxation

### 2.1 Layerwise.lean
| Lean | Definition or proof statement |
| --- | --- |
|`P1RelaxedSet`|Define the $\mathcal{P}_1$ relaxation.|
|`P1OutputSet`|Define the output feasible set induced $\mathcal{P}_1$ by on a network and an input set.|
|`reach_subset_P1OutputSet`|Prove that $\mathcal{P}_1$ is sound: the output feasible set induced $\mathcal{P}_1$ is a superset of the exact feasible set. |
|`convex_reach_subset_P1OutputSet`|Prove that if an input set is convex, then the output feasible set induced $\mathcal{P}_1$ contains the convex hull of the exact feasible set. |
|`reach_comp_convex_subset_P1OutputSet_comp`|Prove Lemma 3.0.|
|`P1OutputSet_bounded`|Prove that if an input set is convex and bounded, then the output feasible set induced by $\mathcal{P}_1$ is bounded. |

### 2.2 Crosslayer.lean
| Lean | Definition or proof statement |
| --- | --- |
|`layerCount`|Define the function counting the number of layers in a network.|
|`blockRelax`|Define the relaxation of a block of layers by way of taking its convex hull.|
|`T`|Define the trace containing of all intermediate variables.|
|`instAddCommMonoidFullTrace`|Prove that `T` is `AddCommMonoid'. |
|`instModuleFullTrace`|Prove that `T` is `Module'. |
|`PrRelaxedSet`|Define the relaxed set induced by $\mathcal{P}_r$.|
|`PrOutputSet`|Define the feasible output set induced by $\mathcal{P}_r$|
|`reach_subset_PrOutputSet`|Prove that $\mathcal{P}_r$ is sound: the feasible output set induced by $\mathcal{P}_r$ always contains the exact reachable set. |


## 3. Results
### 3.1 Lemma3-1.lean
| Lean | Definition or proof statement |
| --- | --- |
|`splitProjectio`|Define the projection of the relaxed set induced by $\mathcal{P}_1$ onto an intermediate layer.|
|`lemma31`|Prove Lemma 3.1.|
### 3.2 Lemma3-2.lean
| Lean | Definition or proof statement |
| --- | --- |
|`lbP1` |Define the lower bound on some coordinate induced by $\mathcal{P}_1$.|
|      `ubP1` |Define the upper bound on some coordinate induced by $\mathcal{P}_1$.|
|`lemma32Polytope_lower`|Prove the lower bound half of Lemma 3.2.|
|`lemma32Polytope_upper`|Prove the upper bound half of Lemma 3.2|
|`lemma32Polytope`|Prove Lemma 3.2.|


### 3.3 auxNets.lean
| Lean | Definition or proof statement |
| --- | --- |
|`valleyNet`|Define the ReLU network that realizes the function $f(x,y)=2T\vert x-1 \vert + 2T\vert y-0.5\vert $.|
|`negValleyNet`|Define the ReLU network that realizes the function $f(x,y)=-2T\vert x-1 \vert - 2T\vert y-0.5\vert $.|
|`prefixNet`|Define the ReLU network that maps an input set to the 2-D set $\{(x_1,x_2): 0 ≤ x_1 ≤ 1, x_2 = 0\} ∪ \{(x_1,x_2): 1 ≤ x_1 ≤ 2, x_2 = x_1 - 1\}$.|
|`valleyValue_nonneg`|Prove that the network function of `valleyNet` is nonnegative. |

### 3.4 Theorem3-3.lean
| Lean | Definition or proof statement |
| --- | --- |
|`valleyValue_prefix_ge`|Prove that the function of `prefixNet` composed with `valleyNet` is lower bounded by $T$. |
|`theorem33Polytope_lower`|Prove the lower bound half of Theorem 3.3.|
|`theorem33Polytope_upper`|Prove the upper bound half of Theorem 3.3.|

### 3.5 Lemma4-1.lean
| Lean | Definition or proof statement |
| --- | --- |
|`gammaRadius`|Define the $\max(1, \alpha L)$ in the paper.|
|`lbPr`|Define the lower bound on some output coordinate returned by $\mathcal{P_r}$. |
|`ubPr`|Define the upper bound on some output coordinate returned by $\mathcal{P_r}$.|
|`pumpNet`|Define the operation of pumping dummy layers in the paper. |
|`PrOutputSetOnPolytope_pumpDecomposition_eq`|Prove that after pumping dummy layers, $\mathcal{P_r}$ computes exactly on the convex hull of the image of the prefix net.|
|`lemma41`|Prove Lemma 4.1.|
|||

### 3.6 Theorem4-2.lean
| Lean | Definition or proof statement |
| --- | --- |
|||
|||