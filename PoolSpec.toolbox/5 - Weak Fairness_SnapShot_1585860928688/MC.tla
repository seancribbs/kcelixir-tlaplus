---- MODULE MC ----
EXTENDS PoolSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Resources
const_1585860925667210000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_1585860925667211000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1585860925667212000 == 
Permutations(const_1585860925667210000) \union Permutations(const_1585860925667211000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 15:55:25 CDT 2020 by seancribbs
