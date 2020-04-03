---- MODULE MC ----
EXTENDS PoolSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3, c4, c5
----

\* MV CONSTANT definitions Resources
const_158587351268418000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_158587351268419000 == 
{c1, c2, c3, c4, c5}
----

\* SYMMETRY definition
symm_158587351268420000 == 
Permutations(const_158587351268418000) \union Permutations(const_158587351268419000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 19:25:12 CDT 2020 by seancribbs
