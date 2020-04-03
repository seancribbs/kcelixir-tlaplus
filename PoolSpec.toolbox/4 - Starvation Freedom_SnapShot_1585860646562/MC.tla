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
const_1585860644532196000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_1585860644532197000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1585860644532198000 == 
Permutations(const_1585860644532196000) \union Permutations(const_1585860644532197000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 15:50:44 CDT 2020 by seancribbs
