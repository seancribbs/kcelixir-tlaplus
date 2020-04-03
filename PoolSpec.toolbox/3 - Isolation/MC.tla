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
const_158587407969950000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_158587407969951000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_158587407969952000 == 
Permutations(const_158587407969950000) \union Permutations(const_158587407969951000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 19:34:39 CDT 2020 by seancribbs
