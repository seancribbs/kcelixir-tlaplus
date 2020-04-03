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
const_158587434265256000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_158587434265257000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_158587434265258000 == 
Permutations(const_158587434265256000) \union Permutations(const_158587434265257000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 19:39:02 CDT 2020 by seancribbs
