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
const_158587449737563000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_158587449737664000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_158587449737665000 == 
Permutations(const_158587449737563000) \union Permutations(const_158587449737664000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 19:41:37 CDT 2020 by seancribbs
