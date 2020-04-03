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
const_1585860124558185000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Consumers
const_1585860124558186000 == 
{c1, c2, c3, c4, c5}
----

\* SYMMETRY definition
symm_1585860124558187000 == 
Permutations(const_1585860124558185000) \union Permutations(const_1585860124558186000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 02 15:42:04 CDT 2020 by seancribbs
