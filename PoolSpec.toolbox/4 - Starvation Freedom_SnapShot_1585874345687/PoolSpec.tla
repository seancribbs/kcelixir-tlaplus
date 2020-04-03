------------------------------ MODULE PoolSpec ------------------------------
(* Our resource pool has a fixed set of resources, defined in the model. *)
CONSTANT Resources

(* Our resource pool has a fixed set of consumers, defined in the model. *)
CONSTANT Consumers

(* Abstract state of our model
 *   - state of each resource, either idle or claimed
 *   - what consumers own what resources *) 
VARIABLES resState,
          leases

(* An invariant that checks we never build a state that is invalid. 
   - All resources are always idle or claimed 
   - Every set of leases is a subset of the resources 
*)
TypeOK == /\ \A r \in Resources : resState[r] \in {"idle", "claimed"}
          /\ \A c \in Consumers : leases[c] \subseteq Resources

(* Starting state:
   - All resources are idle
   - All consumers have claimed no resources
 *)
Init == /\ resState = [r \in Resources |-> "idle"]
        /\ leases = [c \in Consumers |-> {}]

(* Checkout a resource.
   - The resource must be idle in the current state
   - In the next state, it is claimed and owned by the consumer *)
Checkout(r, c) == /\ resState[r] = "idle"
                  /\ resState' = [resState EXCEPT ![r] = "claimed"]
                  /\ leases' = [leases EXCEPT ![c] = leases[c] \union {r}]
                 
                             

(* Checkin a resource.
   - The resource must be claimed and it must be in a consumer's resources
   - In the next state, it is idle and no consumers own it
 *)  
Checkin(r) == /\ resState[r] = "claimed"
              /\ resState' = [resState EXCEPT ![r] = "idle"]
              /\ leases' = [c \in Consumers |-> leases[c] \ {r}]
             

(* Next state: For a resource, we either check it in or check it out to a consumer. *)
Next == \E r \in Resources : \/ Checkin(r) 
                             \/ \E c \in Consumers: Checkout(r, c)   

(* This is a convenience for the sake of our Spec definition, listing all variables. *)
vars == << resState, leases >>

(* Temporal specification:
   - The initial state holds, and
   - We can always move to a next state through an action or by changing nothing. *)
Spec == Init /\ [][Next]_vars

(****************************************************************************
 * Additional safety properties
 ****************************************************************************)

(* If a resource is checked out, it belongs to a consumer. 
   Otherwise, it is not claimed by any consumer. *)
ClaimedStateConsistent == \A r \in Resources: \/ /\ resState[r] = "claimed"
                                                 /\ \E c \in Consumers : r \in leases[c]
                                              \/ /\ resState[r] = "idle"
                                                 /\ \A c \in Consumers : r \notin leases[c]


(* Only one consumer may have a resource that is checked out, in other words,
   all sets of leases are disjoint from one another. *)
OnlyOneOwner == \A c \in Consumers: 
                    \A c2 \in Consumers: \/ c = c2
                                         \/ leases[c] \intersect leases[c2] = {}    

(****************************************************************************
 * Additional liveness properties
 ****************************************************************************)
 
(* If there is a resource that is claimed, on a future step it must eventually 
   transition back to the pool. *)
AllResourcesReturnToPool == \E r \in Resources: (resState[r] = "claimed") ~> (resState[r] = "idle")


(* We need a spec that allows for fairness in order for the above liveness properties to work. 
   Otherwise, we could sit forever in a state that all resources are checked out 
   (aka "stuttering")! *) 
FairSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Modification History
\* Last modified Thu Apr 02 19:38:25 CDT 2020 by seancribbs
=============================================================================
\* Created Thu Apr 02 12:18:37 CDT 2020 by seancribbs
