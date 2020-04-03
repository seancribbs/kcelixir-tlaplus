------------------------------ MODULE PoolSpec ------------------------------
(* Our resource pool has a fixed set of resources, defined in the model. *)
CONSTANT Resources

(* Our resource pool has a fixed set of consumers, defined in the model. *)
CONSTANT Consumers

(* Abstract state of our model
 *   - state of each resource
 *   - consumer ownership *) 
VARIABLES resState,
          leases

(* This is a convenience for the sake of our Spec definition at the bottom. *)
vars == << resState, leases >>

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
              /\ \E c \in Consumers : {r} \subseteq leases[c]
              /\ resState' = [resState EXCEPT ![r] = "idle"]
              /\ leases' = [c \in Consumers |-> leases[c] \ {r}] 

(* Next state: For a resource, we either check it in or check it out to a consumer. *)
Next == \E r \in Resources : \/ Checkin(r) 
                             \/ \E c \in Consumers: Checkout(r, c)   

(* Temporal specification:
   - Either we are in the initial state, or
   - We can always move to a next state through an action or by changing nothing. *)
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Apr 02 15:20:14 CDT 2020 by seancribbs
\* Created Thu Apr 02 12:18:37 CDT 2020 by seancribbs
